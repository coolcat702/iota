// 1. read lang manifest
// 2. parse prelude + every file imported from entry
// 3. typecheck everything together
// 4. lower to anf
// 5. specialize
// 6. optimize
// 7. backend (lower to mir, strictness analysis, refcount, llvm)
// 8. link
// 9. run

use std::{
	collections::HashMap,
	fs,
	panic::{catch_unwind, AssertUnwindSafe},
	path::{Path, PathBuf},
	process::{self, Command},
};

use ariadne::{Color, Label, Report, ReportKind};
use clap::{Parser, ValueEnum};

mod backend;
mod diag;
mod ir;
mod lang;
mod optimize;
mod parser;
mod spec;
mod typechecker;
mod types;
mod ui;

use backend::mir::{EntryKind, Facts, MProgram};
use diag::{has_errors, Diagnostic, Severity};
use lang::{Lang, LangItem};
use parser::{parse, Program, SourceRegistry, Span, Spanned, TopLevel};
use typechecker::{typecheck, Subst};
use types::TypeInfo;
use ui::stage;

// everything included in bin
const PRELUDE_SRC: &str = include_str!("../prelude/mod.iota");
const LANG_DEF: &str = include_str!("../prelude/lang.def");
const RUNTIME_C: &str = include_str!("../runtime/iota_rt.c");

struct Diag<'r> {
	registry: &'r mut SourceRegistry,
	errors: usize,
}

impl<'r> Diag<'r> {
	fn report(&mut self, d: &Diagnostic) {
		let (kind, color) = match d.severity {
			Severity::Error => (ReportKind::Error, Color::Red),
			Severity::Warning => (ReportKind::Warning, Color::Yellow),
			Severity::Advice => (ReportKind::Advice, Color::Blue),
		};
		if d.is_error() {
			self.errors += 1;
		}
		// synthetic
		match d.span.filter(|s| !(s.start == 0 && s.end == 0)) {
			Some(span) => {
				let mut label = Label::new(span).with_color(color);
				if let Some(l) = &d.label {
					label = label.with_message(l);
				}
				let mut report = Report::build(kind, span)
					.with_message(&d.message)
					.with_label(label);
				if let Some(h) = &d.help {
					report = report.with_help(h);
				}
				let _ = report.finish().eprint(&mut *self.registry);
			}
			None => {
				let (name, c) = match d.severity {
					Severity::Error => ("Error:", "\x1b[31m"),
					Severity::Warning => ("Warning:", "\x1b[33m"),
					Severity::Advice => ("Advice:", "\x1b[34m"),
				};
				eprintln!("{}{}\x1b[0m {}", c, name, d.message);
				if let Some(h) = &d.help {
					eprintln!("\x1b[36mHelp:\x1b[0m {}", h);
				}
			}
		}
	}

	fn report_all(&mut self, ds: &[Diagnostic]) {
		for d in ds {
			self.report(d);
		}
	}

	fn error(&mut self, msg: impl Into<String>, span: Option<Span>, help: Option<&str>) {
		let mut d = Diagnostic::error(msg, span);
		if let Some(h) = help {
			d = d.with_help(h);
		}
		self.report(&d);
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum Stage {
	/// Parse and type-check.
	Check,
	/// Print the typed, optimized ANF IR.
	Ir,
	/// Print the monomorphic, reference-counted MIR.
	Mir,
	/// Write LLVM IR.
	Llvm,
	/// Build an executable (the default).
	Exe,
}

#[derive(Parser, Debug)]
#[command(name = "iota", version, about = "The Iota compiler")]
struct Cli {
	/// Entry point source file
	file: PathBuf,

	/// How far to go
	#[arg(long, value_enum, default_value_t = Stage::Exe)]
	emit: Stage,

	/// Output path: the executable, or the `.ll` file with `--emit llvm`
	/// Defaults to build/[exe] where exe is the input file stripped of its extension.
	#[arg(short, long)]
	output: Option<PathBuf>,

	/// Run the program after building it (exit status is the program's)
	#[arg(short, long)]
	run: bool,

	/// Optimization strategy: `off` leaves the IR exactly as specialization
	/// produced it; `standard` runs the local per-function fixpoint (constant
	/// folding, copy propagation, CSE, DCE, case-of-known-value, float-in);
	/// `aggressive` (the default) also inlines and partially evaluates calls to
	/// known functions, whole-program, within a bounded effort budget — worth it
	/// under lazy evaluation, where it turns calls like `cond` into plain branches
	/// and removes the thunks their arguments would become
	#[arg(long, value_enum, default_value_t = optimize::OptimizeMode::Aggressive)]
	opt_mode: optimize::OptimizeMode,

	/// With `--emit ir`: also print the IR before optimization
	#[arg(long)]
	show_unoptimized: bool,

	/// Entry point; defaults to the manifest's `entry` (`Main:main`)
	#[arg(long)]
	entry: Option<String>,

	/// Use this prelude instead of the one built into the compiler
	#[arg(long, value_name = "FILE")]
	prelude: Option<PathBuf>,

	/// Use this lang manifest (which prelude entities play which role) instead of
	/// the built-in `prelude/lang.def`
	#[arg(long, value_name = "FILE")]
	lang: Option<PathBuf>,

	/// C compiler used to turn the LLVM IR into an executable (must be clang,
	/// or accept `.ll` files)
	#[arg(long, env = "IOTA_CC", default_value = "clang")]
	cc: String,

	/// Optimization level handed to the C compiler
	#[arg(long, default_value = "-O2", allow_hyphen_values = true)]
	cc_opt: String,

	/// Keep the intermediate `.ll` next to the executable
	#[arg(long)]
	keep_ll: bool,

	/// Narrate each stage (and how long it took) on stderr
	#[arg(short, long)]
	verbose: bool,

	/// Print parser debug output
	#[arg(short, long)]
	parse_debug: bool,

	/// Print type-checker debug output
	#[arg(short, long)]
	type_debug: bool,

	/// Suppress progress output (errors are still shown)
	#[arg(short, long)]
	quiet: bool,
}

struct Loader<'r, 'd> {
	diag: &'d mut Diag<'r>,
	loaded: HashMap<PathBuf, Program>,
	order: Vec<PathBuf>,
	failed: bool,
	debug: bool,
}

impl<'r, 'd> Loader<'r, 'd> {
	fn new(diag: &'d mut Diag<'r>, debug: bool) -> Self {
		Self {
			diag,
			loaded: HashMap::new(),
			order: Vec::new(),
			failed: false,
			debug,
		}
	}

	fn io_error(&mut self, msg: String, span: Option<Span>) {
		self.diag.error(msg, span, None);
		self.failed = true;
	}

	fn load(&mut self, path: &Path, import_span: Option<Span>) {
		let canonical = match path.canonicalize() {
			Ok(p) => p,
			Err(e) => {
				return self.io_error(
					format!("cannot open '{}': {}", path.display(), e),
					import_span,
				)
			}
		};
		if self.loaded.contains_key(&canonical) {
			return;
		}
		let (source_id, _) = match self.diag.registry.load_file(&canonical) {
			Ok(x) => x,
			Err(e) => {
				return self.io_error(
					format!("cannot read '{}': {}", canonical.display(), e),
					import_span,
				)
			}
		};
		let program = match parse(self.diag.registry, source_id, self.debug) {
			Ok(p) => p,
			Err(ds) => {
				self.diag.report_all(&ds);
				self.failed = true;
				return;
			}
		};
		let imports = collect_file_imports(&program);
		self.loaded.insert(canonical.clone(), program);
		self.order.push(canonical.clone());

		let dir = canonical
			.parent()
			.map(Path::to_path_buf)
			.unwrap_or_else(|| PathBuf::from("."));
		for (import_name, span) in imports {
			match resolve_import(&dir, &import_name) {
				Some(found) => self.load(&found, Some(span)),
				None => {
					self.diag.error(
						format!("import '{}' not found (searched in '{}')", import_name, dir.display()),
						Some(span),
						Some("check the file name, or that `<name>/mod.iota` exists if this is meant to be a directory module"),
					);
					self.failed = true;
				}
			}
		}
	}
}

// `import file utils.iota` means utils.iota OR utils/mod.iota
fn resolve_import(dir: &Path, name: &str) -> Option<PathBuf> {
	let as_file = dir.join(name);
	if as_file.is_file() {
		return Some(as_file);
	}
	let stem = name.strip_suffix(".iota").unwrap_or(name);
	let as_dir = dir.join(stem).join("mod.iota");
	as_dir.is_file().then_some(as_dir)
}

fn collect_file_imports(program: &Program) -> Vec<(String, Span)> {
	fn go(item: &Spanned<TopLevel>, out: &mut Vec<(String, Span)>) {
		match &item.item {
			TopLevel::Module(_, body) => body.iter().for_each(|c| go(c, out)),
			TopLevel::ImportFile(name) => out.push((name.clone(), item.span)),
			_ => {}
		}
	}
	let mut out = Vec::new();
	program.0.iter().for_each(|i| go(i, &mut out));
	out
}

// rust panics VERY BAD for user
fn guarded<T>(diag: &mut Diag, what: &str, f: impl FnOnce() -> T) -> Option<T> {
	match catch_unwind(AssertUnwindSafe(f)) {
		Ok(v) => Some(v),
		Err(p) => {
			let msg = p
				.downcast_ref::<String>()
				.cloned()
				.or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
				.unwrap_or_else(|| "unknown panic".to_string());
			diag.error(
				format!("internal compiler error in {}: {}", what, msg),
				None,
				Some("this is a bug in the Iota compiler -- You didn't fuck up, I did"),
			);
			None
		}
	}
}

fn report_mir_errors(diag: &mut Diag, mir: &MProgram, stage: &str) -> bool {
	let errs = backend::check::check(mir, stage);
	for e in &errs {
		diag.error(
			format!("internal compiler error: inconsistent MIR: {}", e),
			None,
			Some("this is a bug in the Iota compiler -- You didn't fuck up, I did"),
		);
	}
	errs.is_empty()
}

fn dump_mir(m: &MProgram) {
	let facts = Facts { datas: &m.datas };
	println!("=== data types ({}) ===", m.datas.len());
	for (i, d) in m.datas.iter().enumerate() {
		let layout = if d.is_enum() {
			"enum (tag only)".to_string()
		} else if d.is_wide() {
			"wide: tag in header".to_string()
		} else {
			"pointer-tagged".to_string()
		};
		println!("  #{} {} — {}", i, d.name, layout);
		for (ci, c) in d.ctors.iter().enumerate() {
			match &c.payload {
				Some(p) => println!(
					"      {} : {:?}  ({} bytes on the heap{})",
					c.name,
					p,
					facts.obj_size(i, ci),
					if c.packed.iter().any(|b| *b) {
						", packed fields"
					} else {
						""
					}
				),
				None => println!("      {} (immediate)", c.name),
			}
		}
	}
	println!("\n=== instances ({}) ===", m.funcs.len());
	for f in &m.funcs {
		let ps: Vec<String> = f
			.params
			.iter()
			.zip(f.borrowed.iter())
			.map(|((n, t), b)| format!("{}{}: {:?}", if *b { "&" } else { "" }, n, t))
			.collect();
		println!(
			"  {}({}) -> {:?}{}",
			f.name,
			ps.join(", "),
			f.ret,
			if f.caf { "   [cached constant]" } else { "" }
		);
	}
	println!(
		"\nentry: {} ({})",
		m.entry,
		if m.entry_kind == EntryKind::Action {
			"IO action"
		} else {
			"value"
		}
	);
}

fn link(cli: &Cli, diag: &mut Diag, ll: &Path, exe: &Path) -> bool {
	let dir = std::env::temp_dir().join(format!("iota-{}", process::id()));
	if let Err(e) = fs::create_dir_all(&dir) {
		diag.error(
			format!("cannot create temporary directory {}: {}", dir.display(), e),
			None,
			None,
		);
		return false;
	}
	let rt = dir.join("iota_rt.c");
	if let Err(e) = fs::write(&rt, RUNTIME_C) {
		diag.error(format!("cannot write the runtime: {}", e), None, None);
		return false;
	}
	let status = Command::new(&cli.cc)
		.arg(&cli.cc_opt)
		.arg("-Wno-override-module")
		.arg(ll)
		.arg(&rt)
		.arg("-o")
		.arg(exe)
		.arg("-lm")
		.status();
	let _ = fs::remove_dir_all(&dir);
	match status {
		Ok(s) if s.success() => true,
		Ok(s) => {
			diag.error(
				format!("`{}` failed ({})", cli.cc, s),
				None,
				Some("the generated LLVM IR may be invalid (re-run with --emit llvm and --keep-ll to inspect it)"),
			);
			false
		}
		Err(e) => {
			diag.error(
				format!("could not run `{}`: {}", cli.cc, e),
				None,
				Some(
					"install clang, or point --cc / $IOTA_CC at a compiler that accepts .ll files",
				),
			);
			false
		}
	}
}

fn main() {
	let cli = Cli::parse();
	ui::init(cli.quiet);
	// big stack size -- a long let chain is as deep as it is long (bc recursion)
	let worker = std::thread::Builder::new()
		.stack_size(1 << 30)
		.spawn(move || {
			let mut registry = SourceRegistry::new();
			let mut diag = Diag {
				registry: &mut registry,
				errors: 0,
			};
			compile(&cli, &mut diag)
		});
	let status = match worker.map(|h| h.join()) {
		Ok(Ok(code)) => code,
		Ok(Err(_)) => 101,
		Err(e) => {
			eprintln!("error: cannot start the compiler thread: {}", e);
			1
		}
	};
	process::exit(status);
}

fn compile(cli: &Cli, diag: &mut Diag) -> i32 {
	if !cli.file.exists() {
		diag.error(
			format!("file '{}' not found", cli.file.display()),
			None,
			None,
		);
		return 1;
	}

	ui::header(&cli.file.display().to_string());

	// 1. lang manifest
	let (lang_name, lang_src) = match &cli.lang {
		Some(p) => match fs::read_to_string(p) {
			Ok(s) => (p.display().to_string(), s),
			Err(e) => {
				diag.error(
					format!("cannot read lang manifest '{}': {}", p.display(), e),
					None,
					None,
				);
				return 1;
			}
		},
		None => ("<prelude>/lang.def".to_string(), LANG_DEF.to_string()),
	};
	let lang = match Lang::parse(&lang_src, &lang_name) {
		Ok(l) => l,
		Err(msgs) => {
			for m in msgs {
				diag.error(m, None, None);
			}
			return 1;
		}
	};
	let entry = cli
		.entry
		.clone()
		.unwrap_or_else(|| lang.item(LangItem::Entry).to_string());

	// 2. parse
	let t = stage(cli.verbose, "parse");
	let (prelude_name, prelude_src) = match &cli.prelude {
		Some(p) => match fs::read_to_string(p) {
			Ok(s) => (p.display().to_string(), s),
			Err(e) => {
				diag.error(
					format!("cannot read prelude '{}': {}", p.display(), e),
					None,
					None,
				);
				return 1;
			}
		},
		None => ("<prelude>/mod.iota".to_string(), PRELUDE_SRC.to_string()),
	};
	let prelude_id = diag.registry.add(prelude_name, prelude_src);
	let prelude_program = match parse(diag.registry, prelude_id, cli.parse_debug) {
		Ok(p) => p,
		Err(ds) => {
			diag.report_all(&ds);
			diag.error("the prelude failed to parse (see above)", None, None);
			return 1;
		}
	};

	let (load_failed, user_programs): (bool, Vec<Program>) = {
		let mut loader = Loader::new(diag, cli.parse_debug);
		loader.load(&cli.file, None);
		let progs = loader
			.order
			.iter()
			.filter_map(|p| loader.loaded.remove(p))
			.collect();
		(loader.failed, progs)
	};
	if load_failed {
		diag.error("could not load every required file (see above)", None, None);
		return 1;
	}
	let file_count = user_programs.len();
	t.done(format!(
		" ({} user file{})",
		file_count,
		if file_count == 1 { "" } else { "s" }
	));

	let mut items = prelude_program.0;
	for p in user_programs {
		items.extend(p.0);
	}
	let combined = Spanned {
		item: Program(items),
		span: Span::synthetic(prelude_id),
	};

	// 3. typecheck
	let t = stage(cli.verbose, "typecheck");
	let (env, typed, tc_diags) = typecheck(&combined, diag.registry);
	diag.report_all(&tc_diags);
	if has_errors(&tc_diags) {
		diag.error("type-checking failed (see above)", None, None);
		return 1;
	}
	t.done(format!(" ({} top-level bindings)", typed.len()));
	if cli.type_debug {
		for tb in &typed {
			eprintln!(
				"[type] {} | {}",
				tb.span.source_id,
				tb.item
					.scheme
					.display_full(&tb.item.name, &Subst::default())
			);
		}
	}
	if cli.emit == Stage::Check {
		return 0;
	}

	// 4. lower to anf
	let t = stage(cli.verbose, "lower to IR");
	let (generic, overloads) = match ir::lower_program(&typed, &env, &lang) {
		Ok(x) => x,
		Err(ds) => {
			diag.report_all(&ds);
			return 1;
		}
	};
	t.done(format!(
		" ({} functions, {} externs)",
		generic.functions.len(),
		generic.externs.len()
	));
	if let Err(d) = optimize::check_entry(&generic, &entry, &lang) {
		diag.report(&d);
		return 1;
	}

	// 5. specialize
	let t = stage(cli.verbose, "specialize");
	let ti = TypeInfo::new(&env);
	let mut program = match spec::specialize(&generic, &overloads, &ti, &lang, &entry) {
		Ok(p) => p,
		Err(ds) => {
			diag.report_all(&ds);
			return 1;
		}
	};
	t.done(format!(" ({} instances)", program.functions.len()));
	if cli.emit == Stage::Ir && cli.show_unoptimized {
		println!(
			"=== monomorphic typed IR (before optimization) ===\n\n{}",
			program
		);
	}

	// 6. optimize
	let t = stage(cli.verbose, "optimize");
	optimize::optimize(&mut program, cli.opt_mode, &lang);
	optimize::prune_unreachable(&mut program, &entry);
	t.done(format!(
		" (mode {:?}, {} instances left)",
		cli.opt_mode,
		program.functions.len()
	));
	if cli.emit == Stage::Ir {
		let heading = match cli.opt_mode {
			optimize::OptimizeMode::Off => "monomorphic typed IR (optimization off)",
			optimize::OptimizeMode::Standard => "monomorphic typed IR (optimized)",
			optimize::OptimizeMode::Aggressive => "monomorphic typed IR (aggressively optimized)",
		};
		println!("=== {} ===\n\n{}", heading, program);
		return 0;
	}

	// 7. backend
	let t = stage(cli.verbose, "lower to MIR");
	let lowered = guarded(diag, "lowering to MIR", || {
		backend::lower::lower(&program, &ti, &lang, &entry)
	});
	let mut mir = match lowered {
		Some(Ok(m)) => m,
		Some(Err(ds)) => {
			diag.report_all(&ds);
			return 1;
		}
		None => return 1,
	};
	t.done(format!(
		" ({} functions, {} data types)",
		mir.funcs.len(),
		mir.datas.len()
	));

	if !report_mir_errors(diag, &mir, "after lowering") {
		return 1;
	}

	let t = stage(cli.verbose, "strictness analysis");
	if guarded(diag, "lazification", || backend::lazy::run(&mut mir)).is_none() {
		return 1;
	}
	let strict: usize = mir
		.funcs
		.iter()
		.map(|f| f.params.iter().filter(|(_, t)| !t.is_susp()).count())
		.sum();
	let total: usize = mir.funcs.iter().map(|f| f.params.len()).sum();
	t.done(format!(" ({} of {} parameters strict)", strict, total));

	if !report_mir_errors(diag, &mir, "after strictness analysis") {
		return 1;
	}

	let t = stage(cli.verbose, "reference counting");
	if guarded(diag, "reference counting", || {
		backend::refcount::run(&mut mir)
	})
	.is_none()
	{
		return 1;
	}
	let borrowed: usize = mir
		.funcs
		.iter()
		.map(|f| f.borrowed.iter().filter(|b| **b).count())
		.sum();
	t.done(format!(" ({} borrowed parameters)", borrowed));
	if cli.emit == Stage::Mir {
		dump_mir(&mir);
		return 0;
	}

	let stem = cli
		.file
		.file_stem()
		.map(|s| s.to_string_lossy().into_owned())
		.unwrap_or_else(|| "a".to_string());
	let exe = cli
		.output
		.clone()
		.unwrap_or_else(|| PathBuf::from(format!("./build/{}", stem)));
	let ll = exe.with_extension("ll");
	let t = stage(cli.verbose, "LLVM codegen");
	match guarded(diag, "code generation", || {
		backend::codegen::write_ll(&mir, &ll)
	}) {
		Some(Ok(())) => {}
		Some(Err(d)) => {
			diag.report(&d);
			return 1;
		}
		None => return 1,
	}
	t.done(format!(" -> {}", ll.display()));
	if cli.emit == Stage::Llvm {
		return 0;
	}

	// 8. link
	let t = stage(cli.verbose, "link");
	let linked = link(cli, diag, &ll, &exe);
	if !cli.keep_ll {
		let _ = fs::remove_file(&ll);
	}
	if !linked {
		return 1;
	}
	t.done(format!(" -> {}", exe.display()));

	ui::finished(&exe);

	// 9. run
	if cli.run {
		let path = if exe.is_absolute() || exe.components().count() > 1 {
			exe.clone()
		} else {
			PathBuf::from(".").join(&exe)
		};

		ui::running(&path);

		return match Command::new(&path).status() {
			Ok(s) => s.code().unwrap_or(1),
			Err(e) => {
				diag.error(
					format!("could not run {}: {}", path.display(), e),
					None,
					None,
				);
				1
			}
		};
	}
	0
}
