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
	time::Instant,
};

use ariadne::{Color, Label, Report, ReportKind};
use clap::{Parser, ValueEnum};

mod backend;
mod diag;
mod ir;
mod lang;
mod lift_spec;
mod optimize;
mod parser;
mod rtprims;
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

	/// Arguments passed to the program with `--run` (after `--`)
	#[arg(last = true)]
	program_args: Vec<String>,

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

	#[arg(long, short)]
	verbose: bool,

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

	/// Print parser debug output
	#[arg(short, long)]
	parse_debug: bool,

	/// Print type-checker debug output
	#[arg(short, long)]
	type_debug: bool,

	/// Suppress progress output (errors are still shown)
	#[arg(short, long)]
	quiet: bool,

	#[arg(long, env = "IOTA_LD")]
	ld: Option<String>,
}

/// The standard library: `import file std/<name>.iota` falls back to these when the project
/// has no such file of its own.
const STD_FILES: &[(&str, &str)] = &[
	("std/str.iota", include_str!("../std/str.iota")),
	("std/path.iota", include_str!("../std/path.iota")),
	("std/fs.iota", include_str!("../std/fs.iota")),
	("std/sort.iota", include_str!("../std/sort.iota")),
	("std/search.iota", include_str!("../std/search.iota")),
	("std/hashmap.iota", include_str!("../std/hashmap.iota")),
	("std/hashset.iota", include_str!("../std/hashset.iota")),
	("std/json.iota", include_str!("../std/json.iota")),
	("std/time.iota", include_str!("../std/time.iota")),
	("std/rng.iota", include_str!("../std/rng.iota")),
	("std/process.iota", include_str!("../std/process.iota")),
	("std/ansi.iota", include_str!("../std/ansi.iota")),
	("std/term.iota", include_str!("../std/term.iota")),
];

fn std_source(name: &str) -> Option<&'static str> {
	STD_FILES.iter().find(|(n, _)| *n == name).map(|(_, s)| *s)
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

	/// A file of the embedded standard library (it can only import other std files).
	fn load_embedded(&mut self, name: &str, import_span: Option<Span>) {
		let Some(src) = std_source(name) else {
			return self.io_error(format!("no standard library file '{}'", name), import_span);
		};
		let key = PathBuf::from(format!("<std>/{}", name));
		if self.loaded.contains_key(&key) {
			return;
		}
		let source_id = self.diag.registry.add(format!("<{}>", name), src.to_string());
		let program = match parse(self.diag.registry, source_id, self.debug) {
			Ok(p) => p,
			Err(ds) => {
				self.diag.report_all(&ds);
				self.failed = true;
				return;
			}
		};
		let imports = collect_file_imports(&program);
		self.loaded.insert(key.clone(), program);
		for (import_name, span) in imports {
			self.load_embedded(&import_name, Some(span));
		}
		self.order.push(key);
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
		// registered now (so import cycles stop here) but ordered after its imports: type names
		// are global, so a file's imports must come before it
		self.loaded.insert(canonical.clone(), program);

		let dir = canonical
			.parent()
			.map(Path::to_path_buf)
			.unwrap_or_else(|| PathBuf::from("."));
		for (import_name, span) in imports {
			match resolve_import(&dir, &import_name) {
				Some(found) => self.load(&found, Some(span)),
				None if std_source(&import_name).is_some() => {
					self.load_embedded(&import_name, Some(span))
				}
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
		self.order.push(canonical);
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

fn cache_dir() -> PathBuf {
	let base = std::env::var_os("XDG_CACHE_HOME")
		.map(PathBuf::from)
		.or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cache")))
		.unwrap_or_else(std::env::temp_dir);
	base.join("iota")
}

// The runtime only changes when iota_rt.c (or the compiler flags) change, so it is
// built once. Returns the path of the object file.
fn runtime_object(cli: &Cli, diag: &mut Diag) -> Option<PathBuf> {
	use std::hash::{Hash, Hasher};
	let mut h = std::collections::hash_map::DefaultHasher::new();
	RUNTIME_C.hash(&mut h);
	cli.cc.hash(&mut h);
	cli.cc_opt.hash(&mut h);
	let dir = cache_dir();
	let obj = dir.join(format!("iota_rt-{:016x}.o", h.finish()));
	if obj.is_file() {
		return Some(obj);
	}
	if let Err(e) = fs::create_dir_all(&dir) {
		diag.error(
			format!("cannot create cache directory {}: {}", dir.display(), e),
			None,
			None,
		);
		return None;
	}
	// build under a private name, then rename: another compiler running at the
	// same time never sees a half-written object
	let tmp_c = dir.join(format!("iota_rt-{}.c", process::id()));
	let tmp_o = dir.join(format!("iota_rt-{}.o", process::id()));
	if let Err(e) = fs::write(&tmp_c, RUNTIME_C) {
		diag.error(format!("cannot write the runtime: {}", e), None, None);
		return None;
	}
	let status = Command::new(&cli.cc)
		.arg(&cli.cc_opt)
		.arg("-c")
		.arg(&tmp_c)
		.arg("-o")
		.arg(&tmp_o)
		.status();
	let _ = fs::remove_file(&tmp_c);
	match status {
		Ok(s) if s.success() => {
			if fs::rename(&tmp_o, &obj).is_err() {
				// lost a race or cannot rename: use what we built
				return if obj.is_file() {
					Some(obj)
				} else {
					Some(tmp_o)
				};
			}
			Some(obj)
		}
		Ok(s) => {
			let _ = fs::remove_file(&tmp_o);
			diag.error(
				format!("`{}` failed to compile the runtime ({})", cli.cc, s),
				None,
				None,
			);
			None
		}
		Err(e) => {
			diag.error(
				format!("could not run `{}`: {}", cli.cc, e),
				None,
				Some("install clang, or point --cc / $IOTA_CC at a C compiler"),
			);
			None
		}
	}
}

fn run_cc(cli: &Cli, diag: &mut Diag, cmd: &mut Command, what: &str, hint: Option<&str>) -> bool {
	match cmd.status() {
		Ok(s) if s.success() => true,
		Ok(s) => {
			diag.error(
				format!("`{}` failed while {} ({})", cli.cc, what, s),
				None,
				hint,
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

fn link(cli: &Cli, diag: &mut Diag, ll: &Path, exe: &Path) -> bool {
	let t = Instant::now();
	let Some(rt) = runtime_object(cli, diag) else {
		return false;
	};
	let t_rt = t.elapsed();

	// LLVM module -> object
	let obj = exe.with_extension("o");
	let t = Instant::now();
	let ok = run_cc(
		cli,
		diag,
		Command::new(&cli.cc)
			.arg(&cli.cc_opt)
			.arg("-Wno-override-module")
			.arg("-c")
			.arg(ll)
			.arg("-o")
			.arg(&obj),
		"compiling the generated LLVM IR",
		Some("the generated LLVM IR may be invalid (re-run with --emit llvm and --keep-ll to inspect it)"),
	);
	if !ok {
		return false;
	}
	let t_mod = t.elapsed();

	// link
	let t = Instant::now();
	let mut cmd = Command::new(&cli.cc);
	cmd.arg(&obj).arg(&rt).arg("-o").arg(exe).arg("-lm");
	if let Some(ld) = &cli.ld {
		cmd.arg(format!("-fuse-ld={}", ld));
	}
	let ok = run_cc(cli, diag, &mut cmd, "linking", None);
	let _ = fs::remove_file(&obj);
	if !ok {
		return false;
	}
	let t_ld = t.elapsed();

	if cli.verbose {
		eprintln!(
			"[iota]   link: runtime {:.0?}, module {:.0?}, ld {:.0?}",
			t_rt, t_mod, t_ld
		);
	}
	true
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

/// An entry point of type `List String -> IO Int` (or `IO Unit`) gets the command line
/// arguments: this adds a zero-parameter entry `Prelude:entry_with_args = with_args main`
/// and returns its name. Any other entry type is left for `check_entry` to judge.
fn wrap_entry_args(program: &mut ir::IrProgram, entry: &str, lang: &Lang) -> Option<String> {
	use ir::{Atom, Expr, Function, Value};
	use typechecker::Ty;
	let f = program.functions.iter().find(|f| f.name == entry)?;
	// `let main : List String -> IO Int = fn argv -> ... end` is lowered with one parameter;
	// a point-free definition has none and a function type as its result
	let (arg, res): (Ty, Ty) = match (f.params.as_slice(), &f.ret) {
		([(_, a)], r) => (a.clone(), r.clone()),
		([], Ty::Fn(a, r)) => ((**a).clone(), (**r).clone()),
		_ => return None,
	};
	let (arg, res) = (&arg, &res);
	let is_io_of_status = matches!(res, Ty::App(h, a)
		if matches!(h.as_ref(), Ty::Named(n) if n == lang.item(LangItem::IoType))
			&& matches!(a.as_ref(), Ty::Unit | Ty::Int));
	let list = lang.item(LangItem::ListType);
	let is_string_list = matches!(arg, Ty::App(h, a)
		if matches!(h.as_ref(), Ty::Named(n) if n == list)
			&& (matches!(a.as_ref(), Ty::Named(s) if s == "String")
				|| matches!(a.as_ref(), Ty::App(h2, c)
					if matches!(h2.as_ref(), Ty::Named(n) if n == list) && matches!(c.as_ref(), Ty::Char))));
	if !is_io_of_status || !is_string_list {
		return None;
	}
	let (fty, res) = (Ty::Fn(Box::new(arg.clone()), Box::new(res.clone())), res.clone());
	let with_args_ty = Ty::Fn(Box::new(fty.clone()), Box::new(res.clone()));
	let name = "Prelude:entry_with_args".to_string();
	let body = Expr::Let(
		"main".into(),
		fty.clone(),
		Value::Atom(Atom::Global(entry.to_string(), fty)),
		Box::new(Expr::Let(
			"r".into(),
			res.clone(),
			Value::App(
				Atom::Global("Prelude:with_args".into(), with_args_ty),
				Atom::Var("main".into()),
			),
			Box::new(Expr::Halt(Atom::Var("r".into()))),
		)),
	);
	let span = f.span;
	program.functions.push(Function {
		name: name.clone(),
		params: vec![],
		ret: res.clone(),
		ty: res,
		body,
		span,
	});
	Some(name)
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
	let t = stage("parse");
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
	let t = stage("typecheck");
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
	let t = stage("lower to IR");
	let (mut generic, overloads) = match ir::lower_program(&typed, &env, &lang) {
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
	let entry = wrap_entry_args(&mut generic, &entry, &lang).unwrap_or(entry);
	if let Err(d) = optimize::check_entry(&generic, &entry, &lang) {
		diag.report(&d);
		return 1;
	}

	// 5. specialize
	let t = stage("specialize");
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
	let t = stage("optimize");
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
	let t = stage("lower to MIR");
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

	let t = stage("strictness analysis");
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

	let t = stage("reference counting");
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
	let t = stage("LLVM codegen");
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
	let t = stage("link");
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

		return match Command::new(&path).args(&cli.program_args).status() {
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
