// Progress output. Everything on stderr so stdout is clean for piping

use std::io::IsTerminal;
use std::path::Path;
use std::sync::OnceLock;
use std::time::Instant;

struct Ui {
	quiet: bool,
	color: bool,
	started: Instant,
}

static UI: OnceLock<Ui> = OnceLock::new();

pub fn init(quiet: bool) {
	let color = std::io::stderr().is_terminal() && std::env::var_os("NO_COLOR").is_none();
	let _ = UI.set(Ui {
		quiet,
		color,
		started: Instant::now(),
	});
}

fn ui() -> &'static Ui {
	UI.get_or_init(|| Ui {
		quiet: false,
		color: false,
		started: Instant::now(),
	})
}

fn paint(code: &str, s: &str) -> String {
	if ui().color {
		format!("\x1b[{}m{}\x1b[0m", code, s)
	} else {
		s.to_string()
	}
}

const BOLD: &str = "1";
const DIM: &str = "2";
const BOLD_RED: &str = "1;31";
const BOLD_GREEN: &str = "1;32";
const BOLD_CYAN: &str = "1;36";

pub fn header(file: &str) {
	if ui().quiet {
		return;
	}
	eprintln!(
		"{} {} {}",
		paint(BOLD_CYAN, "▸"),
		paint(BOLD, "Compiling"),
		file
	);
}

pub fn finished(out: &Path) {
	if ui().quiet {
		return;
	}
	eprintln!(
		"{} {} {}  {}",
		paint(BOLD_GREEN, "✓"),
		paint(BOLD_GREEN, "Finished"),
		paint(DIM, &format!("in {:.2?}", ui().started.elapsed())),
		paint(DIM, &format!("→ {}", out.display())),
	);
}

pub fn running(path: &Path) {
	if ui().quiet {
		return;
	}
	eprintln!(
		"{} {} {}",
		paint(BOLD_CYAN, "▸"),
		paint(BOLD, "Running"),
		path.display()
	);
}

pub struct Timer {
	label: &'static str,
	start: Instant,
	finished: bool,
}

// Same signature as old helper, so existing call sites don't change.
// verbose prints a "starting" line
pub fn stage(verbose: bool, label: &'static str) -> Timer {
	if verbose && !ui().quiet {
		eprintln!("  {} {}", paint(DIM, "…"), paint(DIM, label));
	}
	Timer {
		label,
		start: Instant::now(),
		finished: false,
	}
}

impl Timer {
	pub fn done(mut self, detail: impl AsRef<str>) {
		self.finished = true;
		if ui().quiet {
			return;
		}
		// call sites pass things like " (12 functions, 3 externs)"
		let detail = detail
			.as_ref()
			.trim()
			.trim_start_matches('(')
			.trim_end_matches(')');
		let time = format!("{:.1?}", self.start.elapsed());
		eprintln!(
			"  {} {} {}  {}",
			paint(BOLD_GREEN, "✓"),
			paint(BOLD, &format!("{:<20}", self.label)),
			paint(DIM, &format!("{:>8}", time)),
			detail
		);
	}
}

// Stage that returns early without calling done failed
impl Drop for Timer {
	fn drop(&mut self) {
		if !self.finished && !ui().quiet {
			eprintln!(
				"  {} {}",
				paint(BOLD_RED, "✗"),
				paint(BOLD_RED, &format!("{} failed", self.label))
			);
		}
	}
}
