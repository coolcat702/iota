// diagnostic type used everywhere

use crate::parser::Span;

#[allow(unused)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
	Error,
	Warning,
	Advice,
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
	pub severity: Severity,
	pub message: String,
	pub span: Option<Span>,
	pub label: Option<String>,
	pub help: Option<String>,
}

impl Diagnostic {
	fn new(severity: Severity, message: impl Into<String>, span: Option<Span>) -> Self {
		Diagnostic {
			severity,
			message: message.into(),
			span,
			label: None,
			help: None,
		}
	}
	pub fn error(message: impl Into<String>, span: Option<Span>) -> Self {
		Self::new(Severity::Error, message, span)
	}
	#[allow(unused)]
	pub fn warning(message: impl Into<String>, span: Option<Span>) -> Self {
		Self::new(Severity::Warning, message, span)
	}
	#[allow(unused)]
	pub fn advice(message: impl Into<String>, span: Option<Span>) -> Self {
		Self::new(Severity::Advice, message, span)
	}
	pub fn with_help(mut self, help: impl Into<String>) -> Self {
		self.help = Some(help.into());
		self
	}
	pub fn with_label(mut self, label: impl Into<String>) -> Self {
		self.label = Some(label.into());
		self
	}
	pub fn is_error(&self) -> bool {
		self.severity == Severity::Error
	}
}

pub fn has_errors(ds: &[Diagnostic]) -> bool {
	ds.iter().any(Diagnostic::is_error)
}
