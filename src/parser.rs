// Parse program file to AST

use std::collections::HashMap;
use std::fmt;
use std::fs;
use std::path::Path;

use crate::diag::Diagnostic;
use ariadne::{Cache, Source};
use logos::Logos;
use serde::Serialize;

pub struct SourceRegistry {
	sources: Vec<(String, String)>,
	cache: HashMap<usize, Source>,
}

impl Default for SourceRegistry {
	fn default() -> Self {
		Self {
			sources: Vec::new(),
			cache: HashMap::new(),
		}
	}
}

impl SourceRegistry {
	pub fn new() -> Self {
		Self::default()
	}

	pub fn add(&mut self, filename: impl Into<String>, content: impl Into<String>) -> usize {
		let id = self.sources.len();
		self.sources.push((filename.into(), content.into()));
		id
	}

	pub fn load_file(&mut self, path: impl AsRef<Path>) -> std::io::Result<(usize, String)> {
		let path = path.as_ref();
		let content = fs::read_to_string(path)?;
		let filename = path.to_string_lossy().into_owned();
		let id = self.add(filename, content.clone());
		Ok((id, content))
	}

	pub fn filename(&self, id: usize) -> &str {
		self.sources
			.get(id)
			.map(|(f, _)| f.as_str())
			.unwrap_or("<unknown>")
	}

	pub fn content(&self, id: usize) -> &str {
		self.sources.get(id).map(|(_, c)| c.as_str()).unwrap_or("")
	}
}

impl Cache<usize> for SourceRegistry {
	type Storage = String;

	fn fetch(&mut self, id: &usize) -> Result<&Source<Self::Storage>, impl fmt::Debug> {
		if !self.cache.contains_key(id) {
			let content = self
				.sources
				.get(*id)
				.map(|(_, c)| c.clone())
				.unwrap_or_default();
			self.cache.insert(*id, Source::from(content));
		}
		Ok::<_, String>(&self.cache[id])
	}

	fn display<'a>(&self, id: &'a usize) -> Option<impl fmt::Display + 'a> {
		self.sources.get(*id).map(|(filename, _)| filename.clone())
	}
}

fn decode_escapes(s: &str) -> String {
	let mut out = String::with_capacity(s.len());
	let mut chars = s.chars();
	while let Some(c) = chars.next() {
		if c != '\\' {
			out.push(c);
			continue;
		}
		match chars.next() {
			Some('n') => out.push('\n'),
			Some('t') => out.push('\t'),
			Some('r') => out.push('\r'),
			Some('0') => out.push('\0'),
			Some('\\') => out.push('\\'),
			Some('\'') => out.push('\''),
			Some('"') => out.push('"'),
			Some(other) => out.push(other),
			None => out.push('\\'),
		}
	}
	out
}

#[derive(Logos, Debug, PartialEq, Clone)]
enum Token {
	#[regex(r"[a-zA-Z][a-zA-Z0-9_\-.]*", |lex| lex.slice().to_string())]
	Ident(String),

	#[token("let")]
	Let,
	#[token("end")]
	End,
	#[token("type")]
	TypeKw,
	#[token("class")]
	Class,
	#[token("instance")]
	Instance,
	#[token("module")]
	Module,
	#[token("file")]
	File,
	#[token("import")]
	Import,
	#[token("export")]
	Export,
	#[token("unqualified")]
	Unqualified,
	#[token("match")]
	Match,
	#[token("with")]
	With,
	#[token("fn")]
	FnKw,
	#[token("is")]
	Is,
	#[token("undefined")]
	Undefined,
	#[token(":")]
	Colon,
	#[token("=")]
	Eq,
	#[token("->")]
	Arrow,
	#[token("*")]
	Star,
	#[token("+")]
	Plus,
	#[token(",")]
	Comma,
	#[token("_")]
	Underscore,

	#[regex(r#""([^"\\]|\\.)*""#, |lex| {
        let slice = lex.slice();
        decode_escapes(&slice[1..slice.len()-1])
    })]
	StringLit(String),

	#[regex(r"[-+]?[0-9]+", |lex| lex.slice().parse::<i32>().unwrap())]
	IntLit(i32),

	#[regex(r"[-+]?[0-9]*(?:\.[0-9]+)", |lex| lex.slice().parse::<f64>().unwrap())]
	FloatLit(f64),

	#[regex(r"'(\\.|[^'\\])'", |lex| {
        let slice = lex.slice();
        let inner = &slice[1..slice.len() - 1];
        decode_escapes(inner).chars().next().unwrap_or_default()
    })]
	CharLit(char),

	#[token("[]")]
	Nil,
	#[token("<")]
	LAngle,
	#[token(">")]
	RAngle,
	#[token("[")]
	LBracket,
	#[token("]")]
	RBracket,
	#[token("(")]
	LParen,
	#[token(")")]
	RParen,

	#[regex(r"#.*?\n", logos::skip)]
	Comment,
	#[regex(r"[ \t\n\r\f]+", logos::skip)]
	Whitespace,
}

impl fmt::Display for Token {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Token::Ident(s) => write!(f, "Identifier '{}'", s),
			Token::Let => write!(f, "Keyword 'let'"),
			Token::End => write!(f, "Keyword 'end'"),
			Token::TypeKw => write!(f, "Keyword 'type'"),
			Token::Class => write!(f, "Keyword 'class'"),
			Token::Instance => write!(f, "Keyword 'instance'"),
			Token::Module => write!(f, "Keyword 'module'"),
			Token::File => write!(f, "Keyword 'file'"),
			Token::Import => write!(f, "Keyword 'import'"),
			Token::Export => write!(f, "Keyword 'export'"),
			Token::Unqualified => write!(f, "Keyword 'unqualified'"),
			Token::Match => write!(f, "Keyword 'match'"),
			Token::With => write!(f, "Keyword 'with'"),
			Token::FnKw => write!(f, "Keyword 'fn'"),
			Token::Is => write!(f, "Keyword 'is'"),
			Token::Undefined => write!(f, "Keyword 'undefined'"),
			Token::Colon => write!(f, "Symbol ':'"),
			Token::Eq => write!(f, "Symbol '='"),
			Token::Arrow => write!(f, "Symbol '->'"),
			Token::Star => write!(f, "Symbol '*'"),
			Token::Plus => write!(f, "Symbol '+'"),
			Token::LAngle => write!(f, "Symbol '<'"),
			Token::RAngle => write!(f, "Symbol '>'"),
			Token::Comma => write!(f, "Symbol ','"),
			Token::Underscore => write!(f, "Symbol '_'"),
			Token::StringLit(s) => write!(f, "String Literal \"{}\"", s),
			Token::IntLit(n) => write!(f, "Integer Literal {}", n),
			Token::FloatLit(x) => write!(f, "Float Literal {}", x),
			Token::CharLit(c) => write!(f, "Character Literal {}", c),
			Token::Nil => write!(f, "Nil"),
			Token::LBracket => write!(f, "Symbol '['"),
			Token::RBracket => write!(f, "Symbol ']'"),
			Token::LParen => write!(f, "Symbol '('"),
			Token::RParen => write!(f, "Symbol ')'"),
			Token::Whitespace => write!(f, "Whitespace"),
			Token::Comment => write!(f, "Comment"),
		}
	}
}

#[derive(Debug, Clone, Copy)]
pub struct Span {
	pub source_id: usize,
	pub start: usize,
	pub end: usize,
}

impl Span {
	pub fn new(source_id: usize, start: usize, end: usize) -> Self {
		Self {
			source_id,
			start,
			end,
		}
	}

	pub fn synthetic(source_id: usize) -> Self {
		Self {
			source_id,
			start: 0,
			end: 0,
		}
	}
}

impl ariadne::Span for Span {
	type SourceId = usize;

	fn source(&self) -> &usize {
		&self.source_id
	}

	fn start(&self) -> usize {
		self.start
	}

	fn end(&self) -> usize {
		self.end
	}
}

#[derive(Serialize, Debug, Clone)]
#[serde(transparent)]
pub struct Spanned<T> {
	pub item: T,
	#[serde(skip)]
	pub span: Span,
}

#[derive(Serialize, Debug, Clone)]
pub enum TopLevel {
	Module(Spanned<String>, Vec<Spanned<TopLevel>>),
	ImportFile(String),
	ImportUnqualified(Qualified),
	ImportAlias(Spanned<Qualified>, Spanned<Qualified>),
	Import(Qualified),
	Export(Qualified),
	Binding(Binding),
	TypeDef(Spanned<Qualified>, Vec<Spanned<String>>, Spanned<Type>),
	ClassDef(Spanned<String>, Vec<Spanned<String>>, Vec<Spanned<Binding>>),
	Instance(Spanned<String>, Vec<Spanned<Type>>, Vec<Spanned<Binding>>),
}

#[derive(PartialEq, Eq, Serialize, Debug, Clone, Hash)]
pub struct Qualified(pub Vec<String>);

fn qualified_string(s: Spanned<String>) -> Spanned<Qualified> {
	let Spanned { item, span } = s;
	Spanned {
		item: Qualified(item.split(":").map(|s| s.to_string()).collect()),
		span,
	}
}

#[derive(Serialize, Debug, Clone)]
pub enum Expr {
	Qualified(Qualified),
	Literal(Literal),
	Fn(Spanned<String>, Box<Spanned<Expr>>),
	App(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
	Match(Vec<(Vec<Spanned<Pattern>>, Spanned<Expr>)>),
	Product(Box<Spanned<Expr>>, Box<Spanned<Expr>>),
}

#[derive(Serialize, Debug, Clone)]
pub struct Binding {
	pub name: Spanned<String>,
	pub constraints: Vec<Spanned<Constraint>>,
	pub typ: Spanned<Type>,
	pub value: Option<Spanned<Expr>>,
	pub with_clauses: Vec<Spanned<Binding>>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Constraint {
	pub type_var: Spanned<String>,
	pub class_names: Vec<Spanned<String>>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Literal {
	Nil,
	Int(i32),
	Float(f64),
	Char(char),
	String(String),
	Constructor(Qualified),
}

#[derive(Debug, Clone, Serialize)]
pub enum Pattern {
	Hole,
	Variable(String),
	Literal(Literal),
	Constructor(Spanned<Qualified>, Box<Spanned<Pattern>>),
	Product(Box<Spanned<Pattern>>, Box<Spanned<Pattern>>),
	Left(Box<Spanned<Pattern>>),
	Right(Box<Spanned<Pattern>>),
}

#[derive(Debug, Clone, Serialize)]
pub enum Type {
	Unit,
	Int,
	Float,
	Char,
	Var(String),
	Fn(Box<Spanned<Type>>, Box<Spanned<Type>>),
	Sum(Box<Spanned<Type>>, Box<Spanned<Type>>),
	Product(Box<Spanned<Type>>, Box<Spanned<Type>>),
	App(Box<Spanned<Type>>, Box<Spanned<Type>>),
}

#[derive(Serialize, Debug, Clone)]
pub struct Program(pub Vec<Spanned<TopLevel>>);

struct Parser {
	tokens: Vec<Spanned<Token>>,
	pos: usize,
	debug: bool,
	source_id: usize,
	src: String,
	failed: bool,
	diags: Vec<Diagnostic>,
}

pub fn parse(
	registry: &mut SourceRegistry,
	source_id: usize,
	debug: bool,
) -> Result<Program, Vec<Diagnostic>> {
	let src = registry.content(source_id).to_owned();
	let mut parser = Parser::new(src, source_id, debug);
	match parser.parse(registry) {
		Some(program) => Ok(program),
		None => {
			if parser.diags.is_empty() {
				parser
					.diags
					.push(Diagnostic::error("the file could not be parsed", None));
			}
			Err(parser.diags)
		}
	}
}

pub fn parse_file(
	registry: &mut SourceRegistry,
	path: impl AsRef<Path>,
) -> std::io::Result<Result<Program, Vec<Diagnostic>>> {
	let (source_id, _) = registry.load_file(path)?;
	Ok(parse(registry, source_id, false))
}

fn lexer_error(span: Span, msg: &str) -> Diagnostic {
	Diagnostic::error(format!("Lex error: {}", msg), Some(span)).with_label("Invalid token")
}

impl Parser {
	fn new(src: String, source_id: usize, debug: bool) -> Self {
		Self {
			tokens: Vec::new(),
			pos: 0,
			source_id,
			debug,
			src,
			failed: false,
			diags: Vec::new(),
		}
	}

	fn lex(&mut self, registry: &mut SourceRegistry) {
		let mut lexer = Token::lexer(&self.src);
		while let Some(tok) = lexer.next() {
			let Ok(tok) = tok else {
				let span = Span::new(self.source_id, lexer.span().start, lexer.span().end);
				let invalid_text = lexer.slice();
				self.failed = true;
				self.diags.push(lexer_error(
					span,
					&format!("Invalid characters: '{}'", invalid_text),
				));
				return;
			};
			let span = Span::new(self.source_id, lexer.span().start, lexer.span().end);
			self.tokens.push(Spanned { item: tok, span });
		}
	}

	fn parse(&mut self, registry: &mut SourceRegistry) -> Option<Program> {
		self.lex(registry);

		if self.debug {
			eprintln!(
				"[DEBUG] Tokens: {:#?}",
				self.tokens
					.iter()
					.map(|x| x.item.clone())
					.collect::<Vec<_>>()
			);
		}

		let mut top_levels = Vec::new();

		let first_item = self.parse_top_level(registry)?;
		match &first_item.item {
			TopLevel::Module(_, _) => {}
			_ => {
				self.error(
					registry,
					"File must start with a module declaration",
					first_item.span,
				);
			}
		}
		top_levels.push(first_item);

		while self.pos < self.tokens.len() {
			let item = self.parse_top_level(registry)?;
			top_levels.push(item);
		}
		if self.failed {
			None
		} else {
			Some(Program(top_levels))
		}
	}
}

impl Program {
	pub fn json(&self) -> Result<String, serde_json::Error> {
		serde_json::to_string(self)
	}

	pub fn json_pretty(&self) -> Result<String, serde_json::Error> {
		serde_json::to_string_pretty(self)
	}
}

impl Parser {
	fn span_at_pos(&self) -> Span {
		self.peek()
			.map(|t| t.span)
			.unwrap_or_else(|| Span::new(self.source_id, self.pos, self.pos + 1))
	}

	fn peek(&self) -> Option<&Spanned<Token>> {
		self.tokens.get(self.pos)
	}

	fn peek_at(&self, offset: usize) -> Option<&Spanned<Token>> {
		self.tokens.get(self.pos.saturating_add(offset))
	}

	fn next_is(&self, is: &Token) -> bool {
		self.peek().map(|t| &t.item == is).unwrap_or(false)
	}

	fn nth_is(&self, n: usize, is: &Token) -> bool {
		self.peek_at(n).map(|t| &t.item == is).unwrap_or(false)
	}

	fn skip(&mut self) {
		self.pos += 1;
	}

	fn eat(&mut self, registry: &mut SourceRegistry, expected: &Token) -> Option<Span> {
		self.debug_print("eat");
		let tok = match self.peek() {
			Some(t) => t.clone(),
			None => {
				let eof_span = Span::new(self.source_id, self.pos, self.pos + 1);
				self.error(
					registry,
					&format!("Expected {}, got EOF", expected),
					eof_span,
				);
				return None;
			}
		};

		if &tok.item == expected {
			self.skip();
			Some(tok.span)
		} else {
			self.error(
				registry,
				&format!("Expected {}, got {}", expected, tok.item),
				tok.span,
			);
			None
		}
	}

	fn error(&mut self, registry: &mut SourceRegistry, msg: &str, span: Span) {
		self.failed = true;
		let _ = registry;
		self.diags.push(Diagnostic::error(msg, Some(span)));
	}

	fn debug_print(&self, message: &str) -> Option<()> {
		if self.debug {
			eprintln!("[DEBUG] {} at {} {}", message, self.pos, self.peek()?.item);
		}
		Some(())
	}
}

impl Parser {
	fn parse_ident(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<String>> {
		let tok = self.peek()?.clone();
		match tok.item {
			Token::Ident(name) => {
				self.skip();
				Some(Spanned {
					item: name,
					span: tok.span,
				})
			}
			t => {
				self.error(
					registry,
					&format!("Expected identifier, got {:?}", t),
					tok.span,
				);
				None
			}
		}
	}

	fn parse_expr_with_parens(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<Expr>> {
		self.debug_print("parse expr with parens");
		if self.next_is(&Token::LParen) {
			self.eat(registry, &Token::LParen);
			let expr = self.parse_expr(registry)?;
			self.eat(registry, &Token::RParen);
			return Some(expr);
		}
		self.parse_expr(registry)
	}

	fn parse_top_level(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<TopLevel>> {
		self.debug_print("parse top level");
		let start = self.span_at_pos();
		match self.peek().map(|t| &t.item) {
			Some(Token::Module) => self.parse_module(registry),
			Some(Token::Import) => {
				let imp = self.parse_import(registry)?;
				Some(Spanned {
					item: imp.item,
					span: Span::new(self.source_id, start.start, imp.span.end),
				})
			}
			Some(Token::Export) => {
				let item = self.parse_export(registry)?;
				Some(Spanned {
					item: item.item,
					span: Span::new(self.source_id, start.start, item.span.end),
				})
			}
			Some(Token::Let) => {
				let binding = self.parse_binding(registry, false, false)?;
				Some(Spanned {
					item: TopLevel::Binding(binding.item),
					span: Span::new(self.source_id, start.start, binding.span.end),
				})
			}
			Some(Token::TypeKw) => self.parse_type_def(registry),
			Some(Token::Class) => self.parse_class_def(registry).map(
				|Spanned {
				     item: (name, generics, bindings),
				     span,
				 }| Spanned {
					item: TopLevel::ClassDef(name, generics, bindings),
					span,
				},
			),
			Some(Token::Instance) => self.parse_instance(registry).map(
				|Spanned {
				     item: (name, type_args, bindings),
				     span,
				 }| Spanned {
					item: TopLevel::Instance(name, type_args, bindings),
					span,
				},
			),
			Some(found) => {
				let span = self.span_at_pos();
				self.error(
					registry,
					&format!("Expected top-level expression, found {}", found),
					span,
				);
				None
			}
			None => {
				let span = self.span_at_pos();
				self.error(registry, "Expected top-level expression", span);
				None
			}
		}
	}

	fn parse_module(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<TopLevel>> {
		let start = self.peek().unwrap().span;
		self.eat(registry, &Token::Module)?;
		let name = self.parse_ident(registry)?;
		self.eat(registry, &Token::Is)?;

		let mut body = Vec::new();
		while self.pos < self.tokens.len() && !self.next_is(&Token::End) {
			let item = self.parse_top_level(registry)?;
			body.push(item);
		}
		if self.next_is(&Token::End) {
			self.eat(registry, &Token::End)?;
		}

		let end = body.last().map(|t| t.span.end).unwrap_or(start.end);
		Some(Spanned {
			item: TopLevel::Module(name, body),
			span: Span::new(self.source_id, start.start, end),
		})
	}

	fn parse_binding(
		&mut self,
		registry: &mut SourceRegistry,
		in_class_context: bool,
		is_with: bool,
	) -> Option<Spanned<Binding>> {
		self.debug_print("parse binding");
		let start = self.peek().unwrap().span;
		if is_with {
			self.eat(registry, &Token::With)?;
		} else {
			self.eat(registry, &Token::Let)?;
		}
		let name = self.parse_ident(registry)?;

		let mut constraints = Vec::new();
		while self
			.peek()
			.map(|t| matches!(&t.item, Token::Ident(_) | Token::LParen))
			.unwrap_or(false)
			&& !self
				.peek()
				.map(|t| &t.item == &Token::Colon)
				.unwrap_or(false)
		{
			let constraint = self.parse_type_param(registry)?;
			constraints.push(constraint);
		}

		let typ = if self.next_is(&Token::Colon) {
			self.eat(registry, &Token::Colon)?;
			self.parse_type(registry)?
		} else {
			Spanned {
				item: Type::Var(name.item.clone()),
				span: name.span,
			}
		};

		let value = if in_class_context {
			None
		} else {
			self.eat(registry, &Token::Eq)?;
			if self.next_is(&Token::FnKw) {
				let expr = self.parse_lambda(registry)?;
				Some(expr)
			} else if self.next_is(&Token::Undefined) {
				self.eat(registry, &Token::Undefined);
				None
			} else {
				let expr = self.parse_expr(registry)?;
				Some(expr)
			}
		};

		let mut with_clauses = Vec::new();
		if !is_with {
			while self.next_is(&Token::With) {
				let clause = self.parse_binding(registry, in_class_context, true)?;
				with_clauses.push(clause);
			}
			self.eat(registry, &Token::End)?;
		}

		let end = self.peek().map(|t| t.span).unwrap_or(start).end;
		Some(Spanned {
			item: Binding {
				name,
				constraints,
				typ: typ,
				value,
				with_clauses,
			},
			span: Span::new(self.source_id, start.start, end),
		})
	}

	fn parse_type_param(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<Constraint>> {
		self.debug_print("parse type param");

		if !self.next_is(&Token::LParen) {
			let tok = self.peek()?;
			let Spanned {
				item: Token::Ident(type_var),
				span,
			} = tok.clone()
			else {
				self.error(registry, "Expected type parameter name", tok.span);
				return None;
			};
			self.skip();
			return Some(Spanned {
				item: Constraint {
					type_var: Spanned {
						item: type_var,
						span,
					},
					class_names: Vec::new(),
				},
				span,
			});
		}

		let span_begin = self.pos;
		self.eat(registry, &Token::LParen)?;

		let var_tok = self.peek()?;
		let Spanned {
			item: Token::Ident(type_var),
			span: tok_span,
		} = var_tok.clone()
		else {
			self.error(
				registry,
				"Expected identifier in type parameter",
				var_tok.span,
			);
			return None;
		};
		self.skip();

		if !self.next_is(&Token::Colon) {
			self.eat(registry, &Token::RParen)?;
			return Some(Spanned {
				item: Constraint {
					type_var: Spanned {
						item: type_var,
						span: tok_span,
					},
					class_names: Vec::new(),
				},
				span: Span::new(self.source_id, span_begin, self.pos),
			});
		}

		self.eat(registry, &Token::Colon)?;

		let first = self.parse_ident(registry)?;
		let mut class_names = vec![first];
		while self
			.peek()
			.map(|t| &t.item == &Token::Comma)
			.unwrap_or(false)
		{
			self.eat(registry, &Token::Comma)?;
			class_names.push(self.parse_ident(registry)?);
		}
		self.eat(registry, &Token::RParen)?;

		Some(Spanned {
			item: Constraint {
				type_var: Spanned {
					item: type_var,
					span: tok_span,
				},
				class_names,
			},
			span: Span::new(self.source_id, span_begin, self.pos),
		})
	}

	fn parse_app(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<Expr>> {
		self.debug_print("parse app");
		let mut expr = self.parse_atom(registry)?;

		while matches!(
			self.peek().map(|t| &t.item),
			Some(
				Token::Ident(_)
					| Token::IntLit(_)
					| Token::FloatLit(_)
					| Token::StringLit(_)
					| Token::CharLit(_)
					| Token::Nil | Token::LBracket
					| Token::LParen | Token::FnKw
			)
		) {
			let func = Box::new(expr.clone());
			let arg = self.parse_atom(registry)?;
			expr = Spanned {
				span: Span::new(self.source_id, expr.span.start, arg.span.end),
				item: Expr::App(func, Box::new(arg)),
			};
		}
		Some(expr)
	}

	fn parse_product_op(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<Expr>> {
		self.debug_print("parse product op");
		let mut expr = self.parse_app(registry)?;

		while self.next_is(&Token::Star) {
			self.eat(registry, &Token::Star)?;
			let right = self.parse_app(registry)?;
			expr = Spanned {
				span: Span::new(self.source_id, expr.span.start, right.span.end),
				item: Expr::Product(Box::new(expr), Box::new(right)),
			};
		}
		Some(expr)
	}

	fn parse_app_op(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<Expr>> {
		let expr = self.parse_product_op(registry)?;

		if self.next_is(&Token::LAngle) {
			self.eat(registry, &Token::LAngle)?;
			let right = self.parse_app_op(registry)?;
			return Some(Spanned {
				span: Span::new(self.source_id, expr.span.start, right.span.end),
				item: Expr::App(Box::new(expr), Box::new(right)),
			});
		}
		Some(expr)
	}

	fn parse_expr(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<Expr>> {
		self.debug_print("parse expr");
		let mut expr = self.parse_app_op(registry)?;

		while self
			.peek()
			.map(|t| &t.item == &Token::RAngle)
			.unwrap_or(false)
		{
			self.eat(registry, &Token::RAngle)?;
			let right = self.parse_app_op(registry)?;
			expr = Spanned {
				span: Span::new(self.source_id, expr.span.start, right.span.end),
				item: Expr::App(Box::new(right), Box::new(expr)),
			};
		}
		Some(expr)
	}

	fn parse_atom(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<Expr>> {
		self.debug_print("parse atom");
		let tok = self.peek()?.clone();
		let span = tok.span;

		match &tok.item {
			Token::Ident(_) => self.parse_ident_atom(registry),

			Token::IntLit(_) | Token::FloatLit(_) | Token::CharLit(_) => {
				let Spanned { item: lit, span } = self.parse_literal()?;
				Some(Spanned {
					item: Expr::Literal(lit),
					span,
				})
			}

			Token::Nil => {
				self.skip();
				Some(Spanned {
					item: Self::build_list_expr(Vec::new(), span),
					span,
				})
			}

			Token::StringLit(_) => self.parse_string_literal_expr(registry),

			Token::LParen => self.parse_expr_with_parens(registry),
			Token::LBracket => self.parse_list(registry),
			Token::Match => self.parse_match(registry, span.start),
			Token::FnKw => self.parse_lambda(registry),

			_ => {
				self.error(registry, "Unexpected token in atom", span);
				return None;
			}
		}
	}

	fn parse_ident_atom(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<Expr>> {
		self.debug_print("parse ident atom");
		let tok = self.peek()?;
		let Spanned {
			item: Token::Ident(_),
			span,
		} = tok.clone()
		else {
			unreachable!()
		};
		let name = self.parse_qualified(registry)?.item;
		Some(Spanned {
			item: Expr::Qualified(name),
			span,
		})
	}

	fn parse_literal(&mut self) -> Option<Spanned<Literal>> {
		self.debug_print("parse literal");
		let tok = self.peek()?.clone();
		let span = tok.span;
		let lit = match &tok.item {
			Token::IntLit(n) => {
				self.skip();
				Literal::Int(*n)
			}
			Token::FloatLit(x) => {
				self.skip();
				Literal::Float(*x)
			}
			Token::CharLit(c) => {
				self.skip();
				Literal::Char(*c)
			}
			_ => return None,
		};
		Some(Spanned { item: lit, span })
	}

	fn parse_qualified(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<Qualified>> {
		self.debug_print("parse qualified");
		let Spanned {
			item: Token::Ident(first),
			span: span0,
		} = self.peek()?.clone()
		else {
			return None;
		};
		self.skip();

		let mut span1 = span0;

		let mut segments = vec![first];
		while self.next_is(&Token::Colon) {
			self.eat(registry, &Token::Colon)?;
			let tok1 = self.peek()?.clone();
			span1 = tok1.span;
			let Spanned {
				item: Token::Ident(seg),
				..
			} = tok1
			else {
				self.error(registry, "Expected identifier after ':'", span1);
				return None;
			};
			segments.push(seg);
			self.skip();
		}

		Some(Spanned {
			item: Qualified(segments),
			span: Span {
				source_id: self.source_id,
				start: span0.start,
				end: span1.end,
			},
		})
	}

	fn build_list_expr(items: Vec<Spanned<Expr>>, span: Span) -> Expr {
		let nil = Expr::Qualified(Qualified(vec!["List".to_string(), "Nil".to_string()]));
		items.into_iter().rev().fold(nil, |acc, item| {
			Expr::App(
				Box::new(Spanned {
					item: Expr::Qualified(Qualified(vec!["List".to_string(), "Cons".to_string()])),
					span,
				}),
				Box::new(Spanned {
					item: Expr::Product(Box::new(item), Box::new(Spanned { item: acc, span })),
					span,
				}),
			)
		})
	}

	fn build_list_pattern(items: Vec<Spanned<Pattern>>, span: Span) -> Pattern {
		let nil = Pattern::Literal(Literal::Constructor(Qualified(vec![
			"List".to_string(),
			"Nil".to_string(),
		])));
		items.into_iter().rev().fold(nil, |acc, item| {
			Pattern::Constructor(
				Spanned {
					item: Qualified(vec!["List".to_string(), "Cons".to_string()]),
					span,
				},
				Box::new(Spanned {
					item: Pattern::Product(Box::new(item), Box::new(Spanned { item: acc, span })),
					span,
				}),
			)
		})
	}

	fn parse_string_literal_expr(
		&mut self,
		registry: &mut SourceRegistry,
	) -> Option<Spanned<Expr>> {
		self.debug_print("parse string literal expr");
		let tok = self.peek()?.clone();
		let span = tok.span;
		let Token::StringLit(s) = tok.item else {
			self.error(registry, "Expected string literal", span);
			return None;
		};
		self.skip();

		let char_items: Vec<Spanned<Expr>> = s
			.chars()
			.map(|c| Spanned {
				item: Expr::Literal(Literal::Char(c)),
				span,
			})
			.collect();

		Some(Spanned {
			item: Self::build_list_expr(char_items, span),
			span,
		})
	}

	fn parse_list(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<Expr>> {
		self.debug_print("parse list");
		let start = self.peek().unwrap().span;
		self.eat(registry, &Token::LBracket)?;
		let mut items = Vec::new();

		while !self.next_is(&Token::RBracket) {
			items.push(self.parse_expr_with_parens(registry)?);
			if !self.next_is(&Token::Comma) {
				break;
			}
			self.eat(registry, &Token::Comma);
		}
		self.eat(registry, &Token::RBracket)?;
		let end = self.peek().map(|t| t.span.end).unwrap_or(start.end);
		let full_span = Span::new(self.source_id, start.start, end);

		Some(Spanned {
			item: Self::build_list_expr(items, full_span),
			span: full_span,
		})
	}

	fn parse_match(
		&mut self,
		registry: &mut SourceRegistry,
		match_start: usize,
	) -> Option<Spanned<Expr>> {
		self.debug_print("parse match");
		self.skip();
		let mut cases = Vec::new();
		let mut fresh = 0usize;

		while self.pos < self.tokens.len() && !self.next_is(&Token::End) {
			self.debug_print("Top of parse_match while loop");
			let mut pats = Vec::new();
			while !self.next_is(&Token::Arrow) {
				pats.push(self.parse_pattern(registry)?);
				if !self.next_is(&Token::Arrow) {
					self.eat(registry, &Token::Comma)?;
				}
			}
			self.eat(registry, &Token::Arrow)?;
			let mut body = self.parse_expr(registry)?;
			self.eat(registry, &Token::End)?;
			let mut passed = Vec::new();
			for p in pats.iter_mut() {
				if let Pattern::Left(inner) | Pattern::Right(inner) = &mut p.item {
					if matches!(inner.item, Pattern::Hole) {
						let name = format!("sum${}", fresh);
						fresh += 1;
						inner.item = Pattern::Variable(name.clone());
						passed.push((name, inner.span));
					}
				}
			}
			for (name, span) in passed {
				let sp = Span::new(
					body.span.source_id,
					body.span.start,
					span.end.max(body.span.end),
				);
				let arg = Spanned {
					item: Expr::Qualified(Qualified(vec![name])),
					span,
				};
				body = Spanned {
					item: Expr::App(Box::new(body), Box::new(arg)),
					span: sp,
				};
			}
			cases.push((pats, body));
		}

		self.eat(registry, &Token::End)?;
		let end = self.peek().map(|t| t.span.end).unwrap_or(match_start);

		Some(Spanned {
			item: Expr::Match(cases),
			span: Span::new(self.source_id, match_start, end),
		})
	}

	fn parse_pattern(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<Pattern>> {
		self.debug_print("parse pattern");
		if self.nth_is(1, &Token::Colon) {
			let Spanned {
				item: ctor_name,
				span,
			} = self.parse_qualified(registry)?;

			let arg = match self.peek() {
				Some(Spanned {
					item: Token::Arrow | Token::Comma | Token::End | Token::RParen,
					span: _,
				}) => None,
				_ => Some(self.parse_pattern(registry)?),
			};

			return Some(Spanned {
				item: match arg {
					Some(p) => Pattern::Constructor(
						Spanned {
							item: ctor_name,
							span,
						},
						Box::new(p),
					),
					None => Pattern::Literal(Literal::Constructor(ctor_name)),
				},
				span,
			});
		}

		let tok = self.peek()?.clone();
		let span = tok.span;
		self.skip();

		match tok.item {
			Token::Underscore => Some(Spanned {
				item: Pattern::Hole,
				span,
			}),
			Token::Ident(name) => Some(Spanned {
				item: Pattern::Variable(name),
				span,
			}),
			Token::IntLit(n) => Some(Spanned {
				item: Pattern::Literal(Literal::Int(n)),
				span,
			}),
			Token::FloatLit(x) => Some(Spanned {
				item: Pattern::Literal(Literal::Float(x)),
				span,
			}),
			Token::CharLit(c) => Some(Spanned {
				item: Pattern::Literal(Literal::Char(c)),
				span,
			}),
			Token::Nil => Some(Spanned {
				item: Self::build_list_pattern(Vec::new(), span),
				span,
			}),
			Token::StringLit(s) => {
				let char_items: Vec<Spanned<Pattern>> = s
					.chars()
					.map(|c| Spanned {
						item: Pattern::Literal(Literal::Char(c)),
						span,
					})
					.collect();
				Some(Spanned {
					item: Self::build_list_pattern(char_items, span),
					span,
				})
			}
			Token::LParen => {
				if self.next_is(&Token::Plus) {
					self.eat(registry, &Token::Plus)?;
					let inner = self.parse_pattern(registry)?;
					let close = self.peek().map(|t| t.span.end).unwrap_or(inner.span.end);
					self.eat(registry, &Token::RParen)?;
					return Some(Spanned {
						span: Span::new(self.source_id, span.start, close),
						item: Pattern::Right(Box::new(inner)),
					});
				}
				let left = self.parse_pattern(registry)?;
				if self.next_is(&Token::Plus) {
					self.eat(registry, &Token::Plus)?;
					let close = self.peek().map(|t| t.span.end).unwrap_or(left.span.end);
					self.eat(registry, &Token::RParen)?;
					return Some(Spanned {
						span: Span::new(self.source_id, span.start, close),
						item: Pattern::Left(Box::new(left)),
					});
				}
				if self.next_is(&Token::Star) {
					self.eat(registry, &Token::Star)?;
					let right = self.parse_pattern(registry)?;
					self.eat(registry, &Token::RParen)?;
					Some(Spanned {
						span: Span::new(self.source_id, span.start, right.span.end),
						item: Pattern::Product(Box::new(left), Box::new(right)),
					})
				} else {
					self.eat(registry, &Token::RParen)?;
					Some(left)
				}
			}
			_ => {
				self.error(registry, "Expected pattern", span);
				None
			}
		}
	}

	fn parse_lambda(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<Expr>> {
		self.debug_print("parse lambda");
		self.eat(registry, &Token::FnKw)?;
		let start = self.peek().unwrap().span;
		let arg = self.parse_ident(registry)?;
		self.eat(registry, &Token::Arrow)?;
		let body = self.parse_expr_with_parens(registry)?;
		self.eat(registry, &Token::End)?;

		let end = self.peek().map(|t| t.span.end).unwrap_or(start.end);
		Some(Spanned {
			item: Expr::Fn(arg, Box::new(body)),
			span: Span::new(self.source_id, start.start, end),
		})
	}

	fn parse_type(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<Type>> {
		self.debug_print("parse type");
		let mut typ = self.parse_type_func(registry)?;

		while self
			.peek()
			.map(|t| &t.item == &Token::Star)
			.unwrap_or(false)
		{
			self.eat(registry, &Token::Star)?;
			let right = self.parse_type_func(registry)?;
			typ = Spanned {
				span: Span::new(self.source_id, typ.span.start, right.span.end),
				item: Type::Product(Box::new(typ), Box::new(right)),
			};
		}

		while self
			.peek()
			.map(|t| &t.item == &Token::Plus)
			.unwrap_or(false)
		{
			self.eat(registry, &Token::Plus)?;
			let right = self.parse_type(registry)?;
			typ = Spanned {
				span: Span::new(self.source_id, typ.span.start, right.span.end),
				item: Type::Sum(Box::new(typ), Box::new(right)),
			};
		}

		Some(typ)
	}

	fn parse_type_func(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<Type>> {
		self.debug_print("parse type func");
		let mut typ = self.parse_type_app(registry)?;

		while self
			.peek()
			.map(|t| &t.item == &Token::Arrow)
			.unwrap_or(false)
		{
			self.eat(registry, &Token::Arrow)?;
			let right = self.parse_type_func(registry)?;
			typ = Spanned {
				span: Span::new(self.source_id, typ.span.start, right.span.end),
				item: Type::Fn(Box::new(typ), Box::new(right)),
			};
		}
		Some(typ)
	}

	fn parse_type_app(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<Type>> {
		let mut typ = self.parse_type_atom(registry)?;

		while matches!(
			self.peek().map(|t| &t.item),
			Some(Token::Ident(_) | Token::LParen)
		) {
			let arg = self.parse_type_atom(registry)?;
			typ = Spanned {
				span: Span::new(self.source_id, typ.span.start, arg.span.end),
				item: Type::App(Box::new(typ), Box::new(arg)),
			};
		}
		Some(typ)
	}

	fn parse_type_atom(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<Type>> {
		self.debug_print("parse type atom");
		let tok = self.peek()?.clone();
		let span = tok.span;
		self.skip();

		match tok.item {
			Token::Ident(name) => Some(Spanned {
				item: match name.as_str() {
					"Int" => Type::Int,
					"Float" => Type::Float,
					"Char" => Type::Char,
					"Unit" => Type::Unit,
					_ => Type::Var(name),
				},
				span,
			}),
			Token::LParen => {
				let inner = self.parse_type(registry)?;
				self.eat(registry, &Token::RParen)?;
				Some(inner)
			}
			_ => {
				self.error(registry, "Expected type", span);
				None
			}
		}
	}

	fn parse_type_def(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<TopLevel>> {
		self.debug_print("parse type def");
		let start = self.eat(registry, &Token::TypeKw)?.start;
		let name = self.parse_qualified(registry)?;

		let mut params = Vec::new();
		while !self.next_is(&Token::Eq) {
			params.push(self.parse_ident(registry)?);
		}
		self.eat(registry, &Token::Eq)?;
		let typ = self.parse_type(registry)?;
		self.eat(registry, &Token::End)?;

		let end = self.peek().map(|t| t.span.end).unwrap_or(start);
		Some(Spanned {
			item: TopLevel::TypeDef(name, params, typ),
			span: Span::new(self.source_id, start, end),
		})
	}

	fn parse_class_def(
		&mut self,
		registry: &mut SourceRegistry,
	) -> Option<Spanned<(Spanned<String>, Vec<Spanned<String>>, Vec<Spanned<Binding>>)>> {
		self.debug_print("parse class def");
		let start = self.eat(registry, &Token::Class)?.start;
		let name = self.parse_ident(registry)?;

		let mut params = Vec::new();
		while self
			.peek()
			.map(|t| matches!(&t.item, Token::Ident(_)))
			.unwrap_or(false)
		{
			params.push(self.parse_ident(registry)?);
		}
		self.eat(registry, &Token::Is)?;

		let mut bindings = Vec::new();
		while !self.next_is(&Token::End) {
			bindings.push(self.parse_binding(registry, true, false)?);
		}
		self.eat(registry, &Token::End)?;

		let end = self.peek().map(|t| t.span.end).unwrap_or(start);
		Some(Spanned {
			item: (name, params, bindings),
			span: Span::new(self.source_id, start, end),
		})
	}

	fn parse_instance(
		&mut self,
		registry: &mut SourceRegistry,
	) -> Option<Spanned<(Spanned<String>, Vec<Spanned<Type>>, Vec<Spanned<Binding>>)>> {
		self.debug_print("parse instance");
		let start = self.eat(registry, &Token::Instance)?.start;
		let class_name = self.parse_ident(registry)?;

		let mut type_args = Vec::new();
		while matches!(self.peek()?.item, Token::Ident(_) | Token::LParen) {
			type_args.push(self.parse_type(registry)?);
		}
		self.eat(registry, &Token::Is)?;

		let mut bindings = Vec::new();
		while !self.next_is(&Token::End) {
			bindings.push(self.parse_binding(registry, false, false)?);
		}
		self.eat(registry, &Token::End)?;

		let end = self.peek().map(|t| t.span.end).unwrap_or(start);
		Some(Spanned {
			item: (class_name, type_args, bindings),
			span: Span::new(self.source_id, start, end),
		})
	}

	fn parse_import(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<TopLevel>> {
		self.debug_print("parse import");
		let start = self.eat(registry, &Token::Import)?.start;

		if self.next_is(&Token::File) {
			self.eat(registry, &Token::File)?;
			let mod_name = self.parse_ident(registry)?;
			let end = self.peek().map(|t| t.span.end).unwrap_or(start);
			return Some(Spanned {
				item: TopLevel::ImportFile(mod_name.item),
				span: Span::new(self.source_id, start, end),
			});
		}

		if self.next_is(&Token::Unqualified) {
			self.eat(registry, &Token::Unqualified)?;
			let mod_name = self.parse_ident(registry)?;
			let end = self.peek().map(|t| t.span.end).unwrap_or(start);
			return Some(Spanned {
				item: TopLevel::ImportUnqualified(qualified_string(mod_name).item),
				span: Span::new(self.source_id, start, end),
			});
		}

		let path = self.parse_qualified(registry)?;
		if self.next_is(&Token::Ident("as".to_string())) {
			self.eat(registry, &Token::Ident("as".to_string()))?;
			let local_name = self.parse_ident(registry)?;
			let end = self.peek().map(|t| t.span.end).unwrap_or(path.span.end);
			return Some(Spanned {
				span: Span::new(self.source_id, path.span.start, end),
				item: TopLevel::ImportAlias(path, qualified_string(local_name)),
			});
		}

		let end = self.peek().map(|t| t.span.end).unwrap_or(start);
		Some(Spanned {
			item: TopLevel::Import(path.item),
			span: Span::new(self.source_id, start, end),
		})
	}

	fn parse_export(&mut self, registry: &mut SourceRegistry) -> Option<Spanned<TopLevel>> {
		self.debug_print("parse export");
		let start = self.eat(registry, &Token::Export)?.start;
		let Spanned { item: name, span } = self.parse_qualified(registry)?;

		let end = self.peek().map(|t| t.span.end).unwrap_or(span.end);

		Some(Spanned {
			item: TopLevel::Export(name),

			span: Span::new(self.source_id, start, end),
		})
	}
}
