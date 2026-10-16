// typed ANF IR + lowering pass from type-checked AST

use im::HashMap as ImHashMap;
use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::diag::Diagnostic;
use crate::lang::{Intrinsic, Lang, LangItem};

use crate::parser::{Literal, Pattern, Span, Spanned};
use crate::typechecker::{Scheme, Ty, TypeEnv, TypedBinding, TypedExpr};

pub type Name = String;

// ============================================================================
// IR types
// ============================================================================

/// A trivial, side-effect-free, duplicable value.
#[derive(Debug, Clone, PartialEq)]
pub enum Atom {
	/// A local: lambda/function parameter or `let` binder.
	Var(Name),
	/// `Int`, `Float` or `Char` only (see the module comment).
	Lit(Literal),
	/// A top-level function/extern, with the type it is used at *here*.
	Global(Name, Ty),
	/// A class method used at `ty`; replaced by the specializer with the instance's method.
	Method(Name, Ty),
}

/// The right-hand side of a `let`.
#[allow(unused)]
#[derive(Debug, Clone)]
pub enum Value {
	Atom(Atom),
	/// `fn param : ty -> body end`, one argument at a time.
	Lambda(Name, Ty, Box<Expr>),
	/// Apply a function value to one argument (curried).
	App(Atom, Atom),
	/// Build a product `(a * b)`.
	Pair(Atom, Atom),
	/// A data-constructor value; `tag` is the canonical `Type:Ctor` name.
	Ctor(String, Option<Atom>),
	/// Extract one side of a product.
	Proj(Atom, Side),
	/// Extract the payload of an already tag-checked constructor value.
	Unwrap(Atom),
	/// A string literal (a `List Char`).
	Str(String),
	/// Abort the program with this message when evaluated (`undefined`, or a
	/// non-exhaustive `match`). Never removed or duplicated by the optimizer.
	Fail(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Side {
	Fst,
	Rst,
}

/// An ANF expression: a chain of lets ending in a tail position.
#[derive(Debug, Clone)]
pub enum Expr {
	Let(Name, Ty, Value, Box<Expr>),
	/// Dispatch on a scrutinee's shape. Compiled from `match`.
	Case(Atom, Vec<Arm>),
	Halt(Atom),
}

#[derive(Debug, Clone)]
pub struct Arm {
	pub pat: CasePat,
	pub body: Expr,
}

#[derive(Debug, Clone)]
pub enum CasePat {
	/// Matches unconditionally.
	Wild,
	/// An `Int`, `Float` or `Char` literal.
	Lit(Literal),
	/// A canonical `Type:Ctor` name.
	Ctor(String),
}

#[derive(Debug, Clone)]
pub struct Function {
	pub name: Name,
	pub params: Vec<(Name, Ty)>,
	/// Result type once every parameter has been applied.
	pub ret: Ty,
	/// The signature `p0 -> ... -> ret` — an expression type, so it may have
	/// more arrows than there are parameters when the body is itself a function.
	pub ty: Ty,
	pub body: Expr,
	/// Span of the source binding this was lowered from (for diagnostics).
	pub span: Span,
}

/// A binding whose value is `undefined` in source — implemented by the
/// backend/runtime. `arity` is the number of nested `->`s in its type.
#[derive(Debug, Clone)]
pub struct Extern {
	pub name: Name,
	pub arity: usize,
	pub ty: Ty,
	/// The primitive the backend implements this binding with (from the lang manifest).
	pub intrinsic: Option<Intrinsic>,
	pub span: Span,
}

pub struct IrProgram {
	pub functions: Vec<Function>,
	pub externs: Vec<Extern>,
}

/// What the specializer needs to resolve class-method references.
#[allow(unused)]
#[derive(Default)]
pub struct Overloads {
	/// method name -> (its generic type, the type variable that is the class parameter)
	pub methods: HashMap<String, (Ty, u32)>,
	/// method name -> class name
	pub class_of: ImHashMap<String, String>,
	/// every canonical binding name (instance methods are `Head:method`)
	pub canonical: HashSet<Name>,
	/// zero-parameter type aliases and data types, for naming a type's instance head
	pub type_ctor_names: HashMap<String, Vec<String>>,
	pub type_arity: ImHashMap<String, usize>,
	pub aliases: ImHashMap<String, Ty>,
}

// ============================================================================
// Type helpers
// ============================================================================

/// Number of curried arguments implied by a type: `Int -> Int -> Int` is 2.
pub fn count_arrows(ty: &Ty) -> usize {
	match ty {
		Ty::Fn(_, ret) => 1 + count_arrows(ret),
		_ => 0,
	}
}

/// Split off up to `n` leading arrows: (parameter types, remaining type).
pub fn peel_fn(ty: &Ty, n: usize) -> (Vec<Ty>, Ty) {
	let mut params = Vec::new();
	let mut cur = ty;
	while params.len() < n {
		match cur {
			Ty::Fn(a, b) => {
				params.push((**a).clone());
				cur = b;
			}
			_ => break,
		}
	}
	(params, cur.clone())
}

pub fn display_ty(ty: &Ty) -> String {
	match ty {
		Ty::Unit => "Unit".to_string(),
		Ty::Int => "Int".to_string(),
		Ty::Float => "Float".to_string(),
		Ty::Char => "Char".to_string(),
		Ty::Var(n) => format!("t{}", n),
		Ty::Named(n) => n.clone(),
		Ty::App(f, a) => format!("({} {})", display_ty(f), display_ty(a)),
		Ty::Fn(a, b) => format!("({} -> {})", display_ty(a), display_ty(b)),
		Ty::Product(a, b) => format!("({} * {})", display_ty(a), display_ty(b)),
		Ty::Sum(a, b) => format!("({} + {})", display_ty(a), display_ty(b)),
	}
}

/// Replace type variables according to `m`.
pub fn subst_ty(t: &Ty, m: &HashMap<u32, Ty>) -> Ty {
	match t {
		Ty::Var(v) => m.get(v).cloned().unwrap_or_else(|| t.clone()),
		Ty::Fn(a, b) => Ty::Fn(Box::new(subst_ty(a, m)), Box::new(subst_ty(b, m))),
		Ty::Product(a, b) => Ty::Product(Box::new(subst_ty(a, m)), Box::new(subst_ty(b, m))),
		Ty::Sum(a, b) => Ty::Sum(Box::new(subst_ty(a, m)), Box::new(subst_ty(b, m))),
		Ty::App(a, b) => Ty::App(Box::new(subst_ty(a, m)), Box::new(subst_ty(b, m))),
		other => other.clone(),
	}
}

/// One-directional structural match: wherever `generic` has a type variable,
/// record what sits in the same position in `concrete` (first occurrence wins).
pub fn match_ty(generic: &Ty, concrete: &Ty, out: &mut HashMap<u32, Ty>) {
	match (generic, concrete) {
		(Ty::Var(id), _) => {
			out.entry(*id).or_insert_with(|| concrete.clone());
		}
		(Ty::Fn(a1, b1), Ty::Fn(a2, b2))
		| (Ty::Product(a1, b1), Ty::Product(a2, b2))
		| (Ty::Sum(a1, b1), Ty::Sum(a2, b2))
		| (Ty::App(a1, b1), Ty::App(a2, b2)) => {
			match_ty(a1, a2, out);
			match_ty(b1, b2, out);
		}
		_ => {}
	}
}

/// Is `occurrence` an instance of the shape `candidate` describes, treating
/// every type variable *in `candidate`* as a wildcard? This — not `==` — is
/// what overload resolution needs: a class method can be generic in more than
/// the class parameter (`Monad`'s `bind` is generic in `a` and `b` too, so even
/// `IO:bind` is never literally equal to a use-site type).
fn structurally_compatible(candidate: &Ty, occurrence: &Ty) -> bool {
	match (candidate, occurrence) {
		(Ty::Var(_), _) => true,
		(Ty::Unit, Ty::Unit)
		| (Ty::Int, Ty::Int)
		| (Ty::Float, Ty::Float)
		| (Ty::Char, Ty::Char) => true,
		(Ty::Named(n1), Ty::Named(n2)) => n1 == n2,
		(Ty::Fn(a1, b1), Ty::Fn(a2, b2))
		| (Ty::Product(a1, b1), Ty::Product(a2, b2))
		| (Ty::Sum(a1, b1), Ty::Sum(a2, b2)) => {
			structurally_compatible(a1, a2) && structurally_compatible(b1, b2)
		}
		(Ty::App(f1, a1), Ty::App(f2, a2)) => {
			structurally_compatible(f1, f2) && structurally_compatible(a1, a2)
		}
		_ => false,
	}
}

fn candidate_names(candidates: &[(Name, Ty)]) -> String {
	candidates
		.iter()
		.map(|(n, _)| n.as_str())
		.collect::<Vec<_>>()
		.join(", ")
}

fn candidate_names_ref(candidates: &[&(Name, Ty)]) -> String {
	candidates
		.iter()
		.map(|(n, _)| n.as_str())
		.collect::<Vec<_>>()
		.join(", ")
}

// ============================================================================
// Pretty-printing
// ============================================================================

impl fmt::Display for Atom {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Atom::Var(n) => write!(f, "{}", n),
			Atom::Lit(l) => write!(f, "{}", display_literal(l)),
			Atom::Global(n, _) => write!(f, "@{}", n),
			Atom::Method(n, _) => write!(f, "@?{}", n),
		}
	}
}

fn display_literal(l: &Literal) -> String {
	match l {
		Literal::Nil => "[]".to_string(),
		Literal::Int(n) => n.to_string(),
		Literal::Float(x) => format!("{:?}", x),
		Literal::Char(c) => format!("{:?}", c),
		Literal::String(s) => format!("{:?}", s),
		Literal::Constructor(q) => q.0.join(":"),
	}
}

impl fmt::Display for Value {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Value::Atom(a) => write!(f, "{}", a),
			Value::Lambda(p, t, body) => {
				write!(
					f,
					"fn {} : {} ->\n{}\nend",
					p,
					display_ty(t),
					indent(&body.to_string())
				)
			}
			Value::App(fa, aa) => write!(f, "{} {}", fa, aa),
			Value::Pair(a, b) => write!(f, "({} * {})", a, b),
			Value::Ctor(tag, Some(p)) => write!(f, "{} {}", tag, p),
			Value::Ctor(tag, None) => write!(f, "{}", tag),
			Value::Proj(a, Side::Fst) => write!(f, "fst {}", a),
			Value::Proj(a, Side::Rst) => write!(f, "rst {}", a),
			Value::Unwrap(a) => write!(f, "unwrap {}", a),
			Value::Str(s) => write!(f, "{:?}", s),
			Value::Fail(m) => write!(f, "fail {:?}", m),
		}
	}
}

fn indent(s: &str) -> String {
	s.lines()
		.map(|l| format!("    {}", l))
		.collect::<Vec<_>>()
		.join("\n")
}

impl fmt::Display for Expr {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Expr::Let(x, t, v, rest) => {
				write!(f, "let {} : {} = {}\n{}", x, display_ty(t), v, rest)
			}
			Expr::Halt(a) => write!(f, "{}", a),
			Expr::Case(scrut, arms) => {
				writeln!(f, "case {} of", scrut)?;
				for arm in arms {
					let pat_str = match &arm.pat {
						CasePat::Wild => "_".to_string(),
						CasePat::Lit(l) => display_literal(l),
						CasePat::Ctor(tag) => tag.clone(),
					};
					writeln!(f, "  {} ->", pat_str)?;
					write!(f, "{}", indent(&indent(&arm.body.to_string())))?;
					writeln!(f)?;
				}
				write!(f, "end")
			}
		}
	}
}

impl fmt::Display for Function {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let ps: Vec<String> = self
			.params
			.iter()
			.map(|(n, t)| format!("{} : {}", n, display_ty(t)))
			.collect();
		writeln!(
			f,
			"fn {}({}) : {}:",
			self.name,
			ps.join(", "),
			display_ty(&self.ret)
		)?;
		write!(f, "{}", indent(&self.body.to_string()))
	}
}

impl fmt::Display for IrProgram {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		for e in &self.externs {
			writeln!(
				f,
				"extern {} : {} (arity {})",
				e.name,
				display_ty(&e.ty),
				e.arity
			)?;
		}
		writeln!(f)?;
		for func in &self.functions {
			writeln!(f, "{}\n", func)?;
		}
		Ok(())
	}
}

// ============================================================================
// Lowering
// ============================================================================

type Binds = Vec<(Name, Ty, Value)>;

/// One pattern-matrix row during match compilation.
#[derive(Clone)]
struct Row<'a> {
	pats: Vec<Pattern>,
	env: HashMap<String, Name>,
	body: &'a TypedExpr,
}

/// One column of the pattern matrix: the scrutinee variable and its type.
#[derive(Clone)]
struct Col {
	var: Name,
	ty: Ty,
}

/// What a pattern's head tests for, after normalisation.
#[derive(Clone)]
enum Head {
	Wild,
	Ctor(String, Option<Pattern>),
	Lit(Literal),
}

pub struct Lowerer<'l> {
	lang: &'l Lang,
	counter: u64,
	dispatch: HashMap<String, Vec<(Name, Ty)>>,
	canonical: HashSet<Name>,
	class_methods: ImHashMap<String, String>,
	/// `[Type, Ctor]` -> the constructor's generic scheme.
	data_ctors: HashMap<Vec<String>, Scheme>,
	/// data type name -> its constructor names (sorted).
	type_ctor_names: HashMap<String, Vec<String>>,
	type_arity: ImHashMap<String, usize>,
	aliases: ImHashMap<String, Ty>,
	errors: Vec<(String, Span)>,
	current_span: Span,
}

impl<'l> Lowerer<'l> {
	fn new(
		lang: &'l Lang,
		dispatch: HashMap<String, Vec<(Name, Ty)>>,
		canonical: HashSet<Name>,
		class_methods: ImHashMap<String, String>,
		env: &TypeEnv,
	) -> Self {
		let data_ctors: HashMap<Vec<String>, Scheme> = env
			.data_ctors
			.iter()
			.filter(|(k, _)| k.len() == 2)
			.map(|(k, v)| (k.clone(), v.clone()))
			.collect();
		let mut type_ctor_names: HashMap<String, Vec<String>> = HashMap::new();
		for k in data_ctors.keys() {
			type_ctor_names
				.entry(k[0].clone())
				.or_default()
				.push(k[1].clone());
		}
		for v in type_ctor_names.values_mut() {
			v.sort();
			v.dedup();
		}
		Self {
			lang,
			counter: 0,
			dispatch,
			canonical,
			class_methods,
			data_ctors,
			type_ctor_names,
			type_arity: env.type_ctors.clone(),
			aliases: env.type_aliases.clone(),
			errors: Vec::new(),
			current_span: Span::synthetic(0),
		}
	}

	fn err(&mut self, msg: impl Into<String>) {
		let span = self.current_span;
		self.errors.push((msg.into(), span));
	}

	fn fresh(&mut self, hint: &str) -> Name {
		self.counter += 1;
		let clean: String = hint
			.chars()
			.map(|c| {
				if c.is_alphanumeric() || c == '_' {
					c
				} else {
					'_'
				}
			})
			.collect();
		format!("{}${}", clean, self.counter)
	}

	/// The nominal data-type name of `ty`, seeing through aliases and through the
	/// structural `Sum` a zero-parameter alias like `Bool` unifies down to.
	fn data_head(&self, ty: &Ty) -> Option<String> {
		match ty {
			Ty::Named(n) => {
				if self.type_ctor_names.contains_key(n) {
					Some(n.clone())
				} else {
					self.aliases.get(n).and_then(|a| self.data_head(a))
				}
			}
			Ty::App(f, _) => self.data_head(f),
			Ty::Sum(..) => {
				fn leaves(t: &Ty, out: &mut Vec<String>) -> bool {
					match t {
						Ty::Sum(a, b) => leaves(a, out) && leaves(b, out),
						Ty::Named(n) => {
							out.push(n.clone());
							true
						}
						Ty::App(f, _) => leaves(f, out),
						_ => false,
					}
				}
				let mut ls = Vec::new();
				if !leaves(ty, &mut ls) {
					return None;
				}
				ls.sort();
				ls.dedup();
				self.type_ctor_names
					.iter()
					.find(|(tn, cs)| {
						self.type_arity.get(*tn).copied().unwrap_or(0) == 0 && **cs == ls
					})
					.map(|(tn, _)| tn.clone())
			}
			_ => None,
		}
	}

	// ---- global resolution ---------------------------------------------------

	fn resolve_global(&mut self, path: &[String], occurrence_ty: &Ty) -> Atom {
		let joined = path.join(":");
		if self.canonical.contains(&joined) {
			return Atom::Global(joined, occurrence_ty.clone());
		}
		let bare = path.last().cloned().unwrap_or_else(|| joined.clone());
		// A class method is resolved by the specializer, when its type is concrete.
		if self.class_methods.contains_key(&bare) {
			return Atom::Method(bare, occurrence_ty.clone());
		}
		match self.dispatch.get(&bare) {
			None => {
				self.err(format!("unresolved reference to `{}`", joined));
				Atom::Lit(Literal::Int(0))
			}
			Some(candidates) if candidates.len() == 1 => {
				Atom::Global(candidates[0].0.clone(), occurrence_ty.clone())
			}
			Some(candidates) => {
				let candidates = candidates.clone();
				let matches: Vec<&(Name, Ty)> = candidates
					.iter()
					.filter(|(_, ty)| structurally_compatible(ty, occurrence_ty))
					.collect();
				match matches.as_slice() {
					[one] => Atom::Global(one.0.clone(), occurrence_ty.clone()),
					[] => {
						self.err(format!(
							"ambiguous reference to `{}`: none of its {} definitions ({}) match the type inferred at this use ({})",
							bare,
							candidates.len(),
							candidate_names(&candidates),
							display_ty(occurrence_ty)
						));
						Atom::Lit(Literal::Int(0))
					}
					_ => {
						self.err(format!(
							"ambiguous reference to `{}`: {} definitions ({}) all match the type inferred at this use ({})",
							bare,
							matches.len(),
							candidate_names_ref(&matches),
							display_ty(occurrence_ty)
						));
						Atom::Lit(Literal::Int(0))
					}
				}
			}
		}
	}

	// ---- constructors ----------------------------------------------------------

	/// Canonical `Type:Ctor` for a constructor reference, given the type the
	/// constructor *produces* (needed only when the path is a bare `Ctor`).
	fn ctor_canonical(&self, path: &[String], result_ty: &Ty) -> Option<String> {
		let c = path.last()?;
		let t = if path.len() >= 2 {
			path[path.len() - 2].clone()
		} else {
			self.data_head(result_ty)?
		};
		if self.data_ctors.contains_key(&vec![t.clone(), c.clone()]) {
			Some(format!("{}:{}", t, c))
		} else {
			None
		}
	}

	fn ctor_scheme(&self, canon: &str) -> Option<&Scheme> {
		let (t, c) = canon.rsplit_once(':')?;
		self.data_ctors.get(&vec![t.to_string(), c.to_string()])
	}

	fn ctor_has_payload(&self, canon: &str) -> bool {
		matches!(self.ctor_scheme(canon).map(|s| &s.ty), Some(Ty::Fn(..)))
	}

	/// The payload type of `canon` instantiated so its result is `result_ty`.
	/// `Some(None)` = nullary constructor; `None` = unknown constructor.
	fn ctor_payload_ty(&self, canon: &str, result_ty: &Ty) -> Option<Option<Ty>> {
		// The two constructors of an anonymous sum `a + b` belong to no declared type.
		if let Ty::Sum(a, b) = result_ty {
			if canon == self.lang.item(LangItem::SumLeft) {
				return Some(Some((**a).clone()));
			}
			if canon == self.lang.item(LangItem::SumRight) {
				return Some(Some((**b).clone()));
			}
		}
		let sch = self.ctor_scheme(canon)?;
		let (p, r) = match &sch.ty {
			Ty::Fn(p, r) => (Some(&**p), &**r),
			r => (None, r),
		};
		let mut m = HashMap::new();
		match_ty(r, result_ty, &mut m);
		Some(p.map(|p| subst_ty(p, &m)))
	}

	/// The type a constructor reference of occurrence type `ty` produces.
	fn ctor_result(ty: &Ty) -> &Ty {
		match ty {
			Ty::Fn(_, r) => r,
			other => other,
		}
	}

	/// Is `path` a constructor reference (and not a local or a global)?
	fn is_ctor_ref(&self, path: &[String], ty: &Ty, env: &HashMap<String, Name>) -> Option<String> {
		if path.len() == 1 && env.contains_key(&path[0]) {
			return None;
		}
		let joined = path.join(":");
		let bare = path.last()?;
		if self.canonical.contains(&joined) || self.dispatch.contains_key(bare) {
			return None;
		}
		self.ctor_canonical(path, Self::ctor_result(ty))
	}

	fn ctor_value(&mut self, canon: String, ty: &Ty, binds: &mut Binds) -> Atom {
		let x = self.fresh("ctor");
		if !self.ctor_has_payload(&canon) {
			binds.push((x.clone(), ty.clone(), Value::Ctor(canon, None)));
			return Atom::Var(x);
		}
		let (p_ty, r_ty) = match ty {
			Ty::Fn(a, b) => ((**a).clone(), (**b).clone()),
			other => {
				self.err(format!(
					"constructor `{}` used at non-function type {}",
					canon,
					display_ty(other)
				));
				return Atom::Lit(Literal::Int(0));
			}
		};
		let p = self.fresh("cp");
		let r = self.fresh("cr");
		let body = Expr::Let(
			r.clone(),
			r_ty,
			Value::Ctor(canon, Some(Atom::Var(p.clone()))),
			Box::new(Expr::Halt(Atom::Var(r))),
		);
		binds.push((
			x.clone(),
			ty.clone(),
			Value::Lambda(p, p_ty, Box::new(body)),
		));
		Atom::Var(x)
	}

	/// Constructor reference appearing as the head of an application.
	fn ctor_head(&self, e: &TypedExpr, env: &HashMap<String, Name>) -> Option<String> {
		match e {
			TypedExpr::Var(path, ty) => self.is_ctor_ref(path, ty, env),
			TypedExpr::Literal(Literal::Constructor(q), ty) => {
				self.ctor_canonical(&q.0, Self::ctor_result(ty))
			}
			_ => None,
		}
	}
}

fn lit_eq(a: &Literal, b: &Literal) -> bool {
	match (a, b) {
		(Literal::Int(x), Literal::Int(y)) => x == y,
		(Literal::Char(x), Literal::Char(y)) => x == y,
		(Literal::Float(x), Literal::Float(y)) => x.to_bits() == y.to_bits(),
		_ => false,
	}
}

pub fn fn_chain(params: &[(Name, Ty)], ret: &Ty) -> Ty {
	let mut t = ret.clone();
	for (_, p) in params.iter().rev() {
		t = Ty::Fn(Box::new(p.clone()), Box::new(t));
	}
	t
}

fn wrap_lets(binds: Binds, tail: Expr) -> Expr {
	let mut e = tail;
	for (x, t, v) in binds.into_iter().rev() {
		e = Expr::Let(x, t, v, Box::new(e));
	}
	e
}

impl<'l> Lowerer<'l> {
	// ---- atom-producing lowering, pushing needed `let`s into `binds` --------

	fn lower_atom(
		&mut self,
		e: &TypedExpr,
		env: &HashMap<String, Name>,
		binds: &mut Binds,
	) -> Atom {
		match e {
			TypedExpr::Literal(lit, ty) => match lit {
				Literal::Int(_) | Literal::Float(_) | Literal::Char(_) => Atom::Lit(lit.clone()),
				Literal::String(s) => {
					let x = self.fresh("str");
					binds.push((x.clone(), ty.clone(), Value::Str(s.clone())));
					Atom::Var(x)
				}
				Literal::Nil => {
					self.ctor_value(self.lang.item(LangItem::ListNil).to_string(), ty, binds)
				}
				Literal::Constructor(q) => match self.ctor_canonical(&q.0, Self::ctor_result(ty)) {
					Some(c) => self.ctor_value(c, ty, binds),
					None => {
						self.err(format!("unknown constructor `{}`", q.0.join(":")));
						Atom::Lit(Literal::Int(0))
					}
				},
			},
			TypedExpr::Var(path, ty) => {
				if path.len() == 1 {
					if let Some(mapped) = env.get(&path[0]) {
						return Atom::Var(mapped.clone());
					}
				}
				if let Some(c) = self.is_ctor_ref(path, ty, env) {
					return self.ctor_value(c, ty, binds);
				}
				self.resolve_global(path, ty)
			}
			TypedExpr::Undefined(ty) => {
				let x = self.fresh("undef");
				binds.push((
					x.clone(),
					ty.clone(),
					Value::Fail("evaluated `undefined`".to_string()),
				));
				Atom::Var(x)
			}
			TypedExpr::Fn(arg, body, ty) => {
				let (arg_ty, _) = match ty {
					Ty::Fn(a, b) => ((**a).clone(), (**b).clone()),
					_ => (Ty::Unit, Ty::Unit),
				};
				let fresh_arg = self.fresh(arg);
				let mut env2 = env.clone();
				env2.insert(arg.clone(), fresh_arg.clone());
				let body_expr = self.lower_body(body, &env2);
				let x = self.fresh("clo");
				binds.push((
					x.clone(),
					ty.clone(),
					Value::Lambda(fresh_arg, arg_ty, Box::new(body_expr)),
				));
				Atom::Var(x)
			}
			TypedExpr::App(func, arg, ty) => {
				if let Some(c) = self.ctor_head(func, env) {
					if self.ctor_has_payload(&c) {
						let aa = self.lower_atom(arg, env, binds);
						let x = self.fresh("r");
						binds.push((x.clone(), ty.clone(), Value::Ctor(c, Some(aa))));
						return Atom::Var(x);
					}
				}
				let fa = self.lower_atom(func, env, binds);
				let aa = self.lower_atom(arg, env, binds);
				let x = self.fresh("r");
				binds.push((x.clone(), ty.clone(), Value::App(fa, aa)));
				Atom::Var(x)
			}
			TypedExpr::Product(a, b, ty) => {
				let aa = self.lower_atom(a, env, binds);
				let ba = self.lower_atom(b, env, binds);
				let x = self.fresh("pair");
				binds.push((x.clone(), ty.clone(), Value::Pair(aa, ba)));
				Atom::Var(x)
			}
			TypedExpr::Match(cases, ty) => {
				let arity = cases.first().map(|(p, _)| p.len()).unwrap_or(0);
				if arity == 0 {
					let x = self.fresh("empty_match");
					binds.push((
						x.clone(),
						ty.clone(),
						Value::Fail("empty match".to_string()),
					));
					return Atom::Var(x);
				}
				let (ptys, ret_ty) = peel_fn(ty, arity);
				if ptys.len() < arity {
					self.err(
						"internal error: a `match` has more patterns than its type has parameters",
					);
					return Atom::Lit(Literal::Int(0));
				}
				let params: Vec<(Name, Ty)> =
					ptys.into_iter().map(|t| (self.fresh("m"), t)).collect();
				let cols: Vec<Col> = params
					.iter()
					.map(|(n, t)| Col {
						var: n.clone(),
						ty: t.clone(),
					})
					.collect();
				let rows: Vec<Row> = cases
					.iter()
					.map(|(pats, body)| Row {
						pats: pats.clone(),
						env: env.clone(),
						body,
					})
					.collect();
				let body = self.compile_match(cols, rows, &ret_ty);
				let value = self.build_curried_lambda(&params, &ret_ty, body);
				let x = self.fresh("match");
				binds.push((x.clone(), ty.clone(), value));
				Atom::Var(x)
			}
		}
	}

	/// Lower a sub-expression in tail position into its own let-chain.
	fn lower_body(&mut self, e: &TypedExpr, env: &HashMap<String, Name>) -> Expr {
		let mut binds = Vec::new();
		let atom = self.lower_atom(e, env, &mut binds);
		wrap_lets(binds, Expr::Halt(atom))
	}

	fn build_curried_lambda(&mut self, params: &[(Name, Ty)], ret: &Ty, body: Expr) -> Value {
		let (p, t) = params[0].clone();
		if params.len() == 1 {
			return Value::Lambda(p, t, Box::new(body));
		}
		let inner = self.build_curried_lambda(&params[1..], ret, body);
		let inner_ty = fn_chain(&params[1..], ret);
		let g = self.fresh("g");
		Value::Lambda(
			p,
			t,
			Box::new(Expr::Let(
				g.clone(),
				inner_ty,
				inner,
				Box::new(Expr::Halt(Atom::Var(g))),
			)),
		)
	}

	fn fail_expr(&mut self, ret_ty: &Ty, msg: &str) -> Expr {
		let f = self.fresh("fail");
		Expr::Let(
			f.clone(),
			ret_ty.clone(),
			Value::Fail(msg.to_string()),
			Box::new(Expr::Halt(Atom::Var(f))),
		)
	}

	// ---- match compilation (decision trees) ---------------------------------

	/// Classic column-wise pattern-matrix compilation. Binds variable patterns
	/// directly to scrutinee variables, then dispatches on the first refutable
	/// column of the first row. The tests for one column are emitted once, as a
	/// single `Case`; rows are *specialised* per constructor/literal rather than
	/// re-tested.
	fn compile_match<'a>(&mut self, cols: Vec<Col>, mut rows: Vec<Row<'a>>, ret_ty: &Ty) -> Expr {
		if rows.is_empty() {
			return self.fail_expr(ret_ty, "non-exhaustive pattern match");
		}
		for row in rows.iter_mut() {
			for (j, p) in row.pats.iter_mut().enumerate() {
				if let Pattern::Variable(n) = p {
					row.env.insert(n.clone(), cols[j].var.clone());
					*p = Pattern::Hole;
				}
			}
		}
		let Some(j) = rows[0]
			.pats
			.iter()
			.position(|p| !matches!(p, Pattern::Hole))
		else {
			let env = rows[0].env.clone();
			return self.lower_body(rows[0].body, &env);
		};
		if matches!(rows[0].pats[j], Pattern::Product(..)) {
			self.match_product(cols, rows, j, ret_ty)
		} else {
			self.match_heads(cols, rows, j, ret_ty)
		}
	}

	fn match_product<'a>(
		&mut self,
		cols: Vec<Col>,
		rows: Vec<Row<'a>>,
		j: usize,
		ret_ty: &Ty,
	) -> Expr {
		let col = cols[j].clone();
		let (ta, tb) = match &col.ty {
			Ty::Product(a, b) => ((**a).clone(), (**b).clone()),
			other => {
				self.err(format!(
					"a product pattern is matched against non-product type {}",
					display_ty(other)
				));
				return self.fail_expr(ret_ty, "ill-typed product pattern");
			}
		};
		let fl = self.fresh("fst");
		let fr = self.fresh("rst");
		let mut new_cols = cols.clone();
		new_cols[j] = Col {
			var: fl.clone(),
			ty: ta.clone(),
		};
		new_cols.insert(
			j + 1,
			Col {
				var: fr.clone(),
				ty: tb.clone(),
			},
		);
		let mut new_rows = Vec::new();
		for row in rows {
			let mut nr = row.clone();
			match &row.pats[j] {
				Pattern::Product(l, r) => {
					nr.pats[j] = l.item.clone();
					nr.pats.insert(j + 1, r.item.clone());
				}
				_ => {
					nr.pats[j] = Pattern::Hole;
					nr.pats.insert(j + 1, Pattern::Hole);
				}
			}
			new_rows.push(nr);
		}
		let inner = self.compile_match(new_cols, new_rows, ret_ty);
		Expr::Let(
			fl,
			ta,
			Value::Proj(Atom::Var(col.var.clone()), Side::Fst),
			Box::new(Expr::Let(
				fr,
				tb,
				Value::Proj(Atom::Var(col.var), Side::Rst),
				Box::new(inner),
			)),
		)
	}

	fn head_of(&mut self, p: &Pattern, col_ty: &Ty) -> Head {
		match p {
			Pattern::Hole | Pattern::Variable(_) => Head::Wild,
			Pattern::Literal(Literal::Nil) => {
				Head::Ctor(self.lang.item(LangItem::ListNil).to_string(), None)
			}
			Pattern::Literal(Literal::Constructor(q)) => match self.ctor_canonical(&q.0, col_ty) {
				Some(c) => Head::Ctor(c, None),
				None => {
					self.err(format!("unknown constructor pattern `{}`", q.0.join(":")));
					Head::Wild
				}
			},
			// A string pattern is sugar for the list-of-chars pattern.
			Pattern::Literal(Literal::String(s)) => {
				let mut it = s.chars();
				match it.next() {
					None => Head::Ctor(self.lang.item(LangItem::ListNil).to_string(), None),
					Some(c) => {
						let rest: String = it.collect();
						let sp = self.current_span;
						Head::Ctor(
							self.lang.item(LangItem::ListCons).to_string(),
							Some(Pattern::Product(
								Box::new(Spanned {
									item: Pattern::Literal(Literal::Char(c)),
									span: sp,
								}),
								Box::new(Spanned {
									item: Pattern::Literal(Literal::String(rest)),
									span: sp,
								}),
							)),
						)
					}
				}
			}
			Pattern::Literal(l) => Head::Lit(l.clone()),
			Pattern::Constructor(q, sub) => match self.ctor_canonical(&q.item.0, col_ty) {
				Some(c) => Head::Ctor(c, Some(sub.item.clone())),
				None => {
					self.err(format!(
						"unknown constructor pattern `{}`",
						q.item.0.join(":")
					));
					Head::Wild
				}
			},
			Pattern::Left(sub) => Head::Ctor(
				self.lang.item(LangItem::SumLeft).to_string(),
				Some(sub.item.clone()),
			),
			Pattern::Right(sub) => Head::Ctor(
				self.lang.item(LangItem::SumRight).to_string(),
				Some(sub.item.clone()),
			),
			Pattern::Product(..) => {
				self.err("internal error: a product pattern appeared in a constructor column");
				Head::Wild
			}
		}
	}

	fn match_heads<'a>(
		&mut self,
		cols: Vec<Col>,
		rows: Vec<Row<'a>>,
		j: usize,
		ret_ty: &Ty,
	) -> Expr {
		let col = cols[j].clone();
		let mut heads: Vec<Head> = Vec::with_capacity(rows.len());
		for r in &rows {
			let p = r.pats[j].clone();
			heads.push(self.head_of(&p, &col.ty));
		}
		let mut keys: Vec<(String, Head)> = Vec::new();
		for h in &heads {
			let k = match h {
				Head::Wild => continue,
				Head::Ctor(c, _) => format!("c:{}", c),
				Head::Lit(l) => format!("l:{:?}", l),
			};
			if !keys.iter().any(|(kk, _)| *kk == k) {
				keys.push((k, h.clone()));
			}
		}

		let mut arms: Vec<Arm> = Vec::new();
		let mut all_ctors = true;
		let mut type_name: Option<String> = None;
		for (_, rep) in &keys {
			match rep {
				Head::Ctor(c, _) => {
					if type_name.is_none() {
						type_name = c.rsplit_once(':').map(|(t, _)| t.to_string());
					}
					let pty: Option<Ty> = match self.ctor_payload_ty(c, &col.ty) {
						Some(p) => p,
						None => {
							self.err(format!("unknown constructor `{}`", c));
							None
						}
					};
					let has = pty.is_some();
					let payload_var = self.fresh("payload");
					let mut new_cols = cols.clone();
					if let Some(t) = &pty {
						new_cols[j] = Col {
							var: payload_var.clone(),
							ty: t.clone(),
						};
					} else {
						new_cols.remove(j);
					}
					let mut new_rows = Vec::new();
					for (row, h) in rows.iter().zip(heads.iter()) {
						let mut nr = row.clone();
						match h {
							Head::Ctor(c2, sub) if c2 == c => {
								if has {
									nr.pats[j] = sub.clone().unwrap_or(Pattern::Hole);
								} else {
									nr.pats.remove(j);
								}
							}
							Head::Wild => {
								if has {
									nr.pats[j] = Pattern::Hole;
								} else {
									nr.pats.remove(j);
								}
							}
							_ => continue,
						}
						new_rows.push(nr);
					}
					let inner = self.compile_match(new_cols, new_rows, ret_ty);
					let body = match pty {
						Some(t) => Expr::Let(
							payload_var,
							t,
							Value::Unwrap(Atom::Var(col.var.clone())),
							Box::new(inner),
						),
						None => inner,
					};
					arms.push(Arm {
						pat: CasePat::Ctor(c.clone()),
						body,
					});
				}
				Head::Lit(l) => {
					all_ctors = false;
					let mut new_cols = cols.clone();
					new_cols.remove(j);
					let mut new_rows = Vec::new();
					for (row, h) in rows.iter().zip(heads.iter()) {
						let keep = match h {
							Head::Lit(l2) => lit_eq(l, l2),
							Head::Wild => true,
							Head::Ctor(..) => false,
						};
						if keep {
							let mut nr = row.clone();
							nr.pats.remove(j);
							new_rows.push(nr);
						}
					}
					let body = self.compile_match(new_cols, new_rows, ret_ty);
					arms.push(Arm {
						pat: CasePat::Lit(l.clone()),
						body,
					});
				}
				Head::Wild => {}
			}
		}

		let (lname, rname) = (
			self.lang.item(LangItem::SumLeft),
			self.lang.item(LangItem::SumRight),
		);
		let has = |n: &str| keys.iter().any(|(k, _)| k == &format!("c:{}", n));
		let anon_sum_complete = has(lname) && has(rname);
		let exhaustive = all_ctors
			&& !keys.is_empty()
			&& (anon_sum_complete
				|| type_name
					.as_ref()
					.and_then(|t| self.type_ctor_names.get(t))
					.map_or(false, |cs| cs.len() == keys.len()));
		if !exhaustive {
			// if exactly one ctor missing, just name it instead of `_`
			// removes a redundant case
			let missing = if all_ctors && !keys.is_empty() {
				self.single_missing_ctor(&keys, type_name.as_deref(), lname, rname)
			} else {
				None
			};
			let mut new_cols = cols.clone();
			new_cols.remove(j);
			let mut new_rows = Vec::new();
			for (row, h) in rows.iter().zip(heads.iter()) {
				if matches!(h, Head::Wild) {
					let mut nr = row.clone();
					nr.pats.remove(j);
					new_rows.push(nr);
				}
			}
			let body = self.compile_match(new_cols, new_rows, ret_ty);
			arms.push(Arm {
				pat: match missing {
					Some(c) => CasePat::Ctor(c),
					None => CasePat::Wild,
				},
				body,
			});
		}
		Expr::Case(Atom::Var(col.var), arms)
	}

	fn single_missing_ctor(
		&self,
		keys: &[(String, Head)],
		type_name: Option<&str>,
		lname: &str,
		rname: &str,
	) -> Option<String> {
		let present = |canon: &str| keys.iter().any(|(k, _)| *k == format!("c:{}", canon));

		// anonymous sum: only one of the two sides was matched
		let (pl, pr) = (present(lname), present(rname));
		if pl != pr {
			return Some(if pl { rname } else { lname }.to_string());
		}

		let t = type_name?;
		let all = self.type_ctor_names.get(t)?;
		let missing: Vec<&String> = all
			.iter()
			.filter(|c| !present(&format!("{}:{}", t, c)))
			.collect();
		match missing.as_slice() {
			[one] => Some(format!("{}:{}", t, one)),
			_ => None,
		}
	}

	// ---- top-level bindings --------------------------------------------------

	fn lower_binding(&mut self, name: &str, e: &TypedExpr, span: Span) -> Function {
		self.current_span = span;
		let mut params: Vec<(Name, Ty)> = Vec::new();
		let mut env = HashMap::new();
		let mut cur = e;
		while let TypedExpr::Fn(arg, body, fty) = cur {
			let fresh = self.fresh(arg);
			env.insert(arg.clone(), fresh.clone());
			let pty = match fty {
				Ty::Fn(a, _) => (**a).clone(),
				_ => Ty::Unit,
			};
			params.push((fresh, pty));
			cur = body;
		}

		if let TypedExpr::Match(cases, mty) = cur {
			let arity = cases.first().map(|(p, _)| p.len()).unwrap_or(0);
			if arity > 0 {
				let (ptys, ret_ty) = peel_fn(mty, arity);
				if ptys.len() == arity {
					let match_params: Vec<(Name, Ty)> =
						ptys.into_iter().map(|t| (self.fresh("m"), t)).collect();
					let cols: Vec<Col> = match_params
						.iter()
						.map(|(n, t)| Col {
							var: n.clone(),
							ty: t.clone(),
						})
						.collect();
					let rows: Vec<Row> = cases
						.iter()
						.map(|(pats, body)| Row {
							pats: pats.clone(),
							env: env.clone(),
							body,
						})
						.collect();
					let body_expr = self.compile_match(cols, rows, &ret_ty);
					params.extend(match_params);
					return Function {
						name: name.to_string(),
						params,
						ret: ret_ty,
						ty: e.ty().clone(),
						body: body_expr,
						span,
					};
				}
			}
		}

		let body_expr = self.lower_body(cur, &env);
		Function {
			name: name.to_string(),
			params,
			ret: cur.ty().clone(),
			ty: e.ty().clone(),
			body: body_expr,
			span,
		}
	}
}

/// Lower every top-level binding (already flattened by the typechecker,
/// prelude first) into typed ANF. Bindings whose value is `undefined` become
/// `Extern`s (tagged with the intrinsic the lang manifest maps them to);
/// everything else becomes a `Function`. Class-method references stay
/// `Atom::Method` for the specializer; the returned `Overloads` is what it
/// needs to resolve them.
///
/// Returns every lowering error found (each with the span of the binding it
/// occurred in) as diagnostics, rather than stopping at the first.
pub fn lower_program(
	bindings: &[Spanned<TypedBinding>],
	env: &TypeEnv,
	lang: &Lang,
) -> Result<(IrProgram, Overloads), Vec<Diagnostic>> {
	struct Entry<'a> {
		canonical: Name,
		bare: String,
		ty: &'a Ty,
		value: &'a Option<TypedExpr>,
		span: Span,
	}

	let mut seen: HashSet<Name> = HashSet::new();
	let mut entries: Vec<Entry> = Vec::with_capacity(bindings.len());
	let mut errors: Vec<Diagnostic> = Vec::new();

	for spanned in bindings {
		let b = &spanned.item;
		let canonical = b.qualified_name.clone().unwrap_or_else(|| b.name.clone());
		// Two bindings with one canonical identity would silently alias each other;
		// the typechecker is supposed to prevent it, so say so instead of inventing a suffix.
		if !seen.insert(canonical.clone()) {
			errors.push(Diagnostic::error(
				format!("`{}` is defined more than once", canonical),
				Some(spanned.span),
			));
			continue;
		}
		entries.push(Entry {
			canonical,
			bare: b.name.clone(),
			ty: &b.ty,
			value: &b.value,
			span: spanned.span,
		});
	}

	let mut dispatch: HashMap<String, Vec<(Name, Ty)>> = HashMap::new();
	for e in &entries {
		dispatch
			.entry(e.bare.clone())
			.or_default()
			.push((e.canonical.clone(), e.ty.clone()));
	}
	let canonical_set: HashSet<Name> = entries.iter().map(|e| e.canonical.clone()).collect();

	// The class parameter of a method is the type variable its scheme constrains by its class.
	let mut methods: HashMap<String, (Ty, u32)> = HashMap::new();
	for (class_name, def) in &env.classes {
		for (method, scheme) in &def.methods {
			let class_var = scheme
				.constraints
				.iter()
				.find(|(_, classes)| classes.contains(class_name))
				.map(|(v, _)| *v)
				.or_else(|| scheme.constraints.keys().next().copied());
			match class_var {
				Some(v) => {
					methods.insert(method.clone(), (scheme.ty.clone(), v));
				}
				None => errors.push(Diagnostic::error(
					format!(
						"cannot determine the class parameter of method `{}` of class `{}`",
						method, class_name
					),
					None,
				)),
			}
		}
	}

	let mut data_ctor_names: HashMap<String, Vec<String>> = HashMap::new();
	for k in env.data_ctors.keys().filter(|k| k.len() == 2) {
		data_ctor_names
			.entry(k[0].clone())
			.or_default()
			.push(k[1].clone());
	}
	for v in data_ctor_names.values_mut() {
		v.sort();
		v.dedup();
	}
	let overloads = Overloads {
		methods,
		class_of: env.class_methods.clone(),
		canonical: canonical_set.clone(),
		type_ctor_names: data_ctor_names,
		type_arity: env.type_ctors.clone(),
		aliases: env.type_aliases.clone(),
	};

	let mut lowerer = Lowerer::new(
		lang,
		dispatch,
		canonical_set,
		env.class_methods.clone(),
		env,
	);
	let mut functions = Vec::new();
	let mut externs = Vec::new();
	for e in &entries {
		match e.value {
			None => externs.push(Extern {
				name: e.canonical.clone(),
				arity: count_arrows(e.ty),
				ty: e.ty.clone(),
				intrinsic: lang.intrinsic(&e.canonical),
				span: e.span,
			}),
			Some(value) => functions.push(lowerer.lower_binding(&e.canonical, value, e.span)),
		}
	}
	errors.extend(
		lowerer
			.errors
			.into_iter()
			.map(|(m, sp)| Diagnostic::error(format!("could not lower to IR: {}", m), Some(sp))),
	);
	if errors.is_empty() {
		Ok((IrProgram { functions, externs }, overloads))
	} else {
		Err(errors)
	}
}
