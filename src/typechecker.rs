// HM typechecker (Algorithm W)

use crate::{
	diag::Diagnostic,
	kind::Kind,
	parser::{
		Binding, Constraint, Expr, Literal, Pattern, Program, Qualified, Quantity, SourceRegistry,
		Span, Spanned, TopLevel, Type as AstType,
	},
	tyfun::{is_fn_app, reduce_app, register, take_errors},
	tynorm::{Poly, Solve, poly_apart, solve},
	types::{register_alias, register_promoted, spine},
};
use im::{HashMap as ImMap, Vector as ImVec};
use itertools::Itertools;
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
	Unit,
	Int,
	Float,
	Char,
	Var(u32),
	Named(String),
	App(Box<Ty>, Box<Ty>),
	Fn(Box<Ty>, Box<Ty>),
	Product(Box<Ty>, Box<Ty>),
	Sum(Box<Ty>, Box<Ty>),
	/// A type-level natural number literal.
	Lit(u64),
}

impl Ty {
	pub fn display(&self, subst: &Subst) -> String {
		let names = default_type_var_names(&subst.apply(self));
		display_ty_with_names(&subst.apply(self), subst, &names)
	}
}

fn display_ty_with_names(ty: &Ty, subst: &Subst, names: &HashMap<u32, String>) -> String {
	match ty {
		Ty::Unit => "Unit".into(),
		Ty::Int => "Int".into(),
		Ty::Float => "Float".into(),
		Ty::Char => "Char".into(),

		Ty::Named(s) => s.clone(),

		Ty::Lit(n) => n.to_string(),

		Ty::Var(n) => names.get(n).cloned().unwrap_or_else(|| format!("t{}", n)),

		Ty::App(f, a) => format!(
			"({} {})",
			display_ty_with_names(f, subst, names),
			display_ty_with_names(a, subst, names),
		),

		Ty::Fn(a, b) => format!(
			"({} -> {})",
			display_ty_with_names(a, subst, names),
			display_ty_with_names(b, subst, names),
		),

		Ty::Product(a, b) => format!(
			"({} * {})",
			display_ty_with_names(a, subst, names),
			display_ty_with_names(b, subst, names),
		),

		Ty::Sum(a, b) => format!(
			"({} + {})",
			display_ty_with_names(a, subst, names),
			display_ty_with_names(b, subst, names),
		),
	}
}

fn collect_ty_vars(ty: &Ty, out: &mut Vec<u32>) {
	match ty {
		Ty::Var(n) if !out.contains(n) => {
			out.push(*n);
		}

		Ty::Fn(a, b) | Ty::App(a, b) | Ty::Product(a, b) | Ty::Sum(a, b) => {
			collect_ty_vars(a, out);
			collect_ty_vars(b, out);
		}

		_ => {}
	}
}

fn default_type_var_names(ty: &Ty) -> HashMap<u32, String> {
	let mut vars = Vec::new();
	collect_ty_vars(ty, &mut vars);

	let mut names = HashMap::new();
	let mut used = std::collections::HashSet::new();

	let preferred = [
		"a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r",
		"s", "u", "v", "w", "x", "y", "z",
	];

	let mut letter_idx = 0;
	let mut overflow_idx = 0;

	for var in vars {
		let name = loop {
			let candidate = if letter_idx < preferred.len() {
				letter_idx += 1;
				preferred[letter_idx].to_string()
			} else {
				overflow_idx += 1;
				format!("t{}", overflow_idx)
			};
			if !used.contains(&candidate) {
				break candidate;
			}
		};

		used.insert(name.clone());
		names.insert(var, name);
	}

	names
}

// ∀ α₁…αₙ. τ
#[derive(Debug, Clone)]
pub struct Scheme {
	pub vars: Vec<u32>,
	pub ty: Ty,
	pub constraints: HashMap<u32, HashSet<String>>, // id -> class names
}

impl Scheme {
	pub fn mono(ty: Ty) -> Self {
		Self {
			vars: vec![],
			ty,
			constraints: HashMap::new(),
		}
	}

	#[allow(unused)]
	pub fn display(&self, subst: &Subst, hints: Option<&HashMap<u32, String>>) -> String {
		if self.vars.is_empty() {
			return self.ty.display(subst);
		}

		let names = Self::build_names(&self.vars, hints);

		let ty_str = display_ty_with_names(&subst.apply(&self.ty), subst, &names);

		let var_list: Vec<&str> = self.vars.iter().map(|v| names[v].as_str()).collect();

		format!("∀{}. {}", var_list.join(" "), ty_str)
	}

	pub fn display_full(&self, name: &str, subst: &Subst) -> String {
		let names = Self::build_names(&self.vars, None);
		let ty_str = display_ty_with_names(&subst.apply(&self.ty), subst, &names);

		if self.vars.is_empty() {
			return format!("{} : {}", name, ty_str);
		}

		let var_groups: Vec<String> = self
			.vars
			.iter()
			.map(|v| {
				let vname = &names[v];
				match self.constraints.get(v) {
					Some(classes) if !classes.is_empty() => {
						format!("({}: {})", vname, classes.iter().join(" + "))
					}
					_ => format!("({})", vname),
				}
			})
			.collect();

		format!("{} {} : {}", name, var_groups.join(" "), ty_str)
	}

	fn build_names(vars: &[u32], hints: Option<&HashMap<u32, String>>) -> HashMap<u32, String> {
		let mut names: HashMap<u32, String> = HashMap::new();
		let mut used: HashSet<String> = HashSet::new();

		// assign hinted names where they exist and don't conflict
		if let Some(hints) = hints {
			let mut hint_counts: HashMap<&str, usize> = HashMap::new();
			for v in vars {
				let Some(h) = hints.get(v) else {
					continue;
				};
				*hint_counts.entry(h.as_str()).or_insert(0) += 1;
				if hint_counts[h.as_str()] == 1 {
					names.insert(*v, h.clone());
					used.insert(h.clone());
				}
			}
		}

		// assign letters then tN
		let mut candidates = (0..26)
			.map(|i| ((b'a' + i) as char).to_string())
			.chain((1..).map(|i| format!("t{i}")));
		for v in vars {
			if names.contains_key(v) {
				continue;
			}

			let name = candidates.by_ref().find(|c| !used.contains(c)).unwrap();

			used.insert(name.clone());
			names.insert(*v, name);
		}
		names
	}
}

#[derive(Debug, Clone, Default)]
/// Bindings, the order they were made in, and local rewrite rules `stuck application := type`
/// (a given equality that a branch learned about a type-level fn)
pub struct Subst(HashMap<u32, Ty>, Vec<u32>, Vec<(Ty, Ty)>);

impl Subst {
	pub fn apply(&self, ty: &Ty) -> Ty {
		match ty {
			Ty::Var(n) => match self.0.get(n) {
				Some(t) => self.apply(t),
				None => Ty::Var(*n),
			},
			Ty::Fn(a, b) => Ty::Fn(Box::new(self.apply(a)), Box::new(self.apply(b))),
			Ty::App(f, a) => {
				let before = Ty::App(Box::new(self.apply(f)), Box::new(self.apply(a)));
				let reduced = reduce_app(before.clone());
				if !self.2.is_empty() {
					// a reduction can expose new applications and a given can rewrite a stuck one
					if reduced != before {
						return self.apply(&reduced);
					}
					if is_fn_app(&reduced)
						&& let Some((_, rhs)) = self.2.iter().find(|(l, _)| *l == reduced)
					{
						return self.apply(&rhs.clone());
					}
				}
				normalize_arith(reduced)
			}
			Ty::Product(a, b) => Ty::Product(Box::new(self.apply(a)), Box::new(self.apply(b))),
			Ty::Sum(a, b) => Ty::Sum(Box::new(self.apply(a)), Box::new(self.apply(b))),
			other => other.clone(),
		}
	}

	pub fn apply_scheme(&self, s: &Scheme) -> Scheme {
		let mut sub = self.clone();
		for v in &s.vars {
			sub.0.remove(v);
		}
		Scheme {
			vars: s.vars.clone(),
			ty: sub.apply(&s.ty),
			constraints: s.constraints.clone(),
		}
	}

	// other then self
	#[allow(unused)]
	pub fn compose(&self, other: &Subst) -> Subst {
		let mut result: HashMap<u32, Ty> =
			other.0.iter().map(|(k, v)| (*k, self.apply(v))).collect();
		for (k, v) in &self.0 {
			result.entry(*k).or_insert_with(|| v.clone());
		}
		Subst(result, Vec::new(), Vec::new())
	}

	pub fn extend(&mut self, var: u32, ty: Ty) {
		self.0.insert(var, ty);
		self.1.push(var);
	}

	/// A position in the binding history, for `bound_since` / `retract` (given equalities are local to a `match` branch).
	pub fn mark(&self) -> usize {
		self.1.len()
	}

	/// Variables bound since `mark`, in order.
	pub fn bound_since(&self, mark: usize) -> Vec<u32> {
		self.1[mark..].to_vec()
	}

	/// Assume `lhs = rhs` for a stuck type-function application `lhs`, until `retract_rewrites`.
	pub fn assume_rewrite(&mut self, lhs: Ty, rhs: Ty) {
		self.2.push((lhs, rhs));
	}

	pub fn rewrite_mark(&self) -> usize {
		self.2.len()
	}

	pub fn retract_rewrites(&mut self, mark: usize) {
		self.2.truncate(mark);
	}

	/// Forget the binding of `var` (end of the branch that assumed it).
	pub fn retract(&mut self, var: u32) {
		self.0.remove(&var);
	}
}

// ---- type-level math stuff, the math itself is in tynorm.rs ----

fn arith_arity(name: &str) -> Option<usize> {
	match name {
		"Succ" => Some(1),
		"Add" | "Mul" | "Sub" => Some(2),
		_ => None,
	}
}

/// Is `t` a saturated application of a built-in type-level function?
pub fn is_arith(t: &Ty) -> bool {
	let mut n = 0;
	let mut cur = t;
	while let Ty::App(f, _) = cur {
		n += 1;
		cur = f;
	}
	matches!(cur, Ty::Named(name) if n > 0 && arith_arity(name) == Some(n))
}

/// `Some(poly)` when `t` is built from literals, variables and the built-ins
pub fn ty_to_poly(t: &Ty) -> Option<Poly<u32>> {
	match t {
		Ty::Lit(n) => Some(Poly::lit(*n)),
		Ty::Var(v) => Some(Poly::atom(*v)),
		Ty::App(..) if is_arith(t) => {
			let (h, args) = spine(t);
			let Ty::Named(name) = h else { return None };
			let ps: Vec<Poly<u32>> = args
				.iter()
				.map(|a| ty_to_poly(a))
				.collect::<Option<Vec<_>>>()?;
			match name.as_str() {
				"Succ" => ps[0].add(&Poly::constant(1)).ok(),
				"Add" => ps[0].add(&ps[1]).ok(),
				"Mul" => ps[0].mul(&ps[1]).ok(),
				// reduces only when a >= b is provable
				"Sub" => {
					let d = ps[0].sub(&ps[1]).ok()?;
					d.is_natural().then_some(d)
				}
				_ => None,
			}
		}
		_ => None,
	}
}

fn app2(name: &str, a: Ty, b: Ty) -> Ty {
	Ty::App(
		Box::new(Ty::App(Box::new(Ty::Named(name.to_string())), Box::new(a))),
		Box::new(b),
	)
}

fn add_ty(acc: Option<Ty>, t: Ty) -> Option<Ty> {
	Some(match acc {
		None => t,
		Some(a) => app2("Add", a, t),
	})
}

/// Canonical type for a natural-number polynomial: a literal, or a left-nested `Add` of
/// monomials in a fixed order, so equal polynomials give equal types
pub fn poly_to_ty(p: &Poly<u32>) -> Option<Ty> {
	poly_to_ty_with(p, &|k: &u32| Ty::Var(*k))
}

/// `poly_to_ty` for any atom type
/// `atom` says how an atom is written as a type
pub fn poly_to_ty_with<K: Ord + Clone>(p: &Poly<K>, atom: &dyn Fn(&K) -> Ty) -> Option<Ty> {
	if let Some(n) = p.as_lit() {
		return Some(Ty::Lit(n));
	}
	if !p.is_natural() {
		return None;
	}
	let mut acc: Option<Ty> = None;
	for (m, c) in p.iter() {
		if m.is_one() {
			continue;
		}
		let mut mono: Option<Ty> = None;
		for (k, e) in m.factors() {
			for _ in 0..*e {
				let v = atom(k);
				mono = Some(match mono {
					None => v,
					Some(a) => app2("Mul", a, v),
				});
			}
		}
		let mut term = mono?;
		let c = u64::try_from(*c).ok()?;
		if c != 1 {
			term = app2("Mul", Ty::Lit(c), term);
		}
		acc = add_ty(acc, term);
	}
	let k = u64::try_from(p.const_term()).ok()?;
	if k > 0 {
		acc = add_ty(acc, Ty::Lit(k));
	}
	acc
}

/// Rewrite a saturated built-in application to canonical form
/// anything else unchanged
fn normalize_arith(t: Ty) -> Ty {
	if is_arith(&t)
		&& let Some(p) = ty_to_poly(&t)
		&& let Some(n) = poly_to_ty(&p)
	{
		return n;
	}
	t
}

// ---- apartness of types (no intersection), for pruning impossible ctors ----

fn expand_alias(t: &Ty, env: &TypeEnv) -> Ty {
	let mut cur = t.clone();
	for _ in 0..16 {
		match &cur {
			Ty::Named(n) if env.type_aliases.contains_key(n) => {
				cur = env.type_aliases[n].clone();
			}
			_ => break,
		}
	}
	cur
}

/// A tag for the outermost type constructor, when it is certain.
/// Structural sums are untagged: `False + True` and `Bool` mean the same type
fn head_tag(t: &Ty) -> Option<String> {
	Some(match t {
		Ty::Unit => "Unit".to_string(),
		Ty::Int => "Int".to_string(),
		Ty::Float => "Float".to_string(),
		Ty::Char => "Char".to_string(),
		Ty::Fn(..) => "->".to_string(),
		Ty::Product(..) => "*".to_string(),
		Ty::Named(n) => n.clone(),
		Ty::App(..) => match spine(t).0 {
			Ty::Named(n) => n.clone(),
			_ => return None,
		},
		Ty::Sum(..) | Ty::Var(_) | Ty::Lit(_) => return None,
	})
}

/// Can `a` and `b` never be equal, whatever their variables stand for?
/// any doubt answers `false`, because a wrong `true` prunes a reachable
/// ctor and the program would crash at runtime
fn types_apart(a: &Ty, b: &Ty, env: &TypeEnv) -> bool {
	let (a, b) = (expand_alias(a, env), expand_alias(b, env));
	let numeric = |t: &Ty| matches!(t, Ty::Lit(_)) || is_arith(t);
	if numeric(&a) || numeric(&b) {
		return match (ty_to_poly(&a), ty_to_poly(&b)) {
			(Some(p), Some(q)) => poly_apart(&p, &q),
			_ => false,
		};
	}
	if let (Some(x), Some(y)) = (head_tag(&a), head_tag(&b))
		&& x != y
	{
		return true;
	}
	match (&a, &b) {
		(Ty::App(f1, x1), Ty::App(f2, x2)) => types_apart(f1, f2, env) || types_apart(x1, x2, env),
		(Ty::Fn(a1, b1), Ty::Fn(a2, b2))
		| (Ty::Product(a1, b1), Ty::Product(a2, b2))
		| (Ty::Sum(a1, b1), Ty::Sum(a2, b2)) => types_apart(a1, a2, env) || types_apart(b1, b2, env),
		_ => false,
	}
}

#[derive(Debug, Clone, Default)]
pub struct TypeEnv {
	pub vars: ImMap<String, Scheme>,            // binding -> scheme
	pub type_ctors: ImMap<String, usize>,       // name -> arity
	pub type_kinds: ImMap<String, Kind>,        // name -> kind
	pub data_ctors: ImMap<Vec<String>, Scheme>, // ctor -> scheme giving constructor fn type
	pub class_methods: ImMap<String, String>,   // method name -> class name
	pub classes: ImMap<String, ClassDef>,       // class name -> (params, methods)
	pub instances: ImVec<(String, Ty)>,         // (class, concrete ty head)
	pub type_aliases: ImMap<String, Ty>,
	pub instance_methods: ImMap<String, Scheme>, // per-instance concrete schemes
	pub sigma_defs: ImMap<String, SigmaDef>,     // hidden dependent-pair types
}

/// A dependent pair `(n : Nat) * T`: a hidden single-ctor data type whose
/// payload is the product `SNat n * T` with `n` existential. It is transparent: the
/// product syntax `(e1 * e2)` builds and matches it (`Checker::sigma_expand`), and
/// the backend lowers it to that product.
#[derive(Debug, Clone)]
pub struct SigmaDef {
	pub nparams: usize,
	/// `(0 n : Nat) * T`: the first component is erased, the pair is just `T`
	pub erased: bool,
	/// the payload over `Var(SIGMA_PARAM + i)` for the parameters and `Var(SIGMA_EXIST)`
	pub payload: Ty,
}

// kinda hacky but who cares, nobody will actually use that many tvars
pub const SIGMA_PARAM: u32 = 4_000_000_000;
pub const SIGMA_EXIST: u32 = 4_100_000_000;

#[allow(unused)]
#[derive(Debug, Clone)]
pub struct ClassDef {
	pub params: Vec<String>,
	pub methods: HashMap<String, Scheme>,
}

impl TypeEnv {
	#[allow(unused)]
	pub fn apply(&self, subst: &Subst) -> TypeEnv {
		let vars = self
			.vars
			.iter()
			.map(|(k, v)| (k.clone(), subst.apply_scheme(v)))
			.collect();
		TypeEnv {
			vars,
			..self.clone()
		}
	}

	pub fn insert(&mut self, name: String, scheme: Scheme) {
		self.vars.insert(name, scheme);
	}
}

fn free_vars_into(ty: &Ty, out: &mut HashSet<u32>) {
	match ty {
		Ty::Var(n) => {
			out.insert(*n);
		}
		Ty::Fn(a, b) | Ty::Product(a, b) | Ty::Sum(a, b) | Ty::App(a, b) => {
			free_vars_into(a, out);
			free_vars_into(b, out);
		}
		_ => {}
	}
}

impl TypeEnv {
	pub fn free_vars(&self) -> HashSet<u32> {
		let mut fvs = HashSet::new();
		for s in self.vars.values() {
			if s.vars.is_empty() {
				free_vars_into(&s.ty, &mut fvs);
			} else {
				let mut tmp = HashSet::new();
				free_vars_into(&s.ty, &mut tmp);
				fvs.extend(tmp.into_iter().filter(|v| !s.vars.contains(v)));
			}
		}
		fvs
	}
}

fn generalise_with_constraints(
	env: &TypeEnv,
	ty: &Ty,
	constraints: &HashMap<u32, HashSet<String>>,
) -> Scheme {
	// first-occurrence order, deduped (same order as before)
	let mut ty_fvs: Vec<u32> = Vec::new();
	collect_ty_vars(ty, &mut ty_fvs);

	// nothing to generalise: skip walking the whole environment
	if ty_fvs.is_empty() {
		return Scheme {
			vars: Vec::new(),
			ty: ty.clone(),
			constraints: HashMap::new(),
		};
	}

	let env_fvs = env.free_vars();
	let bound: Vec<u32> = ty_fvs
		.into_iter()
		.filter(|v| !env_fvs.contains(v))
		.collect();
	let bound_constraints: HashMap<u32, HashSet<String>> = bound
		.iter()
		.filter_map(|v| constraints.get(v).map(|cs| (*v, cs.clone())))
		.collect();
	Scheme {
		vars: bound,
		ty: ty.clone(),
		constraints: bound_constraints,
	}
}

fn generalise(env: &TypeEnv, ty: &Ty) -> Scheme {
	generalise_with_constraints(env, ty, &HashMap::new())
}

fn class_method_constraint_map(
	class_name: &str,
	params: &[Spanned<String>],
	method_constraints: &[Spanned<Constraint>],
	tvars: &HashMap<String, Ty>,
	subst: &Subst,
) -> HashMap<u32, HashSet<String>> {
	let mut map: HashMap<u32, HashSet<String>> = HashMap::new();

	let mut add = |var_name: &str, class: String| {
		if let Some(tv) = tvars.get(var_name)
			&& let Ty::Var(id) = subst.apply(tv)
		{
			map.entry(id).or_default().insert(class);
		}
	};

	for param in params {
		add(&param.item, class_name.to_string());
	}
	for constraint in method_constraints {
		for class_name in &constraint.item.class_names {
			add(&constraint.item.type_var.item, class_name.item.clone());
		}
	}

	map
}

fn occurs(n: u32, ty: &Ty) -> bool {
	match ty {
		Ty::Var(m) => *m == n,
		Ty::Fn(a, b) | Ty::Product(a, b) | Ty::Sum(a, b) | Ty::App(a, b) => {
			occurs(n, a) || occurs(n, b)
		}
		_ => false,
	}
}

#[allow(unused)]
pub struct Checker<'r> {
	pub registry: &'r mut SourceRegistry,
	pub subst: Subst,
	next_var: u32,
	pub typed: Vec<Spanned<TypedBinding>>,
	pub had_error: bool,
	pub diags: Vec<Diagnostic>,
	suppress_errors: bool,
	/// Type-level equalities that could not be decided yet: retried when more is
	/// known, an error if still unresolved at the end.
	deferred: Vec<(Ty, Ty, Span)>,
	/// Data types with a GADT-style constructor: matches on them are checked against the
	/// expected type, with the refinement of each branch as a local given.
	gadt_types: HashSet<String>,
	/// Scheme variables that are existential (they occur in a constructor's payload, as
	/// indices only, and not in its result): sealed indices.
	exist_vars: HashSet<u32>,
	/// What the latest `instantiate` replaced, for `Pattern::Constructor`.
	last_inst: Vec<(u32, Ty)>,
	/// Fresh variables standing for the existential indices opened by patterns so far.
	skolems: Vec<u32>,
	pub sigma_defs: HashMap<String, SigmaDef>,
	/// while checking a branch's patterns, an equality involving a stuck type-function
	/// application is a given (a local rewrite) instead of an obligation
	assume_given: bool,
	/// Types whose constructor result repeats an index (`Refl : Equal n n`): their inhabitants
	/// are proofs, which must be total (totality.rs).
	pub proof_types: HashSet<String>,
	/// top-level `let name : Int = <constant>` definitions
	consts: crate::consteval::Consts,
	/// local names in scope, which shadow top-level constants
	shadowed: Vec<String>,
}

impl<'r> Checker<'r> {
	pub fn new(registry: &'r mut SourceRegistry) -> Self {
		Self {
			registry,
			subst: Subst::default(),
			next_var: 0,
			typed: Vec::new(),
			had_error: false,
			diags: Vec::new(),
			assume_given: false,
			proof_types: HashSet::new(),
			consts: HashMap::new(),
			shadowed: Vec::new(),
			sigma_defs: HashMap::new(),
			exist_vars: HashSet::new(),
			last_inst: Vec::new(),
			skolems: Vec::new(),
			suppress_errors: false,
			deferred: Vec::new(),
			gadt_types: HashSet::new(),
		}
	}

	pub fn fresh(&mut self) -> Ty {
		let n = self.next_var;
		self.next_var += 1;
		Ty::Var(n)
	}

	fn error(&mut self, msg: impl Into<String>, span: Span) {
		self.had_error = true;
		if self.suppress_errors {
			return;
		}
		self.diags.push(Diagnostic::error(msg, Some(span)));
	}

	fn error_with_help(&mut self, msg: impl Into<String>, help: impl Into<String>, span: Span) {
		self.had_error = true;
		if self.suppress_errors {
			return;
		}
		self.diags
			.push(Diagnostic::error(msg, Some(span)).with_help(help));
	}

	#[allow(unused)]
	fn note(&mut self, msg: impl Into<String>, span: Span) {
		if self.suppress_errors {
			return;
		}
		self.diags.push(Diagnostic::advice(msg, Some(span)));
	}

	fn type_mismatch(&mut self, a: &Ty, b: &Ty, span: Span) {
		self.error(
			format!(
				"Type mismatch:\n  expected: {}\n  found:    {}",
				a.display(&self.subst),
				b.display(&self.subst)
			),
			span,
		);
	}

	// `a ~ b` where at least one side is type-level arithmetic and neither is a bare
	// variable. Normalization (in `Subst::apply`) already put both sides in canonical form.
	fn unify_arith(&mut self, a: &Ty, b: &Ty, span: Span) {
		let is_num = |t: &Ty| matches!(t, Ty::Lit(_) | Ty::Var(_)) || is_arith(t);
		if !is_num(a) || !is_num(b) {
			self.type_mismatch(a, b, span);
			return;
		}
		let (Some(pa), Some(pb)) = (ty_to_poly(a), ty_to_poly(b)) else {
			// stuck, e.g. `Sub n 1` with n unknown
			if a != b {
				self.deferred.push((a.clone(), b.clone(), span));
			}
			return;
		};
		match solve(&pa, &pb) {
			Ok(Solve::Trivial) => {}
			Ok(Solve::Unsat) => self.type_mismatch(a, b, span),
			Ok(Solve::Solved(k, v)) => match poly_to_ty(&v) {
				Some(t) => self.subst.extend(k, t),
				None => self.deferred.push((a.clone(), b.clone(), span)),
			},
			Ok(Solve::Unsolved) => {
				self.deferred.push((a.clone(), b.clone(), span));
			}
			Err(e) => self.error(e.to_string(), span),
		}
	}

	/// Retry equalities that were undecidable when first seen. With `final_pass`, whatever
	/// is still open is an error.
	pub fn retry_deferred(&mut self, env: &TypeEnv, final_pass: bool) {
		loop {
			let pending = std::mem::take(&mut self.deferred);
			if pending.is_empty() {
				break;
			}
			let n = pending.len();
			for (a, b, span) in pending {
				self.unify(&a, &b, env, span);
			}
			// no equality was decided: stop (they stay deferred)
			if self.deferred.len() >= n {
				break;
			}
		}
		if final_pass {
			// reduction errors raised where no span was at hand (e.g. out of fuel)
			for msg in take_errors() {
				self.error(msg, Span::synthetic(0));
			}
			for (a, b, span) in std::mem::take(&mut self.deferred) {
				self.error_with_help(
					format!(
						"cannot prove the type-level equality {} ~ {}",
						a.display(&self.subst),
						b.display(&self.subst)
					),
					"add the missing fact to the function's signature",
					span,
				);
			}
		}
	}

	fn mentions_gadt(&self, t: &Ty) -> bool {
		if self.gadt_types.is_empty() {
			return false;
		}
		match t {
			Ty::Named(n) => self.gadt_types.contains(n),
			Ty::Fn(a, b) | Ty::Product(a, b) | Ty::Sum(a, b) | Ty::App(a, b) => {
				self.mentions_gadt(a) || self.mentions_gadt(b)
			}
			_ => false,
		}
	}

	/// Check `e` against a known type. Ordinary code stays on inference (this is
	/// `annotate` + `unify`); only expressions whose expected type mentions a GADT take the
	/// checking path, so existing programs are unaffected (checking mode is needed
	/// only here).
	fn check_expr(
		&mut self,
		e: &Spanned<Expr>,
		expected: &Ty,
		env: &TypeEnv,
		span: Span,
	) -> TypedExpr {
		let exp = self.subst.apply(expected);
		// `(3 * v)` against `(n : Nat) * T`: the literal is the numeral, and fixes `n`
		if let Expr::Product(a, b) = &e.item
			&& !self.sigma_erased(&exp)
			&& let Some((Ty::Product(single, rest), _)) = self.sigma_expand(&exp)
			&& let Ty::App(h, idx) = &*single
			&& matches!(&**h, Ty::Named(n) if n == "SNat")
			&& let Some(first) = self.snat_numeral(idx, a, env)
		{
			let second = self.check_expr(b, &rest, env, span);
			let ty = Ty::Product(Box::new(first.ty().clone()), Box::new(second.ty().clone()));
			return TypedExpr::Product(Box::new(first), Box::new(second), ty);
		}
		if self.mentions_gadt(&exp) {
			match (&e.item, &exp) {
				(Expr::Fn(arg, body), Ty::Fn(a, r)) => {
					let mut env2 = env.clone();
					env2.insert(arg.item.clone(), Scheme::mono((**a).clone()));
					self.shadowed.push(arg.item.clone());
					let body_e = self.check_expr(body, r, &env2, span);
					self.shadowed.pop();
					let fn_ty =
						Ty::Fn(Box::new(self.subst.apply(a)), Box::new(body_e.ty().clone()));
					return TypedExpr::Fn(arg.item.clone(), Box::new(body_e), fn_ty);
				}
				(Expr::Match(cases), _) => {
					if let Some(te) = self.check_match(cases, &exp, env, e.span) {
						return te;
					}
				}
				_ => {}
			}
		}
		let te = self.annotate(e, env);
		self.unify(expected, te.ty(), env, span);
		te
	}

	/// `match` against a known type `A1 -> .. -> Ak -> R`. Matching a constructor whose
	/// result type refines a variable of the expected type (`n ~ Succ k`) gives an equality
	/// that holds in that branch only: the binding stays in the substitution while the
	/// branch body is checked and is retracted afterwards.
	fn check_match(
		&mut self,
		cases: &[(Vec<Spanned<Pattern>>, Spanned<Expr>)],
		expected: &Ty,
		env: &TypeEnv,
		span: Span,
	) -> Option<TypedExpr> {
		let k = cases.first()?.0.len();
		if k == 0 || cases.iter().any(|c| c.0.len() != k) {
			return None;
		}
		let mut cols: Vec<Ty> = Vec::new();
		let mut cur = expected.clone();
		for _ in 0..k {
			match cur {
				Ty::Fn(a, b) => {
					cols.push(*a);
					cur = *b;
				}
				_ => return None,
			}
		}
		let result = cur;

		// every variable of the expected type comes from the signature: those are the ones
		// a branch can refine
		let mut rigid: HashSet<u32> = HashSet::new();
		free_vars_into(expected, &mut rigid);

		let mut typed_cases: Vec<(Vec<Pattern>, TypedExpr)> = Vec::with_capacity(cases.len());
		for (pats, body) in cases {
			let mark = self.subst.mark();
			let rewrite_mark = self.subst.rewrite_mark();
			let skolem_mark = self.skolems.len();
			let mut branch_env = env.clone();
			self.assume_given = true;
			for (pat, col) in pats.iter().zip(&cols) {
				branch_env.vars.extend(self.check_pattern(pat, col, env));
			}
			self.assume_given = false;
			let bound: Vec<u32> = self
				.subst
				.bound_since(mark)
				.into_iter()
				.filter(|v| rigid.contains(v))
				.collect();
			let targets: Vec<Option<u32>> = bound
				.iter()
				.map(|v| match self.subst.apply(&Ty::Var(*v)) {
					Ty::Var(w) => Some(w),
					_ => None,
				})
				.collect();
			// `a := a'` (a signature variable aliased to a fresh one) is plain unification,
			// not a refinement: it must outlive the branch, or `a'` is left unresolved and
			// defaults to `Unit` in specialization. But two signature variables made equal
			// (`Refl : Equal k k` against `Equal n m`), or one aliased to another signature
			// variable, is a given: it holds in *this branch only*.
			let givens: Vec<u32> = bound
				.iter()
				.zip(&targets)
				.filter(|(_, t)| match t {
					None => true,
					Some(w) => {
						rigid.contains(w) || targets.iter().filter(|o| **o == Some(*w)).count() > 1
					}
				})
				.map(|(v, _)| *v)
				.collect();

			// A branch can refine a runtime type parameter too (`a := Int` for `Expr Int`):
			// specialization drops the arms that cannot occur at each instance (spec.rs).

			let bound = pattern_names(pats);
			let depth = self.shadowed.len();
			self.shadowed.extend(bound);
			let body_e = self.check_expr(body, &result, &branch_env, span);
			self.shadowed.truncate(depth);
			for v in givens {
				self.subst.retract(v);
			}
			self.subst.retract_rewrites(rewrite_mark);
			self.check_skolems(
				skolem_mark,
				&result,
				&rigid,
				env,
				pats.first().map(|p| p.span).unwrap_or(span),
			);
			typed_cases.push((pats.iter().map(|p| p.item.clone()).collect(), body_e));
		}

		let final_cols: Vec<Ty> = cols.iter().map(|t| self.subst.apply(t)).collect();
		self.check_exhaustiveness(cases, &final_cols, env, span);
		Some(TypedExpr::Match(typed_cases, self.subst.apply(expected)))
	}

	/// The singleton type of a promotable domain: `SNat n` for `Nat`, `SBool b` for `Bool`.
	fn singleton_of(&mut self, dom: &Spanned<AstType>, env: &TypeEnv) -> Option<String> {
		if let AstType::Var(n) = &dom.item {
			let last = n.rsplit(':').next().unwrap_or(n);
			match last {
				"Nat" => return Some("SNat".to_string()),
				"Bool" => return Some("SBool".to_string()),
				_ => {}
			}
			// a user data type `Color` is promoted with a singleton type `SColor` that the
			// program declares itself: `type SColor (c : Color) = SRed : SColor Color:Red + ..`
			let single = match n.rsplit_once(':') {
				Some((m, l)) => format!("{}:S{}", m, l),
				None => format!("S{}", n),
			};
			if env.type_ctors.contains_key(single.as_str())
				&& env.type_ctors.contains_key(n.as_str())
			{
				return Some(single);
			}
			self.error_with_help(
				format!("`{}` has no singleton type", n),
				format!(
					"declare `type S{0} (c : {0}) = ..` with one constructor per constructor of `{0}`, each with result `S{0} {0}:Ctor`",
					last
				),
				dom.span,
			);
			return None;
		}
		self.error_with_help(
			"a dependent binder must range over a promotable data type",
			"write `(n : Nat)`, `(b : Bool)`, or a plain data type that has a singleton type",
			dom.span,
		);
		None
	}

	/// Is `t` an erased dependent pair `(0 n : Nat) * T`?
	fn sigma_erased(&self, t: &Ty) -> bool {
		let (head, args) = spine(t);
		match head {
			Ty::Named(n) => self
				.sigma_defs
				.get(n)
				.is_some_and(|d| d.erased && d.nparams == args.len()),
			_ => false,
		}
	}

	/// The hidden type for `(x : Nat) * body`, where `x` is the variable `xv` in `body`
	fn make_sigma(&mut self, xv: &Ty, body: &Ty, erased: bool, singleton: &str) -> Ty {
		let Ty::Var(x) = self.subst.apply(xv) else {
			return body.clone();
		};
		let body = self.subst.apply(body);
		let mut params: Vec<u32> = Vec::new();
		fn order(t: &Ty, out: &mut Vec<u32>) {
			match t {
				Ty::Var(v) => {
					if !out.contains(v) {
						out.push(*v);
					}
				}
				Ty::Fn(a, b) | Ty::Product(a, b) | Ty::Sum(a, b) | Ty::App(a, b) => {
					order(a, out);
					order(b, out);
				}
				_ => {}
			}
		}
		order(&body, &mut params);
		params.retain(|v| *v != x);
		let mut m: HashMap<u32, Ty> = HashMap::new();
		m.insert(x, Ty::Var(SIGMA_EXIST));
		for (i, v) in params.iter().enumerate() {
			m.insert(*v, Ty::Var(SIGMA_PARAM + i as u32));
		}
		let inner = crate::ir::subst_ty(&body, &m);
		let payload = if erased {
			inner
		} else {
			let single = Ty::App(
				Box::new(Ty::Named(singleton.to_string())),
				Box::new(Ty::Var(SIGMA_EXIST)),
			);
			Ty::Product(Box::new(single), Box::new(inner))
		};
		let key = crate::ir::display_ty(&payload);
		let name = match self.sigma_defs.iter().find(|(_, d)| {
			d.nparams == params.len()
				&& d.erased == erased
				&& crate::ir::display_ty(&d.payload) == key
		}) {
			Some((n, _)) => n.clone(),
			None => {
				let n = format!("Sigma${}", self.sigma_defs.len());
				self.sigma_defs.insert(
					n.clone(),
					SigmaDef {
						nparams: params.len(),
						erased,
						payload,
					},
				);
				n
			}
		};
		params.iter().fold(Ty::Named(name), |t, v| {
			Ty::App(Box::new(t), Box::new(Ty::Var(*v)))
		})
	}

	/// If `t` is a dependent-pair type, its payload product with the existential index
	/// replaced by a fresh variable (returned too).
	fn sigma_expand(&mut self, t: &Ty) -> Option<(Ty, u32)> {
		let (head, args) = spine(t);
		let Ty::Named(n) = head else { return None };
		let def = self.sigma_defs.get(n)?.clone();
		if args.len() != def.nparams {
			return None;
		}
		let e = self.next_var;
		self.next_var += 1;
		let mut m: HashMap<u32, Ty> = HashMap::new();
		m.insert(SIGMA_EXIST, Ty::Var(e));
		for (i, a) in args.iter().enumerate() {
			m.insert(SIGMA_PARAM + i as u32, (**a).clone());
		}
		Some((crate::ir::subst_ty(&def.payload, &m), e))
	}

	/// Sealed existentials: the indices a branch's patterns opened must stay
	/// abstract. They may not be equated with anything (a number, a signature variable,
	/// another opened index), and may not occur in the match's result type.
	fn check_skolems(
		&mut self,
		mark: usize,
		result: &Ty,
		rigid: &HashSet<u32>,
		env: &TypeEnv,
		span: Span,
	) {
		if self.skolems.len() <= mark {
			return;
		}
		let opened: Vec<u32> = self.skolems.split_off(mark);
		let mut seen: HashSet<u32> = HashSet::new();
		let mut bad: Option<&str> = None;
		let mut vars: Vec<u32> = Vec::new();
		for s in &opened {
			match self.subst.apply(&Ty::Var(*s)) {
				Ty::Var(w) if !rigid.contains(&w) && seen.insert(w) => vars.push(w),
				Ty::Var(_) => bad = Some("an existential index was equated with another index"),
				_ => bad = Some("an existential index was equated with a known type-level value"),
			}
		}
		if bad.is_none() {
			let mut fv: HashSet<u32> = HashSet::new();
			free_vars_into(&self.subst.apply(result), &mut fv);
			for r in rigid {
				free_vars_into(&self.subst.apply(&Ty::Var(*r)), &mut fv);
			}
			if vars.iter().any(|w| fv.contains(w)) {
				bad = Some("an existential index escapes the `match` that opened it");
			}
			// ... or into a variable of the enclosing scope (a lambda parameter, say)
			if bad.is_none() {
				for (_, scheme) in env.vars.iter() {
					if !scheme.vars.is_empty() {
						continue;
					}
					let mut ev: HashSet<u32> = HashSet::new();
					free_vars_into(&self.subst.apply(&scheme.ty), &mut ev);
					if vars.iter().any(|w| ev.contains(w)) {
						bad = Some(
							"an existential index escapes into a variable of the enclosing scope",
						);
						break;
					}
				}
			}
		}
		if let Some(msg) = bad {
			self.error_with_help(
				msg,
				"a constructor with a hidden index (`Some (SNat n * Vec n a)`) only reveals it inside its branch; carry a runtime `SNat` witness instead of returning the index",
				span,
			);
		}
	}

	pub fn instantiate(&mut self, scheme: &Scheme) -> Ty {
		let mapping: HashMap<u32, Ty> = scheme.vars.iter().map(|v| (*v, self.fresh())).collect();
		self.last_inst = mapping.iter().map(|(k, v)| (*k, v.clone())).collect();
		self.substitute_ty(&scheme.ty, &mapping)
	}

	fn substitute_ty(&self, ty: &Ty, mapping: &HashMap<u32, Ty>) -> Ty {
		match ty {
			Ty::Var(n) => mapping.get(n).cloned().unwrap_or(Ty::Var(*n)),
			Ty::Fn(a, b) => Ty::Fn(
				Box::new(self.substitute_ty(a, mapping)),
				Box::new(self.substitute_ty(b, mapping)),
			),
			Ty::App(f, a) => Ty::App(
				Box::new(self.substitute_ty(f, mapping)),
				Box::new(self.substitute_ty(a, mapping)),
			),
			Ty::Product(a, b) => Ty::Product(
				Box::new(self.substitute_ty(a, mapping)),
				Box::new(self.substitute_ty(b, mapping)),
			),
			Ty::Sum(a, b) => Ty::Sum(
				Box::new(self.substitute_ty(a, mapping)),
				Box::new(self.substitute_ty(b, mapping)),
			),
			other => other.clone(),
		}
	}

	pub fn unify(&mut self, a: &Ty, b: &Ty, env: &TypeEnv, span: Span) {
		let a = self.subst.apply(a);
		let b = self.subst.apply(b);
		for msg in take_errors() {
			self.error(msg, span);
		}
		// a stuck type function application is not assumed injective: it unifies only
		// with itself, otherwise the equality waits for more information
		if (is_fn_app(&a) || is_fn_app(&b)) && !matches!(a, Ty::Var(_)) && !matches!(b, Ty::Var(_))
		{
			if a != b && self.assume_given {
				if is_fn_app(&a) {
					self.subst.assume_rewrite(a.clone(), b.clone());
				} else {
					self.subst.assume_rewrite(b.clone(), a.clone());
				}
				return;
			}
			if a != b {
				self.deferred.push((a.clone(), b.clone(), span));
			}
			return;
		}
		// type-level arithmetic: compare as polynomials. A plain
		// variable on either side binds as usual (with the occurs check).
		if (is_arith(&a) || is_arith(&b)) && !matches!(a, Ty::Var(_)) && !matches!(b, Ty::Var(_)) {
			self.unify_arith(&a, &b, span);
			return;
		}
		// two dependent-pair types of the same shape may have been interned separately
		// (`(n : Nat) * Vec n Int` and `(n : Nat) * Vec n a` at `a = Int`): compare payloads
		if let (Some((pa, _)), Some((pb, _))) = (self.sigma_expand(&a), self.sigma_expand(&b))
			&& spine(&a).0 != spine(&b).0
		{
			self.unify(&pa, &pb, env, span);
			return;
		}
		// an erased pair is its payload: it unifies with any non-variable type that is not
		// itself a pair type of the same name
		if self.sigma_erased(&a)
			&& !matches!(b, Ty::Var(_))
			&& spine(&a).0 != spine(&b).0
			&& let Some((payload, _)) = self.sigma_expand(&a)
		{
			self.unify(&payload, &b, env, span);
			return;
		}
		if self.sigma_erased(&b)
			&& !matches!(a, Ty::Var(_))
			&& spine(&a).0 != spine(&b).0
			&& let Some((payload, _)) = self.sigma_expand(&b)
		{
			self.unify(&a, &payload, env, span);
			return;
		}
		// a dependent pair is transparent: it unifies with its payload product
		if matches!(b, Ty::Product(..))
			&& let Some((payload, _)) = self.sigma_expand(&a)
		{
			self.unify(&payload, &b, env, span);
			return;
		}
		if matches!(a, Ty::Product(..))
			&& let Some((payload, _)) = self.sigma_expand(&b)
		{
			self.unify(&a, &payload, env, span);
			return;
		}
		match (&a, &b) {
			(Ty::Unit, Ty::Unit)
			| (Ty::Int, Ty::Int)
			| (Ty::Float, Ty::Float)
			| (Ty::Char, Ty::Char) => {}
			// named is either actual zero-param alias or head of ctor
			(Ty::Named(n1), Ty::Named(n2)) if n1 == n2 => {}
			(Ty::Lit(n1), Ty::Lit(n2)) if n1 == n2 => {}
			(Ty::Named(name), _) if env.type_aliases.contains_key(name) => {
				let def = env.type_aliases[name].clone();
				self.unify(&def, &b, env, span);
			}
			(_, Ty::Named(name)) if env.type_aliases.contains_key(name) => {
				let def = env.type_aliases[name].clone();
				self.unify(&a, &def, env, span);
			}
			(Ty::Var(n), t) | (t, Ty::Var(n)) => {
				let n = *n;

				if matches!(t, Ty::Var(m) if *m == n) {
					return;
				}

				if occurs(n, t) {
					self.error(
						format!("Infinite type: t{} ~ {}", n, t.display(&self.subst)),
						span,
					);
					return;
				}

				self.subst.extend(n, t.clone());
			}
			(Ty::Named(n1), Ty::Named(n2)) if n1 == n2 => {}
			(Ty::Fn(a1, b1), Ty::Fn(a2, b2)) => {
				let (a1, b1, a2, b2) = (a1.clone(), b1.clone(), a2.clone(), b2.clone());
				self.unify(&a1, &a2, env, span);
				self.unify(&b1, &b2, env, span);
			}
			(Ty::App(f1, a1), Ty::App(f2, a2)) => {
				let (f1, a1, f2, a2) = (f1.clone(), a1.clone(), f2.clone(), a2.clone());
				self.unify(&f1, &f2, env, span);
				self.unify(&a1, &a2, env, span);
			}
			(Ty::Product(a1, b1), Ty::Product(a2, b2)) => {
				let (a1, b1, a2, b2) = (a1.clone(), b1.clone(), a2.clone(), b2.clone());
				self.unify(&a1, &a2, env, span);
				self.unify(&b1, &b2, env, span);
			}
			(Ty::Sum(a1, b1), Ty::Sum(a2, b2)) => {
				let (a1, b1, a2, b2) = (a1.clone(), b1.clone(), a2.clone(), b2.clone());
				self.unify(&a1, &a2, env, span);
				self.unify(&b1, &b2, env, span);
			}
			(t1, t2) => self.error(
				format!(
					"Type mismatch:\n  expected: {}\n  found:    {}",
					t1.display(&self.subst),
					t2.display(&self.subst)
				),
				span,
			),
		}
	}

	pub fn ast_type_to_ty(
		&mut self,
		spanned_ast: &Spanned<AstType>,
		tvars: &mut HashMap<String, Ty>,
		env: &TypeEnv,
	) -> Ty {
		self.ast_type_to_ty_inner(spanned_ast, tvars, env, false)
	}

	pub fn ast_type_to_ty_in_def(
		&mut self,
		spanned_ast: &Spanned<AstType>,
		tvars: &mut HashMap<String, Ty>,
		env: &TypeEnv,
	) -> Ty {
		self.ast_type_to_ty_inner(spanned_ast, tvars, env, true)
	}

	fn ast_type_to_ty_inner(
		&mut self,
		spanned_ast: &Spanned<AstType>,
		tvars: &mut HashMap<String, Ty>,
		env: &TypeEnv,
		in_type_def: bool,
	) -> Ty {
		let Spanned { item: ast, span } = spanned_ast;
		match ast {
			AstType::Unit => Ty::Unit,
			AstType::Int => Ty::Int,
			AstType::Float => Ty::Float,
			AstType::Char => Ty::Char,
			AstType::Lit(n) => Ty::Lit(*n),
			AstType::Hole => self.fresh(),
			// `(0 n : Nat) -> T`: the index is erased, so it is just an implicitly quantified
			// type-level variable that unification fills in at each use
			AstType::Pi(Quantity::Zero, x, _dom, cod) => {
				let v = self.fresh();
				let saved = tvars.insert(x.clone(), v);
				let cod = Spanned {
					item: cod.item.clone(),
					span: *span,
				};
				let t = self.ast_type_to_ty_inner(&cod, tvars, env, in_type_def);
				match saved {
					Some(old) => {
						tvars.insert(x.clone(), old);
					}
					None => {
						tvars.remove(x);
					}
				}
				t
			}
			// `(1 x : A) -> B`: an ordinary function type; linearity is enforced by
			// linear.rs on the source, not by the types
			AstType::Pi(Quantity::One, _x, dom, cod) => {
				let d = self.ast_type_to_ty_inner(dom, tvars, env, in_type_def);
				let c = self.ast_type_to_ty_inner(cod, tvars, env, in_type_def);
				Ty::Fn(Box::new(d), Box::new(c))
			}
			// `(n : Nat) -> T`: the argument exists at run time and `n` is its value, so the
			// argument is the singleton `SNat n` (a plain literal stands for its numeral at
			// call sites, see `Expr::App`)
			AstType::Pi(Quantity::Omega, x, dom, cod) => {
				let Some(single) = self.singleton_of(dom, env) else {
					return self.fresh();
				};
				let v = self.fresh();
				let saved = tvars.insert(x.clone(), v.clone());
				let cod = Spanned {
					item: cod.item.clone(),
					span: *span,
				};
				let t = self.ast_type_to_ty_inner(&cod, tvars, env, in_type_def);
				match saved {
					Some(old) => {
						tvars.insert(x.clone(), old);
					}
					None => {
						tvars.remove(x);
					}
				}
				let snat = Ty::App(Box::new(Ty::Named(single.into())), Box::new(v));
				Ty::Fn(Box::new(snat), Box::new(t))
			}
			// `(n : Nat) * T`: a hidden type whose only constructor packs `SNat n * T`
			AstType::Sigma(q @ (Quantity::Omega | Quantity::Zero), x, dom, cod) => {
				let erased = *q == Quantity::Zero;
				let Some(single) = self.singleton_of(dom, env) else {
					return self.fresh();
				};
				let v = self.fresh();
				let saved = tvars.insert(x.clone(), v.clone());
				let cod = Spanned {
					item: cod.item.clone(),
					span: *span,
				};
				let t = self.ast_type_to_ty_inner(&cod, tvars, env, in_type_def);
				match saved {
					Some(old) => {
						tvars.insert(x.clone(), old);
					}
					None => {
						tvars.remove(x);
					}
				}
				self.make_sigma(&v, &t, erased, &single)
			}
			AstType::Sigma(..) => {
				self.error_with_help(
					"only dependent function and pair types with an unrestricted first component are implemented",
					"write `(n : Nat) -> ...` / `(n : Nat) * ...`, or `(0 n : Nat) -> ...`; linear binders are not supported yet",
					*span,
				);
				self.fresh()
			}
			AstType::Annot(inner, _) if in_type_def => {
				// the declaration's own shape: the result annotation only matters when the
				// constructor is registered
				let inner = Spanned {
					item: inner.item.clone(),
					span: *span,
				};
				self.ast_type_to_ty_inner(&inner, tvars, env, in_type_def)
			}
			AstType::Match(..) if in_type_def => self.fresh(),
			AstType::Annot(..) => {
				self.error(
					"a constructor result type `: T` is only allowed in a `type` declaration",
					*span,
				);
				self.fresh()
			}
			AstType::Match(..) => {
				self.error(
					"a type-level `match` is only allowed as the body of a `type` declaration",
					*span,
				);
				self.fresh()
			}
			AstType::Var(name) => {
				// local tvar
				if let Some(t) = tvars.get(name) {
					return t.clone();
				}

				// built-in type-level numbers
				match name.as_str() {
					"Add" | "Mul" | "Sub" | "Ls" | "Lse" => return Ty::Named(name.clone()),
					// promoted Bool values
					"Bool:True" => return Ty::Named("True".to_string()),
					"Bool:False" => return Ty::Named("False".to_string()),
					"Nat:Succ" => return Ty::Named("Succ".to_string()),
					"Nat:Zero" => return Ty::Lit(0),
					_ => {}
				}

				// a constructor of a plain data type used as a type-level value: `Color:Red`
				if let Some((owner, c)) = name.rsplit_once(':')
					&& c.chars().next().is_some_and(|ch| ch.is_uppercase())
					&& env.type_ctors.contains_key(owner)
					&& !env.type_ctors.contains_key(name.as_str())
				{
					register_promoted(name);
					return Ty::Named(name.clone());
				}

				// global ctor or data ctor name
				if env.type_ctors.contains_key(name.as_str())
					|| env.type_aliases.contains_key(name.as_str())
					|| in_type_def
				{
					return Ty::Named(name.clone());
				}

				self.error(format!("Undefined type: {}", name), *span);

				self.fresh()
			}
			AstType::Fn(a, b) => Ty::Fn(
				Box::new(self.ast_type_to_ty_inner(
					&Spanned {
						item: a.item.clone(),
						span: *span,
					},
					tvars,
					env,
					in_type_def,
				)),
				Box::new(self.ast_type_to_ty_inner(
					&Spanned {
						item: b.item.clone(),
						span: *span,
					},
					tvars,
					env,
					in_type_def,
				)),
			),
			AstType::Product(a, b) => Ty::Product(
				Box::new(self.ast_type_to_ty_inner(
					&Spanned {
						item: a.item.clone(),
						span: *span,
					},
					tvars,
					env,
					in_type_def,
				)),
				Box::new(self.ast_type_to_ty_inner(
					&Spanned {
						item: b.item.clone(),
						span: *span,
					},
					tvars,
					env,
					in_type_def,
				)),
			),
			AstType::Sum(a, b) => Ty::Sum(
				Box::new(self.ast_type_to_ty_inner(
					&Spanned {
						item: a.item.clone(),
						span: *span,
					},
					tvars,
					env,
					in_type_def,
				)),
				Box::new(self.ast_type_to_ty_inner(
					&Spanned {
						item: b.item.clone(),
						span: *span,
					},
					tvars,
					env,
					in_type_def,
				)),
			),
			AstType::App(f, a) => Ty::App(
				Box::new(self.ast_type_to_ty_inner(
					&Spanned {
						item: f.item.clone(),
						span: *span,
					},
					tvars,
					env,
					in_type_def,
				)),
				Box::new(self.ast_type_to_ty_inner(
					&Spanned {
						item: a.item.clone(),
						span: *span,
					},
					tvars,
					env,
					in_type_def,
				)),
			),
		}
	}

	pub fn annotate(&mut self, spanned_expr: &Spanned<Expr>, env: &TypeEnv) -> TypedExpr {
		let Spanned { item: expr, span } = spanned_expr;
		match expr {
			Expr::Literal(lit) => {
				let ty = self.infer_literal(
					&Spanned {
						item: lit.clone(),
						span: *span,
					},
					env,
				);
				TypedExpr::Literal(lit.clone(), self.subst.apply(&ty))
			}
			Expr::Qualified(q) => {
				let ty = self.infer_qualified(
					&Spanned {
						item: q.clone(),
						span: *span,
					},
					env,
				);
				TypedExpr::Var(q.0.clone(), self.subst.apply(&ty))
			}
			Expr::Fn(arg, body) => {
				let arg_ty = self.fresh();
				let mut env2 = env.clone();
				env2.insert(arg.item.clone(), Scheme::mono(arg_ty.clone()));
				self.shadowed.push(arg.item.clone());
				let body_expr = self.annotate(body, &env2);
				self.shadowed.pop();
				let fn_ty = Ty::Fn(
					Box::new(self.subst.apply(&arg_ty)),
					Box::new(body_expr.ty().clone()),
				);
				TypedExpr::Fn(arg.item.clone(), Box::new(body_expr), fn_ty)
			}
			Expr::App(func, arg) => {
				let func_expr = self.annotate(func, env);
				let arg_expr = match self.literal_as_snat(func_expr.ty(), arg, env) {
					Some(e) => e,
					None => self.annotate(arg, env),
				};
				let ret = self.fresh();
				let expected_fn = Ty::Fn(Box::new(arg_expr.ty().clone()), Box::new(ret.clone()));
				self.unify(func_expr.ty(), &expected_fn, env, *span);
				let ty = self.subst.apply(&ret);
				TypedExpr::App(Box::new(func_expr), Box::new(arg_expr), ty)
			}
			Expr::Product(a, b) => {
				let ae = self.annotate(a, env);
				let be = self.annotate(b, env);
				let ty = Ty::Product(Box::new(ae.ty().clone()), Box::new(be.ty().clone()));
				TypedExpr::Product(Box::new(ae), Box::new(be), ty)
			}
			Expr::Match(cases) => self.annotate_match(cases, env, *span),
		}
	}

	/// `f 3` where `f : SNat n -> ..`: the literal stands for the singleton `SS (SS (SS SZ))`
	/// and fixes `n := 3` (value-driven refinement). Only for a non-negative literal.
	fn literal_as_snat(
		&mut self,
		func_ty: &Ty,
		arg: &Spanned<Expr>,
		env: &TypeEnv,
	) -> Option<TypedExpr> {
		let Ty::Fn(param, _) = self.subst.apply(func_ty) else {
			return None;
		};
		let Ty::App(head, idx) = *param else {
			return None;
		};
		if !matches!(&*head, Ty::Named(n) if n == "SNat") {
			return None;
		}
		self.snat_numeral(&idx, arg, env)
	}

	/// The numeral `SS (.. SZ)` for a constant expression, with `idx := the number`.
	fn snat_numeral(&mut self, idx: &Ty, arg: &Spanned<Expr>, env: &TypeEnv) -> Option<TypedExpr> {
		// a literal, or a constant expression computed at compile time
		let v = match crate::consteval::eval(&arg.item, &self.consts, &self.shadowed, 0) {
			Ok(Some(v)) => v,
			Ok(None) => return None,
			Err(msg) => {
				self.error(msg, arg.span);
				return Some(TypedExpr::Undefined(self.fresh()));
			}
		};
		let v = &v;
		if *v < 0 {
			self.error_with_help(
				format!("`{}` cannot be used as a type-level number here", v),
				"a dependent argument must be a non-negative constant".to_string(),
				arg.span,
			);
			return Some(TypedExpr::Undefined(self.fresh()));
		}
		// an `SNat n` is an Int at run time, so a numeral of any size is one literal
		let e = TypedExpr::Literal(
			Literal::Int(*v),
			Ty::App(
				Box::new(Ty::Named("SNat".into())),
				Box::new(Ty::Lit(*v as u64)),
			),
		);
		self.unify(idx, &Ty::Lit(*v as u64), env, arg.span);
		Some(e)
	}

	// the old `infer_match`, but building the typed branches as it goes
	fn annotate_match(
		&mut self,
		cases: &[(Vec<Spanned<Pattern>>, Spanned<Expr>)],
		env: &TypeEnv,
		span: Span,
	) -> TypedExpr {
		if cases.is_empty() {
			self.error("match expression has no cases", span);
			let t = self.fresh();
			return TypedExpr::Match(Vec::new(), t);
		}

		let mut expected_branch_ty: Option<Ty> = None;
		// arg types of the first case
		// after every case is unified with the others these are authoritative
		let mut col_tys: Option<Vec<Ty>> = None;
		let mut typed_cases: Vec<(Vec<Pattern>, TypedExpr)> = Vec::with_capacity(cases.len());

		for (pats, body) in cases {
			let skolem_mark = self.skolems.len();
			let mut branch_env = env.clone();
			let pat_tys: Vec<_> = pats.iter().map(|_| self.fresh()).collect();
			for (pat, ty) in pats.iter().zip(&pat_tys) {
				branch_env.vars.extend(self.check_pattern(pat, ty, &env));
			}

			if col_tys.is_none() {
				col_tys = Some(pat_tys.clone());
			}

			let bound = pattern_names(pats);
			let depth = self.shadowed.len();
			self.shadowed.extend(bound);
			let body_e = self.annotate(body, &branch_env);
			self.shadowed.truncate(depth);
			let mut body_ty = body_e.ty().clone();
			for ty in pat_tys.into_iter().rev() {
				body_ty = Ty::Fn(Box::new(self.subst.apply(&ty)), Box::new(body_ty));
			}
			match &expected_branch_ty {
				Some(expected) => {
					self.unify(&body_ty, expected, &branch_env, span);
				}
				None => {
					expected_branch_ty = Some(body_ty.clone());
				}
			}
			self.check_skolems(skolem_mark, &body_ty, &HashSet::new(), env, span);
			typed_cases.push((pats.iter().map(|p| p.item.clone()).collect(), body_e));
		}

		if let Some(tys) = col_tys {
			let final_col_tys: Vec<Ty> = tys.iter().map(|t| self.subst.apply(t)).collect();
			self.check_exhaustiveness(cases, &final_col_tys, env, span);
		}

		let ty = match expected_branch_ty {
			Some(t) => self.subst.apply(&t),
			None => {
				self.error("internal error: match produced no type", span);
				self.fresh()
			}
		};
		TypedExpr::Match(typed_cases, ty)
	}

	fn infer_literal(&mut self, spanned_lit: &Spanned<Literal>, env: &TypeEnv) -> Ty {
		let Spanned { item: lit, span } = spanned_lit;
		match lit {
			Literal::Int(_) => Ty::Int,
			Literal::Float(_) => Ty::Float,
			Literal::Char(_) => Ty::Char,
			Literal::Nil => {
				let a = self.fresh();
				Ty::App(Box::new(Ty::Named("List".into())), Box::new(a))
			}
			Literal::String(_) => Ty::App(Box::new(Ty::Named("List".into())), Box::new(Ty::Char)),
			Literal::Constructor(q) => self.infer_qualified(
				&Spanned {
					item: q.clone(),
					span: *span,
				},
				env,
			),
		}
	}

	fn infer_qualified(&mut self, q: &Spanned<Qualified>, env: &TypeEnv) -> Ty {
		let segments = &q.item.0;
		let Spanned { item: _, span } = q;

		if segments.len() == 1
			&& let Some(scheme) = env.vars.get(&segments[0])
		{
			return self.instantiate(scheme);
		}

		if let Some(scheme) = env.data_ctors.get(segments) {
			return self.instantiate(scheme);
		}

		// shouldnt really happen but better to be safe
		let flat = segments.join(":");
		if let Some(scheme) = env.vars.get(&flat) {
			return self.instantiate(scheme);
		}

		self.error(format!("Unbound variable: {}", segments.join(":")), *span);
		self.fresh()
	}

	// usefulness algorithm
	fn check_exhaustiveness(
		&mut self,
		cases: &[(Vec<Spanned<Pattern>>, Spanned<Expr>)],
		col_tys: &[Ty],
		env: &TypeEnv,
		span: Span,
	) {
		let matrix: Vec<Vec<Pattern>> = cases
			.iter()
			.map(|(pats, _)| pats.iter().map(|p| p.item.clone()).collect())
			.collect();

		if let Some(witness) = self.find_uncovered(&matrix, col_tys, env, span) {
			let parts: Vec<String> = witness.iter().map(|w| w.to_string()).collect();
			let shown = parts.join(", ");
			self.error_with_help(
				format!("non-exhaustive match: the case `{}` is not covered", shown),
				"add an arm for this case, or a trailing `_ -> ...` arm to catch every remaining possibility",
				span,
			);
		}
	}

	/// returns witness -- concrete row of col vals not covered by matrix
	/// if matrix is non-exhaustive for col_tys, or none if it is
	fn find_uncovered(
		&mut self,
		matrix: &[Vec<Pattern>],
		col_tys: &[Ty],
		env: &TypeEnv,
		span: Span,
	) -> Option<Vec<MatchWitness>> {
		let Some((ty0, rest_tys)) = col_tys.split_first() else {
			// no more cols, row is covered iff some row survived
			return matrix.is_empty().then(Vec::new);
		};
		let mut ty0 = self.subst.apply(ty0);
		if let Some((payload, _)) = self.sigma_expand(&ty0) {
			ty0 = payload;
		}

		// product types always complete
		if let Ty::Product(a, b) = &ty0 {
			let sub_matrix: Vec<Vec<Pattern>> = matrix
				.iter()
				.filter_map(|row| specialize_pair_row(row))
				.collect();
			let mut sub_tys = vec![(**a).clone(), (**b).clone()];
			sub_tys.extend(rest_tys.iter().cloned());
			return self
				.find_uncovered(&sub_matrix, &sub_tys, env, span)
				.map(|w| {
					let (head, tail) = w.split_at(2);
					let mut out = vec![MatchWitness::Pair(
						Box::new(head[0].clone()),
						Box::new(head[1].clone()),
					)];
					out.extend_from_slice(tail);
					out
				});
		}

		// resolved type of sum val is Ty::Sum, not Ty::Named
		// bc full ctor signature is read directly off type structure, it must be complete
		// `ctor_signature`/`env.data_ctors` kept in case i fucked up somehow
		if let Ty::Sum(a, b) = &ty0
			&& matrix
				.iter()
				.any(|r| matches!(r[0], Pattern::Left(_) | Pattern::Right(_)))
		{
			for (is_left, payload_ty) in [(true, (**a).clone()), (false, (**b).clone())] {
				let sub_matrix: Vec<Vec<Pattern>> = matrix
					.iter()
					.filter_map(|row| specialize_sum_row(row, is_left))
					.collect();
				let mut sub_tys = vec![payload_ty];
				sub_tys.extend(rest_tys.iter().cloned());
				let Some(w) = self.find_uncovered(&sub_matrix, &sub_tys, env, span) else {
					return None;
				};
				let (head, tail) = w.split_at(1);
				let mut out = vec![MatchWitness::Ctor(
					format!("({})", if is_left { "_ +" } else { "+ _" }),
					head.first()
						.cloned()
						.filter(|h| !matches!(h, MatchWitness::Wild))
						.map(Box::new),
				)];
				out.extend_from_slice(tail);
				return Some(out);
			}
			return None;
		}
		if matches!(ty0, Ty::Sum(_, _)) {
			let full_sig = flatten_sum(&ty0);
			for (name, payload_ty) in &full_sig {
				let arity = if payload_ty.is_some() { 1 } else { 0 };
				let sub_matrix: Vec<Vec<Pattern>> = matrix
					.iter()
					.filter_map(|row| specialize_ctor_row(row, name, arity))
					.collect();
				let mut sub_tys: Vec<Ty> = payload_ty.iter().cloned().collect();
				sub_tys.extend(rest_tys.iter().cloned());
				let Some(w) = self.find_uncovered(&sub_matrix, &sub_tys, env, span) else {
					continue;
				};
				let (head, tail) = w.split_at(arity);
				let payload = head.first().cloned().map(Box::new);
				let mut out = vec![MatchWitness::Ctor(name.clone(), payload)];
				out.extend_from_slice(tail);
				return Some(out);
			}
			return None;
		}

		let sig_result = self.ctor_signature(&ty0, env);

		let Some(full_sig) = sig_result else {
			// only pattern that can actually make it exhaustive is a wildcard
			// so only default matrix (rows alr have one here) can cover
			let default_matrix: Vec<Vec<Pattern>> =
				matrix.iter().filter_map(|row| default_row(row)).collect();
			return self
				.find_uncovered(&default_matrix, rest_tys, env, span)
				.map(|mut w| {
					w.insert(0, MatchWitness::Wild);
					w
				});
		};

		let heads_seen: Vec<&str> = matrix
			.iter()
			.filter_map(|row| pattern_ctor_name(&row[0]))
			.collect();
		let complete = full_sig
			.iter()
			.all(|(name, _)| heads_seen.contains(&name.as_str()));

		if complete {
			// try every ctor, if any has an uncovered case then it's the witness
			for (name, arity) in &full_sig {
				let sub_matrix: Vec<Vec<Pattern>> = matrix
					.iter()
					.filter_map(|row| specialize_ctor_row(row, name, *arity))
					.collect();
				// GADT: under this constructor the idx is refined, which prunes the later
				// columns too (`Nil, Cons _` is impossible when both vectors share a length)
				let scope = self.begin_ctor_refinement(&ty0, name, env, span);
				let mut sub_tys = self.ctor_payload_tys(&ty0, name, *arity, env, span);
				sub_tys.extend(rest_tys.iter().cloned());
				let found = self.find_uncovered(&sub_matrix, &sub_tys, env, span);
				self.end_ctor_refinement(scope);
				let Some(w) = found else {
					continue;
				};
				let (head, tail) = w.split_at(*arity);
				let payload = head.first().cloned().map(Box::new);
				let mut out = vec![MatchWitness::Ctor(name.to_string(), payload)];
				out.extend_from_slice(tail);
				return Some(out);
			}
			return None;
		}

		// if missing a whole ctor, anything under it is uncovered
		let missing = full_sig
			.iter()
			.find(|(name, _)| !heads_seen.contains(&name.as_str()));
		let default_matrix: Vec<Vec<Pattern>> =
			matrix.iter().filter_map(|row| default_row(row)).collect();
		self.find_uncovered(&default_matrix, rest_tys, env, span)
			.map(|mut w| {
				let head_witness = match missing {
					Some((name, arity)) => MatchWitness::Ctor(
						name.clone(),
						if *arity == 1 {
							Some(Box::new(MatchWitness::Wild))
						} else {
							None
						},
					),
					None => MatchWitness::Wild,
				};
				w.insert(0, head_witness);
				w
			})
	}

	/// Assume the scrutinee type equals the constructor's result type, for a GADT only.
	/// Returns what `end_ctor_refinement` needs to undo it.
	fn begin_ctor_refinement(
		&mut self,
		ty: &Ty,
		ctor: &str,
		env: &TypeEnv,
		span: Span,
	) -> Option<(usize, usize)> {
		let head_name = ty_head_name(ty);
		if !self.gadt_types.contains(&head_name) {
			return None;
		}
		let scheme = env
			.data_ctors
			.get(&vec![head_name, ctor.to_string()])?
			.clone();
		let state = (self.subst.mark(), self.deferred.len());
		let inst = self.instantiate(&scheme);
		let res = match inst {
			Ty::Fn(_, r) => *r,
			o => o,
		};
		let saved = self.suppress_errors;
		self.suppress_errors = true;
		self.unify(&res, ty, env, span);
		self.suppress_errors = saved;
		Some(state)
	}

	fn end_ctor_refinement(&mut self, state: Option<(usize, usize)>) {
		if let Some((mark, deferred)) = state {
			for v in self.subst.bound_since(mark) {
				self.subst.retract(v);
			}
			self.deferred.truncate(deferred);
		}
	}

	/// if ty is a registered sum, any (ctor, arity) pairs have arity 0 or 1
	/// ret none for type with no finite, known ctor set
	fn ctor_signature(&mut self, ty: &Ty, env: &TypeEnv) -> Option<Vec<(String, usize)>> {
		let head_name = ty_head_name(ty);
		let prune = self.gadt_types.contains(&head_name);
		let mut out: Vec<(String, usize)> = Vec::new();
		for (key, scheme) in &env.data_ctors {
			if key.len() == 2 && key[0] == head_name && !out.iter().any(|(n, _)| n == &key[1]) {
				// a constructor whose result type is provably apart from the scrutinee's
				// cannot occur, so a match need not cover it (lowering still traps)
				if prune {
					let inst = self.instantiate(scheme);
					let res = match inst {
						Ty::Fn(_, r) => *r,
						o => o,
					};
					let res = self.subst.apply(&res);
					if types_apart(&res, ty, env) {
						continue;
					}
				}
				let arity = if matches!(scheme.ty, Ty::Fn(..)) {
					1
				} else {
					0
				};
				out.push((key[1].clone(), arity));
			}
		}
		if out.is_empty() {
			None
		} else {
			// stable order so errors are deterministic
			out.sort_by(|a, b| a.0.cmp(&b.0));
			Some(out)
		}
	}

	fn ctor_payload_tys(
		&mut self,
		ty: &Ty,
		ctor_name: &str,
		arity: usize,
		env: &TypeEnv,
		span: Span,
	) -> Vec<Ty> {
		if arity == 0 {
			return Vec::new();
		}
		let head_name = ty_head_name(ty);
		let Some(scheme) = env.data_ctors.get(&vec![head_name, ctor_name.to_string()]) else {
			return vec![self.fresh()];
		};
		let instantiated = self.instantiate(scheme);
		if let Ty::Fn(payload, result) = instantiated {
			self.unify(&result, ty, env, span);
			vec![self.subst.apply(&payload)]
		} else {
			vec![self.fresh()]
		}
	}

	fn check_pattern(
		&mut self,
		spanned_pat: &Spanned<Pattern>,
		expected: &Ty,
		env: &TypeEnv,
	) -> Vec<(String, Scheme)> {
		let Spanned { item: pat, span } = spanned_pat;
		match pat {
			Pattern::Hole => vec![],

			Pattern::Variable(name) => {
				let ty = self.subst.apply(expected);
				// binding an erased dependent pair opens its hidden index
				if self.sigma_erased(&ty)
					&& let Some((payload, e)) = self.sigma_expand(&ty)
				{
					self.skolems.push(e);
					return vec![(name.clone(), Scheme::mono(payload))];
				}
				vec![(name.clone(), Scheme::mono(ty))]
			}

			Pattern::Literal(lit) => {
				let lt = self.infer_literal(
					&Spanned {
						item: lit.clone(),
						span: *span,
					},
					env,
				);
				self.unify(&lt, expected, env, *span);
				vec![]
			}

			Pattern::Product(a, b) => {
				let ta = self.fresh();
				let tb = self.fresh();

				// matching a dependent pair opens its hidden index
				let applied = self.subst.apply(expected);
				if let Some((payload, e)) = self.sigma_expand(&applied) {
					self.skolems.push(e);
					self.unify(
						&payload,
						&Ty::Product(Box::new(ta.clone()), Box::new(tb.clone())),
						env,
						*span,
					);
					let mut v1 = self.check_pattern(a, &ta, env);
					let mut v2 = self.check_pattern(b, &tb, env);
					v1.append(&mut v2);
					return v1;
				}

				self.unify(
					expected,
					&Ty::Product(Box::new(ta.clone()), Box::new(tb.clone())),
					env,
					*span,
				);

				let mut v1 = self.check_pattern(a, &ta, env);
				let mut v2 = self.check_pattern(b, &tb, env);

				v1.append(&mut v2);
				v1
			}

			Pattern::Left(p) | Pattern::Right(p) => {
				let ta = self.fresh();
				let tb = self.fresh();
				self.unify(
					expected,
					&Ty::Sum(Box::new(ta.clone()), Box::new(tb.clone())),
					env,
					*span,
				);
				let inner = if matches!(pat, Pattern::Left(_)) {
					ta
				} else {
					tb
				};
				self.check_pattern(p, &inner, env)
			}

			Pattern::Constructor(q, payload) => {
				self.last_inst.clear();
				let ctor_ty = self.infer_qualified(q, env);
				// the existential indices of this constructor are opened here: each is a
				// fresh, unknown index that must not escape the branch (`check_skolems`)
				let opened: Vec<u32> = self
					.last_inst
					.iter()
					.filter(|(old, _)| self.exist_vars.contains(old))
					.filter_map(|(_, new)| match new {
						Ty::Var(v) => Some(*v),
						_ => None,
					})
					.collect();
				self.skolems.extend(opened);

				let payload_ty = self.fresh();
				let result_ty = self.fresh();

				let fn_ty = Ty::Fn(Box::new(payload_ty.clone()), Box::new(result_ty.clone()));
				self.unify(&ctor_ty, &fn_ty, env, *span);

				let result_applied = self.subst.apply(&result_ty);
				self.unify(&result_applied, expected, env, *span);

				let payload_applied = self.subst.apply(&payload_ty);

				self.check_pattern(payload, &payload_applied, env)
			}
		}
	}

	pub fn check_binding(
		&mut self,
		spanned_binding: &Spanned<Binding>,
		env: &mut TypeEnv,
		generalize: bool,
	) {
		self.check_binding_with_tvars(spanned_binding, env, generalize, &HashMap::new());
	}

	pub fn check_binding_with_tvars(
		&mut self,
		spanned_binding: &Spanned<Binding>,
		env: &mut TypeEnv,
		generalize: bool,
		extra_tvars: &HashMap<String, Ty>,
	) {
		self.check_binding_with_tvars_keyed(spanned_binding, env, generalize, extra_tvars, None);
	}

	fn check_with_clauses(
		&mut self,
		enclosing_qualified: &str,
		with_clauses: &[Spanned<Binding>],
		env: &TypeEnv,
	) -> TypeEnv {
		let mut with_env = env.clone();

		struct Pending<'a> {
			wb: &'a Spanned<Binding>,
			tvars: HashMap<String, Ty>,
			declared_ty: Ty,
		}
		let mut pending: Vec<Pending> = Vec::with_capacity(with_clauses.len());
		for wb in with_clauses {
			let mut tvars: HashMap<String, Ty> = HashMap::new();
			for constraint in &wb.item.constraints {
				tvars
					.entry(constraint.item.type_var.clone().item)
					.or_insert_with(|| self.fresh());
			}
			let declared_ty = self.ast_type_to_ty(&wb.item.typ, &mut tvars, &with_env);
			with_env.insert(wb.item.name.item.clone(), Scheme::mono(declared_ty.clone()));
			pending.push(Pending {
				wb,
				tvars,
				declared_ty,
			});
		}

		struct Checked<'a> {
			wb: &'a Spanned<Binding>,
			tvars: HashMap<String, Ty>,
			declared_ty: Ty,
			typed_value: Option<TypedExpr>,
		}
		let mut checked: Vec<Checked> = Vec::with_capacity(pending.len());
		for p in pending {
			let clause_qualified = format!("{}:{}", enclosing_qualified, p.wb.item.name.item);
			let inner_env =
				self.check_with_clauses(&clause_qualified, &p.wb.item.with_clauses, &with_env);
			let typed_value = p.wb.item.value.as_ref().map(|body| {
				let te = self.annotate(body, &inner_env);
				self.unify(&p.declared_ty, te.ty(), &with_env, p.wb.span);
				te
			});
			checked.push(Checked {
				wb: p.wb,
				tvars: p.tvars,
				declared_ty: p.declared_ty,
				typed_value,
			});
		}

		for c in checked {
			let b = &c.wb.item;
			let final_ty = self.subst.apply(&c.declared_ty);

			let mut env_for_gen = with_env.clone();
			env_for_gen.vars.remove(&b.name.item);
			let mut constraint_map: HashMap<u32, HashSet<String>> = HashMap::new();
			for constraint in &b.constraints {
				if let Some(tv) = c.tvars.get(&constraint.item.type_var.item)
					&& let Ty::Var(id) = self.subst.apply(tv)
				{
					constraint_map
						.entry(id)
						.or_default()
						.extend(constraint.item.class_names.iter().map(|cn| cn.item.clone()));
				}
			}
			let scheme = generalise_with_constraints(&env_for_gen, &final_ty, &constraint_map);
			with_env.insert(b.name.item.clone(), scheme.clone());

			let typed_value = c.typed_value.map(|te| refresh_tys(te, &self.subst));
			self.typed.push(Spanned {
				item: TypedBinding {
					name: b.name.item.clone(),
					qualified_name: Some(format!("{}:{}", enclosing_qualified, b.name.item)),
					ty: final_ty,
					scheme,
					value: typed_value,
				},
				span: c.wb.span,
			});
		}

		with_env
	}

	fn check_binding_group(
		&mut self,
		module_path: &[String],
		bindings: &[(&Binding, Span)],
		env: &mut TypeEnv,
	) {
		struct Pending<'a> {
			b: &'a Binding,
			span: Span,
			tvars: HashMap<String, Ty>,
			declared_ty: Ty,
		}
		let mut pending: Vec<Pending> = Vec::with_capacity(bindings.len());
		for (b, span) in bindings {
			let mut tvars: HashMap<String, Ty> = HashMap::new();
			for constraint in &b.constraints {
				tvars
					.entry(constraint.item.type_var.clone().item)
					.or_insert_with(|| self.fresh());
			}
			let declared_ty = self.ast_type_to_ty(&b.typ, &mut tvars, env);

			// A function over a GADT recurses at other idxs (`vmap f xs` with a shorter
			// `xs`), so its own signature is usable polymorphically inside its body.
			let own = if self.mentions_gadt(&self.subst.apply(&declared_ty)) {
				let mut cm: HashMap<u32, HashSet<String>> = HashMap::new();
				for constraint in &b.constraints {
					if let Some(tv) = tvars.get(&constraint.item.type_var.item)
						&& let Ty::Var(id) = self.subst.apply(tv)
					{
						cm.entry(id)
							.or_default()
							.extend(constraint.item.class_names.iter().map(|c| c.item.clone()));
					}
				}
				generalise_with_constraints(env, &declared_ty, &cm)
			} else {
				Scheme::mono(declared_ty.clone())
			};
			env.insert(b.name.item.clone(), own);
			pending.push(Pending {
				b,
				span: *span,
				tvars,
				declared_ty,
			});
		}

		struct Checked<'a> {
			b: &'a Binding,
			span: Span,
			tvars: HashMap<String, Ty>,
			declared_ty: Ty,
			typed_value: Option<TypedExpr>,
			qualified: String,
		}
		let mut checked: Vec<Checked> = Vec::with_capacity(pending.len());
		for p in pending {
			let qualified = if module_path.is_empty() {
				p.b.name.item.clone()
			} else {
				format!("{}:{}", module_path.join(":"), p.b.name.item)
			};
			let inner_env = self.check_with_clauses(&qualified, &p.b.with_clauses, env);
			let typed_value =
				p.b.value
					.as_ref()
					.map(|body| self.check_expr(body, &p.declared_ty, &inner_env, p.span));
			checked.push(Checked {
				b: p.b,
				span: p.span,
				tvars: p.tvars,
				declared_ty: p.declared_ty,
				typed_value,
				qualified,
			});
		}

		for c in checked {
			let final_ty = self.subst.apply(&c.declared_ty);

			let mut env_for_gen = env.clone();
			env_for_gen.vars.remove(&c.b.name.item);
			let mut constraint_map: HashMap<u32, HashSet<String>> = HashMap::new();
			for constraint in &c.b.constraints {
				if let Some(tv) = c.tvars.get(&constraint.item.type_var.item)
					&& let Ty::Var(id) = self.subst.apply(tv)
				{
					constraint_map
						.entry(id)
						.or_default()
						.extend(constraint.item.class_names.iter().map(|cn| cn.item.clone()));
				}
			}
			let scheme = generalise_with_constraints(&env_for_gen, &final_ty, &constraint_map);
			env.insert(c.b.name.item.clone(), scheme.clone());

			let typed_value = c.typed_value.map(|te| refresh_tys(te, &self.subst));
			self.retry_deferred(&*env, false);
			self.typed.push(Spanned {
				item: TypedBinding {
					name: c.b.name.item.clone(),
					qualified_name: if module_path.is_empty() {
						None
					} else {
						Some(c.qualified)
					},
					ty: final_ty,
					scheme,
					value: typed_value,
				},
				span: c.span,
			});
		}
	}

	pub fn check_binding_with_tvars_keyed(
		&mut self,
		spanned_binding: &Spanned<Binding>,
		env: &mut TypeEnv,
		generalize: bool,
		extra_tvars: &HashMap<String, Ty>,
		register_key: Option<String>,
	) {
		let Spanned {
			item: binding,
			span,
		} = spanned_binding;

		let mut tvars: HashMap<String, Ty> = extra_tvars.clone();

		for constraint in &binding.constraints {
			tvars
				.entry(constraint.item.type_var.clone().item)
				.or_insert_with(|| self.fresh());
		}

		let declared_ty = self.ast_type_to_ty(&binding.typ, &mut tvars, env);

		let mut with_env = env.clone();

		if register_key.is_none() {
			with_env.insert(binding.name.item.clone(), Scheme::mono(declared_ty.clone()));
		}

		let enclosing_qualified = register_key
			.clone()
			.unwrap_or_else(|| binding.name.item.clone());
		let with_env =
			self.check_with_clauses(&enclosing_qualified, &binding.with_clauses, &with_env);

		let typed_value = binding.value.as_ref().map(|body| {
			let te = self.annotate(body, &with_env);
			self.unify(&declared_ty, te.ty(), env, *span);
			te
		});
		// extern body -- just trust the annotation

		let final_ty = self.subst.apply(&declared_ty);
		let scheme = if generalize {
			let mut env_for_gen = env.clone();
			env_for_gen.vars.remove(&binding.name.item);

			let mut constraint_map: HashMap<u32, HashSet<String>> = HashMap::new();
			for constraint in &binding.constraints {
				if let Some(tv) = tvars.get(&constraint.item.type_var.item)
					&& let Ty::Var(id) = self.subst.apply(tv)
				{
					constraint_map
						.entry(id)
						.or_default()
						.extend(constraint.item.class_names.iter().map(|cn| cn.item.clone()));
				}
			}

			generalise_with_constraints(&env_for_gen, &final_ty, &constraint_map)
		} else {
			Scheme::mono(final_ty.clone())
		};

		let typed_value = typed_value.map(|te| refresh_tys(te, &self.subst));
		self.typed.push(Spanned {
			item: TypedBinding {
				name: binding.name.item.clone(),
				qualified_name: register_key.clone(),
				ty: final_ty,
				scheme: scheme.clone(),
				value: typed_value,
			},
			span: *span,
		});

		match register_key {
			Some(key) => {
				env.instance_methods.insert(key, scheme);
			}
			None => {
				env.insert(binding.name.clone().item, scheme);
			}
		}
	}
}

pub fn collect_program(
	program: &Spanned<Program>,
	env: &mut TypeEnv,
	checker: &mut Checker<'_>,
) -> bool {
	for spanned in &program.item.0 {
		collect_top_level(spanned, env, checker);
	}
	!checker.had_error
}

/// return ctor name and payload if leaf of sum, otherwise none (shouldnt happen, if it does i fucked
/// up somewhere)
fn sum_leaf(ty: &Ty) -> Option<(&str, Option<&Ty>)> {
	match ty {
		Ty::Named(name) => Some((name.as_str(), None)),
		Ty::App(f, payload) => match f.as_ref() {
			Ty::Named(name) => Some((name.as_str(), Some(payload.as_ref()))),
			_ => None,
		},
		_ => None,
	}
}

fn flatten_sum(ty: &Ty) -> Vec<(String, Option<Ty>)> {
	match ty {
		Ty::Sum(a, b) => {
			let mut out = flatten_sum(a);
			out.extend(flatten_sum(b));
			out
		}
		other => match sum_leaf(other) {
			Some((name, payload)) => vec![(name.to_string(), payload.cloned())],
			// again shouldnt happen unless i fucked up
			None => vec![("?".to_string(), None)],
		},
	}
}

#[derive(Clone)]
enum MatchWitness {
	Wild,
	Pair(Box<MatchWitness>, Box<MatchWitness>),
	Ctor(String, Option<Box<MatchWitness>>),
}

impl fmt::Display for MatchWitness {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			MatchWitness::Wild => write!(f, "_"),
			MatchWitness::Pair(a, b) => write!(f, "({} * {})", a, b),
			MatchWitness::Ctor(name, None) => write!(f, "{}", name),
			MatchWitness::Ctor(name, Some(payload)) => write!(f, "{} ({})", name, payload),
		}
	}
}

fn pattern_ctor_name(p: &Pattern) -> Option<&str> {
	match p {
		Pattern::Literal(Literal::Constructor(q)) => q.0.last().map(|s| s.as_str()),
		Pattern::Constructor(q, _) => q.item.0.last().map(|s| s.as_str()),
		_ => None,
	}
}

fn specialize_pair_row(row: &[Pattern]) -> Option<Vec<Pattern>> {
	let mut out = Vec::with_capacity(row.len() + 1);
	match &row[0] {
		Pattern::Hole | Pattern::Variable(_) => {
			out.push(Pattern::Hole);
			out.push(Pattern::Hole);
		}
		Pattern::Product(a, b) => {
			out.push(a.item.clone());
			out.push(b.item.clone());
		}
		_ => return None,
	}
	out.extend_from_slice(&row[1..]);
	Some(out)
}

fn specialize_sum_row(row: &[Pattern], left: bool) -> Option<Vec<Pattern>> {
	let mut out = Vec::with_capacity(row.len());
	match &row[0] {
		Pattern::Hole | Pattern::Variable(_) => out.push(Pattern::Hole),
		Pattern::Left(p) if left => out.push(p.item.clone()),
		Pattern::Right(p) if !left => out.push(p.item.clone()),
		_ => return None,
	}
	out.extend_from_slice(&row[1..]);
	Some(out)
}

fn specialize_ctor_row(row: &[Pattern], ctor_name: &str, arity: usize) -> Option<Vec<Pattern>> {
	let mut out = Vec::with_capacity(row.len() + arity);
	match &row[0] {
		Pattern::Hole | Pattern::Variable(_) => {
			for _ in 0..arity {
				out.push(Pattern::Hole);
			}
		}
		Pattern::Literal(Literal::Constructor(q)) => {
			if q.0.last().map(|s| s.as_str()) != Some(ctor_name) || arity != 0 {
				return None;
			}
		}
		Pattern::Constructor(q, payload) => {
			if q.item.0.last().map(|s| s.as_str()) != Some(ctor_name) || arity != 1 {
				return None;
			}
			out.push(payload.item.clone());
		}
		_ => return None,
	}
	out.extend_from_slice(&row[1..]);
	Some(out)
}

fn default_row(row: &[Pattern]) -> Option<Vec<Pattern>> {
	match &row[0] {
		Pattern::Hole | Pattern::Variable(_) => Some(row[1..].to_vec()),
		_ => None,
	}
}

pub fn ty_head_name(ty: &Ty) -> String {
	match ty {
		Ty::App(f, _) => ty_head_name(f),
		Ty::Named(name) => name.clone(),
		Ty::Unit => "Unit".to_string(),
		Ty::Int => "Int".to_string(),
		Ty::Float => "Float".to_string(),
		Ty::Char => "Char".to_string(),
		Ty::Fn(_, _) => "->".to_string(),
		Ty::Product(_, _) => "*".to_string(),
		Ty::Sum(_, _) => "+".to_string(),
		Ty::Var(id) => format!("?{}", id),
		Ty::Lit(n) => n.to_string(),
	}
}

fn instance_method_key(inst_ty: &Ty, method_name: &str) -> String {
	format!("{}:{}", ty_head_name(inst_ty), method_name)
}

fn collect_top_level(spanned_tl: &Spanned<TopLevel>, env: &mut TypeEnv, checker: &mut Checker<'_>) {
	collect_top_level_in(spanned_tl, env, checker, &[]);
}

/// every bare name that b references, exc. local bindings
/// used to build the call graph among bindings so they can be split into mutual-recursion groups
/// instead of one blob. name not part of a cycle should be fully generalized before its callers are
/// checked so it stays usable w/ different types
fn binding_refs(b: &Binding) -> HashSet<String> {
	let mut bound: HashSet<String> = HashSet::new();
	for wc in &b.with_clauses {
		bound.insert(wc.item.name.item.clone());
	}
	let mut out = HashSet::new();
	if let Some(body) = &b.value {
		collect_expr_refs(&body.item, &bound, &mut out);
	}
	for wc in &b.with_clauses {
		collect_expr_refs_binding(&wc.item, &bound, &mut out);
	}
	out
}

fn collect_expr_refs_binding(
	b: &Binding,
	outer_bound: &HashSet<String>,
	out: &mut HashSet<String>,
) {
	let mut bound = outer_bound.clone();
	for wc in &b.with_clauses {
		bound.insert(wc.item.name.item.clone());
	}
	if let Some(body) = &b.value {
		collect_expr_refs(&body.item, &bound, out);
	}
	for wc in &b.with_clauses {
		collect_expr_refs_binding(&wc.item, &bound, out);
	}
}

fn collect_expr_refs(e: &Expr, bound: &HashSet<String>, out: &mut HashSet<String>) {
	match e {
		Expr::Qualified(q) => {
			if q.0.len() == 1 && !bound.contains(&q.0[0]) {
				out.insert(q.0[0].clone());
			}
		}
		Expr::Literal(_) => {}
		Expr::Fn(param, body) => {
			let mut bound2 = bound.clone();
			bound2.insert(param.item.clone());
			collect_expr_refs(&body.item, &bound2, out);
		}
		Expr::App(f, a) => {
			collect_expr_refs(&f.item, bound, out);
			collect_expr_refs(&a.item, bound, out);
		}
		Expr::Product(a, b) => {
			collect_expr_refs(&a.item, bound, out);
			collect_expr_refs(&b.item, bound, out);
		}
		Expr::Match(cases) => {
			for (pats, body) in cases {
				let mut bound2 = bound.clone();
				for p in pats {
					collect_pattern_binds(&p.item, &mut bound2);
				}
				collect_expr_refs(&body.item, &bound2, out);
			}
		}
	}
}

fn pattern_names(pats: &[Spanned<Pattern>]) -> Vec<String> {
	let mut set = HashSet::new();
	for p in pats {
		collect_pattern_binds(&p.item, &mut set);
	}
	set.into_iter().collect()
}

fn collect_pattern_binds(p: &Pattern, out: &mut HashSet<String>) {
	match p {
		Pattern::Hole | Pattern::Literal(_) => {}
		Pattern::Variable(name) => {
			out.insert(name.clone());
		}
		Pattern::Product(a, b) => {
			collect_pattern_binds(&a.item, out);
			collect_pattern_binds(&b.item, out);
		}
		Pattern::Constructor(_, p) => collect_pattern_binds(&p.item, out),
		Pattern::Left(p) | Pattern::Right(p) => collect_pattern_binds(&p.item, out),
	}
}

// split bindings into mutual-recursion groups, scc's of the call graph among group members only
// irrelevant for prelude fns or already checked modules. return in dependency order
fn scc_order<'a>(group: &[(&'a Binding, Span)]) -> Vec<Vec<(&'a Binding, Span)>> {
	let n = group.len();
	let name_to_idx: HashMap<&str, usize> = group
		.iter()
		.enumerate()
		.map(|(i, (b, _))| (b.name.item.as_str(), i))
		.collect();

	let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
	for (i, (b, _)) in group.iter().enumerate() {
		for referenced in binding_refs(b) {
			if let Some(&j) = name_to_idx.get(referenced.as_str())
				&& j != i
			{
				adj[i].push(j);
			}
		}
	}

	// Tarjan's algorithm
	struct State {
		counter: usize,
		stack: Vec<usize>,
		on_stack: Vec<bool>,
		index: Vec<Option<usize>>,
		low_link: Vec<usize>,
		sccs: Vec<Vec<usize>>,
	}
	fn strongconnect(v: usize, adj: &[Vec<usize>], st: &mut State) {
		st.index[v] = Some(st.counter);
		st.low_link[v] = st.counter;
		st.counter += 1;
		st.stack.push(v);
		st.on_stack[v] = true;

		for &w in &adj[v] {
			if st.index[w].is_none() {
				strongconnect(w, adj, st);
				st.low_link[v] = st.low_link[v].min(st.low_link[w]);
			} else if st.on_stack[w] {
				st.low_link[v] = st.low_link[v].min(st.index[w].unwrap());
			}
		}

		if st.low_link[v] == st.index[v].unwrap() {
			let mut component = Vec::new();
			loop {
				let w = st.stack.pop().unwrap();
				st.on_stack[w] = false;
				component.push(w);
				if w == v {
					break;
				}
			}
			st.sccs.push(component);
		}
	}

	let mut st = State {
		counter: 0,
		stack: Vec::new(),
		on_stack: vec![false; n],
		index: vec![None; n],
		low_link: vec![0; n],
		sccs: Vec::new(),
	};
	for v in 0..n {
		if st.index[v].is_none() {
			strongconnect(v, &adj, &mut st);
		}
	}

	st.sccs
		.into_iter()
		.map(|component| component.into_iter().map(|i| group[i]).collect())
		.collect()
}

fn collect_top_level_in(
	spanned_tl: &Spanned<TopLevel>,
	env: &mut TypeEnv,
	checker: &mut Checker<'_>,
	module_path: &[String],
) {
	let Spanned { item: tl, span } = spanned_tl;
	match tl {
		TopLevel::Module(mod_name, body) => {
			let mut path = module_path.to_vec();
			path.push(mod_name.item.clone());

			let exported = collect_exports(body);
			let mut local_env = env.clone();

			// 2 passes, non-binding items first
			for item in body {
				if !matches!(&item.item, TopLevel::Binding(_)) {
					collect_top_level_in(item, &mut local_env, checker, &path);
				}
			}
			let group: Vec<(&Binding, Span)> = body
				.iter()
				.filter_map(|item| match &item.item {
					TopLevel::Binding(b) => Some((b, item.span)),
					_ => None,
				})
				.collect();
			for scc in scc_order(&group) {
				checker.check_binding_group(&path, &scc, &mut local_env);
			}

			for (local_key, scheme) in &local_env.vars {
				if local_key.contains(':') {
					// `export Math` re-exports a whole imported module as `Outer:Math:name`
					let first = local_key.split(':').next().unwrap_or("");
					if exported.contains(first) {
						env.insert(format!("{}:{}", path.join(":"), local_key), scheme.clone());
					}
					continue;
				}
				if env
					.vars
					.get(local_key.as_str())
					.map(|s| s.ty == scheme.ty)
					.unwrap_or(false)
				{
					continue;
				}

				let qualified = format!("{}:{}", path.join(":"), local_key);
				env.insert(qualified, scheme.clone());
				// Only the Prelude is visible without a qualifier. Publishing every module's
				// names bare would let a library's `filter` silently replace the Prelude's.
				if path.len() == 1 && path[0] == "Prelude" {
					env.insert(local_key.clone(), scheme.clone());
				}

				let short = local_key
					.split(':')
					.last()
					.unwrap_or(local_key.as_str())
					.to_string();
				if exported.contains(local_key) || exported.contains(&short) {
					let parent_key = format!("{}:{}", mod_name.item, local_key);
					env.insert(parent_key, scheme.clone());
				}
			}
			for (key, arity) in &local_env.type_ctors {
				if !env.type_ctors.contains_key(key.as_str()) {
					let qualified = format!("{}:{}", path.join(":"), key);
					env.type_ctors.insert(qualified, *arity);
					env.type_ctors.insert(key.clone(), *arity);
				}
			}
			for (key, scheme) in &local_env.data_ctors {
				env.data_ctors
					.entry(key.clone())
					.or_insert_with(|| scheme.clone());
			}
			for inst in &local_env.instances {
				if !env.instances.contains(inst) {
					env.instances.push_back(inst.clone());
				}
			}
			for (key, scheme) in &local_env.instance_methods {
				env.instance_methods
					.entry(key.clone())
					.or_insert_with(|| scheme.clone());
			}
			for (name, def) in &local_env.classes {
				env.classes
					.entry(name.clone())
					.or_insert_with(|| def.clone());
			}
			for (method, class) in &local_env.class_methods {
				env.class_methods
					.entry(method.clone())
					.or_insert_with(|| class.clone());
			}
		}
		TopLevel::TypeDef(name, params, body, _header) => {
			let local_name = name.item.0.join(":");
			let flat_name = if module_path.is_empty() {
				local_name.clone()
			} else {
				format!("{}:{}", module_path.join(":"), local_name)
			};
			let arity = arity_from_kind(env, &local_name, params.len());
			env.type_ctors.insert(flat_name.clone(), arity);
			env.type_ctors.insert(local_name.clone(), arity);

			// IMPORTANT only register data ctors against local type name, not flat
			register_data_ctors(
				&local_name,
				&params
					.iter()
					.map(|Spanned { item, .. }| item)
					.cloned()
					.collect::<Vec<_>>(),
				&Spanned {
					item: body.item.clone(),
					span: *span,
				},
				env,
				checker,
			);
		}
		TopLevel::ClassDef(name, params, methods) => {
			let mut method_sigs: HashMap<String, Scheme> = HashMap::new();
			for method in methods {
				let mut tvars: HashMap<String, Ty> = HashMap::new();
				for param in params {
					let tv = checker.fresh();
					tvars.insert(param.item.clone(), tv);
				}
				for constraint in &method.item.constraints {
					tvars
						.entry(constraint.item.type_var.item.clone())
						.or_insert_with(|| checker.fresh());
				}
				let ty = checker.ast_type_to_ty(&method.item.typ, &mut tvars, env);
				let constraint_map = class_method_constraint_map(
					&name.item,
					params,
					&method.item.constraints,
					&tvars,
					&checker.subst,
				);
				let scheme = generalise_with_constraints(env, &ty, &constraint_map);
				method_sigs.insert(method.item.name.item.clone(), scheme.clone());
				env.insert(method.item.name.item.clone(), scheme);
				env.class_methods
					.insert(method.item.name.item.clone(), name.item.clone());
			}
			env.classes.insert(
				name.item.clone(),
				ClassDef {
					params: params
						.iter()
						.map(|Spanned { item, .. }| item)
						.cloned()
						.collect(),
					methods: method_sigs,
				},
			);
		}
		TopLevel::Instance(class_name, type_args, bindings) => {
			let mut inst_tvars: HashMap<String, Ty> = HashMap::new();
			for arg in type_args {
				collect_free_type_vars(arg, &mut inst_tvars, env, checker);
			}
			let inst_ty = type_args
				.first()
				.map(|first| checker.ast_type_to_ty(first, &mut inst_tvars.clone(), env));
			if let Some(inst_ty) = &inst_ty {
				env.instances
					.push_back((class_name.item.clone(), inst_ty.clone()));
			}
			for binding in bindings {
				// every instance has same bare name
				let register_key = inst_ty
					.as_ref()
					.map(|ty| instance_method_key(ty, &binding.item.name.item));
				checker.check_binding_with_tvars_keyed(
					binding,
					env,
					true,
					&inst_tvars,
					register_key,
				);
			}
		}
		TopLevel::Binding(b) => {
			checker.check_binding(
				&Spanned {
					item: b.clone(),
					span: *span,
				},
				env,
				true,
			);
		}
		TopLevel::ImportAlias(path, alias) => {
			let flat = path.item.0.join(":");
			if let Some(scheme) = env.vars.get(&flat).cloned() {
				let local = alias.item.0.join(":");
				// the IR resolves names by definition, so it needs the alias too
				register_alias(&local, &flat);
				env.insert(local, scheme);
			}
		}
		TopLevel::Import(_)
		| TopLevel::ImportFile(_)
		| TopLevel::ImportUnqualified(_)
		| TopLevel::Export(_) => {}
	}
}

fn collect_exports(body: &[Spanned<TopLevel>]) -> std::collections::HashSet<String> {
	let mut out = std::collections::HashSet::new();
	for item in body {
		if let TopLevel::Export(q) = &item.item {
			out.insert(q.0.join(":"));
		}
	}
	out
}

/// Does `x` occur in `ty` only as (part of) an index argument of a data type, i.e. at a
/// position whose kind is a promoted data type such as `Nat`? Such a variable is erased.
fn index_only(ty: &Ty, x: u32, env: &TypeEnv) -> bool {
	match ty {
		Ty::Var(v) => *v != x,
		Ty::Fn(a, b) | Ty::Product(a, b) | Ty::Sum(a, b) => {
			index_only(a, x, env) && index_only(b, x, env)
		}
		Ty::App(..) => {
			let (head, args) = spine(ty);
			let kinds = match head {
				Ty::Named(n) => env
					.type_kinds
					.get(n.as_str())
					.or_else(|| env.type_kinds.get(n.rsplit(':').next().unwrap_or(n)))
					.cloned(),
				_ => None,
			};
			let kind_args: Vec<Kind> = kinds
				.map(|k| k.args().into_iter().cloned().collect())
				.unwrap_or_default();
			let head_ok = index_only(head, x, env);
			head_ok
				&& args.iter().enumerate().all(|(i, a)| {
					matches!(kind_args.get(i), Some(Kind::Data(_))) || index_only(a, x, env)
				})
		}
		_ => true,
	}
}

fn collect_free_type_vars(
	ast: &Spanned<AstType>,
	tvars: &mut HashMap<String, Ty>,
	env: &TypeEnv,
	checker: &mut Checker<'_>,
) {
	match &ast.item {
		AstType::Var(name)
			if !env.type_ctors.contains_key(name.as_str())
				&& !env.type_aliases.contains_key(name.as_str())
				&& !name
					.rsplit_once(':')
					.is_some_and(|(owner, _)| env.type_ctors.contains_key(owner))
				// the built-in type-level functions are not variables
				&& !matches!(
					name.as_str(),
					"Add" | "Mul" | "Sub" | "Ls" | "Lse" | "Bool:True" | "Bool:False" | "Nat:Succ" | "Nat:Zero"
				) =>
		{
			tvars.entry(name.clone()).or_insert_with(|| checker.fresh());
		}
		AstType::Fn(a, b) | AstType::Sum(a, b) | AstType::Product(a, b) | AstType::App(a, b) => {
			collect_free_type_vars(a, tvars, env, checker);
			collect_free_type_vars(b, tvars, env, checker);
		}
		// `(n : Nat) * T`: the binder is not a free variable, the rest of the body may be
		AstType::Pi(_, x, _, cod) | AstType::Sigma(_, x, _, cod) => {
			let had = tvars.contains_key(x);
			collect_free_type_vars(cod, tvars, env, checker);
			if !had {
				tvars.remove(x);
			}
		}
		_ => {}
	}
}

fn register_data_ctors(
	type_name: &str,
	params: &[String],
	body: &Spanned<AstType>,
	env: &mut TypeEnv,
	checker: &mut Checker<'_>,
) {
	let result_ty = params
		.iter()
		.fold(Ty::Named(type_name.to_string()), |t, _| {
			Ty::App(Box::new(t), Box::new(checker.fresh()))
		});
	collect_ctors_from_sum(type_name, body, &result_ty, params, env, checker);
}

fn collect_ctors_from_sum(
	type_name: &str,
	spanned_body: &Spanned<AstType>,
	result_ty: &Ty,
	params: &[String],
	env: &mut TypeEnv,
	checker: &mut Checker<'_>,
) {
	let Spanned {
		item: body,
		span: _span,
	} = spanned_body;
	match body {
		AstType::Sum(a, b) => {
			collect_ctors_from_sum(type_name, a, result_ty, params, env, checker);
			collect_ctors_from_sum(type_name, b, result_ty, params, env, checker);
		}
		AstType::Var(name) => {
			let ctor_key = vec![type_name.to_string(), name.clone()];
			let scheme = generalise(&TypeEnv::default(), result_ty);
			env.data_ctors.insert(ctor_key.clone(), scheme.clone());

			env.data_ctors.insert(vec![name.clone()], scheme.clone());
			env.insert(format!("{}:{}", type_name, name), scheme.clone());
			env.insert(name.clone(), scheme);
		}
		// GADT constructor: `Ctor payload : Result`
		AstType::Annot(ctor, result) => {
			let (ctor_name, payload) = match &ctor.item {
				AstType::Var(n) => (n.clone(), None),
				AstType::App(f, p) => match &f.item {
					AstType::Var(n) => (n.clone(), Some(p.as_ref())),
					_ => {
						checker.error("malformed constructor in `type` declaration", ctor.span);
						return;
					}
				},
				_ => {
					checker.error("malformed constructor in `type` declaration", ctor.span);
					return;
				}
			};
			// every lowercase variable in the constructor is universally quantified
			// the declaration's own parameters are not in scope: GADT results name their own
			let mut tvars: HashMap<String, Ty> = HashMap::new();
			if let Some(p) = payload {
				collect_free_type_vars(p, &mut tvars, env, checker);
			}
			collect_free_type_vars(result, &mut tvars, env, checker);
			let payload_ty = payload.map(|p| checker.ast_type_to_ty_in_def(p, &mut tvars, env));
			let result_ty = checker.ast_type_to_ty_in_def(result, &mut tvars, env);
			let head_ok = matches!(
				spine(&result_ty).0,
				Ty::Named(n) if n == type_name
			);
			if !head_ok {
				checker.error(
					format!("constructor `{}` must produce a `{}`", ctor_name, type_name),
					result.span,
				);
				return;
			}
			// a variable in the payload that the result does not mention is existential. A
			// hidden *index* is fine (it is erased, so nothing about it needs a layout); a
			// hidden type would need a sealed box and is rejected.
			let mut in_result: HashSet<u32> = HashSet::new();
			free_vars_into(&result_ty, &mut in_result);
			if let Some(p) = &payload_ty {
				let mut in_payload: HashSet<u32> = HashSet::new();
				free_vars_into(p, &mut in_payload);
				let hidden: Vec<u32> = in_payload
					.iter()
					.copied()
					.filter(|v| !in_result.contains(v))
					.collect();
				if hidden.iter().any(|v| !index_only(p, *v, env)) {
					checker.error_with_help(
						format!("constructor `{}` has an existential type variable", ctor_name),
						"only a hidden type-level number (used as an index, e.g. `Vec n a`) is allowed; every other variable in the payload must also occur in the result type",
						ctor.span,
					);
					return;
				}
				checker.exist_vars.extend(hidden);
			}
			// a result like `Vec (Succ n) a` refines its parameters: matches on this type are
			// checked with given equalities
			let mut seen: HashSet<u32> = HashSet::new();
			let plain = spine(&result_ty)
				.1
				.iter()
				.all(|a| matches!(a, Ty::Var(v) if seen.insert(*v)));
			if !plain {
				checker.gadt_types.insert(type_name.to_string());
			}
			// a repeated index (`Equal n n`) makes the type an equality-like proof type
			let mut seen_idx: HashSet<u32> = HashSet::new();
			let repeated = spine(&result_ty)
				.1
				.iter()
				.any(|a| matches!(a, Ty::Var(v) if !seen_idx.insert(*v)));
			if repeated {
				checker.proof_types.insert(type_name.to_string());
			}
			let ctor_ty = match payload_ty {
				Some(p) => Ty::Fn(Box::new(p), Box::new(result_ty)),
				None => result_ty,
			};
			let scheme = generalise(&TypeEnv::default(), &ctor_ty);
			let ctor_key = vec![type_name.to_string(), ctor_name.clone()];
			env.data_ctors.insert(ctor_key, scheme.clone());
			env.data_ctors
				.insert(vec![ctor_name.clone()], scheme.clone());
			env.insert(format!("{}:{}", type_name, ctor_name), scheme.clone());
			env.insert(ctor_name, scheme);
		}
		AstType::Match(clauses) => {
			// a type-level function: validate, check termination, register
			if let Err((msg, span)) = register(type_name, params.len(), clauses, *_span) {
				checker.error(msg, span);
			}
		}
		// App where fn is Var = ctor
		AstType::App(f, payload)
			if let Spanned {
				item: AstType::Var(ctor_name),
				..
			} = f.as_ref() =>
		{
			let mut tvars: HashMap<String, Ty> = HashMap::new();
			for p in params {
				let tv = checker.fresh();
				tvars.insert(p.clone(), tv);
			}
			let payload_ty = checker.ast_type_to_ty_in_def(payload, &mut tvars, env);

			let result_rebuilt = rebuild_result_ty(type_name, params, &tvars);
			let ctor_fn_ty = Ty::Fn(Box::new(payload_ty), Box::new(result_rebuilt));
			let scheme = generalise(&TypeEnv::default(), &ctor_fn_ty);
			let ctor_key = vec![type_name.to_string(), ctor_name.clone()];
			env.data_ctors.insert(ctor_key.clone(), scheme.clone());
			env.data_ctors
				.insert(vec![ctor_name.clone()], scheme.clone());
			env.insert(format!("{}:{}", type_name, ctor_name), scheme.clone());
			env.insert(ctor_name.clone(), scheme);
		}
		_ => {}
	}
}

fn rebuild_result_ty(type_name: &str, params: &[String], tvars: &HashMap<String, Ty>) -> Ty {
	params
		.iter()
		.map(|p| tvars.get(p))
		.flatten()
		.fold(Ty::Named(type_name.to_string()), |t, tv| {
			Ty::App(Box::new(t), Box::new(tv.clone()))
		})
}

#[allow(unused)]
#[derive(Debug, Clone)]
pub enum TypedExpr {
	Literal(Literal, Ty),
	Var(Vec<String>, Ty),
	Fn(String, Box<TypedExpr>, Ty),
	App(Box<TypedExpr>, Box<TypedExpr>, Ty),
	Product(Box<TypedExpr>, Box<TypedExpr>, Ty),
	Match(Vec<(Vec<Pattern>, TypedExpr)>, Ty),
	Undefined(Ty),
}

impl TypedExpr {
	pub fn ty(&self) -> &Ty {
		match self {
			TypedExpr::Literal(_, t) => t,
			TypedExpr::Var(_, t) => t,
			TypedExpr::Fn(_, _, t) => t,
			TypedExpr::App(_, _, t) => t,
			TypedExpr::Product(_, _, t) => t,
			TypedExpr::Match(_, t) => t,
			TypedExpr::Undefined(t) => t,
		}
	}
}

#[derive(Debug, Clone)]
pub struct TypedBinding {
	pub name: String,
	pub qualified_name: Option<String>,
	pub ty: Ty,
	pub scheme: Scheme,
	pub value: Option<TypedExpr>,
}

#[allow(unused)]
#[derive(Debug, Clone)]
pub struct TypedModule {
	pub name: String,
	pub bindings: Vec<TypedBinding>,
	pub submodules: Vec<TypedModule>,
}

pub fn refresh_tys(te: TypedExpr, subst: &Subst) -> TypedExpr {
	match te {
		TypedExpr::Literal(lit, ty) => TypedExpr::Literal(lit, subst.apply(&ty)),
		TypedExpr::Var(path, ty) => TypedExpr::Var(path, subst.apply(&ty)),
		TypedExpr::Fn(arg, body, ty) => {
			TypedExpr::Fn(arg, Box::new(refresh_tys(*body, subst)), subst.apply(&ty))
		}
		TypedExpr::App(f, a, ty) => TypedExpr::App(
			Box::new(refresh_tys(*f, subst)),
			Box::new(refresh_tys(*a, subst)),
			subst.apply(&ty),
		),
		TypedExpr::Product(a, b, ty) => TypedExpr::Product(
			Box::new(refresh_tys(*a, subst)),
			Box::new(refresh_tys(*b, subst)),
			subst.apply(&ty),
		),
		TypedExpr::Match(cases, ty) => TypedExpr::Match(
			cases
				.into_iter()
				.map(|(pats, body)| (pats, refresh_tys(body, subst)))
				.collect(),
			subst.apply(&ty),
		),
		TypedExpr::Undefined(ty) => TypedExpr::Undefined(subst.apply(&ty)),
	}
}

pub fn typecheck(
	program: &Spanned<Program>,
	registry: &mut SourceRegistry,
) -> (TypeEnv, Vec<Spanned<TypedBinding>>, Vec<Diagnostic>) {
	let mut env = TypeEnv::default();

	// kinds first: this also supplies the built-in `IO` entry that used to be
	// hardcoded here
	let kind_result = crate::kindcheck::check_program(&program.item);
	for (name, kind) in crate::kindcheck::builtin_type_kinds() {
		env.type_ctors.insert(name.to_string(), kind.args().len());
	}
	for (name, kind) in kind_result.kinds {
		env.type_kinds.insert(name, kind);
	}
	let mut checker = Checker::new(registry);
	collect_constants(&program.item.0, &mut checker.consts);

	forward_declare_program(program, &mut env, &mut checker);

	collect_program(program, &mut env, &mut checker);
	checker.retry_deferred(&env, true);

	// The checking order differs from source order (instances before a module's
	// bindings, bindings in dependency order). Restore program order -- prelude
	// first, then each file -- so everything downstream sees what it used to.
	// Bindings nested in another (with-clauses) end before it, so they still
	// come first. The sort is stable.
	let mut typed = std::mem::take(&mut checker.typed);
	typed.sort_by_key(|b| (b.span.source_id, b.span.end));

	for (name, def) in std::mem::take(&mut checker.sigma_defs) {
		env.type_ctors.insert(name.clone(), def.nparams);
		env.sigma_defs.insert(name, def);
	}
	let mut diags = kind_result.diags;
	diags.extend(crate::totality::check_program(
		&program.item,
		&checker.proof_types,
	));
	diags.extend(crate::linear::check_program(&program.item));
	diags.extend(std::mem::take(&mut checker.diags));
	(env, typed, diags)
}

/// The number of parameters of a declared type, read off its inferred kind: kinds are
/// the source of truth and the arity table is derived. A type-level function can have a
/// result kind that is itself an arrow, so only the declared parameters are counted.
fn arity_from_kind(env: &TypeEnv, name: &str, declared: usize) -> usize {
	match env.type_kinds.get(name) {
		Some(k) => k.args().len().min(declared),
		None => declared,
	}
}

/// Top-level `let name : Int = body` definitions, for compile-time evaluation.
fn collect_constants(items: &[Spanned<TopLevel>], out: &mut crate::consteval::Consts) {
	for item in items {
		match &item.item {
			TopLevel::Module(_, body) => collect_constants(body, out),
			TopLevel::Binding(b)
				if matches!(b.typ.item, AstType::Int) && b.constraints.is_empty() =>
			{
				if let Some(v) = &b.value {
					out.insert(b.name.item.clone(), v.clone());
				}
			}
			_ => {}
		}
	}
}

fn forward_declare_program(
	program: &Spanned<Program>,
	env: &mut TypeEnv,
	checker: &mut Checker<'_>,
) {
	for spanned in &program.item.0 {
		forward_declare_tl(spanned, env, checker);
	}
}

fn forward_declare_tl(
	spanned_tl: &Spanned<TopLevel>,
	env: &mut TypeEnv,
	checker: &mut Checker<'_>,
) {
	forward_declare_tl_in(spanned_tl, env, checker, &[]);
}

fn forward_declare_tl_in(
	spanned_tl: &Spanned<TopLevel>,
	env: &mut TypeEnv,
	checker: &mut Checker<'_>,
	module_path: &[String],
) {
	let Spanned {
		item: tl,
		span: _span,
	} = spanned_tl;
	match tl {
		TopLevel::Module(mod_name, body) => {
			let mut path = module_path.to_vec();
			path.push(mod_name.item.clone());

			let exported = collect_exports(body);
			let mut local_env = env.clone();

			for item in body {
				forward_declare_tl_in(item, &mut local_env, checker, &path);
			}

			for (local_key, scheme) in &local_env.vars {
				if local_key.contains(':') {
					// `export Math` re-exports a whole imported module as `Outer:Math:name`
					let first = local_key.split(':').next().unwrap_or("");
					if exported.contains(first) {
						env.insert(format!("{}:{}", path.join(":"), local_key), scheme.clone());
					}
					continue;
				}
				if env
					.vars
					.get(local_key.as_str())
					.map(|s| s.ty == scheme.ty)
					.unwrap_or(false)
				{
					continue;
				}

				let qualified = format!("{}:{}", path.join(":"), local_key);
				env.insert(qualified, scheme.clone());
				if path.len() == 1 && path[0] == "Prelude" {
					env.insert(local_key.clone(), scheme.clone());
				}

				let short = local_key
					.split(':')
					.last()
					.unwrap_or(local_key.as_str())
					.to_string();
				if exported.contains(local_key) || exported.contains(&short) {
					let parent_key = format!("{}:{}", mod_name.item, local_key);
					env.insert(parent_key, scheme.clone());
				}
			}

			for (key, arity) in &local_env.type_ctors {
				if !env.type_ctors.contains_key(key.as_str()) {
					let qualified = format!("{}:{}", path.join(":"), key);
					env.type_ctors.insert(qualified, *arity);
					env.type_ctors.insert(key.clone(), *arity);
				}
			}
			for (key, ty) in &local_env.type_aliases {
				env.type_aliases
					.entry(key.clone())
					.or_insert_with(|| ty.clone());
			}
		}
		TopLevel::TypeDef(name, params, body, _header) => {
			let flat_name = name.item.0.join(":");

			let arity = arity_from_kind(env, &flat_name, params.len());
			env.type_ctors.insert(flat_name.clone(), arity);

			let bare_ctor = matches!(&body.item, AstType::Var(n)
				if !env.type_ctors.contains_key(n.as_str())
					&& !env.type_aliases.contains_key(n.as_str()));
			if params.is_empty() && !bare_ctor && !matches!(body.item, AstType::Match(_)) {
				let alias_ty = checker.ast_type_to_ty_in_def(&body, &mut HashMap::new(), env);
				env.type_aliases.insert(flat_name, alias_ty);
			}
		}
		TopLevel::Binding(b) => {
			let mut tvars = HashMap::new();
			for constraint in &b.constraints {
				let tv = checker.fresh();
				tvars.insert(constraint.item.type_var.clone().item, tv);
			}
			let ty = checker.ast_type_to_ty(&b.typ, &mut tvars, env);

			// instance bodies are checked before following bindings
			let mut constraint_map: HashMap<u32, HashSet<String>> = HashMap::new();
			for constraint in &b.constraints {
				if let Some(Ty::Var(id)) = tvars
					.get(&constraint.item.type_var.item)
					.map(|t| checker.subst.apply(t))
				{
					constraint_map
						.entry(id)
						.or_default()
						.extend(constraint.item.class_names.iter().map(|cn| cn.item.clone()));
				}
			}
			let scheme = generalise_with_constraints(env, &ty, &constraint_map);
			env.insert(b.name.item.clone(), scheme);
		}
		TopLevel::ClassDef(name, params, methods) => {
			for method in methods {
				let mut tvars: HashMap<String, Ty> = HashMap::new();
				for param in params {
					let tv = checker.fresh();
					tvars.insert(param.item.clone(), tv);
				}
				for constraint in &method.item.constraints {
					tvars
						.entry(constraint.item.type_var.item.clone())
						.or_insert_with(|| checker.fresh());
				}
				let ty = checker.ast_type_to_ty(&method.item.typ, &mut tvars, env);
				let constraint_map = class_method_constraint_map(
					&name.item,
					params,
					&method.item.constraints,
					&tvars,
					&checker.subst,
				);
				let scheme = generalise_with_constraints(env, &ty, &constraint_map);
				env.insert(method.item.name.item.clone(), scheme);
				env.class_methods
					.insert(method.item.name.item.clone(), name.item.clone());
			}
		}
		_ => {}
	}
}
