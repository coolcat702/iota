// Kind inference over the parsed program, run before type inference.
//
//   Maybe  : Type -> Type            Vec : Nat -> Type -> Type
//   class Functor f   gives   f : Type -> Type   (from its method signatures)
//
// It works on the AST, so it neither depends on nor changes `typechecker::Ty`. Output is
// the kind of every declared type (stored in `TypeEnv::type_kinds`) plus diagnostics.
//
// Rollout switch: with the environment variable IOTA_KIND_WARN set, kind errors are
// reported as warnings. That keeps every existing program compiling while the checker is
// being validated against the whole prelude and std (compatibility goal, section 1).
//
// Not checked yet: the clauses of a type-level `match` (only the declared header kind is
// used), and quantities (a later pass).

use std::collections::HashMap;

use crate::diag::Diagnostic;
use crate::kind::{Kind, KindSubst};
use crate::parser::{Constraint, KindAst, Program, Quantity, Span, Spanned, TopLevel, Type};

/// Types the prelude assumes to exist (see the header of prelude/mod.iota).
pub fn builtin_type_kinds() -> Vec<(&'static str, Kind)> {
	vec![("IO", Kind::arity(1))]
}

pub struct KindResult {
	pub kinds: HashMap<String, Kind>,
	pub diags: Vec<Diagnostic>,
}

pub fn kind_from_ast(k: &KindAst) -> Kind {
	match k {
		KindAst::Type => Kind::Type,
		KindAst::Data(n) => Kind::Data(n.clone()),
		KindAst::Arrow(a, b) => Kind::arrow(kind_from_ast(a), kind_from_ast(b)),
	}
}

fn nat() -> Kind {
	Kind::Data("Nat".to_string())
}

fn last_segment(name: &str) -> &str {
	name.rsplit(':').next().unwrap_or(name)
}

struct Kc {
	ks: KindSubst,
	types: HashMap<String, Kind>,
	/// promoted constructors of first-order data types: `Color:Red : Color`
	ctors: HashMap<String, Kind>,
	/// kinds of each class's parameters
	classes: HashMap<String, Vec<Kind>>,
	diags: Vec<Diagnostic>,
	warn: bool,
}

pub fn check_program(program: &Program) -> KindResult {
	let mut kc = Kc {
		ks: KindSubst::new(),
		types: HashMap::new(),
		ctors: HashMap::new(),
		classes: HashMap::new(),
		diags: Vec::new(),
		warn: std::env::var_os("IOTA_KIND_WARN").is_some(),
	};
	for (n, k) in builtin_type_kinds() {
		kc.types.insert(n.to_string(), k);
	}
	// plain data types have kind Type until a use says otherwise
	for n in ["Unit", "Int", "Float", "Char"] {
		kc.types.insert(n.to_string(), Kind::Type);
	}

	kc.declare(&program.0);
	kc.check_items(&program.0);

	let kinds = kc
		.types
		.iter()
		.map(|(n, k)| (n.clone(), kc.ks.default_to_type(k)))
		.collect();
	KindResult {
		kinds,
		diags: kc.diags,
	}
}

impl Kc {
	fn err(&mut self, msg: String, span: Span) {
		self.diags.push(if self.warn {
			Diagnostic::warning(msg, Some(span))
		} else {
			Diagnostic::error(msg, Some(span))
		});
	}

	fn show(&self, k: &Kind) -> String {
		self.ks.default_to_type(k).to_string()
	}

	fn unify(&mut self, expected: &Kind, found: &Kind, span: Span, what: &str) {
		if self.ks.unify(expected, found).is_err() {
			let (e, f) = (self.show(expected), self.show(found));
			self.err(
				format!("kind error in {}: expected `{}`, found `{}`", what, e, f),
				span,
			);
		}
	}

	fn declared_or_fresh(&mut self, k: &Option<KindAst>) -> Kind {
		match k {
			Some(k) => kind_from_ast(k),
			None => self.ks.fresh(),
		}
	}

	// pass 1: every type and class gets a kind (with variables for what is not annotated)
	fn declare(&mut self, items: &[Spanned<TopLevel>]) {
		for item in items {
			match &item.item {
				TopLevel::Module(_, body) => self.declare(body),
				TopLevel::TypeDef(name, params, body, header) => {
					let key = name.item.0.join(":");
					if params.is_empty() {
						self.declare_promoted(&key, body);
					}
					let mut kind = match &header.result_kind {
						Some(k) => kind_from_ast(k),
						None => Kind::Type,
					};
					let mut pks = Vec::new();
					for i in 0..params.len() {
						let declared = header.param_kinds.get(i).cloned().flatten();
						pks.push(self.declared_or_fresh(&declared));
					}
					for pk in pks.into_iter().rev() {
						kind = Kind::arrow(pk, kind);
					}
					self.types.insert(key, kind);
				}
				TopLevel::ClassDef(name, params, _) => {
					let ks = params.iter().map(|_| self.ks.fresh()).collect();
					self.classes.insert(name.item.clone(), ks);
				}
				_ => {}
			}
		}
	}

	/// Promote the constructors of a plain data type `T` (no parameters, no `: Result`
	/// annotations): `T:C payload` becomes a type of kind `payload kinds -> T`.
	fn declare_promoted(&mut self, tname: &str, body: &Spanned<Type>) {
		fn ctors<'a>(t: &'a Spanned<Type>, out: &mut Vec<&'a Spanned<Type>>) -> bool {
			match &t.item {
				Type::Sum(a, b) => ctors(a, out) && ctors(b, out),
				Type::Annot(..) | Type::Match(_) => false,
				_ => {
					out.push(t);
					true
				}
			}
		}
		fn payload(t: &Type, out: &mut Vec<String>) -> bool {
			match t {
				Type::Var(n) => {
					out.push(n.rsplit(':').next().unwrap_or(n).to_string());
					true
				}
				Type::Product(a, b) => payload(&a.item, out) && payload(&b.item, out),
				_ => false,
			}
		}
		let mut cs = Vec::new();
		if !ctors(body, &mut cs) {
			return;
		}
		let me = last_segment(tname).to_string();
		for c in cs {
			let (name, comps) = match &c.item {
				Type::Var(n) => (n.clone(), Vec::new()),
				Type::App(f, pl) => {
					let Type::Var(n) = &f.item else { continue };
					let mut comps = Vec::new();
					if !payload(&pl.item, &mut comps) {
						continue;
					}
					(n.clone(), comps)
				}
				_ => continue,
			};
			let mut k = Kind::Data(me.clone());
			for comp in comps.into_iter().rev() {
				k = Kind::arrow(Kind::Data(comp), k);
			}
			self.ctors.insert(format!("{}:{}", tname, name), k);
		}
	}

	fn lookup_type(&self, name: &str) -> Option<Kind> {
		self.types
			.get(name)
			.or_else(|| self.types.get(last_segment(name)))
			.cloned()
	}

	fn infer(&mut self, t: &Spanned<Type>, tvars: &mut HashMap<String, Kind>) -> Kind {
		let span = t.span;
		match &t.item {
			Type::Unit | Type::Int | Type::Float | Type::Char => Kind::Type,
			Type::Lit(_) => nat(),
			Type::Hole => self.ks.fresh(),
			Type::Var(name) => {
				if let Some(k) = tvars.get(name) {
					return k.clone();
				}
				if let Some(k) = self.lookup_type(name) {
					return k;
				}
				if let Some(k) = self.ctors.get(name) {
					return k.clone();
				}
				match name.as_str() {
					"Add" | "Mul" | "Sub" => {
						return Kind::arrow(nat(), Kind::arrow(nat(), nat()));
					}
					"Ls" | "Lse" => {
						return Kind::arrow(
							nat(),
							Kind::arrow(nat(), Kind::Data("Bool".to_string())),
						);
					}
					"Bool:True" | "Bool:False" => return Kind::Data("Bool".to_string()),
					"Nat:Succ" => return Kind::arrow(nat(), nat()),
					"Nat:Zero" => return nat(),
					_ => {}
				}
				// an implicitly quantified type variable
				let k = self.ks.fresh();
				tvars.insert(name.clone(), k.clone());
				k
			}
			Type::Fn(a, b) | Type::Product(a, b) | Type::Sum(a, b) => {
				for side in [a, b] {
					let k = self.infer(side, tvars);
					self.unify(&Kind::Type, &k, side.span, "a type");
				}
				Kind::Type
			}
			Type::App(f, a) => {
				let kf = self.infer(f, tvars);
				let ka = self.infer(a, tvars);
				let r = self.ks.fresh();
				let want = Kind::arrow(ka, r.clone());
				if self.ks.unify(&kf, &want).is_err() {
					let (kf, want) = (self.show(&kf), self.show(&want));
					self.err(
						format!(
							"kind error in a type application: this takes `{}` but is applied as `{}`",
							kf, want
						),
						span,
					);
				}
				r
			}
			// a linear arrow is a plain function type: both sides are types
			Type::Pi(Quantity::One, _, dom, cod) => {
				let kd = self.infer(dom, tvars);
				self.unify(&Kind::Type, &kd, dom.span, "a linear binder's type");
				let kc = self.infer(cod, tvars);
				self.unify(&Kind::Type, &kc, cod.span, "the body of a linear arrow");
				Kind::Type
			}
			Type::Pi(_, x, dom, cod) | Type::Sigma(_, x, dom, cod) => {
				let kd = self.infer(dom, tvars);
				self.unify(&Kind::Type, &kd, dom.span, "a binder's type");
				let mut local = tvars.clone();
				// the bound variable ranges over the promoted data type named by `dom`
				match &dom.item {
					Type::Var(n) if self.lookup_type(n).is_some() => {
						local.insert(x.clone(), Kind::Data(last_segment(n).to_string()));
					}
					_ => self.err(
						"a dependent binder must have a promotable data type such as `Nat` or `Bool`"
							.to_string(),
						dom.span,
					),
				}
				let kc = self.infer(cod, &mut local);
				self.unify(&Kind::Type, &kc, cod.span, "the body of a dependent type");
				// variables first seen in the body are still implicit type variables
				for (n, k) in local {
					if n != *x {
						tvars.entry(n).or_insert(k);
					}
				}
				Kind::Type
			}
			// only meaningful in a declaration body: handled by `check_body`
			Type::Annot(..) | Type::Match(_) => Kind::Type,
		}
	}

	fn expect_type(&mut self, t: &Spanned<Type>, tvars: &mut HashMap<String, Kind>, what: &str) {
		let k = self.infer(t, tvars);
		self.unify(&Kind::Type, &k, t.span, what);
	}

	// `Ctor`, `Ctor payload`, or an alias body such as `List Char` (the typechecker also
	// reads `App(Var, x)` as a constructor, so a payload is all there is to check)
	fn check_ctor(&mut self, c: &Spanned<Type>, tvars: &mut HashMap<String, Kind>) {
		match &c.item {
			Type::Var(_) => {}
			Type::App(f, payload) if matches!(f.item, Type::Var(_)) => {
				self.expect_type(payload, tvars, "a constructor payload");
			}
			_ => self.expect_type(c, tvars, "a type definition"),
		}
	}

	fn check_body(&mut self, body: &Spanned<Type>, tvars: &mut HashMap<String, Kind>) {
		match &body.item {
			Type::Sum(a, b) => {
				self.check_body(a, tvars);
				self.check_body(b, tvars);
			}
			// a type-level function: only its header kind is used for now
			Type::Match(_) => {}
			// GADT constructor: its variables are its own, not the declaration's parameters
			Type::Annot(c, result) => {
				let mut local = HashMap::new();
				self.check_ctor(c, &mut local);
				self.expect_type(result, &mut local, "a constructor result type");
			}
			_ => self.check_ctor(body, tvars),
		}
	}

	fn bind_binders(&mut self, binders: &[Spanned<Constraint>], tvars: &mut HashMap<String, Kind>) {
		for b in binders {
			let c = &b.item;
			let k = if let Some(k) = &c.kind {
				kind_from_ast(k)
			} else if let [one] = c.class_names.as_slice()
				&& !self.classes.contains_key(&one.item)
				&& self.lookup_type(&one.item).is_some()
			{
				// `(n : Nat)`: a promoted data type, not a class
				Kind::Data(last_segment(&one.item).to_string())
			} else {
				let v = match tvars.get(&c.type_var.item) {
					Some(existing) => existing.clone(),
					None => self.ks.fresh(),
				};
				for cn in &c.class_names {
					if let Some(pk) = self.classes.get(&cn.item).and_then(|p| p.first()).cloned() {
						self.unify(&pk, &v, cn.span, "a class constraint");
					}
				}
				v
			};
			tvars.insert(c.type_var.item.clone(), k);
		}
	}

	fn check_binding(&mut self, b: &crate::parser::Binding, outer: &HashMap<String, Kind>) {
		let mut tvars = outer.clone();
		self.bind_binders(&b.constraints, &mut tvars);
		self.expect_type(&b.typ, &mut tvars, "a binding's type");
		for w in &b.with_clauses {
			self.check_binding(&w.item, &tvars);
		}
	}

	fn check_items(&mut self, items: &[Spanned<TopLevel>]) {
		for item in items {
			match &item.item {
				TopLevel::Module(_, body) => self.check_items(body),
				TopLevel::TypeDef(name, params, body, _) => {
					let key = name.item.0.join(":");
					let Some(kind) = self.types.get(&key).cloned() else {
						continue;
					};
					let mut tvars = HashMap::new();
					for (p, pk) in params.iter().zip(kind.args()) {
						tvars.insert(p.item.clone(), pk.clone());
					}
					self.check_body(body, &mut tvars);
				}
				TopLevel::ClassDef(name, params, methods) => {
					let pks = self.classes.get(&name.item).cloned().unwrap_or_default();
					for m in methods {
						let mut tvars = HashMap::new();
						for (p, k) in params.iter().zip(&pks) {
							tvars.insert(p.item.clone(), k.clone());
						}
						self.bind_binders(&m.item.constraints, &mut tvars);
						self.expect_type(&m.item.typ, &mut tvars, "a method signature");
					}
				}
				TopLevel::Instance(class, type_args, bindings) => {
					let mut tvars = HashMap::new();
					if let Some(first) = type_args.first() {
						let k = self.infer(first, &mut tvars);
						if let Some(pk) = self
							.classes
							.get(&class.item)
							.and_then(|p| p.first())
							.cloned()
						{
							self.unify(&pk, &k, first.span, "an instance head");
						}
					}
					for b in bindings {
						self.check_binding(&b.item, &tvars);
					}
				}
				TopLevel::Binding(b) => self.check_binding(b, &HashMap::new()),
				_ => {}
			}
		}
	}
}
