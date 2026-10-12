// HM typechecker (Algorithm W)

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::diag::Diagnostic;

use crate::parser::{
	Binding, Constraint, Expr, Literal, Pattern, Program, Qualified, SourceRegistry, Span, Spanned,
	TopLevel, Type as AstType,
};

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
		Ty::Var(n) => {
			if !out.contains(n) {
				out.push(*n);
			}
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
			if letter_idx < preferred.len() {
				let candidate = preferred[letter_idx].to_string();
				letter_idx += 1;

				if !used.contains(&candidate) {
					break candidate;
				}
			} else {
				let candidate = format!("t{}", overflow_idx);
				overflow_idx += 1;

				if !used.contains(&candidate) {
					break candidate;
				}
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
	pub constraints: HashMap<u32, Vec<String>>, // id -> class names
}

impl Scheme {
	pub fn mono(ty: Ty) -> Self {
		Self {
			vars: vec![],
			ty,
			constraints: HashMap::new(),
		}
	}

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
						format!("({}: {})", vname, classes.join(" + "))
					}
					_ => format!("({})", vname),
				}
			})
			.collect();

		format!("{} {} : {}", name, var_groups.join(" "), ty_str)
	}

	fn build_names(vars: &[u32], hints: Option<&HashMap<u32, String>>) -> HashMap<u32, String> {
		let mut names: HashMap<u32, String> = HashMap::new();
		let mut used: std::collections::HashSet<String> = std::collections::HashSet::new();

		// assign hinted names where they exist and don't conflict
		if let Some(hints) = hints {
			let mut hint_counts: HashMap<&str, usize> = HashMap::new();
			for v in vars {
				if let Some(h) = hints.get(v) {
					*hint_counts.entry(h.as_str()).or_insert(0) += 1;
				}
			}
			for v in vars {
				if let Some(h) = hints.get(v) {
					if hint_counts[h.as_str()] == 1 {
						names.insert(*v, h.clone());
						used.insert(h.clone());
					}
				}
			}
		}

		// assign letters then tN
		let mut letter_idx: usize = 0;
		let mut overflow_idx: usize = 0;

		for v in vars {
			if names.contains_key(v) {
				continue;
			}
			let name = loop {
				if letter_idx < 26 {
					let candidate = ((b'a' + letter_idx as u8) as char).to_string();
					letter_idx += 1;
					if !used.contains(&candidate) {
						break candidate;
					}
				} else {
					let candidate = format!("t{}", overflow_idx);
					overflow_idx += 1;
					if !used.contains(&candidate) {
						break candidate;
					}
				}
			};
			used.insert(name.clone());
			names.insert(*v, name);
		}

		names
	}
}

#[derive(Debug, Clone, Default)]
pub struct Subst(HashMap<u32, Ty>);

impl Subst {
	pub fn apply(&self, ty: &Ty) -> Ty {
		match ty {
			Ty::Var(n) => match self.0.get(n) {
				Some(t) => self.apply(t),
				None => Ty::Var(*n),
			},
			Ty::Fn(a, b) => Ty::Fn(Box::new(self.apply(a)), Box::new(self.apply(b))),
			Ty::App(f, a) => Ty::App(Box::new(self.apply(f)), Box::new(self.apply(a))),
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
	pub fn compose(&self, other: &Subst) -> Subst {
		let mut result: HashMap<u32, Ty> =
			other.0.iter().map(|(k, v)| (*k, self.apply(v))).collect();
		for (k, v) in &self.0 {
			result.entry(*k).or_insert_with(|| v.clone());
		}
		Subst(result)
	}

	pub fn extend(&mut self, var: u32, ty: Ty) {
		self.0.insert(var, ty);
	}
}

#[derive(Debug, Clone, Default)]
pub struct TypeEnv {
	pub vars: HashMap<String, Scheme>,            // binding -> scheme
	pub type_ctors: HashMap<String, usize>,       // name -> arity
	pub data_ctors: HashMap<Vec<String>, Scheme>, // ctor -> scheme giving constructor fn type
	pub class_methods: HashMap<String, String>,   // method name -> class name
	pub classes: HashMap<String, ClassDef>,       // class name -> (params, methods)
	pub instances: Vec<(String, Ty)>,             // (class, concrete ty head)
	pub type_aliases: HashMap<String, Ty>,
	pub instance_methods: HashMap<String, Scheme>, // per-instance concrete schemes
}

#[derive(Debug, Clone)]
pub struct ClassDef {
	pub params: Vec<String>,
	pub methods: HashMap<String, Scheme>,
}

impl TypeEnv {
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

	pub fn free_vars(&self) -> Vec<u32> {
		let mut fvs = vec![];
		for s in self.vars.values() {
			fvs.extend(free_vars_scheme(s));
		}
		fvs
	}

	pub fn insert(&mut self, name: String, scheme: Scheme) {
		self.vars.insert(name, scheme);
	}
}

fn free_vars_ty(ty: &Ty) -> Vec<u32> {
	match ty {
		Ty::Var(n) => vec![*n],
		Ty::Fn(a, b) | Ty::Product(a, b) | Ty::Sum(a, b) | Ty::App(a, b) => {
			[free_vars_ty(a), free_vars_ty(b)].concat()
		}
		_ => vec![],
	}
}

fn free_vars_scheme(s: &Scheme) -> Vec<u32> {
	free_vars_ty(&s.ty)
		.into_iter()
		.filter(|v| !s.vars.contains(v))
		.collect()
}

fn generalise(env: &TypeEnv, ty: &Ty) -> Scheme {
	generalise_with_constraints(env, ty, &HashMap::new())
}

fn generalise_with_constraints(
	env: &TypeEnv,
	ty: &Ty,
	constraints: &HashMap<u32, Vec<String>>,
) -> Scheme {
	let env_fvs = env.free_vars();
	let ty_fvs = free_vars_ty(ty);
	let mut bound: Vec<u32> = Vec::new();
	for v in ty_fvs {
		if !env_fvs.contains(&v) && !bound.contains(&v) {
			bound.push(v);
		}
	}
	let bound_constraints: HashMap<u32, Vec<String>> = bound
		.iter()
		.filter_map(|v| constraints.get(v).map(|cs| (*v, cs.clone())))
		.collect();
	Scheme {
		vars: bound,
		ty: ty.clone(),
		constraints: bound_constraints,
	}
}

fn class_method_constraint_map(
	class_name: &str,
	params: &[Spanned<String>],
	method_constraints: &[Spanned<Constraint>],
	tvars: &HashMap<String, Ty>,
	subst: &Subst,
) -> HashMap<u32, Vec<String>> {
	let mut map: HashMap<u32, Vec<String>> = HashMap::new();

	let mut add = |var_name: &str, class: String| {
		if let Some(tv) = tvars.get(var_name) {
			if let Ty::Var(id) = subst.apply(tv) {
				let classes = map.entry(id).or_default();
				if !classes.contains(&class) {
					classes.push(class);
				}
			}
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

pub struct Checker<'r> {
	pub registry: &'r mut SourceRegistry,
	pub subst: Subst,
	next_var: u32,
	pub had_error: bool,
	pub diags: Vec<Diagnostic>,
	suppress_errors: bool,
}

impl<'r> Checker<'r> {
	pub fn new(registry: &'r mut SourceRegistry) -> Self {
		Self {
			registry,
			subst: Subst::default(),
			next_var: 0,
			had_error: false,
			diags: Vec::new(),
			suppress_errors: false,
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

	fn note(&mut self, msg: impl Into<String>, span: Span) {
		if self.suppress_errors {
			return;
		}
		self.diags.push(Diagnostic::advice(msg, Some(span)));
	}

	pub fn instantiate(&mut self, scheme: &Scheme) -> Ty {
		let mapping: HashMap<u32, Ty> = scheme.vars.iter().map(|v| (*v, self.fresh())).collect();
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
		match (&a, &b) {
			(Ty::Unit, Ty::Unit)
			| (Ty::Int, Ty::Int)
			| (Ty::Float, Ty::Float)
			| (Ty::Char, Ty::Char) => {}
			// named is either actual zero-param alias or head of ctor
			(Ty::Named(n1), Ty::Named(n2)) if n1 == n2 => {}
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

				if free_vars_ty(t).contains(&n) {
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
			(t1, t2) => {
				self.error(
					format!(
						"Type mismatch:\n  expected: {}\n  found:    {}",
						t1.display(&self.subst),
						t2.display(&self.subst)
					),
					span,
				);
			}
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
			AstType::Var(name) => {
				// local tvar
				if let Some(t) = tvars.get(name) {
					return t.clone();
				}

				// global ctor
				if env.type_ctors.contains_key(name.as_str()) {
					return Ty::Named(name.clone());
				}

				if env.type_aliases.contains_key(name.as_str()) {
					return Ty::Named(name.clone());
				}

				// data ctor name
				if in_type_def {
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
			AstType::Product(a, b) => {
				let ta = self.ast_type_to_ty_inner(
					&Spanned {
						item: a.item.clone(),
						span: *span,
					},
					tvars,
					env,
					in_type_def,
				);
				let tb = self.ast_type_to_ty_inner(
					&Spanned {
						item: b.item.clone(),
						span: *span,
					},
					tvars,
					env,
					in_type_def,
				);
				Ty::Product(Box::new(ta), Box::new(tb))
			}
			AstType::Sum(a, b) => {
				let ta = self.ast_type_to_ty_inner(
					&Spanned {
						item: a.item.clone(),
						span: *span,
					},
					tvars,
					env,
					in_type_def,
				);
				let tb = self.ast_type_to_ty_inner(
					&Spanned {
						item: b.item.clone(),
						span: *span,
					},
					tvars,
					env,
					in_type_def,
				);
				Ty::Sum(Box::new(ta), Box::new(tb))
			}
			AstType::App(f, a) => {
				let tf = self.ast_type_to_ty_inner(
					&Spanned {
						item: f.item.clone(),
						span: *span,
					},
					tvars,
					env,
					in_type_def,
				);
				let ta = self.ast_type_to_ty_inner(
					&Spanned {
						item: a.item.clone(),
						span: *span,
					},
					tvars,
					env,
					in_type_def,
				);
				Ty::App(Box::new(tf), Box::new(ta))
			}
		}
	}

	pub fn infer(&mut self, spanned_expr: &Spanned<Expr>, env: &TypeEnv) -> Ty {
		let Spanned { item: expr, span } = spanned_expr;
		match expr {
			Expr::Literal(lit) => self.infer_literal(
				&Spanned {
					item: lit.clone(),
					span: *span,
				},
				env,
			),
			Expr::Qualified(q) => self.infer_qualified(
				&Spanned {
					item: q.clone(),
					span: *span,
				},
				env,
			),
			Expr::Fn(arg, body) => {
				let arg_ty = self.fresh();
				let mut env2 = env.clone();
				env2.insert(arg.item.clone(), Scheme::mono(arg_ty.clone()));
				let body_ty = self.infer(body, &env2);
				Ty::Fn(Box::new(self.subst.apply(&arg_ty)), Box::new(body_ty))
			}
			Expr::App(func, arg) => {
				let ft = self.infer(func, env);
				let at = self.infer(arg, env);
				let ret = self.fresh();
				let expected_fn = Ty::Fn(Box::new(at), Box::new(ret.clone()));
				self.unify(&ft, &expected_fn, env, *span);
				self.subst.apply(&ret)
			}
			Expr::Product(a, b) => {
				let ta = self.infer(a, env);
				let tb = self.infer(b, env);
				Ty::Product(Box::new(ta), Box::new(tb))
			}
			Expr::Match(cases) => self.infer_match(cases, env, *span),
		}
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

		if segments.len() == 1 {
			let name = &segments[0];
			if let Some(scheme) = env.vars.get(name.as_str()) {
				return self.instantiate(scheme);
			}
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

	fn infer_match(
		&mut self,
		cases: &[(Vec<Spanned<Pattern>>, Spanned<Expr>)],
		env: &TypeEnv,
		span: Span,
	) -> Ty {
		let mut expected_branch_ty: Option<Ty> = None;
		// arg types of first case before folded into fn type
		// after each case unified w/ others, these are authoritative regardless of origin
		let mut col_tys: Option<Vec<Ty>> = None;

		if cases.is_empty() {
			self.error("match expression has no cases", span);
			return self.fresh();
		}

		for (pats, body) in cases {
			let mut branch_env = env.clone();

			let mut pat_tys = Vec::new();

			for pat in pats {
				let ty = self.fresh();
				branch_env
					.vars
					.extend(self.check_pattern(pat, &ty, &branch_env));
				pat_tys.push(ty);
			}

			if col_tys.is_none() {
				col_tys = Some(pat_tys.clone());
			}

			let mut body_ty = self.infer(body, &branch_env);

			for ty in pat_tys.into_iter().rev() {
				body_ty = Ty::Fn(Box::new(self.subst.apply(&ty)), Box::new(body_ty));
			}

			match &expected_branch_ty {
				Some(expected) => {
					self.unify(&body_ty, expected, &branch_env, span);
				}
				None => {
					expected_branch_ty = Some(body_ty);
				}
			}
		}

		if let Some(tys) = col_tys {
			let final_col_tys: Vec<Ty> = tys.iter().map(|t| self.subst.apply(t)).collect();
			self.check_exhaustiveness(cases, &final_col_tys, env, span);
		}

		match expected_branch_ty {
			Some(ty) => self.subst.apply(&ty),
			None => {
				self.error("internal error: match produced no type", span);
				self.fresh()
			}
		}
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

	// returns witness -- concrete row of col vals not covered by matrix
	// if matrix is non-exhaustive for col_tys, or none if it is
	fn find_uncovered(
		&mut self,
		matrix: &[Vec<Pattern>],
		col_tys: &[Ty],
		env: &TypeEnv,
		span: Span,
	) -> Option<Vec<MatchWitness>> {
		let Some((ty0, rest_tys)) = col_tys.split_first() else {
			// no more cols, row is covered iff some row survived
			return if matrix.is_empty() {
				Some(Vec::new())
			} else {
				None
			};
		};
		let ty0 = self.subst.apply(ty0);

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
		if let Ty::Sum(a, b) = &ty0 {
			if matrix
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
					if let Some(w) = self.find_uncovered(&sub_matrix, &sub_tys, env, span) {
						let (head, tail) = w.split_at(1);
						let shown = if is_left { "left" } else { "right" };
						let mut out = vec![MatchWitness::Ctor(
							format!("({})", if is_left { "_ +" } else { "+ _" }),
							head.first()
								.cloned()
								.filter(|h| !matches!(h, MatchWitness::Wild))
								.map(Box::new),
						)];
						let _ = shown;
						out.extend_from_slice(tail);
						return Some(out);
					}
				}
				return None;
			}
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
				if let Some(w) = self.find_uncovered(&sub_matrix, &sub_tys, env, span) {
					let (head, tail) = w.split_at(arity);
					let payload = head.first().cloned().map(Box::new);
					let mut out = vec![MatchWitness::Ctor(name.clone(), payload)];
					out.extend_from_slice(tail);
					return Some(out);
				}
			}
			return None;
		}

		let sig_result = self.ctor_signature(&ty0, env);
		match sig_result {
			Some(full_sig) => {
				let heads_seen: Vec<&str> = matrix
					.iter()
					.filter_map(|row| pattern_ctor_name(&row[0]))
					.collect();
				let complete = full_sig
					.iter()
					.all(|(name, _)| heads_seen.contains(&name.as_str()));

				if complete {
					// try every ctor, if any has an uncovered case then it's
					// the witness
					for (name, arity) in &full_sig {
						let sub_matrix: Vec<Vec<Pattern>> = matrix
							.iter()
							.filter_map(|row| specialize_ctor_row(row, name, *arity))
							.collect();
						let mut sub_tys = self.ctor_payload_tys(&ty0, name, *arity, env, span);
						sub_tys.extend(rest_tys.iter().cloned());
						if let Some(w) = self.find_uncovered(&sub_matrix, &sub_tys, env, span) {
							let (head, tail) = w.split_at(*arity);
							let payload = head.first().cloned().map(Box::new);
							let mut out = vec![MatchWitness::Ctor(name.clone(), payload)];
							out.extend_from_slice(tail);
							return Some(out);
						}
					}
					None
				} else {
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
			}
			// only pattern that can actually make it exhaustive is a wildcard
			// so only default matrix (rows alr have one here) can cover
			None => {
				let default_matrix: Vec<Vec<Pattern>> =
					matrix.iter().filter_map(|row| default_row(row)).collect();
				self.find_uncovered(&default_matrix, rest_tys, env, span)
					.map(|mut w| {
						w.insert(0, MatchWitness::Wild);
						w
					})
			}
		}
	}

	// if ty is a registered sum, any (ctor, arity) pairs have arity 0 or 1
	// ret none for type with no finite, known ctor set
	fn ctor_signature(&self, ty: &Ty, env: &TypeEnv) -> Option<Vec<(String, usize)>> {
		let head_name = ty_head_name(ty);
		let mut out: Vec<(String, usize)> = Vec::new();
		for (key, scheme) in &env.data_ctors {
			if key.len() == 2 && key[0] == head_name && !out.iter().any(|(n, _)| n == &key[1]) {
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
				let ctor_ty = self.infer_qualified(q, env);

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

	fn check_with_clauses(&mut self, with_clauses: &[Spanned<Binding>], env: &TypeEnv) -> TypeEnv {
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
		}
		let mut checked: Vec<Checked> = Vec::with_capacity(pending.len());
		for p in pending {
			let inner_env = self.check_with_clauses(&p.wb.item.with_clauses, &with_env);
			if let Some(body) = &p.wb.item.value {
				let inferred = self.infer(body, &inner_env);
				self.unify(&p.declared_ty, &inferred, &with_env, p.wb.span);
			}
			checked.push(Checked {
				wb: p.wb,
				tvars: p.tvars,
				declared_ty: p.declared_ty,
			});
		}

		for c in checked {
			let b = &c.wb.item;
			let final_ty = self.subst.apply(&c.declared_ty);

			let mut env_for_gen = with_env.clone();
			env_for_gen.vars.remove(&b.name.item);
			let mut constraint_map: HashMap<u32, Vec<String>> = HashMap::new();
			for constraint in &b.constraints {
				if let Some(tv) = c.tvars.get(&constraint.item.type_var.item) {
					if let Ty::Var(id) = self.subst.apply(tv) {
						let classes = constraint_map.entry(id).or_default();
						for class_name in &constraint.item.class_names {
							if !classes.contains(&class_name.item) {
								classes.push(class_name.item.clone());
							}
						}
					}
				}
			}
			let scheme = generalise_with_constraints(&env_for_gen, &final_ty, &constraint_map);
			with_env.insert(b.name.item.clone(), scheme);
		}

		with_env
	}

	fn check_binding_group(&mut self, bindings: &[(&Binding, Span)], env: &mut TypeEnv) {
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

			env.insert(b.name.item.clone(), Scheme::mono(declared_ty.clone()));
			pending.push(Pending {
				b,
				span: *span,
				tvars,
				declared_ty,
			});
		}

		struct Checked<'a> {
			b: &'a Binding,
			tvars: HashMap<String, Ty>,
			declared_ty: Ty,
		}
		let mut checked: Vec<Checked> = Vec::with_capacity(pending.len());
		for p in pending {
			let inner_env = self.check_with_clauses(&p.b.with_clauses, env);
			if let Some(body) = &p.b.value {
				let inferred = self.infer(body, &inner_env);
				self.unify(&p.declared_ty, &inferred, env, p.span);
			}
			checked.push(Checked {
				b: p.b,
				tvars: p.tvars,
				declared_ty: p.declared_ty,
			});
		}

		for c in checked {
			let final_ty = self.subst.apply(&c.declared_ty);

			let mut env_for_gen = env.clone();
			env_for_gen.vars.remove(&c.b.name.item);
			let mut constraint_map: HashMap<u32, Vec<String>> = HashMap::new();
			for constraint in &c.b.constraints {
				if let Some(tv) = c.tvars.get(&constraint.item.type_var.item) {
					if let Ty::Var(id) = self.subst.apply(tv) {
						let classes = constraint_map.entry(id).or_default();
						for class_name in &constraint.item.class_names {
							if !classes.contains(&class_name.item) {
								classes.push(class_name.item.clone());
							}
						}
					}
				}
			}
			let scheme = generalise_with_constraints(&env_for_gen, &final_ty, &constraint_map);
			env.insert(c.b.name.item.clone(), scheme);
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

		let with_env = self.check_with_clauses(&binding.with_clauses, &with_env);

		if let Some(body) = &binding.value {
			let inferred = self.infer(body, &with_env);
			self.unify(&declared_ty, &inferred, env, *span);
		}
		// extern body -- just trust the annotation

		let final_ty = self.subst.apply(&declared_ty);
		let scheme = if generalize {
			let mut env_for_gen = env.clone();
			env_for_gen.vars.remove(&binding.name.item);

			let mut constraint_map: HashMap<u32, Vec<String>> = HashMap::new();
			for constraint in &binding.constraints {
				if let Some(tv) = tvars.get(&constraint.item.type_var.item) {
					if let Ty::Var(id) = self.subst.apply(tv) {
						let classes = constraint_map.entry(id).or_default();
						for class_name in &constraint.item.class_names {
							if !classes.contains(&class_name.item) {
								classes.push(class_name.item.clone());
							}
						}
					}
				}
			}

			generalise_with_constraints(&env_for_gen, &final_ty, &constraint_map)
		} else {
			Scheme::mono(final_ty)
		};

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

// return ctor name and payload if leaf of sum, otherwise none (shouldnt happen, if it does i fucked
// up somewhere)
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
	}
}

fn instance_method_key(inst_ty: &Ty, method_name: &str) -> String {
	format!("{}:{}", ty_head_name(inst_ty), method_name)
}

fn collect_top_level(spanned_tl: &Spanned<TopLevel>, env: &mut TypeEnv, checker: &mut Checker<'_>) {
	collect_top_level_in(spanned_tl, env, checker, &[]);
}

// every bare name that b references, exc. local bindings
// used to build the call graph among bindings so they can be split into mutual-recursion groups
// instead of one blob. name not part of a cycle should be fully generalized before its callers are
// checked so it stays usable w/ different types
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
			if let Some(&j) = name_to_idx.get(referenced.as_str()) {
				if j != i {
					adj[i].push(j);
				}
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
				checker.check_binding_group(&scc, &mut local_env);
			}

			for (local_key, scheme) in &local_env.vars {
				if local_key.contains(':') {
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
				env.insert(local_key.clone(), scheme.clone());

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
					env.instances.push(inst.clone());
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
		TopLevel::TypeDef(name, params, body) => {
			let local_name = name.item.0.join(":");
			let flat_name = if module_path.is_empty() {
				local_name.clone()
			} else {
				format!("{}:{}", module_path.join(":"), local_name)
			};
			env.type_ctors.insert(flat_name.clone(), params.len());
			env.type_ctors.insert(local_name.clone(), params.len());

			// IMPORTANT only register data ctors against local type name, not flate
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
					.push((class_name.item.clone(), inst_ty.clone()));
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

fn collect_free_type_vars(
	ast: &Spanned<AstType>,
	tvars: &mut HashMap<String, Ty>,
	env: &TypeEnv,
	checker: &mut Checker<'_>,
) {
	match &ast.item {
		AstType::Var(name) => {
			if !env.type_ctors.contains_key(name.as_str())
				&& !env.type_aliases.contains_key(name.as_str())
			{
				tvars.entry(name.clone()).or_insert_with(|| checker.fresh());
			}
		}
		AstType::Fn(a, b) | AstType::Sum(a, b) | AstType::Product(a, b) | AstType::App(a, b) => {
			collect_free_type_vars(a, tvars, env, checker);
			collect_free_type_vars(b, tvars, env, checker);
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
	let result_ty = {
		let mut t: Ty = Ty::Named(type_name.to_string());
		for p in params {
			let tv = checker.fresh();
			t = Ty::App(Box::new(t), Box::new(tv));
		}
		t
	};
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
	let Spanned { item: body, span } = spanned_body;
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
		// App where fn is Var = ctor
		AstType::App(f, payload) => {
			if let Spanned {
				item: AstType::Var(ctor_name),
				..
			} = f.as_ref()
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
		}
		_ => {}
	}
}

fn rebuild_result_ty(type_name: &str, params: &[String], tvars: &HashMap<String, Ty>) -> Ty {
	let mut t: Ty = Ty::Named(type_name.to_string());
	for p in params {
		if let Some(tv) = tvars.get(p) {
			t = Ty::App(Box::new(t), Box::new(tv.clone()));
		}
	}
	t
}

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

#[derive(Debug, Clone)]
pub struct TypedModule {
	pub name: String,
	pub bindings: Vec<TypedBinding>,
	pub submodules: Vec<TypedModule>,
}

pub fn annotate_expr(
	spanned_expr: &Spanned<Expr>,
	env: &TypeEnv,
	checker: &mut Checker<'_>,
) -> TypedExpr {
	let Spanned { item: expr, span } = spanned_expr;
	match expr {
		Expr::Literal(lit) => {
			let ty = checker.infer_literal(
				&Spanned {
					item: lit.clone(),
					span: *span,
				},
				env,
			);
			TypedExpr::Literal(lit.clone(), checker.subst.apply(&ty))
		}
		Expr::Qualified(q) => {
			let ty = checker.infer_qualified(
				&Spanned {
					item: q.clone(),
					span: *span,
				},
				env,
			);
			TypedExpr::Var(q.0.clone(), checker.subst.apply(&ty))
		}
		Expr::Fn(arg, body) => {
			let arg_ty = checker.fresh();
			let mut env2 = env.clone();
			env2.insert(arg.item.clone(), Scheme::mono(arg_ty.clone()));
			let body_expr = annotate_expr(body, &env2, checker);
			let fn_ty = Ty::Fn(
				Box::new(checker.subst.apply(&arg_ty)),
				Box::new(body_expr.ty().clone()),
			);
			TypedExpr::Fn(arg.item.clone(), Box::new(body_expr), fn_ty)
		}
		Expr::App(func, arg) => {
			let func_expr = annotate_expr(func, env, checker);
			let arg_expr = annotate_expr(arg, env, checker);
			let ret = checker.fresh();
			let expected_fn = Ty::Fn(Box::new(arg_expr.ty().clone()), Box::new(ret.clone()));
			checker.unify(func_expr.ty(), &expected_fn, env, *span);
			let ty = checker.subst.apply(&ret);
			TypedExpr::App(Box::new(func_expr), Box::new(arg_expr), ty)
		}
		Expr::Product(a, b) => {
			let ae = annotate_expr(a, env, checker);
			let be = annotate_expr(b, env, checker);
			let ty = Ty::Product(Box::new(ae.ty().clone()), Box::new(be.ty().clone()));
			TypedExpr::Product(Box::new(ae), Box::new(be), ty)
		}
		Expr::Match(cases) => {
			let ty = checker.infer_match(cases, env, *span);
			TypedExpr::Match(
				cases
					.iter()
					.map(|(pats, body)| {
						let mut branch_env = env.clone();
						// tie each pat to match's col type, so vars binded
						// share tvars with enclosing fn instead of being fresh
						let mut cur = checker.subst.apply(&ty);
						for pat in pats {
							let pat_ty = match cur.clone() {
								Ty::Fn(a, b) => {
									cur = *b;
									*a
								}
								_ => checker.fresh(),
							};
							branch_env.vars.extend(checker.check_pattern(
								pat,
								&pat_ty,
								&branch_env,
							));
						}
						let body_e = annotate_expr(body, &branch_env, checker);
						checker.unify(body_e.ty(), &cur, &branch_env, body.span);
						(
							pats.iter()
								.map(|Spanned { item, .. }| item)
								.cloned()
								.collect(),
							body_e,
						)
					})
					.collect(),
				checker.subst.apply(&ty),
			)
		}
	}
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

	// TODO fix this
	env.type_ctors.insert("IO".to_string(), 1);
	let mut checker = Checker::new(registry);

	forward_declare_program(program, &mut env, &mut checker);

	collect_program(program, &mut env, &mut checker);

	checker.suppress_errors = true;
	let typed = build_typed_bindings(program, &env, &mut checker);
	checker.suppress_errors = false;

	let diags = std::mem::take(&mut checker.diags);
	(env, typed, diags)
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
	let Spanned { item: tl, span } = spanned_tl;
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

				env.insert(local_key.clone(), scheme.clone());

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
		TopLevel::TypeDef(name, params, body) => {
			let flat_name = name.item.0.join(":");

			env.type_ctors.insert(flat_name.clone(), params.len());

			if params.is_empty() {
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
			let mut constraint_map: HashMap<u32, Vec<String>> = HashMap::new();
			for constraint in &b.constraints {
				if let Some(Ty::Var(id)) = tvars
					.get(&constraint.item.type_var.item)
					.map(|t| checker.subst.apply(t))
				{
					let classes = constraint_map.entry(id).or_default();
					for c in &constraint.item.class_names {
						if !classes.contains(&c.item) {
							classes.push(c.item.clone());
						}
					}
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

fn build_typed_bindings(
	program: &Spanned<Program>,
	env: &TypeEnv,
	checker: &mut Checker<'_>,
) -> Vec<Spanned<TypedBinding>> {
	let mut result = Vec::new();
	for spanned in &program.item.0 {
		collect_typed_tl(spanned, env, checker, &mut result, &[]);
	}
	result
}

fn annotate_with_clauses(
	enclosing_qualified: &str,
	with_clauses: &[Spanned<Binding>],
	env: &TypeEnv,
	checker: &mut Checker<'_>,
	out: &mut Vec<Spanned<TypedBinding>>,
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
				.entry(constraint.item.type_var.item.clone())
				.or_insert_with(|| checker.fresh());
		}
		let declared_ty = checker.ast_type_to_ty(&wb.item.typ, &mut tvars, &with_env);
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
		let inner_env = annotate_with_clauses(
			&clause_qualified,
			&p.wb.item.with_clauses,
			&with_env,
			checker,
			out,
		);
		let typed_value = p.wb.item.value.as_ref().map(|v| {
			let te = annotate_expr(v, &inner_env, checker);
			checker.unify(&p.declared_ty, te.ty(), &with_env, v.span);
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
		let typed_value = c.typed_value.map(|te| refresh_tys(te, &checker.subst));
		let final_ty = checker.subst.apply(&c.declared_ty);

		let mut env_for_gen = with_env.clone();
		env_for_gen.vars.remove(&b.name.item);
		let mut constraint_map: HashMap<u32, Vec<String>> = HashMap::new();
		for constraint in &b.constraints {
			if let Some(tv) = c.tvars.get(&constraint.item.type_var.item) {
				if let Ty::Var(id) = checker.subst.apply(tv) {
					let classes = constraint_map.entry(id).or_default();
					for class_name in &constraint.item.class_names {
						if !classes.contains(&class_name.item) {
							classes.push(class_name.item.clone());
						}
					}
				}
			}
		}
		let scheme = generalise_with_constraints(&env_for_gen, &final_ty, &constraint_map);

		with_env.insert(b.name.item.clone(), scheme.clone());

		let clause_qualified = format!("{}:{}", enclosing_qualified, b.name.item);
		out.push(Spanned {
			item: TypedBinding {
				name: b.name.item.clone(),
				qualified_name: Some(clause_qualified),
				ty: final_ty,
				scheme,
				value: typed_value,
			},
			span: c.wb.span,
		});
	}

	with_env
}

fn collect_typed_tl(
	spanned_tl: &Spanned<TopLevel>,
	env: &TypeEnv,
	checker: &mut Checker<'_>,
	out: &mut Vec<Spanned<TypedBinding>>,
	module_path: &[String],
) {
	let Spanned { item: tl, span } = spanned_tl;
	match tl {
		TopLevel::Module(mod_name, body) => {
			// should probably just store module-local view but whatever
			let mut path = module_path.to_vec();
			path.push(mod_name.item.clone());
			let prefix = format!("{}:", path.join(":"));

			let mut local_env = env.clone();
			for (k, v) in &env.vars {
				if let Some(bare) = k.strip_prefix(prefix.as_str()) {
					local_env.vars.insert(bare.to_string(), v.clone());
				}
			}

			for item in body {
				collect_typed_tl(item, &local_env, checker, out, &path);
			}
		}
		TopLevel::Binding(b) => {
			let scheme = env
				.vars
				.get(&b.name.item)
				.cloned()
				.unwrap_or_else(|| Scheme::mono(checker.fresh()));
			let ty = checker.instantiate(&scheme);
			let qualified_name = if module_path.is_empty() {
				None
			} else {
				Some(format!("{}:{}", module_path.join(":"), b.name.item))
			};
			let enclosing_qualified = qualified_name
				.clone()
				.unwrap_or_else(|| b.name.item.clone());
			let with_env =
				annotate_with_clauses(&enclosing_qualified, &b.with_clauses, env, checker, out);
			let typed_value = b.value.as_ref().map(|v| {
				let te = annotate_expr(v, &with_env, checker);
				checker.unify(&ty, te.ty(), &with_env, v.span);
				te
			});
			let typed_value = typed_value.map(|te| refresh_tys(te, &checker.subst));
			out.push(Spanned {
				item: TypedBinding {
					name: b.name.item.clone(),
					qualified_name,
					ty: checker.subst.apply(&ty),
					scheme: checker.subst.apply_scheme(&scheme),
					value: typed_value,
				},
				span: *span,
			});
		}
		TopLevel::Instance(_, type_args, bindings) => {
			let mut inst_tvars: HashMap<String, Ty> = HashMap::new();
			for arg in type_args {
				collect_free_type_vars(arg, &mut inst_tvars, env, checker);
			}
			let inst_ty = type_args
				.first()
				.map(|first| checker.ast_type_to_ty(first, &mut inst_tvars.clone(), env));

			for b in bindings {
				let qualified_key = inst_ty
					.as_ref()
					.map(|ty| instance_method_key(ty, &b.item.name.item));
				let scheme = qualified_key
					.as_ref()
					.and_then(|k| env.instance_methods.get(k))
					.or_else(|| env.vars.get(&b.item.name.item))
					.cloned()
					.unwrap_or_else(|| Scheme::mono(checker.fresh()));
				let ty = checker.instantiate(&scheme);
				let enclosing_qualified = qualified_key
					.clone()
					.unwrap_or_else(|| b.item.name.item.clone());
				let with_env = annotate_with_clauses(
					&enclosing_qualified,
					&b.item.with_clauses,
					env,
					checker,
					out,
				);
				let typed_value = b.item.value.as_ref().map(|v| {
					let te = annotate_expr(v, &with_env, checker);
					checker.unify(&ty, te.ty(), &with_env, v.span);
					te
				});
				let typed_value = typed_value.map(|te| refresh_tys(te, &checker.subst));
				out.push(Spanned {
					item: TypedBinding {
						name: b.item.name.item.clone(),
						qualified_name: qualified_key,
						ty: checker.subst.apply(&ty),
						scheme: checker.subst.apply_scheme(&scheme),
						value: typed_value,
					},
					span: *span,
				});
			}
		}
		_ => {}
	}
}
