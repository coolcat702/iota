// instance resolution and monomorphization

use std::collections::{HashMap, VecDeque};

use crate::diag::Diagnostic;
use crate::ir::*;
use crate::lang::Lang;
use crate::parser::Span;
use crate::typechecker::Ty;
use crate::types::{default_vars, has_vars, TypeInfo};

// polymorphic recursion is bad
const MAX_INSTANCES: usize = 20000;

struct Job {
	name: Name,
	ty: Ty,
	mangled: Name,
}

#[allow(unused)]
struct Spec<'a> {
	funcs: HashMap<&'a str, &'a Function>,
	externs: HashMap<&'a str, &'a Extern>,
	ov: &'a Overloads,
	ti: &'a TypeInfo,
	lang: &'a Lang,
	instances: HashMap<(Name, String), Name>,
	queue: VecDeque<Job>,
	out_funcs: Vec<Function>,
	out_externs: Vec<Extern>,
	errors: Vec<Diagnostic>,
	counter: usize,
	span: Span,
}

pub fn specialize(
	prog: &IrProgram,
	ov: &Overloads,
	ti: &TypeInfo,
	lang: &Lang,
	entry: &str,
) -> Result<IrProgram, Vec<Diagnostic>> {
	let mut sp = Spec {
		funcs: prog
			.functions
			.iter()
			.map(|f| (f.name.as_str(), f))
			.collect(),
		externs: prog.externs.iter().map(|e| (e.name.as_str(), e)).collect(),
		ov,
		ti,
		lang,
		instances: HashMap::new(),
		queue: VecDeque::new(),
		out_funcs: Vec::new(),
		out_externs: Vec::new(),
		errors: Vec::new(),
		counter: 0,
		span: Span::synthetic(0),
	};
	let Some(f) = sp.funcs.get(entry).copied() else {
		return Err(vec![Diagnostic::error(
			format!("entry point `{}` not found", entry),
			None,
		)]);
	};
	sp.span = f.span;
	sp.request(entry, &f.ret.clone());
	while let Some(job) = sp.queue.pop_front() {
		sp.process(job);
	}
	if sp.errors.is_empty() {
		Ok(IrProgram {
			functions: sp.out_funcs,
			externs: sp.out_externs,
		})
	} else {
		Err(sp.errors)
	}
}

impl<'a> Spec<'a> {
	fn err(&mut self, msg: impl Into<String>) {
		let sp = self.span;
		self.errors.push(Diagnostic::error(msg, Some(sp)));
	}

	fn concrete(&self, t: &Ty, tsub: &HashMap<u32, Ty>) -> Ty {
		self.ti
			.norm(&default_vars(&self.ti.norm(&subst_ty(t, tsub))))
	}

	fn request(&mut self, name: &str, ty: &Ty) -> Name {
		let ty = self.ti.norm(&default_vars(ty));
		let generic = match (self.funcs.get(name), self.externs.get(name)) {
			(Some(f), _) => has_vars(&f.ty) || f.params.iter().any(|(_, t)| has_vars(t)),
			(_, Some(e)) => has_vars(&e.ty),
			_ => false,
		};
		let key = (
			name.to_string(),
			if generic {
				display_ty(&ty)
			} else {
				String::new()
			},
		);
		if let Some(m) = self.instances.get(&key) {
			return m.clone();
		}
		if self.instances.len() > MAX_INSTANCES {
			self.err(format!(
				"more than {} function instances were generated: a polymorphic function probably calls itself at ever larger types",
				MAX_INSTANCES
			));
			return name.to_string();
		}
		let mangled = if generic {
			self.counter += 1;
			format!("{}${}", name, self.counter)
		} else {
			name.to_string()
		};
		self.instances.insert(key, mangled.clone());
		self.queue.push_back(Job {
			name: name.to_string(),
			ty,
			mangled: mangled.clone(),
		});
		mangled
	}

	fn process(&mut self, job: Job) {
		if let Some(f) = self.funcs.get(job.name.as_str()).copied() {
			self.span = f.span;
			self.process_func(f, &job);
		} else if let Some(e) = self.externs.get(job.name.as_str()).copied() {
			self.span = e.span;
			if e.intrinsic.is_none() {
				self.err(format!(
					"`{}` is declared as an extern (`= undefined`) but the lang manifest does not say which intrinsic implements it",
					e.name
				));
			}
			self.out_externs.push(Extern {
				name: job.mangled,
				arity: e.arity,
				ty: job.ty,
				intrinsic: e.intrinsic,
				span: e.span,
			});
		}
	}

	fn process_func(&mut self, f: &Function, job: &Job) {
		let generic = self.ti.norm(&fn_chain(&f.params, &f.ret));
		let mut tsub = HashMap::new();
		match_ty(&generic, &job.ty, &mut tsub);
		let params: Vec<(Name, Ty)> = f
			.params
			.iter()
			.map(|(n, t)| (n.clone(), self.concrete(t, &tsub)))
			.collect();
		let ret = self.concrete(&f.ret, &tsub);
		let body = self.expr(&f.body, &tsub);
		self.out_funcs.push(Function {
			name: job.mangled.clone(),
			ty: fn_chain(&params, &ret),
			params,
			ret,
			body,
			span: f.span,
		});
	}

	fn atom(&mut self, a: &Atom, tsub: &HashMap<u32, Ty>) -> Atom {
		match a {
			Atom::Var(_) | Atom::Lit(_) => a.clone(),
			Atom::Global(n, t) => {
				let t = self.concrete(t, tsub);
				Atom::Global(self.request(n, &t), t)
			}
			Atom::Method(m, t) => {
				let t = self.concrete(t, tsub);
				match self.resolve_method(m, &t) {
					Some(c) => Atom::Global(self.request(&c, &t), t),
					None => Atom::Lit(crate::parser::Literal::Int(0)),
				}
			}
		}
	}

	fn resolve_method(&mut self, m: &str, ty: &Ty) -> Option<Name> {
		let Some((generic, class_var)) = self.ov.methods.get(m) else {
			self.err(format!("`{}` is not a known class method", m));
			return None;
		};
		let mut bound = HashMap::new();
		match_ty(&self.ti.norm(generic), ty, &mut bound);
		let class = self.ov.class_of.get(m).cloned().unwrap_or_default();
		let Some(at) = bound.get(class_var).filter(|t| !matches!(t, Ty::Var(_))) else {
			self.err(format!(
				"cannot tell which instance of `{}` to use for `{}` at type {}: the type of its class parameter is not determined here",
				class, m, display_ty(ty)
			));
			return None;
		};
		let head = self.ti.instance_head(at);
		// an instance for an alias is more specific than one for its head so try it first
		// ONLY when type is the exact expansion of the alias
		// causes issues otherwise (`List Int` using instance for `String`)
		let at_norm = self.ti.norm(at);
		let mut tried: Vec<String> = self
			.ti
			.alias_heads(&head)
			.into_iter()
			.filter(|h| self.ti.norm(&Ty::Named(h.clone())) == at_norm)
			.collect();
		tried.push(head.clone());
		for h in &tried {
			let canonical = format!("{}:{}", h, m);
			if self.ov.canonical.contains(&canonical) {
				return Some(canonical);
			}
		}
		let shown = display_ty(at);
		self.err(format!(
			"there is no instance of class `{}` for type {} (looked for {})",
			class,
			shown,
			tried
				.iter()
				.map(|h| format!("`{}:{}`", h, m))
				.collect::<Vec<_>>()
				.join(", ")
		));
		None
	}

	fn value(&mut self, v: &Value, tsub: &HashMap<u32, Ty>) -> Value {
		match v {
			Value::Atom(a) => Value::Atom(self.atom(a, tsub)),
			Value::App(f, a) => Value::App(self.atom(f, tsub), self.atom(a, tsub)),
			Value::Pair(a, b) => Value::Pair(self.atom(a, tsub), self.atom(b, tsub)),
			Value::Ctor(t, p) => Value::Ctor(t.clone(), p.as_ref().map(|a| self.atom(a, tsub))),
			Value::Proj(a, s) => Value::Proj(self.atom(a, tsub), *s),
			Value::Unwrap(a) => Value::Unwrap(self.atom(a, tsub)),
			Value::Str(s) => Value::Str(s.clone()),
			Value::Fail(m) => Value::Fail(m.clone()),
			Value::Lambda(p, t, body) => Value::Lambda(
				p.clone(),
				self.concrete(t, tsub),
				Box::new(self.expr(body, tsub)),
			),
		}
	}

	fn expr(&mut self, e: &Expr, tsub: &HashMap<u32, Ty>) -> Expr {
		match e {
			Expr::Let(x, t, v, rest) => {
				let ty = self.concrete(t, tsub);
				let nv = self.value(v, tsub);
				Expr::Let(x.clone(), ty, nv, Box::new(self.expr(rest, tsub)))
			}
			Expr::Halt(a) => Expr::Halt(self.atom(a, tsub)),
			Expr::Case(a, arms) => Expr::Case(
				self.atom(a, tsub),
				arms.iter()
					.map(|arm| Arm {
						pat: arm.pat.clone(),
						body: self.expr(&arm.body, tsub),
					})
					.collect(),
			),
		}
	}
}
