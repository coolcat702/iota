// instance resolution and monomorphization

use std::collections::{HashMap, VecDeque};

use crate::diag::Diagnostic;
use crate::ir::*;
use crate::lang::Lang;
use crate::parser::Span;
use crate::typechecker::Ty;
use crate::types::{TypeInfo, default_vars, has_vars};

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
			return;
		}
		let Some(e) = self.externs.get(job.name.as_str()).copied() else {
			return;
		};
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
					Some((c, None)) => Atom::Global(self.request(&c, &t), t),
					Some((c, Some(at))) => match self.structural_wrapper(m, &c, &at, &t) {
						Some(w) => Atom::Global(w, t),
						None => Atom::Lit(crate::parser::Literal::Int(0)),
					},
					None => Atom::Lit(crate::parser::Literal::Int(0)),
				}
			}
		}
	}

	fn resolve_method(&mut self, m: &str, ty: &Ty) -> Option<(Name, Option<Ty>)> {
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
		// Fall back to the structural type head
		let structural_head = self.ti.structural_instance_head(at);
		if !tried.contains(&structural_head) {
			tried.push(structural_head.clone());
		}
		for h in &tried {
			let canonical = format!("{}:{}", h, m);
			if self.ov.canonical.contains(&canonical) {
				let wrap =
					*h == structural_head && *h != head && self.ti.type_ctors.contains_key(&head);
				return Some((canonical, wrap.then(|| at.clone())));
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

	fn sum_ty(tys: &[Ty]) -> Ty {
		match tys {
			[] => Ty::Unit,
			[t] => t.clone(),
			[t, rest @ ..] => Ty::Sum(Box::new(t.clone()), Box::new(Self::sum_ty(rest))),
		}
	}

	// (canonical ctor, payload type) in the same order the backend uses for tags
	fn nominal_ctors(&self, at: &Ty) -> Option<Vec<(String, Option<Ty>)>> {
		let t = self.ti.norm(at);
		let (h, args) = crate::types::spine(&t);
		let Ty::Named(n) = h else { return None };
		let mut out = Vec::new();
		for c in self.ti.type_ctors.get(n)? {
			let canon = format!("{}:{}", n, c);
			let sch = self.ti.ctor_scheme.get(&canon)?;
			let (p, r) = match &sch.ty {
				Ty::Fn(p, r) => (Some((**p).clone()), (**r).clone()),
				r => (None, r.clone()),
			};
			let mut m = HashMap::new();
			for (ra, a) in crate::types::spine(&r).1.iter().zip(args.iter()) {
				if let Ty::Var(v) = ra {
					m.insert(*v, (**a).clone());
				}
			}
			out.push((canon, p.map(|p| subst_ty(&p, &m))));
		}
		Some(out)
	}

	fn from_body(
		&self,
		ctors: &[(String, Option<Ty>)],
		ptys: &[Ty],
		v: &str,
		at: &Ty,
		depth: usize,
	) -> Expr {
		use crate::lang::LangItem;
		let make = |canon: &str, payload: Option<Atom>| {
			let o = format!("o{}", depth);
			Expr::Let(
				o.clone(),
				at.clone(),
				Value::Ctor(canon.to_string(), payload),
				Box::new(Expr::Halt(Atom::Var(o))),
			)
		};
		let (c0, p0) = &ctors[0];
		if ctors.len() == 1 {
			return make(c0, p0.as_ref().map(|_| Atom::Var(v.to_string())));
		}
		let u = format!("u{}", depth);
		let left_body = Expr::Let(
			u.clone(),
			ptys[0].clone(),
			Value::Unwrap(Atom::Var(v.to_string())),
			Box::new(make(c0, p0.as_ref().map(|_| Atom::Var(u.clone())))),
		);
		let w = format!("w{}", depth);
		let right_body = Expr::Let(
			w.clone(),
			Self::sum_ty(&ptys[1..]),
			Value::Unwrap(Atom::Var(v.to_string())),
			Box::new(self.from_body(&ctors[1..], &ptys[1..], &w, at, depth + 1)),
		);
		Expr::Case(
			Atom::Var(v.to_string()),
			vec![
				Arm {
					pat: CasePat::Ctor(self.lang.item(LangItem::SumLeft).to_string()),
					body: left_body,
				},
				Arm {
					pat: CasePat::Ctor(self.lang.item(LangItem::SumRight).to_string()),
					body: right_body,
				},
			],
		)
	}

	// (to_repr, from_repr, repr type) for nominal type `at`, emitted once per type
	fn repr_fns(&mut self, at: &Ty) -> Option<(Name, Name, Ty)> {
		use crate::lang::LangItem;
		let ctors = self.nominal_ctors(at)?;
		let ptys: Vec<Ty> = ctors
			.iter()
			.map(|(_, p)| p.clone().unwrap_or(Ty::Unit))
			.collect();
		let repr = Self::sum_ty(&ptys);
		let at = self.ti.norm(at);
		let key = ("repr$to".to_string(), display_ty(&at));
		if let Some(to) = self.instances.get(&key).cloned() {
			let from = self.instances[&("repr$from".to_string(), display_ty(&at))].clone();
			return Some((to, from, repr));
		}
		self.counter += 1;
		let (to, from) = (
			format!("repr_to${}", self.counter),
			format!("repr_from${}", self.counter),
		);
		self.instances.insert(key, to.clone());
		self.instances
			.insert(("repr$from".to_string(), display_ty(&at)), from.clone());

		// nullary payloads need a Unit value; the prelude's `unit` constant provides it
		let unit_fn = self.request("Prelude:unit", &Ty::Unit);
		let unit = Atom::Global(unit_fn, Ty::Unit);
		let left = self.lang.item(LangItem::SumLeft).to_string();
		let right = self.lang.item(LangItem::SumRight).to_string();
		let n = ctors.len();

		let mut arms = Vec::new();
		for (i, (canon, p)) in ctors.iter().enumerate() {
			let mut stmts: Vec<(Name, Ty, Value)> = Vec::new();
			let mut cur = match p {
				Some(pt) => {
					stmts.push(("p".into(), pt.clone(), Value::Unwrap(Atom::Var("x".into()))));
					Atom::Var("p".into())
				}
				None => unit.clone(),
			};
			if i < n - 1 {
				stmts.push((
					"l".into(),
					Self::sum_ty(&ptys[i..]),
					Value::Ctor(left.clone(), Some(cur)),
				));
				cur = Atom::Var("l".into());
			}
			for j in (0..i).rev() {
				let v = format!("r{}", j);
				stmts.push((
					v.clone(),
					Self::sum_ty(&ptys[j..]),
					Value::Ctor(right.clone(), Some(cur)),
				));
				cur = Atom::Var(v);
			}
			let body = stmts
				.into_iter()
				.rev()
				.fold(Expr::Halt(cur), |acc, (n, t, v)| {
					Expr::Let(n, t, v, Box::new(acc))
				});
			arms.push(Arm {
				pat: CasePat::Ctor(canon.clone()),
				body,
			});
		}
		let params = vec![("x".to_string(), at.clone())];
		self.out_funcs.push(Function {
			name: to.clone(),
			ty: fn_chain(&params, &repr),
			params,
			ret: repr.clone(),
			body: Expr::Case(Atom::Var("x".into()), arms),
			span: self.span,
		});

		let params = vec![("x".to_string(), repr.clone())];
		self.out_funcs.push(Function {
			name: from.clone(),
			ty: fn_chain(&params, &at),
			params,
			ret: at.clone(),
			body: self.from_body(&ctors, &ptys, "x", &at, 0),
			span: self.span,
		});
		Some((to, from, repr))
	}

	fn structural_wrapper(&mut self, m: &str, canon: &str, at: &Ty, occ: &Ty) -> Option<Name> {
		let key = (format!("{}~repr", m), display_ty(occ));
		if let Some(n) = self.instances.get(&key) {
			return Some(n.clone());
		}
		let (generic, cv) = self.ov.methods.get(m)?.clone();
		let generic = self.ti.norm(&generic);
		let (to, from, repr) = self.repr_fns(at)?;
		let at = self.ti.norm(at);

		self.counter += 1;
		let name = format!("{}~repr${}", canon, self.counter);
		self.instances.insert(key, name.clone()); // before building: recursive types

		let mut bound = HashMap::new();
		match_ty(&generic, occ, &mut bound);
		let mut at_repr = bound.clone();
		at_repr.insert(cv, repr.clone());
		let inner_ty = self.concrete(&generic, &at_repr);
		let inst = self.request(canon, &inner_ty);

		let arity = self.funcs.get(canon)?.params.len();
		let (ptys_g, ret_g) = peel_fn(&generic, arity);
		let var = Ty::Var(cv);
		let mentions = |t: &Ty| {
			let mut one = HashMap::new();
			one.insert(cv, Ty::Unit);
			subst_ty(t, &one) != *t
		};
		for t in ptys_g.iter().chain(std::iter::once(&ret_g)) {
			if *t != var && mentions(t) {
				self.err(format!(
                "structural instance of `{}` for {}: the class type may only appear bare in the method's signature",
                m, display_ty(&at)
            ));
				return None;
			}
		}

		let (to_ty, from_ty) = (
			Ty::Fn(Box::new(at.clone()), Box::new(repr.clone())),
			Ty::Fn(Box::new(repr.clone()), Box::new(at.clone())),
		);
		let mut lets: Vec<(Name, Ty, Value)> = Vec::new();
		let mut args = Vec::new();
		let mut params = Vec::new();
		for (i, pg) in ptys_g.iter().enumerate() {
			let p = format!("p{}", i);
			params.push((p.clone(), self.concrete(pg, &bound)));
			if *pg == var {
				let r = format!("r{}", i);
				lets.push((
					r.clone(),
					repr.clone(),
					Value::App(Atom::Global(to.clone(), to_ty.clone()), Atom::Var(p)),
				));
				args.push(Atom::Var(r));
			} else {
				args.push(Atom::Var(p));
			}
		}
		let mut f = Atom::Global(inst, inner_ty.clone());
		let mut f_ty = inner_ty;
		for (i, a) in args.into_iter().enumerate() {
			let Ty::Fn(_, rest) = f_ty.clone() else {
				return None;
			};
			let h = format!("h{}", i);
			lets.push((h.clone(), (*rest).clone(), Value::App(f, a)));
			f = Atom::Var(h);
			f_ty = *rest;
		}
		if ret_g == var {
			lets.push((
				"out".into(),
				at.clone(),
				Value::App(Atom::Global(from, from_ty), f),
			));
			f = Atom::Var("out".into());
		}
		let body = lets
			.into_iter()
			.rev()
			.fold(Expr::Halt(f), |acc, (n, t, v)| {
				Expr::Let(n, t, v, Box::new(acc))
			});
		let ret = self.concrete(&ret_g, &bound);
		self.out_funcs.push(Function {
			name: name.clone(),
			ty: fn_chain(&params, &ret),
			params,
			ret,
			body,
			span: self.span,
		});
		Some(name)
	}
}
