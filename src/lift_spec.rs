use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::ir::{Arm, Atom, Expr, Function, IrProgram, Name, Value, fn_chain, peel_fn};
use crate::optimize::{expr_size, expr_vars, flatten, rebuild, referenced_globals};
use crate::parser::{Literal, Span};
use crate::typechecker::Ty;

type Binds = Vec<(Name, Ty, Value)>;

// same naming scheme as `Cx::fresh` in optimize, same shared counter
fn fresh(counter: &Cell<u64>, base: &str) -> Name {
	counter.set(counter.get() + 1);
	let stem = base.split('~').next().unwrap_or(base);
	format!("{}~{}", stem, counter.get())
}

fn dummy_body() -> Expr {
	Expr::Halt(Atom::Lit(Literal::Int(0)))
}

/// Type of every parameter and binder in `f` (including lambda parameters and
/// everything inside lambda bodies). Also used by the optimizer for join points.
pub(crate) fn collect_fn_tys(f: &Function) -> HashMap<Name, Ty> {
	fn go(e: &Expr, out: &mut HashMap<Name, Ty>) {
		match e {
			Expr::Halt(_) => {}
			Expr::Case(_, arms) => {
				for a in arms {
					go(&a.body, out);
				}
			}
			Expr::Let(x, t, v, rest) => {
				out.insert(x.clone(), t.clone());
				if let Value::Lambda(p, pt, body) = v {
					out.insert(p.clone(), pt.clone());
					go(body, out);
				}
				go(rest, out);
			}
		}
	}
	let mut m = HashMap::new();
	for (n, t) in &f.params {
		m.insert(n.clone(), t.clone());
	}
	go(&f.body, &mut m);
	m
}

// Lambda lifting

/// Returns true if anything was lifted. New fns appended, and
/// themselves scanned for nested lambdas.
pub fn lambda_lift(program: &mut IrProgram, counter: &Cell<u64>) -> bool {
	let mut funcs: Vec<Function> = std::mem::take(&mut program.functions);
	let mut taken: HashSet<String> = funcs.iter().map(|f| f.name.clone()).collect();
	taken.extend(program.externs.iter().map(|e| e.name.clone()));

	let mut any = false;
	let mut i = 0;
	while i < funcs.len() {
		let tys = collect_fn_tys(&funcs[i]);
		let owner = funcs[i].name.clone();
		let span = funcs[i].span;
		let body = std::mem::replace(&mut funcs[i].body, dummy_body());
		let mut created: Vec<Function> = Vec::new();
		let body = lift_expr(body, &tys, &owner, span, counter, &mut taken, &mut created);
		funcs[i].body = body;
		if !created.is_empty() {
			any = true;
			funcs.extend(created);
		}
		i += 1;
	}
	program.functions = funcs;
	any
}

fn lift_expr(
	e: Expr,
	tys: &HashMap<Name, Ty>,
	owner: &str,
	span: Span,
	counter: &Cell<u64>,
	taken: &mut HashSet<String>,
	out: &mut Vec<Function>,
) -> Expr {
	let (binds, tail) = flatten(e);
	let mut new_binds: Binds = Vec::with_capacity(binds.len());

	for (x, ty, v) in binds {
		match v {
			Value::Lambda(p, pty, body) => {
				let mut free: Vec<Name> = {
					let mut s = expr_vars(&body);
					s.remove(&p);
					s.into_iter().collect()
				};
				free.sort();
				let free_tys: Option<Vec<Ty>> = free.iter().map(|n| tys.get(n).cloned()).collect();
				let Some(free_tys) = free_tys else {
					// a captured variable we cannot type: keep the closure, but lift inside it
					let nb = lift_expr(*body, tys, owner, span, counter, taken, out);
					new_binds.push((x, ty, Value::Lambda(p, pty, Box::new(nb))));
					continue;
				};

				counter.set(counter.get() + 1);
				let mut name = format!("{}$lam{}", owner, counter.get());
				while taken.contains(&name) {
					name.push('_');
				}
				taken.insert(name.clone());

				let (_, ret) = peel_fn(&ty, 1);
				let mut params: Vec<(Name, Ty)> = free.iter().cloned().zip(free_tys).collect();
				params.push((p, pty));
				let full_ty = fn_chain(&params, &ret);
				out.push(Function {
					name: name.clone(),
					params,
					ret,
					ty: full_ty.clone(),
					body: *body,
					span,
				});

				if free.is_empty() {
					new_binds.push((x, ty, Value::Atom(Atom::Global(name, full_ty))));
				} else {
					let n = free.len();
					let mut head = Atom::Global(name, full_ty.clone());
					for (k, fv) in free.iter().enumerate() {
						let last = k + 1 == n;
						let res = if last {
							x.clone()
						} else {
							fresh(counter, "pap")
						};
						let rty = if last {
							ty.clone()
						} else {
							peel_fn(&full_ty, k + 1).1
						};
						new_binds.push((res.clone(), rty, Value::App(head, Atom::Var(fv.clone()))));
						head = Atom::Var(res);
					}
				}
			}
			other => new_binds.push((x, ty, other)),
		}
	}

	let tail = match tail {
		Expr::Case(s, arms) => Expr::Case(
			s,
			arms.into_iter()
				.map(|arm| Arm {
					pat: arm.pat,
					body: lift_expr(arm.body, tys, owner, span, counter, taken, out),
				})
				.collect(),
		),
		other => other,
	};
	rebuild(new_binds, tail)
}

// Specialization of recursive higher-order functions

const SPEC_MAX_SIZE: usize = 200; // largest function the optimizer is willing to copy
const MAX_SPECS: usize = 64; // total copies per run

type Paps = HashMap<Name, (String, Vec<Atom>)>; // var -> (global, args applied so far)
type SpecKey = (String, Vec<(usize, String, usize)>); // (function, [(param, head, #captured)])

struct Spec<'a> {
	counter: &'a Cell<u64>,
	arity: HashMap<String, usize>,
	fn_tys: HashMap<String, Ty>,
	param_tys: HashMap<String, Vec<Ty>>,
	/// recursive functions with at least one static fn parameter, and which params are static
	cands: HashMap<String, (Rc<Function>, Vec<bool>)>,
	table: HashMap<SpecKey, String>,
	new_funcs: Vec<Function>,
	changed: bool,
}

/// Returns true if any call was redirected to a specialized copy
pub fn specialize_hof(program: &mut IrProgram, counter: &Cell<u64>) -> bool {
	let mut arity = HashMap::new();
	let mut fn_tys = HashMap::new();
	let mut param_tys = HashMap::new();
	for f in &program.functions {
		arity.insert(f.name.clone(), f.params.len());
		fn_tys.insert(f.name.clone(), f.ty.clone());
		param_tys.insert(
			f.name.clone(),
			f.params.iter().map(|(_, t)| t.clone()).collect::<Vec<_>>(),
		);
	}
	for e in &program.externs {
		arity.insert(e.name.clone(), e.arity);
		fn_tys.insert(e.name.clone(), e.ty.clone());
		param_tys.insert(e.name.clone(), peel_fn(&e.ty, e.arity).0);
	}

	let mut cands = HashMap::new();
	for f in &program.functions {
		// directly self-recursive and small enough to copy
		if !referenced_globals(&f.body).contains(&f.name) || expr_size(&f.body) > SPEC_MAX_SIZE {
			continue;
		}
		let statics = compute_statics(f);
		let has_fn_static = f
			.params
			.iter()
			.zip(statics.iter())
			.any(|((_, t), &s)| s && matches!(t, Ty::Fn(..)));
		if has_fn_static {
			cands.insert(f.name.clone(), (Rc::new(f.clone()), statics));
		}
	}
	if cands.is_empty() {
		return false;
	}

	let mut sp = Spec {
		counter,
		arity,
		fn_tys,
		param_tys,
		cands,
		table: HashMap::new(),
		new_funcs: Vec::new(),
		changed: false,
	};

	// the queue grows as copies are created, so each copy's own recursive calls
	// are redirected to it within this same run
	let mut queue: Vec<Function> = std::mem::take(&mut program.functions);
	let mut i = 0;
	while i < queue.len() {
		let body = std::mem::replace(&mut queue[i].body, dummy_body());
		queue[i].body = spec_block(body, &HashMap::new(), &mut sp);
		let news = std::mem::take(&mut sp.new_funcs);
		queue.extend(news);
		i += 1;
	}
	program.functions = queue;
	sp.changed
}

// which parameters does every recursive call pass through unchanged?

fn f_related(a: &Atom, f: &Function, paps: &HashMap<Name, usize>) -> bool {
	match a {
		Atom::Global(n, _) => *n == f.name,
		Atom::Var(v) => paps.contains_key(v),
		_ => false,
	}
}

fn compute_statics(f: &Function) -> Vec<bool> {
	let mut st = vec![true; f.params.len()];
	let mut escaped = false;
	scan_static(&f.body, f, &mut HashMap::new(), &mut st, &mut escaped);
	if escaped {
		// `f` itself (or a pap of it) is used as a value
		st.iter_mut().for_each(|s| *s = false);
	}
	st
}

// `paps`: variable -> number of arguments already applied to `f`
fn scan_static(
	e: &Expr,
	f: &Function,
	paps: &mut HashMap<Name, usize>,
	st: &mut Vec<bool>,
	escaped: &mut bool,
) {
	let mut cur = e;
	loop {
		match cur {
			Expr::Halt(a) => {
				if f_related(a, f, paps) {
					*escaped = true;
				}
				return;
			}
			Expr::Case(s, arms) => {
				if f_related(s, f, paps) {
					*escaped = true;
				}
				for arm in arms {
					scan_static(&arm.body, f, &mut paps.clone(), st, escaped);
				}
				return;
			}
			Expr::Let(x, _, v, rest) => {
				match v {
					Value::App(h, a) => {
						let n: Option<usize> = match h {
							Atom::Global(g, _) if *g == f.name => Some(0),
							Atom::Var(hv) => paps.get(hv).copied(),
							_ => None,
						};
						if f_related(a, f, paps) {
							*escaped = true;
						}
						if let Some(n) = n {
							if n < f.params.len()
								&& !matches!(a, Atom::Var(av) if *av == f.params[n].0)
							{
								st[n] = false;
							}
							if n + 1 < f.params.len() {
								paps.insert(x.clone(), n + 1);
							}
						}
					}
					Value::Atom(a) | Value::Proj(a, _) | Value::Unwrap(a)
						if f_related(a, f, paps) =>
					{
						*escaped = true;
					}
					Value::Pair(a, b) if f_related(a, f, paps) || f_related(b, f, paps) => {
						*escaped = true;
					}
					Value::Ctor(_, Some(a)) if f_related(a, f, paps) => {
						*escaped = true;
					}
					Value::Lambda(_, _, body) => {
						scan_static(body, f, &mut paps.clone(), st, escaped);
					}
					Value::Ctor(_, None) | Value::Str(_) | Value::Fail(_) => {}
					_ => {}
				}
				cur = &**rest;
			}
		}
	}
}

// rewriting call sites

fn pap_head(a: &Atom, paps: &Paps, sp: &Spec) -> Option<(String, Vec<Atom>)> {
	match a {
		Atom::Global(g, _) if sp.arity.contains_key(g) => Some((g.clone(), Vec::new())),
		Atom::Var(v) => paps.get(v).cloned(),
		_ => None,
	}
}

fn spec_block(e: Expr, outer: &Paps, sp: &mut Spec) -> Expr {
	let (binds, tail) = flatten(e);
	let mut paps: Paps = outer.clone();
	let mut out: Binds = Vec::with_capacity(binds.len());

	for (x, ty, v) in binds {
		match v {
			Value::Atom(a) => {
				if let Some(p) = pap_head(&a, &paps, sp) {
					paps.insert(x.clone(), p);
				}
				out.push((x, ty, Value::Atom(a)));
			}
			Value::App(f, a) => {
				let Some((g, mut args)) = pap_head(&f, &paps, sp) else {
					out.push((x, ty, Value::App(f, a)));
					continue;
				};
				args.push(a.clone());
				match sp.arity.get(&g).copied() {
					// still a pap: remember it
					Some(n) if args.len() < n => {
						paps.insert(x.clone(), (g, args));
						out.push((x, ty, Value::App(f, a)));
					}
					// saturated call: specialize if a static function argument is known
					Some(n) if args.len() == n => match sp.try_specialize(&g, &args, &paps) {
						Some((spec_name, new_args)) => {
							sp.changed = true;
							emit_call(&mut out, sp, x, ty, spec_name, new_args);
						}
						None => out.push((x, ty, Value::App(f, a))),
					},
					_ => out.push((x, ty, Value::App(f, a))),
				}
			}
			Value::Lambda(p, pt, body) => {
				// normally lifted already; stay correct if one survives
				let nb = spec_block(*body, &paps, sp);
				out.push((x, ty, Value::Lambda(p, pt, Box::new(nb))));
			}
			other => out.push((x, ty, other)),
		}
	}

	let tail = match tail {
		Expr::Case(s, arms) => Expr::Case(
			s,
			arms.into_iter()
				.map(|arm| Arm {
					pat: arm.pat,
					body: spec_block(arm.body, &paps, sp),
				})
				.collect(),
		),
		other => other,
	};
	rebuild(out, tail)
}

// `let x = <spec_name> a1 .. an` as a chain of unary applications
fn emit_call(out: &mut Binds, sp: &Spec, x: Name, ty: Ty, spec_name: String, new_args: Vec<Atom>) {
	let spec_ty = sp.fn_tys[&spec_name].clone();
	if new_args.is_empty() {
		out.push((x, ty, Value::Atom(Atom::Global(spec_name, spec_ty))));
		return;
	}
	let n = new_args.len();
	let mut head = Atom::Global(spec_name, spec_ty.clone());
	for (k, arg) in new_args.into_iter().enumerate() {
		let last = k + 1 == n;
		let name = if last {
			x.clone()
		} else {
			fresh(sp.counter, "sp")
		};
		let rty = if last {
			ty.clone()
		} else {
			peel_fn(&spec_ty, k + 1).1
		};
		out.push((name.clone(), rty, Value::App(head, arg)));
		head = Atom::Var(name);
	}
}

impl<'a> Spec<'a> {
	// a function value we can see through: a global (nothing captured) or a
	// pap of one
	fn known_fun(&self, a: &Atom, paps: &Paps) -> Option<(String, Vec<Atom>)> {
		let (h, caps) = match a {
			Atom::Global(g, _) => (g.clone(), Vec::new()),
			Atom::Var(v) => paps.get(v)?.clone(),
			_ => return None,
		};
		let ar = *self.arity.get(&h)?;
		if ar >= 1 && caps.len() < ar {
			Some((h, caps))
		} else {
			None
		}
	}

	fn try_specialize(
		&mut self,
		g: &str,
		args: &[Atom],
		paps: &Paps,
	) -> Option<(String, Vec<Atom>)> {
		let (func, statics) = self.cands.get(g).map(|(f, s)| (f.clone(), s.clone()))?;

		let mut parts: Vec<(usize, String, usize)> = Vec::new();
		let mut caps_of: HashMap<usize, Vec<Atom>> = HashMap::new();
		for (i, (_, pty)) in func.params.iter().enumerate() {
			if !statics[i] || !matches!(pty, Ty::Fn(..)) {
				continue;
			}
			let Some((h, caps)) = self.known_fun(&args[i], paps) else {
				continue;
			};
			if h == g {
				continue;
			}
			parts.push((i, h, caps.len()));
			caps_of.insert(i, caps);
		}
		if parts.is_empty() {
			return None;
		}

		let key: SpecKey = (g.to_string(), parts.clone());
		let spec_name = match self.table.get(&key) {
			Some(n) => n.clone(),
			None => {
				if self.table.len() >= MAX_SPECS {
					return None;
				}
				self.make_spec(&func, &parts, key)?
			}
		};

		// arguments of the new call: captured values replace the function argument
		let mut new_args = Vec::new();
		for (i, a) in args.iter().enumerate() {
			match caps_of.get(&i) {
				Some(caps) => new_args.extend(caps.iter().cloned()),
				None => new_args.push(a.clone()),
			}
		}
		Some((spec_name, new_args))
	}

	fn make_spec(
		&mut self,
		func: &Function,
		parts: &[(usize, String, usize)],
		key: SpecKey,
	) -> Option<String> {
		self.counter.set(self.counter.get() + 1);
		let name = format!("{}$s{}", func.name, self.counter.get());

		let mut params: Vec<(Name, Ty)> = Vec::new();
		let mut prefix: Binds = Vec::new();
		for (i, (pname, pty)) in func.params.iter().enumerate() {
			let Some((_, h, k)) = parts.iter().find(|(pi, _, _)| *pi == i) else {
				params.push((pname.clone(), pty.clone()));
				continue;
			};
			let h_ty = self.fn_tys.get(h)?.clone();
			let cap_tys = self.param_tys.get(h)?.clone();
			let mut head = Atom::Global(h.clone(), h_ty.clone());
			if *k == 0 {
				// the parameter simply becomes `let p = @h`
				prefix.push((pname.clone(), pty.clone(), Value::Atom(head)));
				continue;
			}
			// the k captured values become new parameters; `p` is rebuilt from them
			for c in 0..*k {
				let cap = fresh(self.counter, "cap");
				params.push((cap.clone(), cap_tys.get(c)?.clone()));
				let last = c + 1 == *k;
				let nm = if last {
					pname.clone()
				} else {
					fresh(self.counter, "pap")
				};
				let ty = if last {
					pty.clone()
				} else {
					peel_fn(&h_ty, c + 1).1
				};
				prefix.push((nm.clone(), ty, Value::App(head, Atom::Var(cap))));
				head = Atom::Var(nm);
			}
		}

		let body = rebuild(prefix, func.body.clone());
		let ret = func.ret.clone();
		let ty = fn_chain(&params, &ret);

		self.arity.insert(name.clone(), params.len());
		self.fn_tys.insert(name.clone(), ty.clone());
		self.param_tys.insert(
			name.clone(),
			params.iter().map(|(_, t)| t.clone()).collect(),
		);
		self.table.insert(key, name.clone());
		self.new_funcs.push(Function {
			name: name.clone(),
			params,
			ret,
			ty,
			body,
			span: func.span,
		});
		Some(name)
	}
}
