// lazy eval w/ a strictness analysis
//
//   demand(e) = the variables evaled whenever `e` is evaled.
//
//     Ret x           {x}                       Case x of arms   {x} ∪ ⋂ demand(arm)
//     let x = op in r   demand(op) ∪ (demand(r) − x)   if x ∈ demand(r)  (strict let)
//                       demand(r) − x                  otherwise
//     demand(call f args) = the args at positions f is strict in
//     a failing branch demands everything (it diverges), so it never weakens a ⋂.
//
//   - strict parameter is passed evaled and a strict `let` is evaluated in place, no thunk for either
//   - cheap total primitives on already-evaluated operands are computed eagerly
//   - everything else is delayed: a thunk captures its free vars and runs at most once.
//
// Eval points: `case` scrutinees, fn `Ret`s, primitive operands, fn position of an application, and strict params.
// Ctor fields and pair components are always susps (so infinite structures work). The exception is a
// ctor whose payload is itself a pair: the payload is flattened into the cell, so it is evaluated when the cell is built.

use std::collections::{BTreeSet, HashMap, HashSet};

use super::mir::*;

#[derive(Clone, Debug)]
enum Dem {
	// expr diverges
	Bot,
	Set(BTreeSet<Name>),
}

impl Dem {
	fn empty() -> Dem {
		Dem::Set(BTreeSet::new())
	}
	fn one(a: &MAtom) -> Dem {
		match a {
			MAtom::Var(n) => Dem::Set(BTreeSet::from([n.clone()])),
			_ => Dem::empty(),
		}
	}
	fn contains(&self, x: &str) -> bool {
		match self {
			Dem::Bot => true,
			Dem::Set(s) => s.contains(x),
		}
	}
	// both are evaled
	fn seq(self, o: Dem) -> Dem {
		match (self, o) {
			(Dem::Bot, _) | (_, Dem::Bot) => Dem::Bot,
			(Dem::Set(mut a), Dem::Set(b)) => {
				a.extend(b);
				Dem::Set(a)
			}
		}
	}
	// exactly one is evaled
	fn alt(self, o: Dem) -> Dem {
		match (self, o) {
			(Dem::Bot, x) | (x, Dem::Bot) => x,
			(Dem::Set(a), Dem::Set(b)) => Dem::Set(a.intersection(&b).cloned().collect()),
		}
	}
	fn without(self, x: &str) -> Dem {
		match self {
			Dem::Bot => Dem::Bot,
			Dem::Set(mut s) => {
				s.remove(x);
				Dem::Set(s)
			}
		}
	}
}

type Sig = HashMap<String, Vec<bool>>;

struct Analysis<'a> {
	sig: &'a Sig,
	strict: HashSet<Name>,
}

impl<'a> Analysis<'a> {
	fn value_demand(&mut self, v: &MValue) -> Dem {
		match v {
			MValue::Atom(a)
			| MValue::Proj(a, _)
			| MValue::Field(a, _, _)
			| MValue::Unwrap(a, _) => Dem::one(a),
			MValue::Call { func, args } => {
				let mut d = Dem::empty();
				if let Some(s) = self.sig.get(func) {
					for (i, a) in args.iter().enumerate() {
						if s.get(i).copied().unwrap_or(false) {
							d = d.seq(Dem::one(a));
						}
					}
				}
				d
			}
			MValue::Prim(_, args) => args.iter().fold(Dem::empty(), |d, a| d.seq(Dem::one(a))),
			MValue::Apply(f, _) => Dem::one(f),
			MValue::Fail(_) => Dem::Bot,
			MValue::Lambda { body, .. } => {
				self.expr(body); // record the strict lets inside. nothing goes out
				Dem::empty()
			}
			MValue::Delay { body, .. } => {
				self.expr(body);
				Dem::empty()
			}
			MValue::Str(_)
			| MValue::Pair(..)
			| MValue::Ctor { .. }
			| MValue::CtorReuse { .. }
			| MValue::MakePap { .. }
			| MValue::Force(_)
			| MValue::Wrap(_) => Dem::empty(),
		}
	}

	fn expr(&mut self, e: &MExpr) -> Dem {
		match e {
			MExpr::Ret(a) => Dem::one(a),
			MExpr::Case(a, arms) => {
				let mut it = arms.iter().map(|m| self.expr(&m.body));
				let first = it.next();
				let merged = match first {
					None => Dem::Bot,
					Some(f) => it.fold(f, |acc, d| acc.alt(d)),
				};
				Dem::one(a).seq(merged)
			}
			MExpr::Let(x, _, v, rest) => {
				let dr = self.expr(rest);
				let is_value_form = matches!(
					v,
					MValue::Lambda { .. }
						| MValue::Pair(..) | MValue::Str(_)
						| MValue::MakePap { .. }
						| MValue::Ctor { .. }
				);
				let dv = self.value_demand(v);
				if !is_value_form && dr.contains(x) {
					self.strict.insert(x.clone());
					dv.seq(dr.without(x))
				} else {
					dr.without(x)
				}
			}
			MExpr::Dup(_, r) | MExpr::Drop(_, r) | MExpr::DropReuse(_, _, r) => self.expr(r),
			MExpr::Take { rest, .. } => self.expr(rest),
		}
	}
}

// which fn params and for each fn the set of its `let`s that are strict
fn strictness(prog: &MProgram) -> (Sig, HashMap<String, HashSet<Name>>) {
	let mut sig: Sig = prog
		.funcs
		.iter()
		.map(|f| (f.name.clone(), vec![true; f.params.len()]))
		.collect();
	loop {
		let mut changed = false;
		let mut strict_lets: HashMap<String, HashSet<Name>> = HashMap::new();
		for f in &prog.funcs {
			let mut an = Analysis {
				sig: &sig,
				strict: HashSet::new(),
			};
			let d = an.expr(&f.body);
			let new: Vec<bool> = f.params.iter().map(|(p, _)| d.contains(p)).collect();
			strict_lets.insert(f.name.clone(), an.strict);
			if sig[&f.name] != new {
				sig.insert(f.name.clone(), new);
				changed = true;
			}
		}
		if !changed {
			return (sig, strict_lets);
		}
	}
}

#[derive(Clone, Default)]
struct Env {
	tys: HashMap<Name, MTy>,
	forced: HashMap<Name, Name>, // susp var -> var holding evaled val
}

struct Lz<'a> {
	sig: &'a Sig,
	strict: &'a HashSet<Name>,
	datas: &'a [DataDef],
	n: usize,
}

type Pre = Vec<(Name, MTy, MValue)>;

fn wrap_pre(pre: Pre, tail: MExpr) -> MExpr {
	pre.into_iter()
		.rev()
		.fold(tail, |acc, (n, t, v)| MExpr::Let(n, t, v, Box::new(acc)))
}

impl<'a> Lz<'a> {
	fn fresh(&mut self, hint: &str) -> Name {
		self.n += 1;
		format!("%{}{}", hint, self.n)
	}

	fn atom_ty(&self, a: &MAtom, env: &Env) -> MTy {
		match a {
			MAtom::Var(n) => env.tys[n].clone(),
			MAtom::Unit => MTy::Unit,
			MAtom::Int(_) => MTy::Int,
			MAtom::Float(_) => MTy::Float,
			MAtom::Char(_) => MTy::Char,
		}
	}

	fn is_val(&self, a: &MAtom, env: &Env) -> bool {
		match a {
			MAtom::Var(n) => !env.tys[n].is_susp() || env.forced.contains_key(n),
			_ => true,
		}
	}

	fn val(&mut self, a: &MAtom, env: &mut Env, pre: &mut Pre) -> MAtom {
		let MAtom::Var(x) = a else { return a.clone() };
		match env.tys[x].clone() {
			MTy::Susp(t) => {
				if let Some(v) = env.forced.get(x) {
					return MAtom::Var(v.clone());
				}
				let v = self.fresh("v");
				pre.push((v.clone(), (*t).clone(), MValue::Force(a.clone())));
				env.tys.insert(v.clone(), *t);
				env.forced.insert(x.clone(), v.clone());
				MAtom::Var(v)
			}
			_ => a.clone(),
		}
	}

	fn susp(&mut self, a: &MAtom, env: &mut Env, pre: &mut Pre) -> MAtom {
		let t = self.atom_ty(a, env);
		if t.is_susp() {
			return a.clone();
		}
		let w = self.fresh("w");
		pre.push((w.clone(), MTy::susp(t.clone()), MValue::Wrap(a.clone())));
		env.tys.insert(w.clone(), MTy::susp(t));
		MAtom::Var(w)
	}

	fn payload_of(&self, ty: &MTy, ctor: &str) -> Option<MTy> {
		match ty.inner() {
			MTy::Data(d) => {
				let def = &self.datas[*d];
				def.ctors[def.tag_of(ctor)?].payload.clone()
			}
			_ => None,
		}
	}

	fn expr(&mut self, e: MExpr, env: &mut Env) -> MExpr {
		match e {
			MExpr::Ret(a) => {
				let mut pre = Vec::new();
				let v = self.val(&a, env, &mut pre);
				wrap_pre(pre, MExpr::Ret(v))
			}
			MExpr::Case(a, arms) => {
				let mut pre = Vec::new();
				let va = self.val(&a, env, &mut pre);
				let arms = arms
					.into_iter()
					.map(|m| {
						let mut e2 = env.clone();
						MArm {
							pat: m.pat,
							body: self.expr(m.body, &mut e2),
						}
					})
					.collect();
				wrap_pre(pre, MExpr::Case(va, arms))
			}
			MExpr::Let(x, ty, v, rest) => self.let_(x, ty, v, *rest, env),
			MExpr::Dup(..) | MExpr::Drop(..) | MExpr::DropReuse(..) | MExpr::Take { .. } => {
				unreachable!("reference counting runs after lazification")
			}
		}
	}

	fn let_(&mut self, x: Name, ty: MTy, v: MValue, rest: MExpr, env: &mut Env) -> MExpr {
		let mut pre: Pre = Vec::new();
		let strict_x = self.strict.contains(&x);

		// never delay forms that are values
		let direct: Option<(MTy, MValue)> = match &v {
			MValue::Atom(a) => {
				let t = self.atom_ty(a, env);
				if let Some(f) = a_forced(a, env) {
					env.forced.insert(x.clone(), f);
				}
				Some((t, MValue::Atom(a.clone())))
			}
			MValue::Str(_) => Some((ty.clone(), v.clone())),
			MValue::Pair(a, b) => {
				let (sa, sb) = (self.susp(a, env, &mut pre), self.susp(b, env, &mut pre));
				Some((ty.clone(), MValue::Pair(sa, sb)))
			}
			MValue::MakePap { func, args } => {
				let args = args.iter().map(|a| self.susp(a, env, &mut pre)).collect();
				Some((
					ty.clone(),
					MValue::MakePap {
						func: func.clone(),
						args,
					},
				))
			}
			MValue::Lambda { param, body, .. } => {
				let mut inner = Env {
					tys: env.tys.clone(),
					forced: HashMap::new(),
				};
				let pt = MTy::susp(param.1.clone());
				inner.tys.insert(param.0.clone(), pt.clone());
				let nb = self.expr((**body).clone(), &mut inner);
				let mut free: Vec<(Name, MTy)> = Vec::new();
				let mut names = fv_expr(&nb);
				names.remove(&param.0);
				for n in names {
					let t = env
						.tys
						.get(&n)
						.cloned()
						.unwrap_or_else(|| inner.tys[&n].clone());
					free.push((n, t));
				}
				Some((
					ty.clone(),
					MValue::Lambda {
						param: (param.0.clone(), pt),
						body: Box::new(nb),
						free,
					},
				))
			}
			MValue::Ctor {
				ctor,
				payload: None,
			} => Some((
				ty.clone(),
				MValue::Ctor {
					ctor: ctor.clone(),
					payload: None,
				},
			)),
			MValue::Ctor {
				ctor,
				payload: Some(p),
			} => {
				let pty = self.payload_of(&ty, ctor);
				match pty {
					// payload is a pair, don't force eval. forcing it would make building the ctor demand it
					Some(MTy::Prod(ta, tb)) if !self.is_val(p, env) => {
						let (fa, fb, pp) = (self.fresh("fa"), self.fresh("fb"), self.fresh("pp"));
						let (ta, tb) = ((*ta).clone(), (*tb).clone());
						let rebuilt = MExpr::Let(
							fa.clone(),
							ta.clone(),
							MValue::Proj(p.clone(), crate::ir::Side::Fst),
							Box::new(MExpr::Let(
								fb.clone(),
								tb.clone(),
								MValue::Proj(p.clone(), crate::ir::Side::Rst),
								Box::new(MExpr::Let(
									pp.clone(),
									MTy::Prod(Box::new(ta), Box::new(tb)),
									MValue::Pair(MAtom::Var(fa), MAtom::Var(fb)),
									Box::new(MExpr::Let(
										x,
										ty,
										MValue::Ctor {
											ctor: ctor.clone(),
											payload: Some(MAtom::Var(pp)),
										},
										Box::new(rest),
									)),
								)),
							)),
						);
						return self.expr(rebuilt, env);
					}
					Some(MTy::Prod(..)) => {
						let vp = self.val(p, env, &mut pre);
						Some((
							ty.clone(),
							MValue::Ctor {
								ctor: ctor.clone(),
								payload: Some(vp),
							},
						))
					}
					_ => {
						let sp = self.susp(p, env, &mut pre);
						Some((
							ty.clone(),
							MValue::Ctor {
								ctor: ctor.clone(),
								payload: Some(sp),
							},
						))
					}
				}
			}
			MValue::Proj(a, side) if self.is_val(a, env) => {
				let va = self.val(a, env, &mut pre);
				Some((MTy::susp(ty.clone()), MValue::Proj(va, *side)))
			}
			MValue::Unwrap(a, ctor) if self.is_val(a, env) => {
				let va = self.val(a, env, &mut pre);
				let t = match self.payload_of_atom(a, env, ctor) {
					Some(MTy::Prod(..)) => ty.clone(),
					_ => MTy::susp(ty.clone()),
				};
				Some((t, MValue::Unwrap(va, ctor.clone())))
			}
			_ => None,
		};
		if let Some((fty, fv)) = direct {
			env.tys.insert(x.clone(), fty.clone());
			let r = self.expr(rest, env);
			return wrap_pre(pre, MExpr::Let(x, fty, fv, Box::new(r)));
		}

		let cheap = matches!(&v, MValue::Prim(op, args) if op.is_cheap() && args.iter().all(|a| self.is_val(a, env)));
		if strict_x || cheap {
			let (nv, force_after) = self.build_op(&v, &ty, env, &mut pre);
			if force_after {
				let c = self.fresh("c");
				pre.push((c.clone(), MTy::susp(ty.clone()), nv));
				env.tys.insert(c.clone(), MTy::susp(ty.clone()));
				let fv = MValue::Force(MAtom::Var(c));
				env.tys.insert(x.clone(), ty.clone());
				let r = self.expr(rest, env);
				return wrap_pre(pre, MExpr::Let(x, ty, fv, Box::new(r)));
			}
			env.tys.insert(x.clone(), ty.clone());
			let r = self.expr(rest, env);
			wrap_pre(pre, MExpr::Let(x, ty, nv, Box::new(r)))
		} else {
			// thunk body does its own forcing in a copy of the env
			let mut env_t = Env {
				tys: env.tys.clone(),
				forced: HashMap::new(),
			};
			let mut tpre: Pre = Vec::new();
			let (nv, force_after) = self.build_op(&v, &ty, &mut env_t, &mut tpre);
			let r = self.fresh("r");
			let tail = if force_after {
				let c = self.fresh("c");
				MExpr::Let(
					c.clone(),
					MTy::susp(ty.clone()),
					nv,
					Box::new(MExpr::Let(
						r.clone(),
						ty.clone(),
						MValue::Force(MAtom::Var(c)),
						Box::new(MExpr::Ret(MAtom::Var(r))),
					)),
				)
			} else {
				MExpr::Let(
					r.clone(),
					ty.clone(),
					nv,
					Box::new(MExpr::Ret(MAtom::Var(r))),
				)
			};
			let body = wrap_pre(tpre, tail);
			let free: Vec<(Name, MTy)> = fv_expr(&body)
				.into_iter()
				.map(|n| {
					let t = env.tys[&n].clone();
					(n, t)
				})
				.collect();
			let st = MTy::susp(ty.clone());
			env.tys.insert(x.clone(), st.clone());
			let r = self.expr(rest, env);
			wrap_pre(
				pre,
				MExpr::Let(
					x,
					st,
					MValue::Delay {
						body: Box::new(body),
						free,
					},
					Box::new(r),
				),
			)
		}
	}

	fn payload_of_atom(&self, a: &MAtom, env: &Env, ctor: &str) -> Option<MTy> {
		let MAtom::Var(n) = a else { return None };
		self.payload_of(env.tys.get(n)?, ctor)
	}

	// flag says if result is susp
	fn build_op(&mut self, v: &MValue, ty: &MTy, env: &mut Env, pre: &mut Pre) -> (MValue, bool) {
		match v {
			MValue::Call { func, args } => {
				let strict = self.sig.get(func).cloned().unwrap_or_default();
				let args = args
					.iter()
					.enumerate()
					.map(|(i, a)| {
						if strict.get(i).copied().unwrap_or(false) {
							self.val(a, env, pre)
						} else {
							self.susp(a, env, pre)
						}
					})
					.collect();
				(
					MValue::Call {
						func: func.clone(),
						args,
					},
					false,
				)
			}
			MValue::Apply(f, a) => {
				let f = self.val(f, env, pre);
				let a = self.susp(a, env, pre);
				(MValue::Apply(f, a), false)
			}
			MValue::Prim(op, args) => {
				let args = args.iter().map(|a| self.val(a, env, pre)).collect();
				(MValue::Prim(*op, args), false)
			}
			MValue::Proj(a, side) => {
				let a = self.val(a, env, pre);
				(MValue::Proj(a, *side), true)
			}
			MValue::Unwrap(a, ctor) => {
				let pty = self.payload_of_atom(a, env, ctor);
				let a = self.val(a, env, pre);
				(
					MValue::Unwrap(a, ctor.clone()),
					!matches!(pty, Some(MTy::Prod(..))),
				)
			}
			MValue::Ctor {
				ctor,
				payload: Some(p),
			} => {
				let p = self.val(p, env, pre);
				(
					MValue::Ctor {
						ctor: ctor.clone(),
						payload: Some(p),
					},
					false,
				)
			}
			MValue::Fail(m) => (MValue::Fail(m.clone()), false),
			other => unreachable!("not an operation: {:?} (type {:?})", other, ty),
		}
	}
}

fn a_forced(a: &MAtom, env: &Env) -> Option<Name> {
	match a {
		MAtom::Var(n) => env.forced.get(n).cloned(),
		_ => None,
	}
}

pub fn run(prog: &mut MProgram) {
	let (sig, strict_lets) = strictness(prog);
	let datas = prog.datas.clone();
	for f in &mut prog.funcs {
		let mut lz = Lz {
			sig: &sig,
			strict: &strict_lets[&f.name],
			datas: &datas,
			n: 0,
		};
		let mut env = Env::default();
		let mut params = Vec::new();
		for (i, (p, t)) in f.params.iter().enumerate() {
			let ft = if sig[&f.name][i] {
				t.clone()
			} else {
				MTy::susp(t.clone())
			};
			env.tys.insert(p.clone(), ft.clone());
			params.push((p.clone(), ft));
		}
		let body = std::mem::replace(&mut f.body, MExpr::Ret(MAtom::Unit));
		f.body = dce(lz.expr(body, &mut env), true);
		f.params = params;
	}
}
