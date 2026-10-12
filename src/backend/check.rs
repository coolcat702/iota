// check MIR consistency

use std::collections::HashMap;

use super::mir::*;

fn same(a: &MTy, b: &MTy) -> bool {
	fn strip(t: &MTy) -> MTy {
		match t {
			MTy::Susp(x) => strip(x),
			MTy::Fn(a, b) => MTy::Fn(Box::new(strip(a)), Box::new(strip(b))),
			MTy::Prod(a, b) => MTy::Prod(Box::new(strip(a)), Box::new(strip(b))),
			o => o.clone(),
		}
	}
	strip(a) == strip(b)
}

pub fn check(p: &MProgram, stage: &str) -> Vec<String> {
	let mut errs = Vec::new();
	let sigs: HashMap<&str, &MFunc> = p.funcs.iter().map(|f| (f.name.as_str(), f)).collect();
	for f in &p.funcs {
		let mut env: HashMap<String, MTy> = f.params.iter().cloned().collect();
		let mut cx = Cx {
			sigs: &sigs,
			errs: &mut errs,
			who: format!("{} [{}]", f.name, stage),
		};
		let t = cx.expr(&f.body, &mut env);
		if let Some(t) = t {
			if !same(&t, &f.ret) {
				let msg = format!(
					"{}: body returns {:?} but the function is declared to return {:?}",
					cx.who, t, f.ret
				);
				cx.errs.push(msg);
			}
		}
	}
	errs
}

struct Cx<'a, 'b> {
	sigs: &'a HashMap<&'a str, &'a MFunc>,
	errs: &'b mut Vec<String>,
	who: String,
}

impl Cx<'_, '_> {
	fn atom(&mut self, a: &MAtom, env: &HashMap<String, MTy>) -> Option<MTy> {
		match a {
			MAtom::Var(n) => {
				let t = env.get(n).cloned();
				if t.is_none() {
					let m = format!("{}: unbound variable `{}`", self.who, n);
					self.errs.push(m);
				}
				t
			}
			MAtom::Unit => Some(MTy::Unit),
			MAtom::Int(_) => Some(MTy::Int),
			MAtom::Float(_) => Some(MTy::Float),
			MAtom::Char(_) => Some(MTy::Char),
		}
	}

	fn expr(&mut self, e: &MExpr, env: &mut HashMap<String, MTy>) -> Option<MTy> {
		match e {
			MExpr::Let(x, t, v, rest) => {
				if let Some(vt) = self.value(v, t, env) {
					if !same(&vt, t) {
						let m = format!(
							"{}: `{}` is declared {:?} but its value has type {:?}",
							self.who, x, t, vt
						);
						self.errs.push(m);
					}
				}
				let old = env.insert(x.clone(), t.clone());
				let r = self.expr(rest, env);
				match old {
					Some(o) => env.insert(x.clone(), o),
					None => env.remove(x),
				};
				r
			}
			MExpr::Case(a, arms) => {
				self.atom(a, env);
				let mut res: Option<MTy> = None;
				for arm in arms {
					if let Some(t) = self.expr(&arm.body, env) {
						match &res {
							None => res = Some(t),
							Some(r) if !same(r, &t) => {
								let m = format!(
									"{}: case arms return different types: {:?} and {:?}",
									self.who, r, t
								);
								self.errs.push(m);
							}
							_ => {}
						}
					}
				}
				res
			}
			MExpr::Ret(a) => self.atom(a, env),
			MExpr::Dup(_, r) | MExpr::Drop(_, r) | MExpr::DropReuse(_, _, r) => self.expr(r, env),
			MExpr::Take { binds, rest, .. } => {
				for (n, t, _) in binds {
					env.insert(n.clone(), t.clone());
				}
				self.expr(rest, env)
			}
		}
	}

	fn value(&mut self, v: &MValue, binder: &MTy, env: &mut HashMap<String, MTy>) -> Option<MTy> {
		match v {
			MValue::Atom(a) => self.atom(a, env),
			MValue::Lambda { param, body, free } => {
				let mut inner: HashMap<String, MTy> = free.iter().cloned().collect();
				inner.insert(param.0.clone(), param.1.clone());
				let r = self.expr(body, &mut inner)?;
				Some(MTy::Fn(Box::new(param.1.clone()), Box::new(r)))
			}
			MValue::Delay { body, free } => {
				let mut inner: HashMap<String, MTy> = free.iter().cloned().collect();
				let r = self.expr(body, &mut inner)?;
				Some(MTy::susp(r))
			}
			MValue::Call { func, args } => {
				let f = *self.sigs.get(func.as_str())?;
				if f.params.len() != args.len() {
					let m = format!(
						"{}: call of `{}` with {} arguments, expected {}",
						self.who,
						func,
						args.len(),
						f.params.len()
					);
					self.errs.push(m);
					return None;
				}
				for (i, (a, (_, pt))) in args.iter().zip(&f.params).enumerate() {
					if let Some(at) = self.atom(a, env) {
						if !same(&at, pt) {
							let m = format!(
								"{}: argument {} of `{}` has type {:?}, expected {:?}",
								self.who, i, func, at, pt
							);
							self.errs.push(m);
						}
					}
				}
				Some(f.ret.clone())
			}
			MValue::Apply(f, x) => {
				let ft = self.atom(f, env)?;
				let xt = self.atom(x, env);
				match ft {
					MTy::Fn(a, r) => {
						if let Some(xt) = xt {
							if !same(&a, &xt) {
								let m = format!(
									"{}: applying a {:?} closure to a {:?}",
									self.who, a, xt
								);
								self.errs.push(m);
							}
						}
						Some(*r)
					}
					other => {
						let m =
							format!("{}: applying a non-function of type {:?}", self.who, other);
						self.errs.push(m);
						None
					}
				}
			}
			MValue::Force(a) => match self.atom(a, env)? {
				MTy::Susp(t) => Some(*t),
				other => {
					let m = format!("{}: forcing a non-suspension of type {:?}", self.who, other);
					self.errs.push(m);
					None
				}
			},
			MValue::Wrap(a) => Some(MTy::susp(self.atom(a, env)?)),
			MValue::MakePap { .. } => Some(binder.clone()),
			_ => None,
		}
	}
}
