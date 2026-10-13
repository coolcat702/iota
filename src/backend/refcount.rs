// ref counting (Perceus, Reinking et al., PLDI'21) over the monomorphic ANF,
// plus borrow inference and reuse analysis.
//
// Lazy eval adds three forms (see `lazy.rs`): `Delay` captures its free vars
// like a closure (owned uses, owned and consumed in thunk body), `Force` and
// `Wrap` consume their operand and produce an owned result.
//
// Ownership convention
//   - Owned params, closure captures and let-bound results each hold one
//     reference.
//   - An owned use consumes a ref: call arguments at owned positions, ctor
//     payloads, pair elements, closure captures, `Ret`, `Apply` operands,
//     primitive args.
//   - A borrowed use does not: `Proj`/`Unwrap` read a field (codegen dups the
//     field it loads, so the result is a fresh owned ref), a `Case`
//     scrutinee is only tag-tested, and a `Call` argument at a borrowed
//     parameter position stays owned by the caller.
//
// Borrow inference: a reference-counted parameter is borrowed if the function
// body only ever uses it in borrowed positions (passing it to a callee's
// borrowed param is a borrowed use). Solved as a greatest fixpoint, optimistic
// start. A function with a self tail call keeps all parameters owned so the
// call stays a tail call.
//
// Insertion: for `let x = v in rest` let `L = fv(rest)`. For every owned
// refcounted var `y` used in `v` with `n_own` owned and
// `n_b` borrowed uses:
//     - y in L: dup `y` once per owned use;
//     - y not in L, n_own >= 1: its last ref moves into the first owned use,
//       dup `n_own - 1` times;
//     - y not in L, n_own == 0 (borrowed only): drop `y` right after `v`.
// A fresh `x` that `rest` never uses is dropped immediately, at the start of every
// `Case` arm, every owned variable the arm doesn't mention is dropped.
// Invariant: `owned ⊆ fv(current expression)`.
//
// Reuse: when an owned variable `x` of a known ctor is dropped and a ctor
// of smaller or equal size is built later in the same straight-line block,
// `drop x` becomes `drop-reuse x` (if `x` is unique at runtime its memory
// is kept) and the construction becomes `ctor-reuse`. Together with the
// per-field dup/drop codegen already performs, this makes `map`-style code
// allocation-free on unique data.
//
// Fusion: before insertion, `Unwrap` + `Proj` become `Field`s read straight off the cell.
// after reuse analysis, the `Field`s of a cell that is dropped right after them become
// one `Take`, which moves the fields out without counting when the cell is unique.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use super::mir::*;
use crate::ir::Side;

pub fn run(prog: &mut MProgram) {
	forward(prog);
	super::pack::run(prog);
	infer_borrows(prog);
	let borrowed: HashMap<String, Vec<bool>> = prog
		.funcs
		.iter()
		.map(|f| (f.name.clone(), f.borrowed.clone()))
		.collect();
	let datas = prog.datas.clone();
	let facts = Facts { datas: &datas };
	for f in &mut prog.funcs {
		insert(f, &facts, &borrowed);
		reuse(f, &facts);
	}
	take(prog);
}

// Borrow inference

fn atom_is(a: &MAtom, p: &str) -> bool {
	matches!(a, MAtom::Var(n) if n == p)
}

fn has_self_tail_call(e: &MExpr, name: &str) -> bool {
	match e {
		MExpr::Let(x, _, v, rest) => {
			if let (MValue::Call { func, .. }, MExpr::Ret(MAtom::Var(r))) = (v, &**rest) {
				if func == name && r == x {
					return true;
				}
			}
			has_self_tail_call(rest, name)
		}
		MExpr::Case(_, arms) => arms.iter().any(|a| has_self_tail_call(&a.body, name)),
		MExpr::Ret(_) => false,
		MExpr::Dup(_, r) | MExpr::Drop(_, r) | MExpr::DropReuse(_, _, r) => {
			has_self_tail_call(r, name)
		}
		MExpr::Take { rest, .. } => has_self_tail_call(rest, name),
	}
}

fn allocates_ctor(e: &MExpr) -> bool {
	match e {
		MExpr::Let(_, _, v, rest) => {
			matches!(
				v,
				MValue::Ctor {
					payload: Some(_),
					..
				}
			) || matches!(v, MValue::Lambda { body, .. } | MValue::Delay { body, .. } if allocates_ctor(body))
				|| allocates_ctor(rest)
		}
		MExpr::Case(_, arms) => arms.iter().any(|a| allocates_ctor(&a.body)),
		MExpr::Ret(_) => false,
		MExpr::Dup(_, r) | MExpr::Drop(_, r) | MExpr::DropReuse(_, _, r) => allocates_ctor(r),
		MExpr::Take { rest, .. } => allocates_ctor(rest),
	}
}

fn case_on(e: &MExpr, p: &str) -> bool {
	match e {
		MExpr::Case(a, arms) => atom_is(a, p) || arms.iter().any(|m| case_on(&m.body, p)),
		MExpr::Let(_, _, _, rest) => case_on(rest, p),
		MExpr::Ret(_) => false,
		MExpr::Dup(_, r) | MExpr::Drop(_, r) | MExpr::DropReuse(_, _, r) => case_on(r, p),
		MExpr::Take { rest, .. } => case_on(rest, p),
	}
}

// check if `e` consumes var `p`
fn owned_use(e: &MExpr, p: &str, b: &HashMap<String, Vec<bool>>) -> bool {
	match e {
		MExpr::Ret(a) => atom_is(a, p),
		MExpr::Case(_, arms) => arms.iter().any(|a| owned_use(&a.body, p, b)),
		MExpr::Dup(_, r) | MExpr::Drop(_, r) | MExpr::DropReuse(_, _, r) => owned_use(r, p, b),
		MExpr::Take { from, rest, .. } => from == p || owned_use(rest, p, b),
		MExpr::Let(_, _, v, rest) => {
			let here = match v {
				MValue::Atom(a) => atom_is(a, p),
				MValue::Pair(a, c) | MValue::Apply(a, c) => atom_is(a, p) || atom_is(c, p),
				MValue::Ctor { payload, .. } => payload.as_ref().map_or(false, |a| atom_is(a, p)),
				MValue::CtorReuse { payload, .. } => atom_is(payload, p),
				MValue::Proj(..)
				| MValue::Field(..)
				| MValue::Unwrap(..)
				| MValue::Str(_)
				| MValue::Fail(_) => false,
				MValue::Lambda { free, .. } | MValue::Delay { free, .. } => {
					free.iter().any(|(n, _)| n == p)
				}
				MValue::Force(a) | MValue::Wrap(a) => atom_is(a, p),
				MValue::MakePap { args, .. } | MValue::Prim(_, args) => {
					args.iter().any(|a| atom_is(a, p))
				}
				MValue::Call { func, args } => args.iter().enumerate().any(|(i, a)| {
					atom_is(a, p) && !b.get(func).and_then(|v| v.get(i)).copied().unwrap_or(false)
				}),
			};
			here || owned_use(rest, p, b)
		}
	}
}

fn infer_borrows(prog: &mut MProgram) {
	let datas = prog.datas.clone();
	let facts = Facts { datas: &datas };
	let mut b: HashMap<String, Vec<bool>> = HashMap::new();
	for f in &prog.funcs {
		let tail = has_self_tail_call(&f.body, &f.name);
		let allocates = allocates_ctor(&f.body);
		b.insert(
			f.name.clone(),
			f.params
				.iter()
				.map(|(p, t)| {
					// Borrowing a parameter that is taken apart by a `case` in a function that
					// also builds constructors would forbid reusing its memory (Perceus'
					// borrowing/reuse tension): keep those owned.
					!tail && facts.needs_rc(t) && !(allocates && case_on(&f.body, p))
				})
				.collect(),
		);
	}
	loop {
		let mut changed = false;
		for f in &prog.funcs {
			for (i, (p, _)) in f.params.iter().enumerate() {
				if b[&f.name][i] && owned_use(&f.body, p, &b) {
					b.get_mut(&f.name).unwrap()[i] = false;
					changed = true;
				}
			}
		}
		if !changed {
			break;
		}
	}
	for f in &mut prog.funcs {
		f.borrowed = b[&f.name].clone();
	}
}

// ============================================================================
// Dup / drop insertion
// ============================================================================

struct P<'a> {
	facts: &'a Facts<'a>,
	borrowed: &'a HashMap<String, Vec<bool>>,
	tys: BTreeMap<Name, MTy>,
}

fn insert(f: &mut MFunc, facts: &Facts, borrowed: &HashMap<String, Vec<bool>>) {
	let mut p = P {
		facts,
		borrowed,
		tys: BTreeMap::new(),
	};
	let mut owned = BTreeSet::new();
	for (i, (n, t)) in f.params.iter().enumerate() {
		p.tys.insert(n.clone(), t.clone());
		if facts.needs_rc(t) && !f.borrowed[i] {
			owned.insert(n.clone());
		}
	}
	let body = std::mem::replace(&mut f.body, MExpr::Ret(MAtom::Unit));
	f.body = p.enter(owned, body);
}

fn drops(names: Vec<Name>, mut e: MExpr) -> MExpr {
	for n in names.into_iter().rev() {
		e = MExpr::Drop(n, Box::new(e));
	}
	e
}

fn dups(names: Vec<Name>, mut e: MExpr) -> MExpr {
	for n in names.into_iter().rev() {
		e = MExpr::Dup(n, Box::new(e));
	}
	e
}

impl<'a> P<'a> {
	fn rc(&self, n: &str) -> bool {
		self.tys.get(n).map_or(false, |t| self.facts.needs_rc(t))
	}

	fn enter(&mut self, owned: BTreeSet<Name>, body: MExpr) -> MExpr {
		let live = fv_expr(&body);
		let (keep, dead): (Vec<Name>, Vec<Name>) =
			owned.into_iter().partition(|n| live.contains(n));
		let b = self.go(keep.into_iter().collect(), body);
		drops(dead, b)
	}

	/// (variable, is_owned_use) for every reference-counted variable used by `v`.
	fn uses(&self, v: &MValue) -> Vec<(Name, bool)> {
		let mut out = Vec::new();
		let own = |a: &MAtom, o: bool, out: &mut Vec<(Name, bool)>| {
			if let MAtom::Var(n) = a {
				out.push((n.clone(), o));
			}
		};
		match v {
			MValue::Atom(a) => own(a, true, &mut out),
			MValue::Str(_) | MValue::Fail(_) => {}
			MValue::Pair(a, b) | MValue::Apply(a, b) => {
				own(a, true, &mut out);
				own(b, true, &mut out);
			}
			MValue::Ctor { payload, .. } => {
				if let Some(a) = payload {
					own(a, true, &mut out);
				}
			}
			MValue::CtorReuse { payload, .. } => own(payload, true, &mut out),
			MValue::Proj(a, _) | MValue::Field(a, _, _) | MValue::Unwrap(a, _) => {
				own(a, false, &mut out)
			}
			MValue::Lambda { free, .. } | MValue::Delay { free, .. } => {
				for (n, _) in free {
					out.push((n.clone(), true));
				}
			}
			MValue::Force(a) | MValue::Wrap(a) => own(a, true, &mut out),
			MValue::Call { func, args } => {
				let bw = self.borrowed.get(func);
				for (i, a) in args.iter().enumerate() {
					let is_b = bw.and_then(|v| v.get(i)).copied().unwrap_or(false);
					own(a, !is_b, &mut out);
				}
			}
			MValue::MakePap { args, .. } | MValue::Prim(_, args) => {
				for a in args {
					own(a, true, &mut out);
				}
			}
		}
		out.into_iter().filter(|(n, _)| self.rc(n)).collect()
	}

	fn proc_value(&mut self, v: MValue) -> MValue {
		match v {
			MValue::Lambda { param, body, free } => {
				self.tys.insert(param.0.clone(), param.1.clone());
				let mut owned = BTreeSet::new();
				for (n, t) in &free {
					self.tys.insert(n.clone(), t.clone());
					if self.facts.needs_rc(t) {
						owned.insert(n.clone());
					}
				}
				if self.facts.needs_rc(&param.1) {
					owned.insert(param.0.clone());
				}
				let body = self.enter(owned, *body);
				MValue::Lambda {
					param,
					body: Box::new(body),
					free,
				}
			}
			MValue::Delay { body, free } => {
				let mut owned = BTreeSet::new();
				for (n, t) in &free {
					self.tys.insert(n.clone(), t.clone());
					if self.facts.needs_rc(t) {
						owned.insert(n.clone());
					}
				}
				let body = self.enter(owned, *body);
				MValue::Delay {
					body: Box::new(body),
					free,
				}
			}
			other => other,
		}
	}

	fn go(&mut self, mut owned: BTreeSet<Name>, e: MExpr) -> MExpr {
		struct Step {
			x: Name,
			ty: MTy,
			v: MValue,
			pre_dups: Vec<Name>,
			post_drops: Vec<Name>,
			drop_x: bool,
		}

		// unwind the straight-line block of lets
		let mut spine: Vec<(Name, MTy, MValue)> = Vec::new();
		let mut cur = e;
		while let MExpr::Let(x, ty, v, rest) = cur {
			spine.push((x, ty, v));
			cur = *rest;
		}
		let leaf = cur;
		let n = spine.len();

		// after[i] = free variables of everything that follows binding i
		let mut after: Vec<BTreeSet<Name>> = vec![BTreeSet::new(); n];
		if n > 0 {
			let mut live = fv_expr(&leaf);
			for i in (0..n).rev() {
				after[i] = live.clone();
				if i > 0 {
					let (x, _, v) = &spine[i];
					live.remove(x);
					live.extend(fv_value(v));
				}
			}
		}

		// forward passm same as old per-`Let` case
		let mut steps: Vec<Step> = Vec::with_capacity(n);
		for (i, (x, ty, v)) in spine.into_iter().enumerate() {
			self.tys.insert(x.clone(), ty.clone());
			let live_rest = &after[i];
			let x_rc = self.facts.needs_rc(&ty);

			let mut counts: BTreeMap<Name, (usize, usize)> = BTreeMap::new();
			for (name, o) in self.uses(&v) {
				if !owned.contains(&name) {
					continue; // a borrowed param, never duped or dropped here
				}
				let c = counts.entry(name).or_insert((0, 0));
				if o {
					c.0 += 1;
				} else {
					c.1 += 1;
				}
			}
			let mut pre_dups = Vec::new();
			let mut post_drops = Vec::new();
			for (y, (n_own, n_b)) in &counts {
				if live_rest.contains(y) {
					for _ in 0..*n_own {
						pre_dups.push(y.clone());
					}
				} else if *n_b > 0 {
					// a borrowed use needs to be valid for the whole operation,
					// so every owned use needs its own ref and the caller's is
					// released after (otherwise a callee could free what it's
					// borrowing)
					for _ in 0..*n_own {
						pre_dups.push(y.clone());
					}
					post_drops.push(y.clone());
				} else {
					for _ in 1..*n_own {
						pre_dups.push(y.clone());
					}
				}
			}

			owned.retain(|y| live_rest.contains(y));
			if x_rc && live_rest.contains(&x) {
				owned.insert(x.clone());
			}
			let drop_x = x_rc && !live_rest.contains(&x);
			let v = self.proc_value(v);
			steps.push(Step {
				x,
				ty,
				v,
				pre_dups,
				post_drops,
				drop_x,
			});
		}

		let mut tail = self.go_leaf(owned, leaf);

		// rebuild back to front
		for s in steps.into_iter().rev() {
			if s.drop_x {
				tail = MExpr::Drop(s.x.clone(), Box::new(tail));
			}
			let inner = drops(s.post_drops, tail);
			tail = dups(s.pre_dups, MExpr::Let(s.x, s.ty, s.v, Box::new(inner)));
		}
		tail
	}

	// what ends a let-spine: everything except `Let`
	fn go_leaf(&mut self, owned: BTreeSet<Name>, e: MExpr) -> MExpr {
		match e {
			MExpr::Let(..) => unreachable!("`go` unwinds every leading Let"),
			MExpr::Ret(a) => MExpr::Ret(a),
			MExpr::Dup(n, r) => MExpr::Dup(n, Box::new(self.go(owned, *r))),
			MExpr::Drop(n, r) => MExpr::Drop(n, Box::new(self.go(owned, *r))),
			MExpr::DropReuse(t, x, r) => MExpr::DropReuse(t, x, Box::new(self.go(owned, *r))),
			MExpr::Take { .. } => unreachable!("fusion runs after reference counting insertion"),
			MExpr::Case(a, arms) => {
				let mut out = Vec::new();
				for arm in arms {
					let live = fv_expr(&arm.body);
					let mut keep = BTreeSet::new();
					let mut dead = Vec::new();
					for n in &owned {
						if live.contains(n) {
							keep.insert(n.clone());
						} else {
							dead.push(n.clone());
						}
					}
					let body = self.go(keep, arm.body);
					out.push(MArm {
						pat: arm.pat,
						body: drops(dead, body),
					});
				}
				MExpr::Case(a, out)
			}
		}
	}
}

// ============================================================================
// Reuse analysis
// ============================================================================

struct R<'a> {
	facts: &'a Facts<'a>,
	tys: HashMap<Name, MTy>,
	counter: usize,
}

fn collect_tys(e: &MExpr, out: &mut HashMap<Name, MTy>) {
	match e {
		MExpr::Let(x, t, v, rest) => {
			out.insert(x.clone(), t.clone());
			match v {
				MValue::Lambda { param, body, free } => {
					out.insert(param.0.clone(), param.1.clone());
					for (n, t) in free {
						out.insert(n.clone(), t.clone());
					}
					collect_tys(body, out);
				}
				MValue::Delay { body, free } => {
					for (n, t) in free {
						out.insert(n.clone(), t.clone());
					}
					collect_tys(body, out);
				}
				_ => {}
			}
			collect_tys(rest, out);
		}
		MExpr::Case(_, arms) => {
			for a in arms {
				collect_tys(&a.body, out);
			}
		}
		MExpr::Ret(_) => {}
		MExpr::Dup(_, r) | MExpr::Drop(_, r) | MExpr::DropReuse(_, _, r) => collect_tys(r, out),
		MExpr::Take { binds, rest, .. } => {
			for (n, t, _) in binds {
				out.insert(n.clone(), t.clone());
			}
			collect_tys(rest, out);
		}
	}
}

fn reuse(f: &mut MFunc, facts: &Facts) {
	let mut r = R {
		facts,
		tys: HashMap::new(),
		counter: 0,
	};
	for (n, t) in &f.params {
		r.tys.insert(n.clone(), t.clone());
	}
	collect_tys(&f.body, &mut r.tys);
	let body = std::mem::replace(&mut f.body, MExpr::Ret(MAtom::Unit));
	f.body = r.walk(body, &HashMap::new(), &f.name);
}

impl<'a> R<'a> {
	/// Size of the heap object holding constructor `ctor` of data type `d`.
	fn ctor_size(&self, d: DataId, ctor: &str) -> Option<u64> {
		let def = &self.facts.datas[d];
		let ci = def.tag_of(ctor)?;
		def.ctors[ci].payload.as_ref()?;
		Some(self.facts.obj_size(d, ci))
	}

	/// Replace the first constructor allocation in the straight-line block `e`
	/// whose object fits in `size` bytes with a reuse of `token`.
	fn try_reuse(&self, e: MExpr, size: u64, token: &str) -> Result<MExpr, MExpr> {
		match e {
			MExpr::Let(
				y,
				t,
				MValue::Ctor {
					ctor,
					payload: Some(p),
				},
				rest,
			) => {
				if let MTy::Data(d) = &t {
					if let Some(s) = self.ctor_size(*d, &ctor) {
						if s <= size {
							return Ok(MExpr::Let(
								y,
								t,
								MValue::CtorReuse {
									token: token.to_string(),
									ctor,
									payload: p,
								},
								rest,
							));
						}
					}
				}
				match self.try_reuse(*rest, size, token) {
					Ok(r) => Ok(MExpr::Let(
						y,
						t,
						MValue::Ctor {
							ctor,
							payload: Some(p),
						},
						Box::new(r),
					)),
					Err(r) => Err(MExpr::Let(
						y,
						t,
						MValue::Ctor {
							ctor,
							payload: Some(p),
						},
						Box::new(r),
					)),
				}
			}
			MExpr::Let(y, t, v, rest) => match self.try_reuse(*rest, size, token) {
				Ok(r) => Ok(MExpr::Let(y, t, v, Box::new(r))),
				Err(r) => Err(MExpr::Let(y, t, v, Box::new(r))),
			},
			MExpr::Dup(n, rest) => match self.try_reuse(*rest, size, token) {
				Ok(r) => Ok(MExpr::Dup(n, Box::new(r))),
				Err(r) => Err(MExpr::Dup(n, Box::new(r))),
			},
			MExpr::Drop(n, rest) => match self.try_reuse(*rest, size, token) {
				Ok(r) => Ok(MExpr::Drop(n, Box::new(r))),
				Err(r) => Err(MExpr::Drop(n, Box::new(r))),
			},
			other => Err(other), // Case / Ret / DropReuse: stop at the end of the block
		}
	}

	fn walk(&mut self, e: MExpr, known: &HashMap<Name, (DataId, String)>, fname: &str) -> MExpr {
		match e {
			MExpr::Let(x, t, v, rest) => {
				let v = match v {
					MValue::Lambda { param, body, free } => {
						let b = self.walk(*body, &HashMap::new(), fname);
						MValue::Lambda {
							param,
							body: Box::new(b),
							free,
						}
					}
					MValue::Delay { body, free } => {
						let b = self.walk(*body, &HashMap::new(), fname);
						MValue::Delay {
							body: Box::new(b),
							free,
						}
					}
					o => o,
				};
				MExpr::Let(x, t, v, Box::new(self.walk(*rest, known, fname)))
			}
			MExpr::Dup(n, r) => MExpr::Dup(n, Box::new(self.walk(*r, known, fname))),
			MExpr::DropReuse(t, x, r) => {
				MExpr::DropReuse(t, x, Box::new(self.walk(*r, known, fname)))
			}
			MExpr::Take { .. } => unreachable!("fusion runs after reuse analysis"),
			MExpr::Ret(a) => MExpr::Ret(a),
			MExpr::Case(a, arms) => {
				let mut out = Vec::new();
				for arm in arms {
					let mut k2 = known.clone();
					if let (MPat::Ctor(c), MAtom::Var(s)) = (&arm.pat, &a) {
						if let Some(MTy::Data(d)) = self.tys.get(s) {
							k2.insert(s.clone(), (*d, c.clone()));
						}
					}
					out.push(MArm {
						pat: arm.pat,
						body: self.walk(arm.body, &k2, fname),
					});
				}
				MExpr::Case(a, out)
			}
			MExpr::Drop(x, rest) => {
				let size = known.get(&x).and_then(|(d, c)| self.ctor_size(*d, c));
				let rest = self.walk(*rest, known, fname);
				if let Some(size) = size {
					self.counter += 1;
					let tok = format!("%tok{}", self.counter);
					return match self.try_reuse(rest, size, &tok) {
						Ok(r) => {
							self.tys.insert(tok.clone(), MTy::Token);
							MExpr::DropReuse(tok, x, Box::new(r))
						}
						Err(r) => MExpr::Drop(x, Box::new(r)),
					};
				}
				MExpr::Drop(x, Box::new(rest))
			}
		}
	}
}

// dup/drop fusion

pub fn forward(prog: &mut MProgram) {
	let datas = prog.datas.clone();
	let facts = Facts { datas: &datas };
	for f in &mut prog.funcs {
		let mut tys: HashMap<Name, MTy> = f.params.iter().cloned().collect();
		let body = std::mem::replace(&mut f.body, MExpr::Ret(MAtom::Unit));
		f.body = fwd(body, &mut tys, &facts);
	}
}

fn payload_leaves(facts: &Facts, ty: Option<&MTy>, ctor: &str) -> usize {
	match ty.map(|t| t.inner()) {
		Some(MTy::Data(d)) => {
			let def = &facts.datas[*d];
			def.tag_of(ctor)
				.and_then(|i| def.ctors[i].payload.as_ref())
				.map_or(0, |p| facts.leaves(p).len())
		}
		_ => 0,
	}
}

fn fwd(e: MExpr, tys: &mut HashMap<Name, MTy>, facts: &Facts) -> MExpr {
	match e {
		MExpr::Let(x, ty, v, rest) => {
			tys.insert(x.clone(), ty.clone());
			match v {
				MValue::Unwrap(MAtom::Var(src), ctor) => {
					if matches!(ty, MTy::Prod(..)) {
						if only_proj(&rest, &x) {
							let st = tys.get(&src).cloned();
							let r = subst(*rest, &x, &src, &ctor, st.as_ref());
							return fwd(r, tys, facts);
						}
					} else if payload_leaves(facts, tys.get(&src), &ctor) == 1 {
						let r = fwd(*rest, tys, facts);
						return MExpr::Let(
							x,
							ty,
							MValue::Field(MAtom::Var(src), ctor, 0),
							Box::new(r),
						);
					}
					let r = fwd(*rest, tys, facts);
					MExpr::Let(x, ty, MValue::Unwrap(MAtom::Var(src), ctor), Box::new(r))
				}
				MValue::Lambda { param, body, free } => {
					let mut inner = tys.clone();
					inner.insert(param.0.clone(), param.1.clone());
					for (n, t) in &free {
						inner.insert(n.clone(), t.clone());
					}
					let b = fwd(*body, &mut inner, facts);
					let r = fwd(*rest, tys, facts);
					MExpr::Let(
						x,
						ty,
						MValue::Lambda {
							param,
							body: Box::new(b),
							free,
						},
						Box::new(r),
					)
				}
				MValue::Delay { body, free } => {
					let mut inner = tys.clone();
					for (n, t) in &free {
						inner.insert(n.clone(), t.clone());
					}
					let b = fwd(*body, &mut inner, facts);
					let r = fwd(*rest, tys, facts);
					MExpr::Let(
						x,
						ty,
						MValue::Delay {
							body: Box::new(b),
							free,
						},
						Box::new(r),
					)
				}
				other => {
					let r = fwd(*rest, tys, facts);
					MExpr::Let(x, ty, other, Box::new(r))
				}
			}
		}
		MExpr::Case(a, arms) => MExpr::Case(
			a,
			arms.into_iter()
				.map(|m| {
					let mut t2 = tys.clone();
					MArm {
						pat: m.pat,
						body: fwd(m.body, &mut t2, facts),
					}
				})
				.collect(),
		),
		other => other,
	}
}

// find if `p` is only used as the operand of `Proj` (also in closures + thunks)
fn only_proj(e: &MExpr, p: &str) -> bool {
	match e {
		MExpr::Let(_, _, v, rest) => {
			let ok = match v {
				MValue::Proj(MAtom::Var(a), _) if a == p => true,
				MValue::Lambda { body, .. } | MValue::Delay { body, .. } => only_proj(body, p),
				other => !fv_value(other).contains(p),
			};
			ok && only_proj(rest, p)
		}
		MExpr::Case(a, arms) => {
			!matches!(a, MAtom::Var(n) if n == p) && arms.iter().all(|m| only_proj(&m.body, p))
		}
		MExpr::Ret(a) => !matches!(a, MAtom::Var(n) if n == p),
		MExpr::Dup(n, r) | MExpr::Drop(n, r) => n != p && only_proj(r, p),
		MExpr::DropReuse(_, n, r) => n != p && only_proj(r, p),
		MExpr::Take { from, rest, .. } => from != p && only_proj(rest, p),
	}
}

// replace `Proj(p, side)` by a `Field` of `src`, and `p` by `src` in capture lists
fn subst(e: MExpr, p: &str, src: &str, ctor: &str, src_ty: Option<&MTy>) -> MExpr {
	let sub_free = |free: Vec<(Name, MTy)>| -> Vec<(Name, MTy)> {
		let mut out: Vec<(Name, MTy)> = Vec::new();
		for (n, t) in free {
			let (n, t) = if n == p {
				(
					src.to_string(),
					src_ty.cloned().expect("type of the unwrapped cell"),
				)
			} else {
				(n, t)
			};
			if !out.iter().any(|(m, _)| *m == n) {
				out.push((n, t));
			}
		}
		out
	};
	match e {
		MExpr::Let(y, t, v, rest) => {
			let v = match v {
				MValue::Proj(MAtom::Var(a), side) if a == p => MValue::Field(
					MAtom::Var(src.to_string()),
					ctor.to_string(),
					if matches!(side, Side::Fst) { 0 } else { 1 },
				),
				MValue::Lambda { param, body, free } => MValue::Lambda {
					param,
					body: Box::new(subst(*body, p, src, ctor, src_ty)),
					free: sub_free(free),
				},
				MValue::Delay { body, free } => MValue::Delay {
					body: Box::new(subst(*body, p, src, ctor, src_ty)),
					free: sub_free(free),
				},
				other => other,
			};
			MExpr::Let(y, t, v, Box::new(subst(*rest, p, src, ctor, src_ty)))
		}
		MExpr::Case(a, arms) => MExpr::Case(
			a,
			arms.into_iter()
				.map(|m| MArm {
					pat: m.pat,
					body: subst(m.body, p, src, ctor, src_ty),
				})
				.collect(),
		),
		other => other,
	}
}

pub fn take(prog: &mut MProgram) {
	for f in &mut prog.funcs {
		let body = std::mem::replace(&mut f.body, MExpr::Ret(MAtom::Unit));
		f.body = tk(body);
	}
}

enum Item {
	Let(Name, MTy, MValue),
	Dup(Name),
	Drop(Name),
	DropReuse(Name, Name),
}

fn rebuild(items: Vec<Item>, tail: MExpr) -> MExpr {
	let mut e = tail;
	for it in items.into_iter().rev() {
		e = match it {
			Item::Let(x, t, v) => MExpr::Let(x, t, tk_value(v), Box::new(e)),
			Item::Dup(n) => MExpr::Dup(n, Box::new(e)),
			Item::Drop(n) => MExpr::Drop(n, Box::new(e)),
			Item::DropReuse(t, n) => MExpr::DropReuse(t, n, Box::new(e)),
		};
	}
	e
}

fn tk_value(v: MValue) -> MValue {
	match v {
		MValue::Lambda { param, body, free } => MValue::Lambda {
			param,
			body: Box::new(tk(*body)),
			free,
		},
		MValue::Delay { body, free } => MValue::Delay {
			body: Box::new(tk(*body)),
			free,
		},
		o => o,
	}
}

// find if the `Field`s of `x` that follow can be fused with the `drop x` that ends the block
fn fusable(rest: &MExpr, x: &str, c: &str, first: usize) -> bool {
	let mut seen: BTreeSet<usize> = BTreeSet::new();
	seen.insert(first);
	let mut cur = rest;
	loop {
		match cur {
			MExpr::Drop(n, _) if n == x => return true,
			MExpr::DropReuse(_, n, _) if n == x => return true,
			MExpr::Let(_, _, MValue::Field(MAtom::Var(x2), c2, j), r) if x2 == x => {
				if c2 != c || !seen.insert(*j) {
					return false;
				}
				cur = r;
			}
			MExpr::Let(_, _, v, r) => {
				if fv_value(v).contains(x) {
					return false;
				}
				cur = r;
			}
			MExpr::Dup(n, r) => {
				if n == x {
					return false;
				}
				cur = r;
			}
			MExpr::Drop(_, r) | MExpr::DropReuse(_, _, r) => cur = r,
			MExpr::Case(..) | MExpr::Ret(_) | MExpr::Take { .. } => return false,
		}
	}
}

fn tk(e: MExpr) -> MExpr {
	match e {
		MExpr::Let(y, t, MValue::Field(MAtom::Var(x), c, i), rest) => {
			if !fusable(&rest, &x, &c, i) {
				return MExpr::Let(
					y,
					t,
					MValue::Field(MAtom::Var(x), c, i),
					Box::new(tk(*rest)),
				);
			}
			let mut binds: Vec<(Name, MTy, usize)> = vec![(y, t, i)];
			let mut items: Vec<Item> = Vec::new();
			let mut cur = *rest;
			let (token, tail) = loop {
				match cur {
					MExpr::Drop(n, tail) if n == x => break (None, *tail),
					MExpr::DropReuse(tok, n, tail) if n == x => break (Some(tok), *tail),
					MExpr::Let(y2, t2, MValue::Field(MAtom::Var(x2), _, j), r2) if x2 == x => {
						binds.push((y2, t2, j));
						cur = *r2;
					}
					MExpr::Let(y2, t2, v2, r2) => {
						items.push(Item::Let(y2, t2, v2));
						cur = *r2;
					}
					MExpr::Dup(n, r2) => {
						items.push(Item::Dup(n));
						cur = *r2;
					}
					MExpr::Drop(n, r2) => {
						items.push(Item::Drop(n));
						cur = *r2;
					}
					MExpr::DropReuse(tok, n, r2) => {
						items.push(Item::DropReuse(tok, n));
						cur = *r2;
					}
					_ => unreachable!("`fusable` checked the block"),
				}
			};
			let tail = tk(tail);
			MExpr::Take {
				binds,
				from: x,
				ctor: c,
				token,
				rest: Box::new(rebuild(items, tail)),
			}
		}
		MExpr::Let(y, t, v, rest) => MExpr::Let(y, t, tk_value(v), Box::new(tk(*rest))),
		MExpr::Case(a, arms) => MExpr::Case(
			a,
			arms.into_iter()
				.map(|m| MArm {
					pat: m.pat,
					body: tk(m.body),
				})
				.collect(),
		),
		MExpr::Dup(n, r) => MExpr::Dup(n, Box::new(tk(*r))),
		MExpr::Drop(n, r) => MExpr::Drop(n, Box::new(tk(*r))),
		MExpr::DropReuse(t, n, r) => MExpr::DropReuse(t, n, Box::new(tk(*r))),
		other => other,
	}
}
