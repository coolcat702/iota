// tight packing of ctor fields
//
// In general, every ctor field is a susp word: 8 bytes that is either an evaled imm or a ptr to a
// thunk. A `Cons` of a `List Char` is a 4-byte count, 4 bytes of padding, and two words. When EVERY
// construction of a ctor stores an evaled `Int`, `Char`, or enum, the field can never hold a thunk
// and the scalar is stored bare. The cell becomes `{ i32 rc, i32 char, ptr tail }`, 16 bytes, and
// reading the field doesn't need a thunk check or refcount
//
// NOT strictness annotation, a field is only packed when the program never stores anything lazy in
// it so nothing changes meaning. Analysis is over whole program: start w/ assumption that every
// scalar field is packable and drop a field as soon as some construction site stores anything that
// could be a thunk. A val read from a field that is itself assumed pack counts as evaled, so `map`
// -style code that only shuffles elements keeps them packed.
//
// A site stores an evaled val when the component is bound by `wrap` or is read from a packed field.
// Anything else is assumed to be lazy.

use std::collections::{HashMap, HashSet};

use super::mir::*;

type Key = (DataId, usize, usize);

#[derive(Clone)]
enum Def {
	Wrap,
	Pair(MAtom, MAtom),
	Field(DataId, usize, usize),
	Other,
}

pub fn run(prog: &mut MProgram) {
	let datas = prog.datas.clone();
	let facts = Facts { datas: &datas };
	let mut packed: HashSet<Key> = HashSet::new();
	for (d, def) in datas.iter().enumerate() {
		for (ci, c) in def.ctors.iter().enumerate() {
			if let Some(p) = &c.payload {
				for (i, l) in facts.leaves(p).iter().enumerate() {
					if facts.packable(l) {
						packed.insert((d, ci, i));
					}
				}
			}
		}
	}
	loop {
		let mut next = packed.clone();
		for f in &prog.funcs {
			let mut st = St {
				defs: HashMap::new(),
				tys: HashMap::new(),
			};
			for (n, t) in &f.params {
				st.defs.insert(n.clone(), Def::Other);
				st.tys.insert(n.clone(), t.clone());
			}
			walk(&f.body, &mut st, &packed, &mut next, &datas);
		}
		if next.len() == packed.len() {
			break;
		}
		packed = next;
	}
	for (d, def) in prog.datas.iter_mut().enumerate() {
		for (ci, c) in def.ctors.iter_mut().enumerate() {
			if let Some(p) = &c.payload {
				let n = facts.leaves(p).len();
				c.packed = (0..n).map(|i| packed.contains(&(d, ci, i))).collect();
			}
		}
	}
}

#[derive(Clone)]
struct St {
	defs: HashMap<Name, Def>,
	tys: HashMap<Name, MTy>,
}

fn evaluated(a: &MAtom, st: &St, packed: &HashSet<Key>) -> bool {
	match a {
		MAtom::Var(n) => match st.defs.get(n) {
			Some(Def::Wrap) => true,
			Some(Def::Field(d, ci, i)) => packed.contains(&(*d, *ci, *i)),
			_ => false,
		},
		_ => true,
	}
}

fn walk(e: &MExpr, st: &mut St, packed: &HashSet<Key>, next: &mut HashSet<Key>, datas: &[DataDef]) {
	match e {
		MExpr::Let(x, ty, v, rest) => {
			let site = match v {
				MValue::Ctor {
					ctor,
					payload: Some(p),
				} => Some((ctor, p)),
				MValue::CtorReuse { ctor, payload, .. } => Some((ctor, payload)),
				_ => None,
			};
			if let (Some((ctor, p)), MTy::Data(d)) = (site, ty) {
				let def = &datas[*d];
				if let Some(ci) = def.tag_of(ctor) {
					if let Some(MTy::Prod(..)) = def.ctors[ci].payload {
						let comps = match p {
							MAtom::Var(pn) => match st.defs.get(pn) {
								Some(Def::Pair(a, b)) => Some((a.clone(), b.clone())),
								_ => None,
							},
							_ => None,
						};
						match comps {
							Some((a, b)) => {
								for (i, atom) in [a, b].iter().enumerate() {
									if !evaluated(atom, st, packed) {
										next.remove(&(*d, ci, i));
									}
								}
							}
							None => {
								next.remove(&(*d, ci, 0));
								next.remove(&(*d, ci, 1));
							}
						}
					} else if !evaluated(p, st, packed) {
						next.remove(&(*d, ci, 0));
					}
				}
			}
			let def = match v {
				MValue::Wrap(_) => Def::Wrap,
				MValue::Pair(a, b) => Def::Pair(a.clone(), b.clone()),
				MValue::Field(MAtom::Var(src), ctor, i) => match st.tys.get(src).map(|t| t.inner())
				{
					Some(MTy::Data(d)) => match datas[*d].tag_of(ctor) {
						Some(ci) => Def::Field(*d, ci, *i),
						None => Def::Other,
					},
					_ => Def::Other,
				},
				_ => Def::Other,
			};
			st.defs.insert(x.clone(), def);
			st.tys.insert(x.clone(), ty.clone());
			match v {
				MValue::Lambda { param, body, free } => {
					let mut inner = st.clone();
					inner.defs.insert(param.0.clone(), Def::Other);
					inner.tys.insert(param.0.clone(), param.1.clone());
					for (n, t) in free {
						inner.defs.entry(n.clone()).or_insert(Def::Other);
						inner.tys.entry(n.clone()).or_insert_with(|| t.clone());
					}
					walk(body, &mut inner, packed, next, datas);
				}
				MValue::Delay { body, free } => {
					let mut inner = st.clone();
					for (n, t) in free {
						inner.defs.entry(n.clone()).or_insert(Def::Other);
						inner.tys.entry(n.clone()).or_insert_with(|| t.clone());
					}
					walk(body, &mut inner, packed, next, datas);
				}
				_ => {}
			}
			walk(rest, st, packed, next, datas);
		}
		MExpr::Case(_, arms) => {
			for m in arms {
				let mut s2 = st.clone();
				walk(&m.body, &mut s2, packed, next, datas);
			}
		}
		MExpr::Ret(_) => {}
		MExpr::Dup(_, r) | MExpr::Drop(_, r) | MExpr::DropReuse(_, _, r) => {
			walk(r, st, packed, next, datas)
		}
		MExpr::Take { rest, .. } => walk(rest, st, packed, next, datas),
	}
}
