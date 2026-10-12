// monomorphic, typed, mid-level IR
// it has two dialects:
// - core: produced by `lower.rs`. types are just iota types, everything is lazy
// - final: produced by `lazy.rs`. susps are explicit
//
// representation in `codegen.rs`

use std::collections::BTreeSet;

use crate::ir::Side;
use crate::lang::Intrinsic;
use crate::parser::Span;

pub type Name = String;
pub type DataId = usize;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum MTy {
	Unit,
	Int,
	Float,
	Char,
	Fn(Box<MTy>, Box<MTy>),
	Prod(Box<MTy>, Box<MTy>),
	Data(DataId),
	Token,          // reusable allocation
	Susp(Box<MTy>), // only in final
}

impl MTy {
	pub fn susp(t: MTy) -> MTy {
		MTy::Susp(Box::new(t))
	}
	pub fn inner(&self) -> &MTy {
		match self {
			MTy::Susp(t) => t.inner(),
			t => t,
		}
	}
	pub fn is_susp(&self) -> bool {
		matches!(self, MTy::Susp(_))
	}
}

#[derive(Clone, Debug)]
pub struct CtorDef {
	pub name: String, // bare ctor name
	pub payload: Option<MTy>,
	pub packed: Vec<bool>, // bare evaled scalar instead of susp
}

#[derive(Clone, Debug)]
pub struct DataDef {
	pub name: String,
	pub ctors: Vec<CtorDef>, // runtime tag of a ctor is its index here
}

// types with at most this many ctors keep tag in low bits, wider ones store it in obj header
pub const MAX_TAGGED_CTORS: usize = 7;

impl DataDef {
	// All constructors nullary, represented as a small int
	pub fn is_enum(&self) -> bool {
		self.ctors.iter().all(|c| c.payload.is_none())
	}
	pub fn is_wide(&self) -> bool {
		self.ctors.len() > MAX_TAGGED_CTORS
	}
	pub fn tag_of(&self, name: &str) -> Option<usize> {
		self.ctors.iter().position(|c| c.name == name)
	}
}

#[derive(Clone, Debug)]
pub enum MAtom {
	Var(Name),
	Unit,
	Int(i32),
	Float(f64),
	Char(char),
}

#[derive(Clone, Debug)]
pub enum MValue {
	Atom(MAtom),
	Str(String),
	Fail(String), // abort program when evaled
	Pair(MAtom, MAtom),
	Ctor {
		ctor: String,
		payload: Option<MAtom>,
	},
	CtorReuse {
		// reuse `token`'s allocation when non-null
		token: Name,
		ctor: String,
		payload: MAtom,
	},
	Proj(MAtom, Side),
	Field(MAtom, String, usize),
	Unwrap(MAtom, String),
	Lambda {
		param: (Name, MTy),
		body: Box<MExpr>,
		free: Vec<(Name, MTy)>,
	},
	Delay {
		// thunk (final)
		body: Box<MExpr>,
		free: Vec<(Name, MTy)>,
	},
	Call {
		func: String,
		args: Vec<MAtom>,
	},
	MakePap {
		func: String,
		args: Vec<MAtom>,
	},
	Apply(MAtom, MAtom),
	Prim(Intrinsic, Vec<MAtom>),
	Force(MAtom), // force a susp (final)
	Wrap(MAtom),  // susp (final)
}

#[derive(Clone, Debug)]
pub enum MPat {
	Wild,
	Int(i32),
	Char(char),
	Float(f64),
	Ctor(String),
}

#[derive(Clone, Debug)]
pub struct MArm {
	pub pat: MPat,
	pub body: MExpr,
}

#[derive(Clone, Debug)]
pub enum MExpr {
	Let(Name, MTy, MValue, Box<MExpr>),
	Case(MAtom, Vec<MArm>),
	Ret(MAtom),
	Dup(Name, Box<MExpr>),
	Drop(Name, Box<MExpr>),
	DropReuse(Name, Name, Box<MExpr>),
	Take {
		binds: Vec<(Name, MTy, usize)>,
		from: Name,
		ctor: String,
		token: Option<Name>,
		rest: Box<MExpr>,
	},
}

pub struct MFunc {
	pub name: String,
	pub params: Vec<(Name, MTy)>,
	pub borrowed: Vec<bool>, // callers keep ownership
	pub ret: MTy,
	pub caf: bool, // constant applicative form -- cached because no possible side effects
	pub body: MExpr,
	pub span: Option<Span>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EntryKind {
	Value,
	Action,
}

#[derive(Clone, Copy, Debug)]
pub struct ListInfo {
	pub data: DataId,
	pub nil: usize,
	pub cons: usize,
}

#[derive(Clone, Copy, Debug)]
pub struct BoolInfo {
	pub data: DataId,
	pub false_tag: usize,
	pub true_tag: usize,
}

pub struct MProgram {
	pub datas: Vec<DataDef>,
	pub funcs: Vec<MFunc>,
	pub entry: String,
	pub entry_kind: EntryKind,
	pub entry_ret: MTy,
	pub list: Option<ListInfo>,
	pub bool_ty: Option<BoolInfo>,
}

fn fv_atom(a: &MAtom, s: &mut BTreeSet<Name>) {
	if let MAtom::Var(n) = a {
		s.insert(n.clone());
	}
}

pub fn fv_value(v: &MValue) -> BTreeSet<Name> {
	let mut s = BTreeSet::new();
	match v {
		MValue::Atom(a)
		| MValue::Proj(a, _)
		| MValue::Field(a, _, _)
		| MValue::Unwrap(a, _)
		| MValue::Force(a)
		| MValue::Wrap(a) => fv_atom(a, &mut s),
		MValue::Str(_) | MValue::Fail(_) => {}
		MValue::Pair(a, b) | MValue::Apply(a, b) => {
			fv_atom(a, &mut s);
			fv_atom(b, &mut s);
		}
		MValue::Ctor { payload, .. } => {
			if let Some(a) = payload {
				fv_atom(a, &mut s);
			}
		}
		MValue::CtorReuse { token, payload, .. } => {
			s.insert(token.clone());
			fv_atom(payload, &mut s);
		}
		MValue::Lambda { param, body, .. } => {
			s = fv_expr(body);
			s.remove(&param.0);
		}
		MValue::Delay { body, .. } => s = fv_expr(body),
		MValue::Call { args, .. } | MValue::MakePap { args, .. } | MValue::Prim(_, args) => {
			for a in args {
				fv_atom(a, &mut s);
			}
		}
	}
	s
}

pub fn fv_expr(e: &MExpr) -> BTreeSet<Name> {
	match e {
		MExpr::Let(x, _, v, rest) => {
			let mut s = fv_expr(rest);
			s.remove(x);
			s.extend(fv_value(v));
			s
		}
		MExpr::Case(a, arms) => {
			let mut s = BTreeSet::new();
			fv_atom(a, &mut s);
			for arm in arms {
				s.extend(fv_expr(&arm.body));
			}
			s
		}
		MExpr::Ret(a) => {
			let mut s = BTreeSet::new();
			fv_atom(a, &mut s);
			s
		}
		MExpr::Dup(n, r) | MExpr::Drop(n, r) => {
			let mut s = fv_expr(r);
			s.insert(n.clone());
			s
		}
		MExpr::DropReuse(tok, x, r) => {
			let mut s = fv_expr(r);
			s.remove(tok);
			s.insert(x.clone());
			s
		}
		MExpr::Take {
			binds,
			from,
			token,
			rest,
			..
		} => {
			let mut s = fv_expr(rest);
			for (n, _, _) in binds {
				s.remove(n);
			}
			if let Some(t) = token {
				s.remove(t);
			}
			s.insert(from.clone());
			s
		}
	}
}

// in core everything is lazy so any unused is dead. in final only operations that eval something must be kept.
pub fn dce(e: MExpr, final_dialect: bool) -> MExpr {
	fn keep(v: &MValue, final_dialect: bool) -> bool {
		final_dialect
			&& matches!(
				v,
				MValue::Call { .. }
					| MValue::Apply(..)
					| MValue::Prim(..)
					| MValue::Force(_)
					| MValue::Fail(_)
			)
	}
	match e {
		MExpr::Let(x, t, v, rest) => {
			let rest = dce(*rest, final_dialect);
			let v = match v {
				MValue::Lambda { param, body, free } => MValue::Lambda {
					param,
					body: Box::new(dce(*body, final_dialect)),
					free,
				},
				MValue::Delay { body, free } => MValue::Delay {
					body: Box::new(dce(*body, final_dialect)),
					free,
				},
				other => other,
			};
			if !keep(&v, final_dialect) && !fv_expr(&rest).contains(&x) {
				rest
			} else {
				MExpr::Let(x, t, v, Box::new(rest))
			}
		}
		MExpr::Case(a, arms) => MExpr::Case(
			a,
			arms.into_iter()
				.map(|m| MArm {
					pat: m.pat,
					body: dce(m.body, final_dialect),
				})
				.collect(),
		),
		MExpr::Ret(a) => MExpr::Ret(a),
		MExpr::Dup(n, r) => MExpr::Dup(n, Box::new(dce(*r, final_dialect))),
		MExpr::Drop(n, r) => MExpr::Drop(n, Box::new(dce(*r, final_dialect))),
		MExpr::DropReuse(t, x, r) => MExpr::DropReuse(t, x, Box::new(dce(*r, final_dialect))),
		MExpr::Take {
			binds,
			from,
			ctor,
			token,
			rest,
		} => MExpr::Take {
			binds,
			from,
			ctor,
			token,
			rest: Box::new(dce(*rest, final_dialect)),
		},
	}
}

// see codegen for representation
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SuspKind {
	Imm,
	Direct,
	Boxed,
}

pub struct Facts<'a> {
	pub datas: &'a [DataDef],
}

impl<'a> Facts<'a> {
	pub fn needs_rc(&self, t: &MTy) -> bool {
		match t {
			MTy::Fn(..) | MTy::Susp(_) | MTy::Prod(..) => true,
			MTy::Data(id) => !self.datas[*id].is_enum(),
			_ => false,
		}
	}

	pub fn susp_kind(&self, t: &MTy) -> SuspKind {
		match t {
			MTy::Int | MTy::Char | MTy::Unit => SuspKind::Imm,
			MTy::Data(id) if self.datas[*id].is_enum() => SuspKind::Imm,
			MTy::Fn(..) | MTy::Data(_) => SuspKind::Direct,
			MTy::Float | MTy::Prod(..) => SuspKind::Boxed,
			MTy::Susp(t) => self.susp_kind(t),
			MTy::Token => SuspKind::Direct,
		}
	}

	pub fn leaves(&self, payload: &MTy) -> Vec<MTy> {
		match payload {
			MTy::Unit => vec![],
			MTy::Prod(a, b) => vec![MTy::susp((**a).clone()), MTy::susp((**b).clone())],
			other => vec![MTy::susp(other.clone())],
		}
	}

	pub fn is_packed(&self, d: DataId, ci: usize, i: usize) -> bool {
		self.datas[d].ctors[ci]
			.packed
			.get(i)
			.copied()
			.unwrap_or(false)
	}

	pub fn stored_leaves(&self, d: DataId, ci: usize) -> Vec<MTy> {
		let Some(p) = self.datas[d].ctors[ci].payload.as_ref() else {
			return vec![];
		};
		self.leaves(p)
			.into_iter()
			.enumerate()
			.map(|(i, l)| match (self.is_packed(d, ci, i), l) {
				(true, MTy::Susp(t)) => *t,
				(_, l) => l,
			})
			.collect()
	}

	pub fn packable(&self, leaf: &MTy) -> bool {
		match leaf {
			MTy::Susp(t) => match &**t {
				MTy::Int | MTy::Char => true,
				MTy::Data(id) => self.datas[*id].is_enum(),
				_ => false,
			},
			_ => false,
		}
	}

	pub fn obj_size(&self, d: DataId, ci: usize) -> u64 {
		let hdr: u64 = if self.datas[d].is_wide() { 8 } else { 4 };
		let leaves = self.stored_leaves(d, ci);
		if leaves.is_empty() {
			return hdr;
		}
		let (mut off, mut al) = (hdr, 4u64);
		for l in &leaves {
			let (s, a) = match l {
				MTy::Susp(_) => (8, 8),
				t => self.val_size_align(t),
			};
			off = off.div_ceil(a) * a + s;
			al = al.max(a);
		}
		off.div_ceil(al) * al
	}

	// (size, align) of a value of `t`
	pub fn val_size_align(&self, t: &MTy) -> (u64, u64) {
		match t {
			MTy::Unit => (0, 1),
			MTy::Int | MTy::Char => (4, 4),
			MTy::Float => (8, 8),
			MTy::Data(id) if self.datas[*id].is_enum() => {
				if self.datas[*id].ctors.len() <= 256 {
					(1, 1)
				} else {
					(4, 4)
				}
			}
			MTy::Prod(..) => (16, 8),
			_ => (8, 8),
		}
	}
}
