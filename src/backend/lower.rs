// lower specced IR to MIR
//   - map Iota types to runtime types (`MTy`). data types are interned for each
//     instantiation (`List Int` and `List Float` are different `DataDef`s), `IO a`
//     becomes the closure type `Unit -> a`, anonymous sum becomes a two-ctor data type;
//   - turn curried application of known globals into saturated `Call`s or explicit
//     partial apps (`MakePap`)
//   - intrinsic externs (arithmetic, strings, IO, sums) as small MIR functions

use std::collections::{BTreeSet, HashMap};

use crate::diag::Diagnostic;
use crate::ir::{
	display_ty, peel_fn, Atom, CasePat, Expr, Extern, Function, IrProgram, Side, Value,
};
use crate::lang::{bare, split_ctor, Intrinsic, Lang, LangItem};
use crate::parser::{Literal, Span};
use crate::typechecker::Ty;
use crate::types::{spine, TypeInfo};

use super::mir::*;

#[derive(Clone)]
struct Pap {
	func: String,
	ptys: Vec<Ty>,
	ret: Ty,
	args: Vec<MAtom>,
}

impl Pap {
	fn remaining_fn_ty(&self) -> Ty {
		let mut t = self.ret.clone();
		for pt in self.ptys[self.args.len()..].iter().rev() {
			t = Ty::Fn(Box::new(pt.clone()), Box::new(t));
		}
		t
	}
}

enum VR {
	Val(MValue),
	Pap(Pap),
}

enum Head {
	Pap(Pap),
	Closure(MAtom),
}

#[derive(Default)]
struct Frame {
	tys: HashMap<String, MTy>,
	pap: HashMap<String, Pap>,
	known: HashMap<String, String>,
	n: usize,
}

type Pre = Vec<(String, MTy, MValue)>;

fn wrap_pre(pre: Pre, tail: MExpr) -> MExpr {
	pre.into_iter()
		.rev()
		.fold(tail, |acc, (n, t, v)| MExpr::Let(n, t, v, Box::new(acc)))
}

struct L<'a> {
	ti: &'a TypeInfo,
	lang: &'a Lang,
	funcs: HashMap<&'a str, &'a Function>,
	externs: HashMap<&'a str, &'a Extern>,
	datas: Vec<DataDef>,
	data_ix: HashMap<String, DataId>,
	out: Vec<MFunc>,
	errors: Vec<Diagnostic>,
}

pub fn lower(
	prog: &IrProgram,
	ti: &TypeInfo,
	lang: &Lang,
	entry: &str,
) -> Result<MProgram, Vec<Diagnostic>> {
	let mut l = L {
		ti,
		lang,
		funcs: prog
			.functions
			.iter()
			.map(|f| (f.name.as_str(), f))
			.collect(),
		externs: prog.externs.iter().map(|e| (e.name.as_str(), e)).collect(),
		datas: Vec::new(),
		data_ix: HashMap::new(),
		out: Vec::new(),
		errors: Vec::new(),
	};
	l.run(prog, entry)
}

impl<'a> L<'a> {
	fn err(&mut self, msg: impl Into<String>, span: Option<Span>) {
		self.errors.push(Diagnostic::error(msg, span));
	}

	fn is_io(&self, t: &Ty) -> Option<Ty> {
		let t = self.ti.norm(t);
		let (h, args) = spine(&t);
		match (h, args.as_slice()) {
			(Ty::Named(n), [a]) if n == self.lang.item(LangItem::IoType) => Some((*a).clone()),
			_ => None,
		}
	}

	fn run(&mut self, prog: &IrProgram, entry: &str) -> Result<MProgram, Vec<Diagnostic>> {
		let Some(ef) = self.funcs.get(entry).copied() else {
			return Err(vec![Diagnostic::error(
				format!("entry point `{}` not found", entry),
				None,
			)]);
		};
		for f in &prog.functions {
			if let Err(e) = self.func(f) {
				self.err(format!("in `{}`: {}", f.name, e), Some(f.span));
			}
		}
		for x in &prog.externs {
			if let Err(e) = self.extern_fn(x) {
				self.err(e, Some(x.span));
			}
		}
		let (kind, inner) = match self.is_io(&ef.ret) {
			Some(a) => (EntryKind::Action, a),
			None => (EntryKind::Value, ef.ret.clone()),
		};
		let entry_ret = self.canon(&inner).unwrap_or(MTy::Unit);

		let list = {
			let list_ty = self.lang.item(LangItem::ListType).to_string();
			if self.ti.type_ctors.contains_key(&list_ty) {
				let t = Ty::App(Box::new(Ty::Named(list_ty)), Box::new(Ty::Char));
				match self.canon(&t) {
					Ok(MTy::Data(id)) => {
						let d = &self.datas[id];
						match (
							d.tag_of(bare(self.lang.item(LangItem::ListNil))),
							d.tag_of(bare(self.lang.item(LangItem::ListCons))),
						) {
							(Some(nil), Some(cons)) => Some(ListInfo {
								data: id,
								nil,
								cons,
							}),
							_ => None,
						}
					}
					_ => None,
				}
			} else {
				None
			}
		};
		let bool_ty = {
			let bool_name = split_ctor(self.lang.item(LangItem::BoolTrue)).0.to_string();
			if self.ti.type_ctors.contains_key(&bool_name) {
				match self.canon(&Ty::Named(bool_name)) {
					Ok(MTy::Data(id)) => {
						let d = &self.datas[id];
						match (
							d.tag_of(bare(self.lang.item(LangItem::BoolFalse))),
							d.tag_of(bare(self.lang.item(LangItem::BoolTrue))),
						) {
							(Some(f), Some(t)) => Some(BoolInfo {
								data: id,
								false_tag: f,
								true_tag: t,
							}),
							_ => None,
						}
					}
					_ => None,
				}
			} else {
				None
			}
		};
		if !self.errors.is_empty() {
			return Err(std::mem::take(&mut self.errors));
		}
		Ok(MProgram {
			datas: std::mem::take(&mut self.datas),
			funcs: std::mem::take(&mut self.out),
			entry: entry.to_string(),
			entry_kind: kind,
			entry_ret,
			list,
			bool_ty,
		})
	}

	fn canon(&mut self, t: &Ty) -> Result<MTy, String> {
		let t = self.ti.norm(t);
		Ok(match &t {
			Ty::Unit | Ty::Var(_) => MTy::Unit,
			Ty::Int => MTy::Int,
			Ty::Float => MTy::Float,
			Ty::Char => MTy::Char,
			Ty::Fn(a, b) => MTy::Fn(Box::new(self.canon(a)?), Box::new(self.canon(b)?)),
			Ty::Product(a, b) => MTy::Prod(Box::new(self.canon(a)?), Box::new(self.canon(b)?)),
			Ty::Sum(a, b) => self.intern_sum(&t, a, b)?,
			Ty::Named(_) | Ty::App(..) => {
				let (h, args) = spine(&t);
				match h {
					Ty::Named(n) => {
						if let (true, [a]) =
							(n == self.lang.item(LangItem::IoType), args.as_slice())
						{
							return Ok(MTy::Fn(Box::new(MTy::Unit), Box::new(self.canon(a)?)));
						}
						if self.ti.type_ctors.contains_key(n) {
							let args: Vec<Ty> = args.into_iter().cloned().collect();
							let n = n.clone();
							return self.intern_data(&n, &args);
						}
						return Err(format!(
							"type `{}` has no runtime representation",
							display_ty(&t)
						));
					}
					_ => return Err(format!("unsupported higher-kinded type {}", display_ty(&t))),
				}
			}
		})
	}

	fn intern_sum(&mut self, whole: &Ty, a: &Ty, b: &Ty) -> Result<MTy, String> {
		let key = display_ty(whole);
		if let Some(id) = self.data_ix.get(&key) {
			return Ok(MTy::Data(*id));
		}
		let id = self.datas.len();
		self.data_ix.insert(key.clone(), id);
		self.datas.push(DataDef {
			name: key,
			ctors: vec![],
		});
		let (ca, cb) = (self.canon(a)?, self.canon(b)?);
		self.datas[id].ctors = vec![
			CtorDef {
				name: self.lang.item(LangItem::SumLeft).to_string(),
				payload: Some(ca),
				packed: vec![],
			},
			CtorDef {
				name: self.lang.item(LangItem::SumRight).to_string(),
				payload: Some(cb),
				packed: vec![],
			},
		];
		Ok(MTy::Data(id))
	}

	fn intern_data(&mut self, name: &str, args: &[Ty]) -> Result<MTy, String> {
		let mut nom = Ty::Named(name.to_string());
		for a in args {
			nom = Ty::App(Box::new(nom), Box::new(a.clone()));
		}
		let key = display_ty(&nom);
		if let Some(id) = self.data_ix.get(&key) {
			return Ok(MTy::Data(*id));
		}
		let arity = self.ti.type_arity.get(name).copied().unwrap_or(0);
		if arity != args.len() {
			return Err(format!(
				"type `{}` expects {} argument(s), got {}",
				name,
				arity,
				args.len()
			));
		}
		let id = self.datas.len();
		self.data_ix.insert(key.clone(), id);
		self.datas.push(DataDef {
			name: key,
			ctors: vec![],
		});
		let mut ctors = Vec::new();
		for cname in self.ti.type_ctors[name].clone() {
			let sch = self.ti.ctor_scheme[&format!("{}:{}", name, cname)].clone();
			let (pay, res) = match &sch.ty {
				Ty::Fn(p, r) => (Some((**p).clone()), (**r).clone()),
				r => (None, r.clone()),
			};
			let mut m: HashMap<u32, Ty> = HashMap::new();
			for (ra, a) in spine(&res).1.iter().zip(args.iter()) {
				if let Ty::Var(v) = ra {
					m.insert(*v, a.clone());
				}
			}
			let payload = match pay {
				Some(p) => Some(self.canon(&crate::ir::subst_ty(&p, &m))?),
				None => None,
			};
			ctors.push(CtorDef {
				name: cname,
				payload,
				packed: vec![],
			});
		}
		self.datas[id].ctors = ctors;
		Ok(MTy::Data(id))
	}

	fn extern_fn(&mut self, x: &Extern) -> Result<(), String> {
		let op = x
			.intrinsic
			.ok_or_else(|| format!("extern `{}` has no implementation in the backend", x.name))?;
		let (ptys, rty) = peel_fn(&x.ty, x.arity);
		let mut params = Vec::new();
		for (i, t) in ptys.iter().enumerate() {
			params.push((format!("a{}", i), self.canon(t)?));
		}
		let ret = self.canon(&rty)?;
		let a = |i: usize| MAtom::Var(format!("a{}", i));
		let r = "r".to_string();
		let ret_r = |t: MTy, v: MValue| {
			MExpr::Let(r.clone(), t, v, Box::new(MExpr::Ret(MAtom::Var(r.clone()))))
		};
		// a closure over `free` running `body` when applied to world
		let action = |free: Vec<(String, MTy)>, body: MExpr| {
			MExpr::Let(
				"f".into(),
				ret.clone(),
				MValue::Lambda {
					param: ("w".into(), MTy::Unit),
					body: Box::new(body),
					free,
				},
				Box::new(MExpr::Ret(MAtom::Var("f".into()))),
			)
		};
		use Intrinsic::*;
		let body = match op {
			IAdd | ISub | IMul | IDiv | IMod | IEq | INeq | IGr | IGre | ILs | ILse | FAdd
			| FSub | FMul | FDiv | FEq | FNeq | FGr | FGre | FLs | FLse | ShowInt | ShowFloat
			| FloatRepr | IAnd | IOr | IXor | IShl | IShr | ISar | CharOrd | CharChr | IToF
			| FToI => ret_r(
				ret.clone(),
				MValue::Prim(op, (0..params.len()).map(a).collect()),
			),
			Print | Println => {
				let inner = ret_r(MTy::Unit, MValue::Prim(op, vec![a(0)]));
				action(vec![("a0".into(), params[0].1.clone())], inner)
			}
			GetLn => {
				let res = match &ret {
					MTy::Fn(_, b) => (**b).clone(),
					_ => MTy::Unit,
				};
				action(vec![], ret_r(res, MValue::Prim(GetLn, vec![])))
			}
			// the one value of `Unit`
			UnitVal => MExpr::Ret(MAtom::Unit),
			// Every runtime primitive is an `IO` action: building it has no effect, applying
			// the closure to the world token runs the C function.
			Rt(_) => {
				let res = match &ret {
					MTy::Fn(_, b) => (**b).clone(),
					_ => MTy::Unit,
				};
				let args = (0..params.len()).map(a).collect();
				action(params.clone(), ret_r(res, MValue::Prim(op, args)))
			}
			IoReturn => action(vec![("a0".into(), params[0].1.clone())], MExpr::Ret(a(0))),
			IoBind => {
				// `bind f m = \w -> let x = m w; g = f x in g w`
				let (fty, mty) = (params[0].1.clone(), params[1].1.clone());
				let (aty, gty, bty) = match (&fty, &ret) {
					(MTy::Fn(a, g), MTy::Fn(_, b)) => ((**a).clone(), (**g).clone(), (**b).clone()),
					_ => return Err("malformed instance of IO bind".into()),
				};
				let inner = MExpr::Let(
					"x".into(),
					aty,
					MValue::Apply(a(1), MAtom::Unit),
					Box::new(MExpr::Case(
						MAtom::Var("x".into()),
						vec![MArm {
							pat: MPat::Wild,
							body: MExpr::Let(
								"g".into(),
								gty,
								MValue::Apply(a(0), MAtom::Var("x".into())),
								Box::new(ret_r(
									bty,
									MValue::Apply(MAtom::Var("g".into()), MAtom::Unit),
								)),
							),
						}],
					)),
				);
				action(vec![("a0".into(), fty), ("a1".into(), mty)], inner)
			}
			SumLeft | SumRight => {
				let name = self.lang.item(if op == SumLeft {
					LangItem::SumLeft
				} else {
					LangItem::SumRight
				});
				ret_r(
					ret.clone(),
					MValue::Ctor {
						ctor: name.to_string(),
						payload: Some(a(0)),
					},
				)
			}
		};
		let caf = params.is_empty();
		self.out.push(MFunc {
			name: x.name.clone(),
			borrowed: vec![false; params.len()],
			params,
			ret,
			caf,
			body,
			span: Some(x.span),
		});
		Ok(())
	}

	fn func(&mut self, f: &Function) -> Result<(), String> {
		let mut fr = Frame::default();
		let mut params = Vec::new();
		for (p, t) in &f.params {
			let mt = self.canon(t)?;
			fr.tys.insert(p.clone(), mt.clone());
			params.push((p.clone(), mt));
		}
		let ret = self.canon(&f.ret)?;
		let body = self.expr(&mut fr, &f.body)?;
		let caf = params.is_empty();
		self.out.push(MFunc {
			name: f.name.clone(),
			borrowed: vec![false; params.len()],
			params,
			ret,
			caf,
			body: dce(body, false),
			span: Some(f.span),
		});
		Ok(())
	}

	fn fresh(&self, fr: &mut Frame, hint: &str) -> String {
		fr.n += 1;
		format!("%{}{}", hint, fr.n)
	}

	fn push_pre(&self, fr: &mut Frame, pre: &mut Pre, hint: &str, ty: MTy, v: MValue) -> MAtom {
		let x = self.fresh(fr, hint);
		fr.tys.insert(x.clone(), ty.clone());

		pre.push((x.clone(), ty, v));
		MAtom::Var(x)
	}

	fn expr(&mut self, fr: &mut Frame, e: &Expr) -> Result<MExpr, String> {
		match e {
			Expr::Let(x, ty, v, rest) => {
				let mut pre: Pre = Vec::new();
				let mt = self.canon(ty)?;
				let vr = self.value(fr, &mt, v, &mut pre)?;
				let tail = match vr {
					VR::Pap(p) => {
						fr.pap.insert(x.clone(), p);
						self.expr(fr, rest)?
					}
					VR::Val(mv) => {
						fr.tys.insert(x.clone(), mt.clone());
						let r = self.expr(fr, rest)?;
						MExpr::Let(x.clone(), mt, mv, Box::new(r))
					}
				};
				Ok(wrap_pre(pre, tail))
			}
			Expr::Halt(a) => {
				let mut pre: Pre = Vec::new();
				let m = self.atom(fr, a, &mut pre)?;
				Ok(wrap_pre(pre, MExpr::Ret(m)))
			}
			Expr::Case(a, arms) => {
				let mut pre: Pre = Vec::new();
				let ms = self.atom(fr, a, &mut pre)?;
				let mut out = Vec::new();
				for arm in arms {
					let (pat, ctor) = match &arm.pat {
						CasePat::Wild => (MPat::Wild, None),
						CasePat::Lit(Literal::Int(n)) => (MPat::Int(*n), None),
						CasePat::Lit(Literal::Char(c)) => (MPat::Char(*c), None),
						CasePat::Lit(Literal::Float(x)) => (MPat::Float(*x), None),
						CasePat::Lit(other) => {
							return Err(format!("unsupported literal pattern {:?}", other))
						}
						CasePat::Ctor(t) => {
							(MPat::Ctor(bare(t).to_string()), Some(bare(t).to_string()))
						}
					};
					let saved = match (&ctor, known_key(a)) {
						(Some(c), Some(v)) => Some((v.clone(), fr.known.insert(v, c.clone()))),
						_ => None,
					};
					let body = self.expr(fr, &arm.body)?;
					if let Some((v, old)) = saved {
						match old {
							Some(o) => {
								fr.known.insert(v, o);
							}
							None => {
								fr.known.remove(&v);
							}
						}
					}
					out.push(MArm { pat, body });
				}
				Ok(wrap_pre(pre, MExpr::Case(ms, out)))
			}
		}
	}

	fn arity_of(&self, name: &str) -> Option<usize> {
		if let Some(f) = self.funcs.get(name) {
			Some(f.params.len())
		} else {
			self.externs.get(name).map(|x| x.arity)
		}
	}

	fn pap_for(&mut self, name: &str, ty: &Ty) -> Result<Pap, String> {
		let n = self
			.arity_of(name)
			.ok_or_else(|| format!("reference to unknown global `{}`", name))?;
		let conc = self.ti.norm(ty);
		let (ptys, ret) = peel_fn(&conc, n);
		if ptys.len() < n {
			return Err(format!(
				"`{}` takes {} argument(s) but is used at type {}",
				name,
				n,
				display_ty(&conc)
			));
		}
		Ok(Pap {
			func: name.to_string(),
			ptys,
			ret,
			args: Vec::new(),
		})
	}

	fn materialize(&mut self, fr: &mut Frame, p: Pap, pre: &mut Pre) -> Result<MAtom, String> {
		let ty = self.canon(&p.remaining_fn_ty())?;
		Ok(self.push_pre(
			fr,
			pre,
			"pap",
			ty,
			MValue::MakePap {
				func: p.func,
				args: p.args,
			},
		))
	}

	fn global_atom(
		&mut self,
		fr: &mut Frame,
		g: &str,
		ty: &Ty,
		pre: &mut Pre,
	) -> Result<MAtom, String> {
		let p = self.pap_for(g, ty)?;
		if p.ptys.is_empty() {
			// constant, reffed by calling its instance
			let rt = self.canon(&p.ret)?;
			return Ok(self.push_pre(
				fr,
				pre,
				"g",
				rt,
				MValue::Call {
					func: p.func,
					args: vec![],
				},
			));
		}
		self.materialize(fr, p, pre)
	}

	fn atom(&mut self, fr: &mut Frame, a: &Atom, pre: &mut Pre) -> Result<MAtom, String> {
		match a {
			Atom::Lit(Literal::Int(n)) => Ok(MAtom::Int(*n)),
			Atom::Lit(Literal::Float(x)) => Ok(MAtom::Float(*x)),
			Atom::Lit(Literal::Char(c)) => Ok(MAtom::Char(*c)),
			Atom::Lit(other) => Err(format!("unsupported literal atom {:?}", other)),
			Atom::Global(g, t) => self.global_atom(fr, g, t, pre),
			Atom::Method(m, _) => Err(format!(
				"unresolved class method `{}` reached the backend",
				m
			)),
			Atom::Var(n) => {
				if let Some(p) = fr.pap.get(n).cloned() {
					return self.materialize(fr, p, pre);
				}
				if fr.tys.contains_key(n) {
					return Ok(MAtom::Var(n.clone()));
				}
				Err(format!("internal: variable `{}` has no known type", n))
			}
		}
	}

	fn head(&mut self, fr: &mut Frame, f: &Atom, pre: &mut Pre) -> Result<Head, String> {
		match f {
			Atom::Global(g, t) => {
				let p = self.pap_for(g, t)?;
				if p.ptys.is_empty() {
					Ok(Head::Closure(self.global_atom(fr, g, t, pre)?))
				} else {
					Ok(Head::Pap(p))
				}
			}
			Atom::Var(n) => match fr.pap.get(n) {
				Some(p) => Ok(Head::Pap(p.clone())),
				None => Ok(Head::Closure(self.atom(fr, f, pre)?)),
			},
			_ => Err("a literal was applied as a function".into()),
		}
	}

	fn value(&mut self, fr: &mut Frame, mt: &MTy, v: &Value, pre: &mut Pre) -> Result<VR, String> {
		match v {
			Value::Atom(a) => match a {
				Atom::Var(n) if fr.pap.contains_key(n) => Ok(VR::Pap(fr.pap[n].clone())),
				Atom::Global(g, t) => {
					let p = self.pap_for(g, t)?;
					if p.ptys.is_empty() {
						Ok(VR::Val(MValue::Atom(self.atom(fr, a, pre)?)))
					} else {
						Ok(VR::Pap(p))
					}
				}
				_ => Ok(VR::Val(MValue::Atom(self.atom(fr, a, pre)?))),
			},
			Value::Lambda(p, pty, body) => {
				let pt = self.canon(pty)?;
				fr.tys.insert(p.clone(), pt.clone());
				let rt = match mt {
					MTy::Fn(_, r) => (**r).clone(),
					_ => return Err("a lambda has a non-function type".into()),
				};
				let _ = rt;
				let b = self.expr(fr, body)?;
				let mut names: BTreeSet<String> = fv_expr(&b);
				names.remove(p);
				let mut free = Vec::new();
				for n in names {
					let t = fr.tys.get(&n).cloned().ok_or_else(|| {
						format!("internal: captured variable `{}` has no type", n)
					})?;
					free.push((n, t));
				}
				Ok(VR::Val(MValue::Lambda {
					param: (p.clone(), pt),
					body: Box::new(b),
					free,
				}))
			}
			Value::App(f, a) => {
				let head = self.head(fr, f, pre)?;
				let ma = self.atom(fr, a, pre)?;
				match head {
					Head::Pap(mut p) => {
						p.args.push(ma);
						if p.args.len() == p.ptys.len() {
							Ok(VR::Val(MValue::Call {
								func: p.func,
								args: p.args,
							}))
						} else {
							Ok(VR::Pap(p))
						}
					}
					Head::Closure(mf) => Ok(VR::Val(MValue::Apply(mf, ma))),
				}
			}
			Value::Pair(a, b) => {
				let ma = self.atom(fr, a, pre)?;
				let mb = self.atom(fr, b, pre)?;
				Ok(VR::Val(MValue::Pair(ma, mb)))
			}
			Value::Proj(a, side) => {
				let ma = self.atom(fr, a, pre)?;
				Ok(VR::Val(MValue::Proj(ma, *side)))
			}
			Value::Ctor(tag, payload) => {
				let pm = match payload {
					Some(a) => Some(self.atom(fr, a, pre)?),
					None => None,
				};
				Ok(VR::Val(MValue::Ctor {
					ctor: bare(tag).to_string(),
					payload: pm,
				}))
			}
			Value::Unwrap(a) => {
				let ma = self.atom(fr, a, pre)?;
				let ctor = known_key(a)
					.and_then(|k| fr.known.get(&k).cloned())
					.ok_or_else(|| {
						"internal: `unwrap` of a value whose constructor is not known".to_string()
					})?;
				Ok(VR::Val(MValue::Unwrap(ma, ctor)))
			}
			Value::Str(s) => Ok(VR::Val(MValue::Str(s.clone()))),
			Value::Fail(m) => Ok(VR::Val(MValue::Fail(m.clone()))),
		}
	}
}

/// What `Frame::known` is keyed by. The optimizer can inline a global into a `case`
/// scrutinee, so a global that was matched is as good as a variable for a later `unwrap`.
/// (`@` cannot start a variable name, so the two never collide.)
fn known_key(a: &Atom) -> Option<String> {
	match a {
		Atom::Var(n) => Some(n.clone()),
		Atom::Global(g, _) => Some(format!("@{}", g)),
		_ => None,
	}
}

#[allow(dead_code)]
fn _side(_: Side) {}
