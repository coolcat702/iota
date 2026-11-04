// User-defined type-level functions: the glue between the parser's `Type::Match`,
// the pure reducer in `tynorm.rs`, and the typechecker's `Ty`.
//
//   type Tuple (n : Nat) a : Type = match
//       Nat:Zero, _   -> Unit end
//       Nat:Succ k, a -> a * Tuple k a end
//   end end
//
// The function table is thread-local, like the optimizer's other whole-program state, so
// that `Subst::apply` (which has no access to the checker) can reduce saturated
// applications as soon as their arguments are known. Everything is bounded: fuel and
// depth come from `tynorm::Reducer`, and recursive definitions must be structural.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use crate::parser::{Span, Spanned, Type as A};
use crate::tynorm::{self, Clause, Defs, Func, Pat, Poly, Reducer, Tm};
use crate::typechecker::{Ty, poly_to_ty_with};

thread_local! {
	static DEFS: RefCell<Defs> = RefCell::new(Defs::new());
	static HAS_FNS: Cell<bool> = const { Cell::new(false) };
	static FUEL: Cell<u64> = const { Cell::new(tynorm::DEFAULT_FUEL) };
	static ERRORS: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
}

/// `--type-fuel N`: reductions allowed per application (default 10000).
pub fn set_fuel(n: u64) {
	FUEL.with(|f| f.set(n));
}

/// Errors raised while reducing inside `Subst::apply` (which cannot report them itself).
pub fn take_errors() -> Vec<String> {
	ERRORS.with(|e| std::mem::take(&mut *e.borrow_mut()))
}

fn is_var_name(n: &str) -> bool {
	n.chars()
		.next()
		.is_some_and(|c| c.is_lowercase() || c == '_')
}

fn canon_ctor(name: &str) -> &str {
	match name {
		"Nat:Zero" | "Zero" => tynorm::ZERO,
		"Nat:Succ" | "Succ" => tynorm::SUCC,
		"Bool:True" | "True" => tynorm::TRUE,
		"Bool:False" | "False" => tynorm::FALSE,
		o => o,
	}
}

fn spine_ast(t: &Spanned<A>) -> (&Spanned<A>, Vec<&Spanned<A>>) {
	let mut args = Vec::new();
	let mut cur = t;
	while let A::App(f, a) = &cur.item {
		args.push(&**a);
		cur = &**f;
	}
	args.reverse();
	(cur, args)
}

type Res<T> = Result<T, (String, Span)>;

struct Cx<'a> {
	vars: HashMap<String, usize>,
	is_fn: &'a dyn Fn(&str) -> bool,
}

impl Cx<'_> {
	fn builtin_con(t: &A) -> Option<&'static str> {
		match t {
			A::Unit => Some("Unit"),
			A::Int => Some("Int"),
			A::Float => Some("Float"),
			A::Char => Some("Char"),
			_ => None,
		}
	}

	fn pat(&mut self, t: &Spanned<A>) -> Res<Pat> {
		let (h, args) = spine_ast(t);
		match &h.item {
			A::Hole if args.is_empty() => Ok(Pat::Wild),
			A::Lit(n) if args.is_empty() => Ok(Pat::Lit(*n)),
			A::Var(name) => {
				if is_var_name(name) && args.is_empty() {
					if self.vars.contains_key(name) {
						return Err((format!("pattern variable `{}` is repeated", name), t.span));
					}
					let id = self.vars.len();
					self.vars.insert(name.clone(), id);
					return Ok(Pat::Var(id));
				}
				let args = args.iter().map(|a| self.pat(a)).collect::<Res<Vec<_>>>()?;
				Ok(Pat::Con(canon_ctor(name).to_string(), args))
			}
			o if args.is_empty() && Self::builtin_con(o).is_some() => {
				Ok(Pat::Con(Self::builtin_con(o).unwrap().to_string(), vec![]))
			}
			A::Product(a, b) => Ok(Pat::Con("*".into(), vec![self.pat(a)?, self.pat(b)?])),
			A::Sum(a, b) => Ok(Pat::Con("+".into(), vec![self.pat(a)?, self.pat(b)?])),
			A::Fn(a, b) => Ok(Pat::Con("->".into(), vec![self.pat(a)?, self.pat(b)?])),
			_ => Err(("unsupported pattern in a type function".to_string(), t.span)),
		}
	}

	fn tm(&mut self, t: &Spanned<A>) -> Res<Tm> {
		let (h, args) = spine_ast(t);
		match &h.item {
			A::Lit(n) if args.is_empty() => Ok(Tm::lit(*n)),
			A::Var(name) => {
				if args.is_empty()
					&& let Some(id) = self.vars.get(name)
				{
					return Ok(Tm::PVar(*id));
				}
				if is_var_name(name) {
					return Err((
						format!(
							"type variable `{}` is not bound by the clause's patterns",
							name
						),
						t.span,
					));
				}
				let c = canon_ctor(name);
				let args = args.iter().map(|a| self.tm(a)).collect::<Res<Vec<_>>>()?;
				if c == tynorm::ZERO && args.is_empty() {
					Ok(Tm::zero())
				} else if (self.is_fn)(name) || tynorm::builtin_arity(name).is_some() {
					Ok(Tm::App(name.clone(), args))
				} else {
					Ok(Tm::Con(c.to_string(), args))
				}
			}
			o if args.is_empty() && Self::builtin_con(o).is_some() => {
				Ok(Tm::con(Self::builtin_con(o).unwrap(), vec![]))
			}
			A::Product(a, b) => Ok(Tm::con("*", vec![self.tm(a)?, self.tm(b)?])),
			A::Sum(a, b) => Ok(Tm::con("+", vec![self.tm(a)?, self.tm(b)?])),
			A::Fn(a, b) => Ok(Tm::con("->", vec![self.tm(a)?, self.tm(b)?])),
			_ => Err((
				"unsupported type in a type function body".to_string(),
				t.span,
			)),
		}
	}
}

/// Validate and register `type name p1 .. pn = match ... end end`.
pub fn register(
	name: &str,
	arity: usize,
	clauses: &[(Vec<Spanned<A>>, Spanned<A>)],
	span: Span,
) -> Result<(), (String, Span)> {
	let known: Vec<String> = DEFS.with(|d| d.borrow().funcs.keys().cloned().collect());
	let own = name.to_string();
	let is_fn = move |n: &str| n == own || known.iter().any(|k| k == n);

	let mut out = Vec::with_capacity(clauses.len());
	for (pats, rhs) in clauses {
		if pats.len() != arity {
			return Err((
				format!(
					"a clause of `{}` has {} patterns, but the type takes {} parameters",
					name,
					pats.len(),
					arity
				),
				pats.first().map(|p| p.span).unwrap_or(span),
			));
		}
		let mut cx = Cx {
			vars: HashMap::new(),
			is_fn: &is_fn,
		};
		let pats = pats.iter().map(|p| cx.pat(p)).collect::<Res<Vec<_>>>()?;
		let rhs = cx.tm(rhs)?;
		out.push(Clause { pats, rhs });
	}
	let func = Func {
		name: name.to_string(),
		arity,
		clauses: out,
	};
	// well-formedness and the structural-recursion check
	tynorm::check_wellformed(&func).map_err(|m| (m, span))?;
	tynorm::check_terminates(&func).map_err(|m| (m, span))?;
	// a user definition of a built-in is checked but never consulted
	if tynorm::builtin_arity(name).is_none() {
		DEFS.with(|d| d.borrow_mut().funcs.insert(name.to_string(), func));
		HAS_FNS.with(|h| h.set(true));
	}
	Ok(())
}

fn nullary(name: &str) -> Tm {
	Tm::Con(name.to_string(), vec![])
}

pub fn ty_to_tm(t: &Ty, is_fn: &dyn Fn(&str) -> bool) -> Option<Tm> {
	Some(match t {
		Ty::Lit(n) => Tm::lit(*n),
		Ty::Var(v) => Tm::Atom(*v as usize),
		Ty::Unit => nullary("Unit"),
		Ty::Int => nullary("Int"),
		Ty::Float => nullary("Float"),
		Ty::Char => nullary("Char"),
		Ty::Fn(a, b) => Tm::con("->", vec![ty_to_tm(a, is_fn)?, ty_to_tm(b, is_fn)?]),
		Ty::Product(a, b) => Tm::con("*", vec![ty_to_tm(a, is_fn)?, ty_to_tm(b, is_fn)?]),
		Ty::Sum(a, b) => Tm::con("+", vec![ty_to_tm(a, is_fn)?, ty_to_tm(b, is_fn)?]),
		Ty::Named(n) => nullary(n),
		Ty::App(..) => {
			let (h, args) = crate::types::spine(t);
			let Ty::Named(n) = h else { return None };
			let args = args
				.iter()
				.map(|a| ty_to_tm(a, is_fn))
				.collect::<Option<Vec<_>>>()?;
			if n == "Succ" && args.len() == 1 {
				Tm::succ(args.into_iter().next()?)
			} else if is_fn(n) || tynorm::builtin_arity(n).is_some() {
				Tm::App(n.clone(), args)
			} else {
				Tm::Con(n.clone(), args)
			}
		}
	})
}

fn fold_app(name: &str, args: Vec<Ty>) -> Ty {
	args.into_iter().fold(Ty::Named(name.to_string()), |f, a| {
		Ty::App(Box::new(f), Box::new(a))
	})
}

pub fn tm_to_ty(t: &Tm) -> Option<Ty> {
	Some(match t {
		Tm::Nat(p) => return nat_to_ty(p),
		Tm::Atom(k) => Ty::Var(*k as u32),
		Tm::PVar(_) => return None,
		Tm::Con(n, args) => {
			let tys = args.iter().map(tm_to_ty).collect::<Option<Vec<_>>>()?;
			match (n.as_str(), tys.len()) {
				("Unit", 0) => Ty::Unit,
				("Int", 0) => Ty::Int,
				("Float", 0) => Ty::Float,
				("Char", 0) => Ty::Char,
				("->", 2) => {
					let mut it = tys.into_iter();
					Ty::Fn(Box::new(it.next()?), Box::new(it.next()?))
				}
				("*", 2) => {
					let mut it = tys.into_iter();
					Ty::Product(Box::new(it.next()?), Box::new(it.next()?))
				}
				("+", 2) => {
					let mut it = tys.into_iter();
					Ty::Sum(Box::new(it.next()?), Box::new(it.next()?))
				}
				// a stuck `Succ x` stays an application of the built-in
				(_, _) => fold_app(n, tys),
			}
		}
		Tm::App(n, args) => {
			let tys = args.iter().map(tm_to_ty).collect::<Option<Vec<_>>>()?;
			fold_app(n, tys)
		}
	})
}

fn nat_to_ty(p: &Poly<usize>) -> Option<Ty> {
	poly_to_ty_with(p, &|k: &usize| Ty::Var(*k as u32))
}

/// Number of arguments and head name of an application spine, without allocating.
fn head_of(t: &Ty) -> Option<(&str, usize)> {
	let mut n = 0;
	let mut cur = t;
	while let Ty::App(f, _) = cur {
		n += 1;
		cur = f;
	}
	match cur {
		Ty::Named(name) if n > 0 => Some((name.as_str(), n)),
		_ => None,
	}
}

/// Is `t` a saturated application of a user type function (reduced or stuck)?
pub fn is_fn_app(t: &Ty) -> bool {
	// the built-in comparisons return a type-level Bool
	if let Some((name, n)) = head_of(t)
		&& n == 2
		&& matches!(name, "Ls" | "Lse")
	{
		return true;
	}
	if !HAS_FNS.with(|h| h.get()) {
		return false;
	}
	let Some((name, n)) = head_of(t) else {
		return false;
	};
	DEFS.with(|d| d.borrow().funcs.get(name).is_some_and(|f| f.arity == n))
}

/// Reduce `t` if it is a saturated user type function application whose arguments are
/// known enough; otherwise return it unchanged. Called from `Subst::apply`, innermost
/// applications first, so the arguments are already normalized.
pub fn reduce_app(t: Ty) -> Ty {
	if !is_fn_app(&t) {
		return t;
	}
	let fuel = FUEL.with(|f| f.get());
	let result = DEFS.with(|d| {
		let defs = d.borrow();
		let is_fn = |n: &str| defs.funcs.contains_key(n);
		let tm = ty_to_tm(&t, &is_fn)?;
		let mut r = Reducer::new(&defs, fuel);
		match r.reduce(&tm) {
			Ok(out) => tm_to_ty(&out),
			Err(e) => {
				let msg = e.to_string();
				ERRORS.with(|errs| {
					let mut errs = errs.borrow_mut();
					if !errs.contains(&msg) {
						errs.push(msg);
					}
				});
				None
			}
		}
	});
	result.unwrap_or(t)
}
