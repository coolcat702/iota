// Compile-time evaluation of constant `Int` expressions
//
// Used where a *value* has to become a type-level number: the argument of a dependent arrow
// (`replicate (add 1 2) 7`, `replicate size 7`). The evaluator is pure and bounded and
// computes with `arith.rs`, the same semantics the optimizer's folder and the runtime use,
// so a compile-time `10 / 3` can never disagree with the program's `10 / 3`.
//
// Supported: `Int` literals, `add` / `sub` / `mul` / `div` / `mod` applied to two constants,
// and references to top-level `let name : Int = <constant>`. Anything else is "not a
// constant" and the caller falls back to ordinary checking.

use std::collections::HashMap;

use crate::arith;
use crate::parser::{Expr, Literal, Spanned};

/// Top-level constants: name -> definition body.
pub type Consts = HashMap<String, Spanned<Expr>>;

const MAX_DEPTH: usize = 64;

/// `Ok(Some(v))`: a constant. `Ok(None)`: not a constant. `Err`: a constant whose
/// evaluation fails (division by zero, a cycle, too deep).
pub fn eval(
	e: &Expr,
	consts: &Consts,
	shadowed: &[String],
	depth: usize,
) -> Result<Option<i32>, String> {
	if depth > MAX_DEPTH {
		return Err(
			"compile-time evaluation is too deep (is a constant defined in terms of itself?)"
				.to_string(),
		);
	}
	match e {
		Expr::Literal(Literal::Int(v)) => Ok(Some(*v)),
		Expr::Qualified(q) => match q.0.as_slice() {
			[name] if shadowed.contains(name) => Ok(None),
			[name] => match consts.get(name) {
				Some(body) => eval(&body.item, consts, &[], depth + 1),
				None => Ok(None),
			},
			_ => Ok(None),
		},
		Expr::App(..) => {
			let mut args: Vec<&Expr> = Vec::new();
			let mut cur = e;
			while let Expr::App(f, a) = cur {
				args.push(&a.item);
				cur = &f.item;
			}
			args.reverse();
			let Expr::Qualified(q) = cur else {
				return Ok(None);
			};
			let [op] = q.0.as_slice() else {
				return Ok(None);
			};
			if shadowed.contains(op)
				|| args.len() != 2
				|| !matches!(op.as_str(), "add" | "sub" | "mul" | "div" | "mod")
			{
				return Ok(None);
			}
			let (Some(a), Some(b)) = (
				eval(args[0], consts, shadowed, depth + 1)?,
				eval(args[1], consts, shadowed, depth + 1)?,
			) else {
				return Ok(None);
			};
			match op.as_str() {
				"add" => Ok(Some(arith::iadd(a, b))),
				"sub" => Ok(Some(arith::isub(a, b))),
				"mul" => Ok(Some(arith::imul(a, b))),
				"div" => arith::idiv(a, b)
					.map(Some)
					.ok_or_else(|| "division by zero in a compile-time constant".to_string()),
				_ => arith::imod(a, b)
					.map(Some)
					.ok_or_else(|| "modulo by zero in a compile-time constant".to_string()),
			}
		}
		_ => Ok(None),
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::parser::{Qualified, Span};

	fn sp<T>(item: T) -> Spanned<T> {
		Spanned {
			item,
			span: Span::synthetic(0),
		}
	}
	fn int(v: i32) -> Spanned<Expr> {
		sp(Expr::Literal(Literal::Int(v)))
	}
	fn var(n: &str) -> Spanned<Expr> {
		sp(Expr::Qualified(Qualified(vec![n.to_string()])))
	}
	fn call(op: &str, a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
		sp(Expr::App(
			Box::new(sp(Expr::App(Box::new(var(op)), Box::new(a)))),
			Box::new(b),
		))
	}

	#[test]
	fn folds_like_the_runtime() {
		let mut c = Consts::new();
		c.insert("size".into(), call("mul", int(3), int(4)));
		let e = call("add", var("size"), int(1));
		assert_eq!(eval(&e.item, &c, &[], 0), Ok(Some(13)));
		// Euclidean division, as rt_idiv
		assert_eq!(
			eval(&call("div", int(-7), int(2)).item, &c, &[], 0),
			Ok(Some(-4))
		);
		assert_eq!(
			eval(&call("mod", int(-7), int(2)).item, &c, &[], 0),
			Ok(Some(1))
		);
	}

	#[test]
	fn rejects_division_by_zero_and_cycles() {
		let mut c = Consts::new();
		assert!(eval(&call("div", int(1), int(0)).item, &c, &[], 0).is_err());
		c.insert("a".into(), call("add", var("a"), int(1)));
		assert!(eval(&var("a").item, &c, &[], 0).is_err());
	}

	#[test]
	fn unknown_names_are_not_constants() {
		let c = Consts::new();
		assert_eq!(eval(&var("x").item, &c, &[], 0), Ok(None));
		assert_eq!(
			eval(&call("foo", int(1), int(2)).item, &c, &[], 0),
			Ok(None)
		);
	}
}
