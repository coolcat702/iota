// Kinds: `Type`, a promoted data type such as `Nat`, or `K1 -> K2`
//
// Kinds live in their own namespace and are never types, so there is no `Type : Type`
// and the Girard paradox is unreachable. Inference is plain first-order unification
// with an occurs check; `KindSubst::default_to_type` resolves whatever is left
// unconstrained to `Type`.

#![allow(dead_code)]

use std::collections::HashMap;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
	Type,
	/// A promoted data type, e.g. `Nat` or `Bool`.
	Data(String),
	Arrow(Box<Kind>, Box<Kind>),
	Var(u32),
}

impl Kind {
	pub fn arrow(a: Kind, b: Kind) -> Kind {
		Kind::Arrow(Box::new(a), Box::new(b))
	}

	/// `Type -> Type -> ... -> Type` with `n` arguments: what an unannotated parameter list
	/// of length `n` gets by default.
	pub fn arity(n: usize) -> Kind {
		(0..n).fold(Kind::Type, |k, _| Kind::arrow(Kind::Type, k))
	}

	/// The argument kinds of a (possibly curried) arrow kind.
	pub fn args(&self) -> Vec<&Kind> {
		let mut out = Vec::new();
		let mut cur = self;
		while let Kind::Arrow(a, b) = cur {
			out.push(&**a);
			cur = &**b;
		}
		out
	}

	/// Is this the kind of a promoted data type, i.e. does a value of it get erased when it
	/// appears as a type argument? (`Type` and arrows are not index kinds.)
	pub fn is_index(&self) -> bool {
		matches!(self, Kind::Data(_))
	}
}

impl fmt::Display for Kind {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Kind::Type => write!(f, "Type"),
			Kind::Data(n) => write!(f, "{}", n),
			Kind::Var(v) => write!(f, "k{}", v),
			Kind::Arrow(a, b) => match **a {
				Kind::Arrow(..) => write!(f, "({}) -> {}", a, b),
				_ => write!(f, "{} -> {}", a, b),
			},
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KindError {
	Mismatch(Kind, Kind),
	Infinite(u32, Kind),
}

impl fmt::Display for KindError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			KindError::Mismatch(a, b) => {
				write!(f, "kind mismatch: expected `{}`, found `{}`", a, b)
			}
			KindError::Infinite(v, k) => write!(f, "infinite kind: k{} ~ {}", v, k),
		}
	}
}

#[derive(Debug, Clone, Default)]
pub struct KindSubst {
	map: HashMap<u32, Kind>,
	next: u32,
}

impl KindSubst {
	pub fn new() -> Self {
		Self::default()
	}

	pub fn fresh(&mut self) -> Kind {
		let v = self.next;
		self.next += 1;
		Kind::Var(v)
	}

	pub fn apply(&self, k: &Kind) -> Kind {
		match k {
			Kind::Var(v) => match self.map.get(v) {
				Some(k) => self.apply(k),
				None => Kind::Var(*v),
			},
			Kind::Arrow(a, b) => Kind::arrow(self.apply(a), self.apply(b)),
			other => other.clone(),
		}
	}

	fn occurs(&self, v: u32, k: &Kind) -> bool {
		match self.apply(k) {
			Kind::Var(w) => v == w,
			Kind::Arrow(a, b) => self.occurs(v, &a) || self.occurs(v, &b),
			_ => false,
		}
	}

	pub fn unify(&mut self, a: &Kind, b: &Kind) -> Result<(), KindError> {
		let (a, b) = (self.apply(a), self.apply(b));
		match (&a, &b) {
			(Kind::Type, Kind::Type) => Ok(()),
			(Kind::Data(x), Kind::Data(y)) if x == y => Ok(()),
			(Kind::Var(x), Kind::Var(y)) if x == y => Ok(()),
			(Kind::Var(v), k) | (k, Kind::Var(v)) => {
				if self.occurs(*v, k) {
					return Err(KindError::Infinite(*v, k.clone()));
				}
				self.map.insert(*v, k.clone());
				Ok(())
			}
			(Kind::Arrow(a1, b1), Kind::Arrow(a2, b2)) => {
				self.unify(a1, a2)?;
				self.unify(b1, b2)
			}
			_ => Err(KindError::Mismatch(a, b)),
		}
	}

	/// Resolve every remaining variable to `Type`.
	pub fn default_to_type(&self, k: &Kind) -> Kind {
		match self.apply(k) {
			Kind::Var(_) => Kind::Type,
			Kind::Arrow(a, b) => Kind::arrow(self.default_to_type(&a), self.default_to_type(&b)),
			other => other,
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	fn nat() -> Kind {
		Kind::Data("Nat".into())
	}

	#[test]
	fn unifies_arrows() {
		let mut s = KindSubst::new();
		let (a, b) = (s.fresh(), s.fresh());
		s.unify(
			&Kind::arrow(a.clone(), b.clone()),
			&Kind::arrow(nat(), Kind::Type),
		)
		.unwrap();
		assert_eq!(s.apply(&a), nat());
		assert_eq!(s.apply(&b), Kind::Type);
	}

	#[test]
	fn mismatch_and_occurs() {
		let mut s = KindSubst::new();
		assert!(matches!(
			s.unify(&Kind::Type, &nat()),
			Err(KindError::Mismatch(..))
		));
		let v = s.fresh();
		assert!(matches!(
			s.unify(&v, &Kind::arrow(v.clone(), Kind::Type)),
			Err(KindError::Infinite(..))
		));
	}

	#[test]
	fn defaults_to_type() {
		let mut s = KindSubst::new();
		let v = s.fresh();
		let k = Kind::arrow(v, Kind::Type);
		assert_eq!(s.default_to_type(&k), Kind::arity(1));
	}

	#[test]
	fn constructor_class_kind() {
		// Functor f: f : Type -> Type, inferred from `f a` with a : Type
		let mut s = KindSubst::new();
		let f = s.fresh();
		let r = s.fresh();
		s.unify(&f, &Kind::arrow(Kind::Type, r.clone())).unwrap();
		s.unify(&r, &Kind::Type).unwrap();
		assert_eq!(s.apply(&f), Kind::arity(1));
	}
}
