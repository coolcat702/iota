// Type-level computation
//
// This module is independent of `typechecker::Ty`: it works on a small term language (`Tm`)
// and the typechecker converts to and from it.
//   - `Poly`      polynomial normal form for type-level naturals. Atoms are type variables
//                 or stuck terms, all assumed >= 0. Ring identities hold by construction:
//                 `Add n m ~ Add m n`, `Mul n m ~ Mul m n`, `Add n 0 ~ n`.
//   - `solve`     one-unknown equations (`Add n 1 ~ 4` gives `n = 3`).
//   - `apart`     sound (but incomplete) impossibility test used for exhaustiveness pruning.
//   - `Reducer`   closed, ordered clauses (closed type families) with fuel, a depth bound and
//                 a memo table.
//   - `check_terminates`  structural-recursion check for user type functions.
//
// Everything here is pure and bounded: term counts, steps and depth all have caps.

#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;

/// Cap on the number of monomials in a polynomial
pub const MAX_TERMS: usize = 64;
pub const DEFAULT_FUEL: u64 = 10_000;
pub const DEFAULT_DEPTH: usize = 1_500;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NormError {
	TooManyTerms,
	Overflow,
}

impl fmt::Display for NormError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			NormError::TooManyTerms => write!(f, "type-level arithmetic expression is too large"),
			NormError::Overflow => write!(f, "type-level number is too large"),
		}
	}
}

// ---------------------------------------------------------------------------
// Polynomials
// ---------------------------------------------------------------------------

/// A product of atoms with exponents. The empty product is the constant `1`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Mono<K: Ord>(BTreeMap<K, u32>);

impl<K: Ord + Clone> Mono<K> {
	pub fn one() -> Self {
		Mono(BTreeMap::new())
	}

	pub fn atom(k: K) -> Self {
		let mut m = BTreeMap::new();
		m.insert(k, 1);
		Mono(m)
	}

	pub fn is_one(&self) -> bool {
		self.0.is_empty()
	}

	/// `(atom, exponent)` pairs, in a stable order.
	pub fn factors(&self) -> impl Iterator<Item = (&K, &u32)> {
		self.0.iter()
	}

	fn mul(&self, o: &Self) -> Result<Self, NormError> {
		let mut m = self.0.clone();
		for (k, e) in &o.0 {
			let slot = m.entry(k.clone()).or_insert(0);
			*slot = slot.checked_add(*e).ok_or(NormError::Overflow)?;
		}
		Ok(Mono(m))
	}

	fn without(&self, k: &K) -> Self {
		let mut m = self.0.clone();
		m.remove(k);
		Mono(m)
	}
}

/// `sum of coeff * monomial`, no zero coefficients. The constant is the coefficient of the
/// empty monomial.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Poly<K: Ord> {
	terms: BTreeMap<Mono<K>, i128>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sign {
	Zero,
	/// provably > 0
	Pos,
	/// provably < 0
	Neg,
	/// provably >= 0
	NonNeg,
	/// provably <= 0
	NonPos,
	Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Solve<K: Ord> {
	/// `0 = 0`.
	Trivial,
	/// No natural-number solution exists.
	Unsat,
	/// `atom := poly` (poly has only non-negative coefficients, so it is a natural).
	Solved(K, Poly<K>),
	/// More than one unknown or a non-linear equation: defer.
	Unsolved,
}

fn gcd(a: i128, b: i128) -> i128 {
	let (mut a, mut b) = (a.abs(), b.abs());
	while b != 0 {
		(a, b) = (b, a % b);
	}
	a
}

impl<K: Ord + Clone> Poly<K> {
	fn from_terms(mut terms: BTreeMap<Mono<K>, i128>) -> Result<Self, NormError> {
		terms.retain(|_, c| *c != 0);
		if terms.len() > MAX_TERMS {
			return Err(NormError::TooManyTerms);
		}
		Ok(Poly { terms })
	}

	pub fn zero() -> Self {
		Poly {
			terms: BTreeMap::new(),
		}
	}

	pub fn constant(c: i128) -> Self {
		let mut terms = BTreeMap::new();
		if c != 0 {
			terms.insert(Mono::one(), c);
		}
		Poly { terms }
	}

	pub fn lit(n: u64) -> Self {
		Self::constant(n as i128)
	}

	pub fn atom(k: K) -> Self {
		let mut terms = BTreeMap::new();
		terms.insert(Mono::atom(k), 1);
		Poly { terms }
	}

	pub fn is_zero(&self) -> bool {
		self.terms.is_empty()
	}

	/// `Some(c)` when the polynomial has no atoms.
	pub fn as_const(&self) -> Option<i128> {
		match self.terms.len() {
			0 => Some(0),
			1 => {
				let (m, c) = self.terms.iter().next().unwrap();
				m.is_one().then_some(*c)
			}
			_ => None,
		}
	}

	/// `Some(n)` when this is a literal natural that fits `u64`.
	pub fn as_lit(&self) -> Option<u64> {
		self.as_const().and_then(|c| u64::try_from(c).ok())
	}

	/// `Some(k)` when this is exactly one atom.
	pub fn as_atom(&self) -> Option<&K> {
		if self.terms.len() != 1 {
			return None;
		}
		let (m, c) = self.terms.iter().next().unwrap();
		if *c == 1 && m.0.len() == 1 {
			let (k, e) = m.0.iter().next().unwrap();
			if *e == 1 {
				return Some(k);
			}
		}
		None
	}

	pub fn const_term(&self) -> i128 {
		self.terms.get(&Mono::one()).copied().unwrap_or(0)
	}

	pub fn atoms(&self) -> BTreeSet<K> {
		self.terms
			.keys()
			.flat_map(|m| m.0.keys().cloned())
			.collect()
	}

	pub fn mentions(&self, k: &K) -> bool {
		self.terms.keys().any(|m| m.0.contains_key(k))
	}

	pub fn term_count(&self) -> usize {
		self.terms.len()
	}

	/// Iterate over `(monomial, coefficient)` for rendering.
	pub fn iter(&self) -> impl Iterator<Item = (&Mono<K>, &i128)> {
		self.terms.iter()
	}

	pub fn add(&self, o: &Self) -> Result<Self, NormError> {
		let mut t = self.terms.clone();
		for (m, c) in &o.terms {
			let slot = t.entry(m.clone()).or_insert(0);
			*slot = slot.checked_add(*c).ok_or(NormError::Overflow)?;
		}
		Self::from_terms(t)
	}

	pub fn neg(&self) -> Result<Self, NormError> {
		self.scale(-1)
	}

	pub fn sub(&self, o: &Self) -> Result<Self, NormError> {
		self.add(&o.neg()?)
	}

	pub fn scale(&self, k: i128) -> Result<Self, NormError> {
		let mut t = BTreeMap::new();
		for (m, c) in &self.terms {
			t.insert(m.clone(), c.checked_mul(k).ok_or(NormError::Overflow)?);
		}
		Self::from_terms(t)
	}

	pub fn mul(&self, o: &Self) -> Result<Self, NormError> {
		let mut t: BTreeMap<Mono<K>, i128> = BTreeMap::new();
		for (m1, c1) in &self.terms {
			for (m2, c2) in &o.terms {
				let m = m1.mul(m2)?;
				let c = c1.checked_mul(*c2).ok_or(NormError::Overflow)?;
				let slot = t.entry(m).or_insert(0);
				*slot = slot.checked_add(c).ok_or(NormError::Overflow)?;
			}
		}
		Self::from_terms(t)
	}

	fn pow(&self, e: u32) -> Result<Self, NormError> {
		let mut out = Self::constant(1);
		for _ in 0..e {
			out = out.mul(self)?;
		}
		Ok(out)
	}

	/// Replace atom `k` with `q`.
	pub fn subst(&self, k: &K, q: &Self) -> Result<Self, NormError> {
		let mut out = Self::zero();
		for (m, c) in &self.terms {
			match m.0.get(k) {
				None => {
					let mut one = BTreeMap::new();
					one.insert(m.clone(), *c);
					out = out.add(&Poly { terms: one })?;
				}
				Some(e) => {
					let mut rest = BTreeMap::new();
					rest.insert(m.without(k), *c);
					let term = Poly { terms: rest }.mul(&q.pow(*e)?)?;
					out = out.add(&term)?;
				}
			}
		}
		Ok(out)
	}

	/// What is provable about the value of the polynomial when every atom is >= 0.
	pub fn sign(&self) -> Sign {
		if self.terms.is_empty() {
			return Sign::Zero;
		}
		let all_nonneg = self.terms.values().all(|c| *c >= 0);
		let all_nonpos = self.terms.values().all(|c| *c <= 0);
		let k = self.const_term();
		if all_nonneg {
			if k > 0 { Sign::Pos } else { Sign::NonNeg }
		} else if all_nonpos {
			if k < 0 { Sign::Neg } else { Sign::NonPos }
		} else {
			Sign::Unknown
		}
	}

	/// Is every coefficient (constant included) non-negative? Such a polynomial is
	/// provably a natural number.
	pub fn is_natural(&self) -> bool {
		self.terms.values().all(|c| *c >= 0)
	}

	fn div_exact(&self, d: i128) -> Option<Self> {
		let mut t = BTreeMap::new();
		for (m, c) in &self.terms {
			if c % d != 0 {
				return None;
			}
			t.insert(m.clone(), c / d);
		}
		Some(Poly { terms: t })
	}

	/// Render with a caller-supplied atom printer: `2*n + m + 3`.
	pub fn render(&self, atom: &dyn Fn(&K) -> String) -> String {
		if self.terms.is_empty() {
			return "0".to_string();
		}
		// constant last, like the spec's examples
		let mut parts: Vec<String> = Vec::new();
		for (m, c) in self.terms.iter().filter(|(m, _)| !m.is_one()) {
			let mono: Vec<String> =
				m.0.iter()
					.map(|(k, e)| {
						if *e == 1 {
							atom(k)
						} else {
							format!("{}^{}", atom(k), e)
						}
					})
					.collect();
			let mono = mono.join("*");
			parts.push(match *c {
				1 => mono,
				-1 => format!("-{}", mono),
				c => format!("{}*{}", c, mono),
			});
		}
		let k = self.const_term();
		if k != 0 {
			parts.push(k.to_string());
		}
		parts.join(" + ").replace("+ -", "- ")
	}
}

/// Is `a ~ b` impossible for every assignment of naturals to the atoms?
pub fn poly_apart<K: Ord + Clone>(a: &Poly<K>, b: &Poly<K>) -> bool {
	let Ok(d) = a.sub(b) else {
		return false;
	};
	if d.is_zero() {
		return false;
	}
	if let Some(c) = d.as_const() {
		return c != 0;
	}
	if matches!(d.sign(), Sign::Pos | Sign::Neg) {
		return true;
	}
	// 2n ~ 1 has no integer solution at all
	let g = d
		.terms
		.iter()
		.filter(|(m, _)| !m.is_one())
		.fold(0, |g, (_, c)| gcd(g, *c));
	g > 1 && d.const_term() % g != 0
}

/// `a < b` as far as it is provable: `Some(true)`, `Some(false)` or undecided.
pub fn poly_lt<K: Ord + Clone>(a: &Poly<K>, b: &Poly<K>) -> Result<Option<bool>, NormError> {
	// a < b  <=>  b - a > 0
	let d = b.sub(a)?;
	Ok(match d.sign() {
		Sign::Pos => Some(true),
		// b - a <= 0 means a >= b
		Sign::Zero | Sign::NonPos | Sign::Neg => Some(false),
		_ => {
			// a - b >= 0 also decides it
			if matches!(a.sub(b)?.sign(), Sign::NonNeg | Sign::Pos) {
				Some(false)
			} else {
				None
			}
		}
	})
}

/// `a <= b` as far as it is provable.
pub fn poly_le<K: Ord + Clone>(a: &Poly<K>, b: &Poly<K>) -> Result<Option<bool>, NormError> {
	// a <= b  <=>  b - a >= 0 ; a > b  <=>  a - b > 0
	let d = b.sub(a)?;
	Ok(match d.sign() {
		Sign::Zero | Sign::NonNeg | Sign::Pos => Some(true),
		_ => {
			if matches!(a.sub(b)?.sign(), Sign::Pos) {
				Some(false)
			} else {
				None
			}
		}
	})
}

/// Solve `a ~ b` for one atom. `Add n 1 ~ 4` gives `n := 3`.
pub fn solve<K: Ord + Clone>(a: &Poly<K>, b: &Poly<K>) -> Result<Solve<K>, NormError> {
	let d = a.sub(b)?;
	if d.is_zero() {
		return Ok(Solve::Trivial);
	}
	if poly_apart(a, b) {
		return Ok(Solve::Unsat);
	}
	// candidates: atoms that occur only linearly and in exactly one monomial
	for k in d.atoms() {
		let Some(c) = d.terms.get(&Mono::atom(k.clone())).copied() else {
			continue;
		};
		let occurs_elsewhere = d
			.terms
			.keys()
			.any(|m| m.0.contains_key(&k) && *m != Mono::atom(k.clone()));
		if occurs_elsewhere {
			continue;
		}
		// d = c*k + rest = 0  =>  k = -rest / c
		let rest = d.sub(&Poly::atom(k.clone()).scale(c)?)?;
		let Some(value) = rest.scale(-1)?.div_exact(c) else {
			// c does not divide the rest: only a hard contradiction if rest is a constant
			if rest.as_const().is_some() {
				return Ok(Solve::Unsat);
			}
			continue;
		};
		if let Some(v) = value.as_const() {
			if v < 0 {
				return Ok(Solve::Unsat);
			}
		}
		if value.is_natural() {
			return Ok(Solve::Solved(k, value));
		}
	}
	Ok(Solve::Unsolved)
}

// ---------------------------------------------------------------------------
// Terms, patterns and type functions
// ---------------------------------------------------------------------------

pub const ZERO: &str = "Zero";
pub const SUCC: &str = "Succ";
pub const TRUE: &str = "True";
pub const FALSE: &str = "False";

/// The built-in type functions of They take priority over a user definition of the
/// same name.
pub const BUILTINS: &[(&str, usize)] = &[("Add", 2), ("Mul", 2), ("Sub", 2), ("Ls", 2), ("Lse", 2)];

pub fn builtin_arity(name: &str) -> Option<usize> {
	BUILTINS.iter().find(|(n, _)| *n == name).map(|(_, a)| *a)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Tm {
	/// A type-level natural in polynomial normal form (a literal when constant).
	Nat(Poly<usize>),
	/// Constructor-headed term (`Unit`, `Prod`, user data). `Zero` and `Succ` are folded
	/// into `Nat` by `Reducer::reduce`.
	Con(String, Vec<Tm>),
	/// Saturated application of a type function.
	App(String, Vec<Tm>),
	/// A rigid variable or unsolved unification variable.
	Atom(usize),
	/// A clause-local variable. Only appears in clause right-hand sides.
	PVar(usize),
}

impl Tm {
	pub fn lit(n: u64) -> Tm {
		Tm::Nat(Poly::lit(n))
	}
	pub fn con(name: &str, args: Vec<Tm>) -> Tm {
		Tm::Con(name.to_string(), args)
	}
	pub fn app(name: &str, args: Vec<Tm>) -> Tm {
		Tm::App(name.to_string(), args)
	}
	pub fn succ(t: Tm) -> Tm {
		Tm::Con(SUCC.to_string(), vec![t])
	}
	pub fn zero() -> Tm {
		Tm::Con(ZERO.to_string(), vec![])
	}

	/// View a term as a natural-number polynomial, if it is one.
	pub fn as_poly(&self) -> Option<Poly<usize>> {
		match self {
			Tm::Nat(p) => Some(p.clone()),
			Tm::Atom(k) => Some(Poly::atom(*k)),
			Tm::Con(n, a) if n == ZERO && a.is_empty() => Some(Poly::zero()),
			Tm::Con(n, a) if n == SUCC && a.len() == 1 => {
				a[0].as_poly()?.add(&Poly::constant(1)).ok()
			}
			_ => None,
		}
	}

	fn subst_pvars(&self, binds: &HashMap<usize, Tm>) -> Tm {
		match self {
			Tm::PVar(v) => binds.get(v).cloned().unwrap_or_else(|| self.clone()),
			Tm::Con(n, a) => Tm::Con(n.clone(), a.iter().map(|t| t.subst_pvars(binds)).collect()),
			Tm::App(n, a) => Tm::App(n.clone(), a.iter().map(|t| t.subst_pvars(binds)).collect()),
			o => o.clone(),
		}
	}

	/// Replace atom `k` by `by` everywhere (used to apply a solved unknown).
	pub fn subst_atom(&self, k: usize, by: &Tm) -> Tm {
		match self {
			Tm::Atom(j) if *j == k => by.clone(),
			Tm::Nat(p) if p.mentions(&k) => match by.as_poly() {
				Some(q) => p
					.subst(&k, &q)
					.map(Tm::Nat)
					.unwrap_or_else(|_| self.clone()),
				None => self.clone(),
			},
			Tm::Con(n, a) => Tm::Con(n.clone(), a.iter().map(|t| t.subst_atom(k, by)).collect()),
			Tm::App(n, a) => Tm::App(n.clone(), a.iter().map(|t| t.subst_atom(k, by)).collect()),
			o => o.clone(),
		}
	}

	pub fn render(&self, atom: &dyn Fn(usize) -> String) -> String {
		match self {
			Tm::Nat(p) => p.render(&|k| atom(*k)),
			Tm::Atom(k) => atom(*k),
			Tm::PVar(v) => format!("%{}", v),
			Tm::Con(n, a) | Tm::App(n, a) => {
				if a.is_empty() {
					n.clone()
				} else {
					let args: Vec<String> = a
						.iter()
						.map(|t| {
							let s = t.render(atom);
							if matches!(t, Tm::Con(_, v) | Tm::App(_, v) if !v.is_empty())
								|| matches!(t, Tm::Nat(p) if p.as_lit().is_none() && p.as_atom().is_none())
							{
								format!("({})", s)
							} else {
								s
							}
						})
						.collect();
					format!("{} {}", n, args.join(" "))
				}
			}
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pat {
	Wild,
	Var(usize),
	Con(String, Vec<Pat>),
	/// A natural-number literal pattern.
	Lit(u64),
}

impl Pat {
	pub fn con(name: &str, args: Vec<Pat>) -> Pat {
		Pat::Con(name.to_string(), args)
	}
	pub fn succ(p: Pat) -> Pat {
		Pat::Con(SUCC.to_string(), vec![p])
	}
	pub fn zero() -> Pat {
		Pat::Con(ZERO.to_string(), vec![])
	}

	fn vars(&self, out: &mut Vec<usize>) {
		match self {
			Pat::Var(v) => out.push(*v),
			Pat::Con(_, ps) => ps.iter().for_each(|p| p.vars(out)),
			Pat::Wild | Pat::Lit(_) => {}
		}
	}

	/// Variables strictly below a constructor: structurally smaller than the scrutinee.
	fn sub_vars(&self, depth: usize, out: &mut BTreeSet<usize>) {
		match self {
			Pat::Var(v) if depth > 0 => {
				out.insert(*v);
			}
			Pat::Con(_, ps) => ps.iter().for_each(|p| p.sub_vars(depth + 1, out)),
			_ => {}
		}
	}
}

#[derive(Debug, Clone)]
pub struct Clause {
	pub pats: Vec<Pat>,
	pub rhs: Tm,
}

#[derive(Debug, Clone)]
pub struct Func {
	pub name: String,
	pub arity: usize,
	pub clauses: Vec<Clause>,
}

#[derive(Debug, Clone, Default)]
pub struct Defs {
	pub funcs: HashMap<String, Func>,
}

impl Defs {
	pub fn new() -> Self {
		Self::default()
	}

	/// Add a function after validating it. A user definition that shadows a built-in is
	/// accepted but never consulted (the built-in takes priority).
	pub fn add(&mut self, f: Func) -> Result<(), String> {
		check_wellformed(&f)?;
		check_terminates(&f)?;
		self.funcs.insert(f.name.clone(), f);
		Ok(())
	}
}

fn rhs_pvars(t: &Tm, out: &mut BTreeSet<usize>) {
	match t {
		Tm::PVar(v) => {
			out.insert(*v);
		}
		Tm::Con(_, a) | Tm::App(_, a) => a.iter().for_each(|t| rhs_pvars(t, out)),
		_ => {}
	}
}

/// Arity of every clause, linear patterns, no unbound variables on the right.
pub fn check_wellformed(f: &Func) -> Result<(), String> {
	if f.clauses.is_empty() {
		return Err(format!("type function `{}` has no clauses", f.name));
	}
	for (i, c) in f.clauses.iter().enumerate() {
		if c.pats.len() != f.arity {
			return Err(format!(
				"clause {} of `{}` has {} patterns, expected {}",
				i + 1,
				f.name,
				c.pats.len(),
				f.arity
			));
		}
		let mut vs = Vec::new();
		c.pats.iter().for_each(|p| p.vars(&mut vs));
		let set: BTreeSet<usize> = vs.iter().copied().collect();
		if set.len() != vs.len() {
			return Err(format!(
				"clause {} of `{}` repeats a pattern variable",
				i + 1,
				f.name
			));
		}
		let mut used = BTreeSet::new();
		rhs_pvars(&c.rhs, &mut used);
		if let Some(v) = used.iter().find(|v| !set.contains(v)) {
			return Err(format!(
				"clause {} of `{}` uses an unbound variable (%{})",
				i + 1,
				f.name,
				v
			));
		}
	}
	Ok(())
}

fn collect_calls<'a>(t: &'a Tm, name: &str, out: &mut Vec<&'a [Tm]>) {
	match t {
		Tm::App(n, a) => {
			if n == name {
				out.push(a);
			}
			a.iter().for_each(|t| collect_calls(t, name, out));
		}
		Tm::Con(_, a) => a.iter().for_each(|t| collect_calls(t, name, out)),
		_ => {}
	}
}

/// termination: every recursive call must be structurally smaller in at least one
/// argument. (The global fuel is the backstop for everything this does not catch.)
pub fn check_terminates(f: &Func) -> Result<(), String> {
	for (i, c) in f.clauses.iter().enumerate() {
		let subs: Vec<BTreeSet<usize>> = c
			.pats
			.iter()
			.map(|p| {
				let mut s = BTreeSet::new();
				p.sub_vars(0, &mut s);
				s
			})
			.collect();
		let mut calls = Vec::new();
		collect_calls(&c.rhs, &f.name, &mut calls);
		for args in calls {
			let smaller = args.len() == f.arity
				&& args
					.iter()
					.enumerate()
					.any(|(pos, a)| matches!(a, Tm::PVar(v) if subs[pos].contains(v)));
			if !smaller {
				return Err(format!(
					"recursive call in clause {} of `{}` is not structurally smaller in any argument",
					i + 1,
					f.name
				));
			}
		}
	}
	Ok(())
}

// ---------------------------------------------------------------------------
// Reduction
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReduceError {
	/// The global fuel ran out. `trace` holds the most recent reductions.
	OutOfFuel {
		fuel: u64,
		trace: Vec<String>,
	},
	TooDeep {
		depth: usize,
		trace: Vec<String>,
	},
	Norm(NormError),
}

impl fmt::Display for ReduceError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			ReduceError::OutOfFuel { fuel, trace } => {
				write!(
					f,
					"type-level computation ran out of fuel after {} reductions (raise it with --type-fuel)",
					fuel
				)?;
				for t in trace {
					write!(f, "\n  {}", t)?;
				}
				Ok(())
			}
			ReduceError::TooDeep { depth, trace } => {
				write!(f, "type-level computation nested deeper than {}", depth)?;
				for t in trace {
					write!(f, "\n  {}", t)?;
				}
				Ok(())
			}
			ReduceError::Norm(e) => write!(f, "{}", e),
		}
	}
}

impl From<NormError> for ReduceError {
	fn from(e: NormError) -> Self {
		ReduceError::Norm(e)
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum M {
	Yes,
	/// provably apart from the pattern
	No,
	Stuck,
}

fn both(a: M, b: M) -> M {
	match (a, b) {
		(M::No, _) | (_, M::No) => M::No,
		(M::Stuck, _) | (_, M::Stuck) => M::Stuck,
		_ => M::Yes,
	}
}

pub struct Reducer<'a> {
	defs: &'a Defs,
	max_fuel: u64,
	fuel: u64,
	max_depth: usize,
	depth: usize,
	memo: HashMap<(String, Vec<Tm>), Tm>,
	trace: std::collections::VecDeque<String>,
}

const TRACE_LEN: usize = 12;

impl<'a> Reducer<'a> {
	pub fn new(defs: &'a Defs, fuel: u64) -> Self {
		Reducer {
			defs,
			max_fuel: fuel,
			fuel,
			max_depth: DEFAULT_DEPTH,
			depth: 0,
			memo: HashMap::new(),
			trace: std::collections::VecDeque::new(),
		}
	}

	pub fn with_depth(mut self, d: usize) -> Self {
		self.max_depth = d;
		self
	}

	/// Reductions performed so far.
	pub fn steps(&self) -> u64 {
		self.max_fuel - self.fuel
	}

	fn note(&mut self, s: String) {
		if self.trace.len() == TRACE_LEN {
			self.trace.pop_front();
		}
		self.trace.push_back(s);
	}

	fn trace_vec(&self) -> Vec<String> {
		self.trace.iter().cloned().collect()
	}

	fn tick(&mut self) -> Result<(), ReduceError> {
		if self.fuel == 0 {
			return Err(ReduceError::OutOfFuel {
				fuel: self.max_fuel,
				trace: self.trace_vec(),
			});
		}
		self.fuel -= 1;
		Ok(())
	}

	/// Normalize completely. Stuck applications stay as `Tm::App`.
	pub fn reduce(&mut self, t: &Tm) -> Result<Tm, ReduceError> {
		if self.depth >= self.max_depth {
			return Err(ReduceError::TooDeep {
				depth: self.max_depth,
				trace: self.trace_vec(),
			});
		}
		self.depth += 1;
		let r = self.reduce_inner(t);
		self.depth -= 1;
		r
	}

	fn reduce_inner(&mut self, t: &Tm) -> Result<Tm, ReduceError> {
		match t {
			Tm::Nat(_) | Tm::Atom(_) | Tm::PVar(_) => Ok(t.clone()),
			Tm::Con(n, args) => {
				let args = args
					.iter()
					.map(|a| self.reduce(a))
					.collect::<Result<Vec<_>, _>>()?;
				let c = Tm::Con(n.clone(), args);
				// fold Zero / Succ chains into the polynomial form
				if (n == ZERO || n == SUCC)
					&& let Some(p) = c.as_poly()
				{
					return Ok(Tm::Nat(p));
				}
				Ok(c)
			}
			Tm::App(f, args) => {
				let args = args
					.iter()
					.map(|a| self.reduce(a))
					.collect::<Result<Vec<_>, _>>()?;
				self.apply(f, args)
			}
		}
	}

	fn apply(&mut self, f: &str, args: Vec<Tm>) -> Result<Tm, ReduceError> {
		if let Some(arity) = builtin_arity(f) {
			if args.len() == arity {
				return self.builtin(f, args);
			}
			return Ok(Tm::App(f.to_string(), args));
		}
		let Some(func) = self.defs.funcs.get(f) else {
			return Ok(Tm::App(f.to_string(), args));
		};
		if func.arity != args.len() {
			return Ok(Tm::App(f.to_string(), args));
		}
		let key = (f.to_string(), args);
		if let Some(r) = self.memo.get(&key) {
			return Ok(r.clone());
		}
		let (f, args) = key;
		let func = &self.defs.funcs[&f];
		for (ci, clause) in func.clauses.iter().enumerate() {
			let mut binds: HashMap<usize, Tm> = HashMap::new();
			let mut res = M::Yes;
			for (p, a) in clause.pats.iter().zip(&args) {
				res = both(res, match_pat(p, a, &mut binds));
			}
			match res {
				M::No => continue,
				// an earlier clause might still apply: the application is stuck
				M::Stuck => {
					let stuck = Tm::App(f.clone(), args.clone());
					self.memo.insert((f, args), stuck.clone());
					return Ok(stuck);
				}
				M::Yes => {
					self.tick()?;
					let rhs = clause.rhs.subst_pvars(&binds);
					self.note(format!(
						"{} => clause {}",
						Tm::App(f.clone(), args.clone()).render(&|k| format!("?{}", k)),
						ci + 1
					));
					let out = self.reduce(&rhs)?;
					self.memo.insert((f, args), out.clone());
					return Ok(out);
				}
			}
		}
		// no clause applies at all: stuck
		let stuck = Tm::App(f.clone(), args.clone());
		self.memo.insert((f, args), stuck.clone());
		Ok(stuck)
	}

	fn builtin(&mut self, f: &str, args: Vec<Tm>) -> Result<Tm, ReduceError> {
		let stuck = |args: Vec<Tm>| Ok(Tm::App(f.to_string(), args));
		let (Some(a), Some(b)) = (args[0].as_poly(), args[1].as_poly()) else {
			return stuck(args);
		};
		self.tick()?;
		match f {
			"Add" => Ok(Tm::Nat(a.add(&b)?)),
			"Mul" => Ok(Tm::Nat(a.mul(&b)?)),
			// reduces only when a >= b is provable
			"Sub" => {
				let d = a.sub(&b)?;
				if d.is_natural() {
					Ok(Tm::Nat(d))
				} else {
					stuck(args)
				}
			}
			"Ls" | "Lse" => {
				let decided = if f == "Ls" {
					poly_lt(&a, &b)?
				} else {
					poly_le(&a, &b)?
				};
				if let Some(v) = decided {
					return Ok(bool_tm(v));
				}
				// undecided: `Ls (x + 2) (y + 1)` is `Ls (x + 1) y`; cancel the common constant
				let m = a.const_term().min(b.const_term());
				if m > 0 {
					let c = Poly::constant(m);
					return Ok(Tm::App(
						f.to_string(),
						vec![Tm::Nat(a.sub(&c)?), Tm::Nat(b.sub(&c)?)],
					));
				}
				stuck(args)
			}
			_ => stuck(args),
		}
	}
}

fn bool_tm(b: bool) -> Tm {
	Tm::Con(if b { TRUE } else { FALSE }.to_string(), vec![])
}

fn match_pat(p: &Pat, t: &Tm, binds: &mut HashMap<usize, Tm>) -> M {
	match p {
		Pat::Wild => M::Yes,
		Pat::Var(v) => {
			binds.insert(*v, t.clone());
			M::Yes
		}
		Pat::Lit(n) => match t.as_poly() {
			Some(q) => match_nat(&q, &Poly::lit(*n)),
			None => M::Stuck,
		},
		Pat::Con(c, ps) if c == ZERO && ps.is_empty() => match t.as_poly() {
			Some(q) => match_nat(&q, &Poly::zero()),
			None => M::Stuck,
		},
		Pat::Con(c, ps) if c == SUCC && ps.len() == 1 => match t.as_poly() {
			Some(q) => {
				if q.is_natural() && q.const_term() >= 1 {
					// n + 1 = Succ n
					let pred = q
						.sub(&Poly::constant(1))
						.expect("subtracting 1 cannot overflow");
					match_pat(&ps[0], &Tm::Nat(pred), binds)
				} else if q.is_zero() {
					M::No
				} else {
					M::Stuck
				}
			}
			None => M::Stuck,
		},
		Pat::Con(c, ps) => match t {
			Tm::Con(d, args) => {
				if c != d || ps.len() != args.len() {
					return M::No;
				}
				ps.iter()
					.zip(args)
					.fold(M::Yes, |acc, (p, a)| both(acc, match_pat(p, a, binds)))
			}
			_ => M::Stuck,
		},
	}
}

fn match_nat(q: &Poly<usize>, lit: &Poly<usize>) -> M {
	if q == lit {
		M::Yes
	} else if poly_apart(q, lit) {
		M::No
	} else {
		M::Stuck
	}
}

/// Are two *normalized* terms provably different for every instantiation of their atoms?
/// Conservative: `false` means "maybe equal". Used for exhaustiveness pruning, where
/// a wrong `true` becomes a runtime abort, so doubt always answers `false`.
pub fn apart(a: &Tm, b: &Tm) -> bool {
	if let (Some(p), Some(q)) = (a.as_poly(), b.as_poly()) {
		return poly_apart(&p, &q);
	}
	match (a, b) {
		(Tm::Con(n1, a1), Tm::Con(n2, a2)) => {
			n1 != n2 || a1.len() != a2.len() || a1.iter().zip(a2).any(|(x, y)| apart(x, y))
		}
		_ => false,
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	type P = Poly<usize>;

	fn n(k: usize) -> P {
		P::atom(k)
	}

	#[test]
	fn ring_identities() {
		let (a, b) = (n(0), n(1));
		assert_eq!(a.add(&b).unwrap(), b.add(&a).unwrap());
		assert_eq!(a.mul(&b).unwrap(), b.mul(&a).unwrap());
		assert_eq!(a.add(&P::zero()).unwrap(), a);
		assert_eq!(a.mul(&P::lit(1)).unwrap(), a);
		// distributivity
		let l = a.mul(&b.add(&P::lit(2)).unwrap()).unwrap();
		let r = a.mul(&b).unwrap().add(&a.scale(2).unwrap()).unwrap();
		assert_eq!(l, r);
		// (n + 1) - 1 = n
		assert_eq!(a.add(&P::lit(1)).unwrap().sub(&P::lit(1)).unwrap(), a);
	}

	#[test]
	fn signs() {
		assert_eq!(n(0).add(&P::lit(1)).unwrap().sign(), Sign::Pos);
		assert_eq!(n(0).sign(), Sign::NonNeg);
		assert_eq!(n(0).sub(&P::lit(1)).unwrap().sign(), Sign::Unknown);
		assert_eq!(P::lit(3).neg().unwrap().sign(), Sign::Neg);
		assert_eq!(P::zero().sign(), Sign::Zero);
	}

	#[test]
	fn apartness_is_sound_and_conservative() {
		// n + 1 vs 0: apart
		assert!(poly_apart(&n(0).add(&P::lit(1)).unwrap(), &P::zero()));
		// n vs n + 1: apart
		assert!(poly_apart(&n(0), &n(0).add(&P::lit(1)).unwrap()));
		// 3 vs 4
		assert!(poly_apart(&P::lit(3), &P::lit(4)));
		// n vs 0: may be equal
		assert!(!poly_apart(&n(0), &P::zero()));
		// n + m vs 0: may be equal (both zero)
		assert!(!poly_apart(&n(0).add(&n(1)).unwrap(), &P::zero()));
		// n vs m: may be equal
		assert!(!poly_apart(&n(0), &n(1)));
		// 2n vs 1: no integer solution
		assert!(poly_apart(&n(0).scale(2).unwrap(), &P::lit(1)));
		// 2n vs 4: n = 2 works
		assert!(!poly_apart(&n(0).scale(2).unwrap(), &P::lit(4)));
	}

	// the apartness test against brute force: whenever it answers "apart", no assignment of
	// small naturals may make the two sides equal
	#[test]
	fn apartness_brute_force() {
		let polys: Vec<P> = {
			let mut v = vec![P::zero(), P::lit(1), P::lit(2), P::lit(5)];
			for k in 0..2 {
				v.push(n(k));
				v.push(n(k).add(&P::lit(1)).unwrap());
				v.push(n(k).scale(2).unwrap());
				v.push(n(k).scale(2).unwrap().add(&P::lit(1)).unwrap());
			}
			v.push(n(0).add(&n(1)).unwrap());
			v.push(n(0).mul(&n(1)).unwrap());
			v.push(n(0).mul(&n(0)).unwrap().add(&P::lit(1)).unwrap());
			v
		};
		fn eval(p: &P, env: &[i128; 2]) -> i128 {
			let mut total = 0i128;
			for (m, c) in p.iter() {
				let mut t = *c;
				for (k, e) in m.0.iter() {
					t *= env[*k].pow(*e);
				}
				total += t;
			}
			total
		}
		for a in &polys {
			for b in &polys {
				if poly_apart(a, b) {
					for x in 0..8 {
						for y in 0..8 {
							let env = [x, y];
							assert_ne!(
								eval(a, &env),
								eval(b, &env),
								"claimed apart but equal at {:?}: {:?} vs {:?}",
								env,
								a,
								b
							);
						}
					}
				}
			}
		}
	}

	#[test]
	fn solves_one_unknown() {
		// Add n 1 ~ 4  =>  n = 3
		let lhs = n(0).add(&P::lit(1)).unwrap();
		assert_eq!(
			solve(&lhs, &P::lit(4)).unwrap(),
			Solve::Solved(0, P::lit(3))
		);
		// 2n ~ 6 => n = 3
		assert_eq!(
			solve(&n(0).scale(2).unwrap(), &P::lit(6)).unwrap(),
			Solve::Solved(0, P::lit(3))
		);
		// n + 1 ~ 0 has no solution
		assert_eq!(solve(&lhs, &P::zero()).unwrap(), Solve::Unsat);
		// n ~ m + 2 => n = m + 2 (first atom wins, both are fine)
		match solve(&n(0), &n(1).add(&P::lit(2)).unwrap()).unwrap() {
			Solve::Solved(k, v) => {
				assert_eq!(k, 0);
				assert_eq!(v, n(1).add(&P::lit(2)).unwrap());
			}
			o => panic!("{:?}", o),
		}
		// x ~ x
		assert_eq!(solve(&n(0), &n(0)).unwrap(), Solve::Trivial);
		// x*y ~ 6: nonlinear, deferred
		assert_eq!(
			solve(&n(0).mul(&n(1)).unwrap(), &P::lit(6)).unwrap(),
			Solve::Unsolved
		);
		// 2n ~ 5: no integer solution
		assert_eq!(
			solve(&n(0).scale(2).unwrap(), &P::lit(5)).unwrap(),
			Solve::Unsat
		);
	}

	#[test]
	fn term_cap() {
		// (a0 + a1 + ... + a9)^3 has 220 monomials
		let mut p = P::zero();
		for k in 0..10 {
			p = p.add(&n(k)).unwrap();
		}
		let sq = p.mul(&p).unwrap(); // 55 terms: still fine
		assert!(sq.term_count() <= MAX_TERMS);
		assert_eq!(sq.mul(&p), Err(NormError::TooManyTerms));
	}

	#[test]
	fn overflow_is_an_error_not_a_wrap() {
		let big = P::constant(i128::MAX);
		assert_eq!(big.add(&P::lit(1)), Err(NormError::Overflow));
		assert_eq!(big.mul(&P::lit(2)), Err(NormError::Overflow));
	}

	#[test]
	fn comparisons() {
		assert_eq!(poly_lt(&P::lit(1), &P::lit(2)).unwrap(), Some(true));
		assert_eq!(poly_lt(&P::lit(2), &P::lit(2)).unwrap(), Some(false));
		assert_eq!(poly_le(&P::lit(2), &P::lit(2)).unwrap(), Some(true));
		// n < n + 1
		assert_eq!(
			poly_lt(&n(0), &n(0).add(&P::lit(1)).unwrap()).unwrap(),
			Some(true)
		);
		// n < 3: undecided
		assert_eq!(poly_lt(&n(0), &P::lit(3)).unwrap(), None);
		// 0 <= n
		assert_eq!(poly_le(&P::zero(), &n(0)).unwrap(), Some(true));
		// n + 1 <= n is false
		assert_eq!(
			poly_le(&n(0).add(&P::lit(1)).unwrap(), &n(0)).unwrap(),
			Some(false)
		);
	}

	fn defs() -> Defs {
		// type Add n m = match Zero, m -> m ; Succ n, m -> Succ (Add n m)
		let add = Func {
			name: "MyAdd".into(),
			arity: 2,
			clauses: vec![
				Clause {
					pats: vec![Pat::zero(), Pat::Var(0)],
					rhs: Tm::PVar(0),
				},
				Clause {
					pats: vec![Pat::succ(Pat::Var(0)), Pat::Var(1)],
					rhs: Tm::succ(Tm::app("MyAdd", vec![Tm::PVar(0), Tm::PVar(1)])),
				},
			],
		};
		// type Tuple n a = match Zero, _ -> Unit ; Succ k, a -> a * Tuple k a
		let tuple = Func {
			name: "Tuple".into(),
			arity: 2,
			clauses: vec![
				Clause {
					pats: vec![Pat::zero(), Pat::Wild],
					rhs: Tm::con("Unit", vec![]),
				},
				Clause {
					pats: vec![Pat::succ(Pat::Var(0)), Pat::Var(1)],
					rhs: Tm::con(
						"Prod",
						vec![
							Tm::PVar(1),
							Tm::app("Tuple", vec![Tm::PVar(0), Tm::PVar(1)]),
						],
					),
				},
			],
		};
		let mut d = Defs::new();
		d.add(add).unwrap();
		d.add(tuple).unwrap();
		d
	}

	#[test]
	fn builtins_reduce() {
		let d = Defs::new();
		let mut r = Reducer::new(&d, 100);
		assert_eq!(
			r.reduce(&Tm::app("Add", vec![Tm::lit(2), Tm::lit(3)]))
				.unwrap(),
			Tm::lit(5)
		);
		assert_eq!(
			r.reduce(&Tm::app("Mul", vec![Tm::lit(4), Tm::lit(3)]))
				.unwrap(),
			Tm::lit(12)
		);
		// Add n 0 ~ n
		assert_eq!(
			r.reduce(&Tm::app("Add", vec![Tm::Atom(7), Tm::lit(0)]))
				.unwrap(),
			Tm::Nat(P::atom(7))
		);
		// Add n m ~ Add m n
		let a = r
			.reduce(&Tm::app("Add", vec![Tm::Atom(1), Tm::Atom(2)]))
			.unwrap();
		let b = r
			.reduce(&Tm::app("Add", vec![Tm::Atom(2), Tm::Atom(1)]))
			.unwrap();
		assert_eq!(a, b);
		// Sub only reduces when provable
		assert_eq!(
			r.reduce(&Tm::app("Sub", vec![Tm::lit(5), Tm::lit(2)]))
				.unwrap(),
			Tm::lit(3)
		);
		let stuck = Tm::app("Sub", vec![Tm::Atom(0), Tm::lit(1)]);
		assert_eq!(r.reduce(&stuck).unwrap(), stuck);
		assert_eq!(
			r.reduce(&Tm::app(
				"Sub",
				vec![Tm::Nat(P::atom(0).add(&P::lit(2)).unwrap()), Tm::lit(1)]
			))
			.unwrap(),
			Tm::Nat(P::atom(0).add(&P::lit(1)).unwrap())
		);
		// Ls / Lse
		assert_eq!(
			r.reduce(&Tm::app("Ls", vec![Tm::lit(1), Tm::lit(2)]))
				.unwrap(),
			Tm::con(TRUE, vec![])
		);
		assert_eq!(
			r.reduce(&Tm::app("Lse", vec![Tm::lit(3), Tm::lit(2)]))
				.unwrap(),
			Tm::con(FALSE, vec![])
		);
		// a common constant cancels: Ls (x + 1) (y + 1) = Ls x y
		let shifted = Tm::app("Ls", vec![Tm::succ(Tm::Atom(0)), Tm::succ(Tm::Atom(1))]);
		assert_eq!(
			r.reduce(&shifted).unwrap(),
			Tm::App("Ls".into(), vec![Tm::Nat(P::atom(0)), Tm::Nat(P::atom(1))])
		);
		let undecided = Tm::app("Ls", vec![Tm::Atom(0), Tm::lit(2)]);
		assert_eq!(r.reduce(&undecided).unwrap(), undecided);
	}

	#[test]
	fn zero_and_succ_fold_into_literals() {
		let d = Defs::new();
		let mut r = Reducer::new(&d, 100);
		let three = Tm::succ(Tm::succ(Tm::succ(Tm::zero())));
		assert_eq!(r.reduce(&three).unwrap(), Tm::lit(3));
		assert_eq!(
			r.reduce(&Tm::succ(Tm::Atom(0))).unwrap(),
			Tm::Nat(P::atom(0).add(&P::lit(1)).unwrap())
		);
	}

	#[test]
	fn user_function_on_literals_and_variables() {
		let d = defs();
		let mut r = Reducer::new(&d, 1000);
		assert_eq!(
			r.reduce(&Tm::app("MyAdd", vec![Tm::lit(3), Tm::lit(4)]))
				.unwrap(),
			Tm::lit(7)
		);
		// MyAdd (n + 2) m  ->  Succ (Succ (MyAdd n m)): the recursion on the first argument
		// gets stuck at the variable, leaving a normalized remainder
		let t = r
			.reduce(&Tm::app(
				"MyAdd",
				vec![Tm::Nat(P::atom(0).add(&P::lit(2)).unwrap()), Tm::Atom(1)],
			))
			.unwrap();
		match &t {
			Tm::Nat(p) => {
				// Succ(Succ(stuck)) where the stuck term is an atom-like App: it was folded
				// only if as_poly succeeds, which it cannot for an App
				panic!("unexpected nat {:?}", p)
			}
			Tm::Con(s, a) => {
				assert_eq!(s, SUCC);
				assert!(matches!(&a[0], Tm::Con(s2, _) if s2 == SUCC));
			}
			o => panic!("{:?}", o),
		}
		// MyAdd n m with n a variable is stuck
		let stuck = Tm::app("MyAdd", vec![Tm::Atom(0), Tm::Atom(1)]);
		assert_eq!(r.reduce(&stuck).unwrap(), stuck);
	}

	#[test]
	fn tuple_computes_a_type() {
		let d = defs();
		let mut r = Reducer::new(&d, 1000);
		let t = r
			.reduce(&Tm::app("Tuple", vec![Tm::lit(2), Tm::con("Int", vec![])]))
			.unwrap();
		let int = Tm::con("Int", vec![]);
		let want = Tm::con(
			"Prod",
			vec![
				int.clone(),
				Tm::con("Prod", vec![int.clone(), Tm::con("Unit", vec![])]),
			],
		);
		assert_eq!(t, want);
	}

	#[test]
	fn closed_clauses_wait_for_earlier_ones() {
		// f Zero -> A ; f n -> B   with n a variable: the first clause is not provably
		// apart, so f n must stay stuck rather than pick B
		let f = Func {
			name: "F".into(),
			arity: 1,
			clauses: vec![
				Clause {
					pats: vec![Pat::zero()],
					rhs: Tm::con("A", vec![]),
				},
				Clause {
					pats: vec![Pat::Var(0)],
					rhs: Tm::con("B", vec![]),
				},
			],
		};
		let mut d = Defs::new();
		d.add(f).unwrap();
		let mut r = Reducer::new(&d, 100);
		let stuck = Tm::app("F", vec![Tm::Atom(0)]);
		assert_eq!(r.reduce(&stuck).unwrap(), stuck);
		// n + 1 is provably not Zero, so the second clause fires
		assert_eq!(
			r.reduce(&Tm::app(
				"F",
				vec![Tm::Nat(P::atom(0).add(&P::lit(1)).unwrap())]
			))
			.unwrap(),
			Tm::con("B", vec![])
		);
		assert_eq!(
			r.reduce(&Tm::app("F", vec![Tm::lit(0)])).unwrap(),
			Tm::con("A", vec![])
		);
	}

	#[test]
	fn rejects_non_structural_recursion() {
		let bad = Func {
			name: "Loop".into(),
			arity: 1,
			clauses: vec![Clause {
				pats: vec![Pat::Var(0)],
				rhs: Tm::app("Loop", vec![Tm::PVar(0)]),
			}],
		};
		assert!(check_terminates(&bad).is_err());
		let also_bad = Func {
			name: "Grow".into(),
			arity: 1,
			clauses: vec![Clause {
				pats: vec![Pat::Var(0)],
				rhs: Tm::app("Grow", vec![Tm::succ(Tm::PVar(0))]),
			}],
		};
		assert!(check_terminates(&also_bad).is_err());
		assert!(Defs::new().add(bad).is_err());
		// structural recursion is accepted
		assert!(check_terminates(&defs().funcs["MyAdd"]).is_ok());
	}

	#[test]
	fn wellformedness() {
		let unbound = Func {
			name: "U".into(),
			arity: 1,
			clauses: vec![Clause {
				pats: vec![Pat::Wild],
				rhs: Tm::PVar(3),
			}],
		};
		assert!(check_wellformed(&unbound).is_err());
		let nonlinear = Func {
			name: "N".into(),
			arity: 2,
			clauses: vec![Clause {
				pats: vec![Pat::Var(0), Pat::Var(0)],
				rhs: Tm::PVar(0),
			}],
		};
		assert!(check_wellformed(&nonlinear).is_err());
	}

	#[test]
	fn fuel_exhaustion_is_a_diagnostic_not_a_hang() {
		// Not structural, so `Defs::add` would reject it; insert it directly to exercise the
		// backstop, the way a bug in the termination check would.
		let mut d = Defs::new();
		d.funcs.insert(
			"Loop".into(),
			Func {
				name: "Loop".into(),
				arity: 1,
				clauses: vec![Clause {
					pats: vec![Pat::Var(0)],
					rhs: Tm::app("Loop", vec![Tm::succ(Tm::PVar(0))]),
				}],
			},
		);
		let mut r = Reducer::new(&d, 50);
		match r.reduce(&Tm::app("Loop", vec![Tm::lit(0)])) {
			Err(ReduceError::OutOfFuel { fuel, trace }) => {
				assert_eq!(fuel, 50);
				assert!(!trace.is_empty());
			}
			Err(ReduceError::TooDeep { .. }) => {} // the depth bound may trip first
			o => panic!("expected fuel or depth error, got {:?}", o),
		}
	}

	#[test]
	fn depth_bound_protects_the_stack() {
		let d = defs();
		let mut r = Reducer::new(&d, 1_000_000).with_depth(100);
		match r.reduce(&Tm::app("MyAdd", vec![Tm::lit(5000), Tm::lit(1)])) {
			Err(ReduceError::TooDeep { .. }) | Err(ReduceError::OutOfFuel { .. }) => {}
			o => panic!("{:?}", o),
		}
	}

	#[test]
	fn memoization_saves_fuel() {
		let d = defs();
		let mut r = Reducer::new(&d, 1000);
		let t = Tm::app("MyAdd", vec![Tm::lit(10), Tm::lit(1)]);
		r.reduce(&t).unwrap();
		let first = r.steps();
		r.reduce(&t).unwrap();
		assert_eq!(r.steps(), first);
	}

	#[test]
	fn apart_on_terms() {
		// distinct constructors
		assert!(apart(&Tm::con("Int", vec![]), &Tm::con("Bool", vec![])));
		assert!(!apart(&Tm::con("Int", vec![]), &Tm::con("Int", vec![])));
		// variables may be anything
		assert!(!apart(&Tm::Atom(0), &Tm::con("Int", vec![])));
		// literals and successors
		assert!(apart(&Tm::lit(3), &Tm::lit(4)));
		assert!(apart(&Tm::zero(), &Tm::succ(Tm::Atom(0))));
		assert!(!apart(&Tm::lit(3), &Tm::succ(Tm::Atom(0))));
		// Vec 0 a  vs  Vec (Succ n) a
		let nil = Tm::con("Vec", vec![Tm::lit(0), Tm::Atom(1)]);
		let cons = Tm::con("Vec", vec![Tm::succ(Tm::Atom(0)), Tm::Atom(1)]);
		assert!(apart(&nil, &cons));
	}

	#[test]
	fn render() {
		let p = n(0)
			.scale(2)
			.unwrap()
			.add(&n(1))
			.unwrap()
			.add(&P::lit(3))
			.unwrap();
		assert_eq!(p.render(&|k| format!("n{}", k)), "2*n0 + n1 + 3");
		assert_eq!(P::zero().render(&|k| format!("n{}", k)), "0");
	}

	#[test]
	fn deep_literal_recursion_with_a_big_stack() {
		// 1000-deep unary recursion through a user function, on a thread with room for it
		let h = std::thread::Builder::new()
			.stack_size(64 * 1024 * 1024)
			.spawn(|| {
				let d = defs();
				let mut r = Reducer::new(&d, 100_000).with_depth(5_000);
				r.reduce(&Tm::app("MyAdd", vec![Tm::lit(1000), Tm::lit(1)]))
					.unwrap()
			})
			.unwrap();
		assert_eq!(h.join().unwrap(), Tm::lit(1001));
	}
}
