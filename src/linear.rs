// Linear quantity 1
//
// `(1 x : T) -> U` is an ordinary function type whose argument must be used *exactly once*:
// never dropped, never duped.
// check every binding w/ a linear parameter, over a usage count {0, 1, many}:
//   - a variable counts once where it is mentioned; applications and pairs add counts
//   - the cases of a `match` must agree (a branch that drops it is an error)
//   - a mention inside a lambda counts as `many` (the closure may run any number of times,
//     captures are counted at creation)
//   - a linear variable may be passed only to a data constructor or to a parameter that the
//     callee's own signature declares linear, otherwise the callee could copy or drop it;
//   - every variable bound by a pattern in a linear column is linear too, and `_` there
//     would drop the value.
//
// Not covered: aliasing through `with`-clauses and class methods, and linear values stored in
// pairs and handed on as a whole to an unrestricted parameter.

use std::collections::HashMap;

use crate::diag::Diagnostic;
use crate::parser::{Binding, Expr, Pattern, Program, Quantity, Span, Spanned, TopLevel, Type};

/// A function's linearity: which parameters are linear, and, for a parameter that is itself a
/// function type, which of *its* parameters are (`lbind : ((1 x : a) -> IO b) -> ..`).
#[derive(Clone, Default)]
struct Sig {
	flags: Vec<bool>,
	inner: Vec<Vec<bool>>,
}

type Sigs = HashMap<String, Sig>;

pub fn check_program(program: &Program) -> Vec<Diagnostic> {
	let mut sigs = Sigs::new();
	collect(&program.0, &mut sigs);
	if !sigs
		.values()
		.any(|f| f.flags.iter().any(|l| *l) || f.inner.iter().any(|i| i.iter().any(|l| *l)))
	{
		return Vec::new();
	}
	let mut out = Vec::new();
	walk(&program.0, &sigs, &mut out);
	out
}

/// Per-parameter linearity along the arrows of a signature.
fn sig_params(t: &Type) -> Vec<bool> {
	let mut out = Vec::new();
	let mut cur = t;
	loop {
		match cur {
			Type::Fn(_, b) => {
				out.push(false);
				cur = &b.item;
			}
			Type::Pi(q, _, _, c) => {
				out.push(*q == Quantity::One);
				cur = &c.item;
			}
			Type::Annot(inner, _) => cur = &inner.item,
			_ => return out,
		}
	}
}

/// The signature's parameter types, in order.
fn sig_param_types(t: &Type) -> Vec<&Type> {
	let mut out = Vec::new();
	let mut cur = t;
	loop {
		match cur {
			Type::Fn(a, b) => {
				out.push(&a.item);
				cur = &b.item;
			}
			Type::Pi(_, _, d, c) => {
				out.push(&d.item);
				cur = &c.item;
			}
			Type::Annot(inner, _) => cur = &inner.item,
			_ => return out,
		}
	}
}

fn full_sig(t: &Type) -> Sig {
	Sig {
		flags: sig_params(t),
		inner: sig_param_types(t).into_iter().map(sig_params).collect(),
	}
}

fn collect(items: &[Spanned<TopLevel>], sigs: &mut Sigs) {
	for item in items {
		match &item.item {
			TopLevel::Module(_, body) => collect(body, sigs),
			TopLevel::Binding(b) => {
				sigs.insert(b.name.item.clone(), full_sig(&b.typ.item));
			}
			// a class method's signature says which of its parameters are linear
			TopLevel::ClassDef(_, _, methods) => {
				for m in methods {
					sigs.insert(m.item.name.item.clone(), full_sig(&m.item.typ.item));
				}
			}
			_ => {}
		}
	}
}

fn walk(items: &[Spanned<TopLevel>], sigs: &Sigs, out: &mut Vec<Diagnostic>) {
	for item in items {
		match &item.item {
			TopLevel::Module(_, body) => walk(body, sigs, out),
			TopLevel::Binding(b) => check_binding(b, sigs, None, out),
			// default methods carry their own signature
			TopLevel::ClassDef(_, _, methods) => {
				for m in methods {
					check_binding(&m.item, sigs, None, out);
				}
			}
			// an instance's methods answer to the class's declared linearity, not to the
			// (plain) arrows of their own instantiated signature
			TopLevel::Instance(_, _, bindings) => {
				for b in bindings {
					let flags = sigs.get(&b.item.name.item).map(|s| s.flags.clone());
					check_binding(&b.item, sigs, flags, out);
				}
			}
			_ => {}
		}
	}
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Count {
	Zero,
	One,
	Many,
}

impl Count {
	fn add(self, o: Count) -> Count {
		match (self, o) {
			(Count::Zero, x) | (x, Count::Zero) => x,
			_ => Count::Many,
		}
	}
}

struct Cx<'a> {
	sigs: &'a Sigs,
	errors: Vec<(String, Span)>,
}

fn check_binding(
	b: &Binding,
	sigs: &Sigs,
	flags_override: Option<Vec<bool>>,
	out: &mut Vec<Diagnostic>,
) {
	// local (`with`) definitions are bindings of their own
	for w in &b.with_clauses {
		check_binding(&w.item, sigs, None, out);
	}
	// a lambda handed to a linear continuation parameter (`lbind (fn h -> ..) m`)
	if let Some(v) = &b.value {
		let mut cx = Cx {
			sigs,
			errors: Vec::new(),
		};
		cx.scan_lambdas(v);
		for (msg, span) in cx.errors {
			out.push(Diagnostic::error(msg, Some(span)).with_help(LINEAR_HELP));
		}
	}
	let flags = flags_override.unwrap_or_else(|| sig_params(&b.typ.item));
	if !flags.iter().any(|l| *l) {
		return;
	}
	let Some(value) = &b.value else {
		return;
	};
	let mut cx = Cx {
		sigs,
		errors: Vec::new(),
	};
	let mut e = &value.item;
	let mut pos = 0;
	// lambda parameters come first, in signature order
	let mut lambdas: Vec<(&str, usize)> = Vec::new();
	let mut body_spanned = value;
	while let Expr::Fn(x, body) = e {
		lambdas.push((x.item.as_str(), pos));
		pos += 1;
		e = &body.item;
		body_spanned = &**body;
	}
	for (x, p) in &lambdas {
		if flags.get(*p).copied().unwrap_or(false) {
			finish(x, cx.count(x, body_spanned), b.name.span, &mut cx.errors);
			capture_by_with(x, b, &mut cx.errors);
		}
	}
	if let Expr::Match(cases) = e {
		for (pats, body) in cases {
			for (i, p) in pats.iter().enumerate() {
				if !flags.get(pos + i).copied().unwrap_or(false) {
					continue;
				}
				if matches!(p.item, Pattern::Hole) {
					cx.errors.push((
						"a linear value is dropped by `_`: it must be used exactly once"
							.to_string(),
						p.span,
					));
				}
				let mut vars = Vec::new();
				pattern_vars(&p.item, &mut vars);
				for v in vars {
					finish(&v, cx.count(&v, body), p.span, &mut cx.errors);
					capture_by_with(&v, b, &mut cx.errors);
				}
			}
		}
	}
	for (msg, span) in cx.errors {
		out.push(Diagnostic::error(msg, Some(span)).with_help(LINEAR_HELP));
	}
}

const LINEAR_HELP: &str = "a `(1 x : T)` argument must be used exactly once: not dropped, not duplicated, and only passed to a constructor or to another linear parameter";

/// A `with`-definition is a local function: a linear variable it mentions would be used once
/// per call of that function, which can be any number of times.
fn capture_by_with(v: &str, b: &Binding, errors: &mut Vec<(String, Span)>) {
	for w in &b.with_clauses {
		if let Some(val) = &w.item.value
			&& mentions(v, &val.item)
		{
			errors.push((
				format!(
					"the linear variable `{}` is captured by a `with` definition, which may run more than once",
					v
				),
				w.span,
			));
		}
	}
}

fn mentions(v: &str, e: &Expr) -> bool {
	match e {
		Expr::Qualified(q) => q.0.len() == 1 && q.0[0] == v,
		Expr::Literal(_) => false,
		Expr::App(f, a) | Expr::Product(f, a) => mentions(v, &f.item) || mentions(v, &a.item),
		Expr::Fn(y, body) => y.item != v && mentions(v, &body.item),
		Expr::Match(cases) => cases
			.iter()
			.any(|(pats, body)| !pats.iter().any(|p| binds(&p.item, v)) && mentions(v, &body.item)),
	}
}

fn finish(v: &str, c: Count, span: Span, errors: &mut Vec<(String, Span)>) {
	match c {
		Count::One => {}
		Count::Zero => errors.push((
			format!(
				"the linear variable `{}` is never used (a linear value cannot be dropped)",
				v
			),
			span,
		)),
		Count::Many => errors.push((
			format!("the linear variable `{}` is used more than once", v),
			span,
		)),
	}
}

fn pattern_vars(p: &Pattern, out: &mut Vec<String>) {
	match p {
		Pattern::Variable(v) => out.push(v.clone()),
		Pattern::Constructor(_, payload) => pattern_vars(&payload.item, out),
		Pattern::Product(a, b) => {
			pattern_vars(&a.item, out);
			pattern_vars(&b.item, out);
		}
		Pattern::Left(a) | Pattern::Right(a) => pattern_vars(&a.item, out),
		_ => {}
	}
}

/// Is `v` handed over as a whole: itself, or a component of a pair built right there?
fn direct(e: &Expr, v: &str) -> bool {
	match e {
		Expr::Qualified(q) => q.0.len() == 1 && q.0[0] == v,
		Expr::Product(a, b) => direct(&a.item, v) || direct(&b.item, v),
		_ => false,
	}
}

fn binds(p: &Pattern, v: &str) -> bool {
	let mut vars = Vec::new();
	pattern_vars(p, &mut vars);
	vars.iter().any(|x| x == v)
}

impl Cx<'_> {
	/// Find calls `f .. (fn x -> body) ..` where `f`'s signature says that parameter is a
	/// function whose argument is linear, and check `x` in `body`. Recurses everywhere.
	fn scan_lambdas(&mut self, e: &Spanned<Expr>) {
		match &e.item {
			Expr::App(..) => {
				let mut args: Vec<&Spanned<Expr>> = Vec::new();
				let mut cur = e;
				while let Expr::App(f, a) = &cur.item {
					args.push(a);
					cur = f;
				}
				args.reverse();
				let sig = match &cur.item {
					Expr::Qualified(q) => q.0.last().and_then(|n| self.sigs.get(n)).cloned(),
					_ => None,
				};
				for (j, a) in args.iter().enumerate() {
					if let (Some(sig), Expr::Fn(..)) = (&sig, &a.item)
						&& let Some(inner) = sig.inner.get(j)
					{
						// the lambda's parameters, outermost first, against the parameter
						// type's arrows
						let mut body = *a;
						let mut k = 0;
						while let Expr::Fn(x, b) = &body.item {
							if inner.get(k).copied().unwrap_or(false) {
								let c = self.count(&x.item, b);
								let mut errs = Vec::new();
								finish(&x.item, c, a.span, &mut errs);
								self.errors.extend(errs);
							}
							body = &**b;
							k += 1;
						}
					}
					self.scan_lambdas(a);
				}
				self.scan_lambdas(cur);
			}
			Expr::Fn(_, body) => self.scan_lambdas(body),
			Expr::Product(a, b) => {
				self.scan_lambdas(a);
				self.scan_lambdas(b);
			}
			Expr::Match(cases) => {
				for (_, body) in cases {
					self.scan_lambdas(body);
				}
			}
			_ => {}
		}
	}

	fn count(&mut self, v: &str, e: &Spanned<Expr>) -> Count {
		match &e.item {
			Expr::Qualified(q) => {
				if q.0.len() == 1 && q.0[0] == v {
					Count::One
				} else {
					Count::Zero
				}
			}
			Expr::Literal(_) => Count::Zero,
			Expr::App(..) => {
				let mut args: Vec<&Spanned<Expr>> = Vec::new();
				let mut cur = e;
				while let Expr::App(f, a) = &cur.item {
					args.push(a);
					cur = f;
				}
				args.reverse();
				let mut total = self.count(v, cur);
				for (j, a) in args.iter().enumerate() {
					if direct(&a.item, v) && !self.accepts_linear(&cur.item, j) {
						self.errors.push((
							format!(
								"the linear variable `{}` is passed to a function that does not take it linearly",
								v
							),
							a.span,
						));
					}
					total = total.add(self.count(v, a));
				}
				total
			}
			Expr::Product(a, b) => {
				let ca = self.count(v, a);
				ca.add(self.count(v, b))
			}
			Expr::Fn(y, body) => {
				if y.item == v {
					return Count::Zero;
				}
				if self.count(v, body) != Count::Zero {
					self.errors.push((
						format!(
							"the linear variable `{}` is captured by a closure, which may run more than once",
							v
						),
						e.span,
					));
					return Count::Many;
				}
				Count::Zero
			}
			Expr::Match(cases) => {
				let mut counts = Vec::new();
				for (pats, body) in cases {
					if pats.iter().any(|p| binds(&p.item, v)) {
						counts.push(Count::Zero);
					} else {
						counts.push(self.count(v, body));
					}
				}
				match counts.split_first() {
					None => Count::Zero,
					Some((first, rest)) => {
						if rest.iter().all(|c| c == first) {
							*first
						} else {
							self.errors.push((
								format!(
									"the linear variable `{}` is used in some branches of a `match` but not in others",
									v
								),
								e.span,
							));
							Count::Many
						}
					}
				}
			}
		}
	}

	/// May argument `j` of `head` be a linear variable? A data constructor stores it (it is
	/// then consumed by whoever matches the value), and a callee whose signature says the
	/// parameter is linear promises to use it exactly once.
	fn accepts_linear(&self, head: &Expr, j: usize) -> bool {
		let Expr::Qualified(q) = head else {
			return false;
		};
		let Some(last) = q.0.last() else {
			return false;
		};
		if last.chars().next().is_some_and(|c| c.is_uppercase()) {
			return true;
		}
		self.sigs
			.get(last)
			.and_then(|f| f.flags.get(j))
			.copied()
			.unwrap_or(false)
	}
}
