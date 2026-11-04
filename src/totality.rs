// Totality checking for proofs
//
// A function whose result is a *proof type* is a proof: it must terminate, or it could "prove"
// anything. A proof type is a GADT with a constructor whose result repeats an index
// (`Refl : Equal n n`), the shape of an equality. A proof function is accepted when
//
//   * it has a body (no `undefined`), and
//   * every self-call passes, at one fixed argument position, a variable that the enclosing
//     case bound *inside a constructor pattern* of that same column (a structural subterm).
//
// Exhaustiveness is already required of every `match` by the type checker, and pruned cases
// of an indexed type trap, so they cannot be reached with a well-typed argument.
// Functions with an erased `(0 n : T)` binder in their signature are held to the same rule.
// Mutual recursion between checked functions is rejected: only self-recursion is analysed,
// so a cycle through two functions could not be justified.

use std::collections::{HashMap, HashSet};

use crate::diag::Diagnostic;
use crate::parser::{Binding, Expr, Pattern, Program, Quantity, Span, Spanned, TopLevel, Type};

pub fn check_program(program: &Program, proof_types: &HashSet<String>) -> Vec<Diagnostic> {
	let mut out = Vec::new();
	walk(&program.0, proof_types, &mut out);
	// mutual recursion among the checked functions
	let mut graph: HashMap<String, (Span, HashSet<String>)> = HashMap::new();
	collect_graph(&program.0, proof_types, &mut graph);
	let names: HashSet<String> = graph.keys().cloned().collect();
	for (f, (span, _)) in &graph {
		// can `f` get back to itself through some *other* checked function?
		let mut seen: HashSet<String> = HashSet::new();
		let mut stack: Vec<String> = graph[f]
			.1
			.iter()
			.filter(|g| *g != f && names.contains(*g))
			.cloned()
			.collect();
		let mut cyclic = false;
		while let Some(g) = stack.pop() {
			if !seen.insert(g.clone()) {
				continue;
			}
			if let Some((_, callees)) = graph.get(&g) {
				for h in callees {
					if h == f {
						cyclic = true;
					} else if names.contains(h) {
						stack.push(h.clone());
					}
				}
			}
		}
		if cyclic {
			out.push(
				Diagnostic::error(
					format!(
						"`{}` is part of a cycle of mutually recursive proofs, which is not checked",
						f
					),
					Some(*span),
				)
				.with_help(
					"make the recursion direct: a proof may only call itself, on a structural subterm",
				),
			);
		}
	}
	out
}

fn is_checked(b: &Binding, proofs: &HashSet<String>) -> bool {
	result_head(&b.typ.item).is_some_and(|h| proofs.contains(&h)) || has_zero_binder(&b.typ.item)
}

/// An erased `(0 x : T) -> ..` binder anywhere along the arrows of a signature.
fn has_zero_binder(t: &Type) -> bool {
	match t {
		Type::Fn(_, b) => has_zero_binder(&b.item),
		Type::Pi(q, _, _, c) => *q == Quantity::Zero || has_zero_binder(&c.item),
		Type::Annot(inner, _) => has_zero_binder(&inner.item),
		_ => false,
	}
}

fn collect_graph(
	items: &[Spanned<TopLevel>],
	proofs: &HashSet<String>,
	out: &mut HashMap<String, (Span, HashSet<String>)>,
) {
	for item in items {
		match &item.item {
			TopLevel::Module(_, body) => collect_graph(body, proofs, out),
			TopLevel::Binding(b) if is_checked(b, proofs) => {
				let mut refs = HashSet::new();
				if let Some(v) = &b.value {
					names_in(&v.item, &mut refs);
				}
				out.insert(b.name.item.clone(), (b.name.span, refs));
			}
			_ => {}
		}
	}
}

fn names_in(e: &Expr, out: &mut HashSet<String>) {
	match e {
		Expr::Qualified(q) => {
			if let Some(n) = q.0.last() {
				out.insert(n.clone());
			}
		}
		Expr::App(f, a) => {
			names_in(&f.item, out);
			names_in(&a.item, out);
		}
		Expr::Product(a, b) => {
			names_in(&a.item, out);
			names_in(&b.item, out);
		}
		Expr::Fn(_, body) => names_in(&body.item, out),
		Expr::Match(cases) => {
			for (_, body) in cases {
				names_in(&body.item, out);
			}
		}
		Expr::Literal(_) => {}
	}
}

fn walk(items: &[Spanned<TopLevel>], proofs: &HashSet<String>, out: &mut Vec<Diagnostic>) {
	for item in items {
		match &item.item {
			TopLevel::Module(_, body) => walk(body, proofs, out),
			TopLevel::Binding(b) => check_binding(b, proofs, out),
			_ => {}
		}
	}
}

/// The head type name of the final result of `t`: `A -> B -> Equal x y` gives `Equal`.
fn result_head(t: &Type) -> Option<String> {
	match t {
		Type::Fn(_, b) => result_head(&b.item),
		Type::Pi(_, _, _, c) | Type::Sigma(_, _, _, c) => result_head(&c.item),
		Type::Annot(inner, _) => result_head(&inner.item),
		Type::App(f, _) => result_head(&f.item),
		Type::Var(n) => Some(n.rsplit(':').next().unwrap_or(n).to_string()),
		_ => None,
	}
}

fn check_binding(b: &Binding, proofs: &HashSet<String>, out: &mut Vec<Diagnostic>) {
	if !is_checked(b, proofs) {
		return;
	}
	let head = result_head(&b.typ.item).unwrap_or_default();
	let name = &b.name.item;
	let Some(value) = &b.value else {
		out.push(
			Diagnostic::error(
				if proofs.contains(&head) {
					format!("`{}` proves a `{}` but has no definition", name, head)
				} else {
					format!(
						"`{}` has an erased (quantity 0) binder but no definition",
						name
					)
				},
				Some(b.name.span),
			)
			.with_help("a proof cannot be `undefined`: it would prove anything"),
		);
		return;
	};
	let mut e = &value.item;
	let mut lambdas = 0;
	while let Expr::Fn(_, body) = e {
		lambdas += 1;
		e = &body.item;
	}
	let mut calls: Vec<Call> = Vec::new();
	match e {
		Expr::Match(cases) if lambdas == 0 => {
			let arity = cases.first().map(|c| c.0.len()).unwrap_or(0);
			for (pats, body) in cases {
				let smaller: Vec<HashSet<String>> = pats
					.iter()
					.map(|p| {
						let mut s = HashSet::new();
						collect_smaller(&p.item, &mut s);
						s
					})
					.collect();
				let mut found = Vec::new();
				find_calls(name, body, &mut found);
				for c in found {
					calls.push(Call {
						args: c.args,
						span: c.span,
						smaller: smaller.clone(),
					});
				}
			}
			if !calls.is_empty() && !(0..arity).any(|i| calls.iter().all(|c| c.decreases_at(i))) {
				let span = calls[0].span;
				out.push(
					Diagnostic::error(
						format!("cannot show that the proof `{}` terminates", name),
						Some(span),
					)
					.with_help(
						"in every recursive call, one fixed argument must be a variable taken out of a constructor pattern of the same argument (a structural subterm)",
					),
				);
			}
		}
		other => {
			// not a plain `match`: a self-reference cannot be justified
			let mut found = Vec::new();
			find_calls_expr(name, other, &mut found);
			if let Some(c) = found.first() {
				out.push(
					Diagnostic::error(
						format!("cannot show that the proof `{}` terminates", name),
						Some(c.span),
					)
					.with_help(
						"write the proof as a `match` and recurse on a subterm of an argument",
					),
				);
			}
		}
	}
}

struct Call {
	args: Vec<Option<String>>,
	span: Span,
	smaller: Vec<HashSet<String>>,
}

impl Call {
	fn decreases_at(&self, i: usize) -> bool {
		match (self.args.get(i), self.smaller.get(i)) {
			(Some(Some(v)), Some(s)) => s.contains(v),
			_ => false,
		}
	}
}

struct Found {
	args: Vec<Option<String>>,
	span: Span,
}

/// Variables bound inside a constructor pattern: strict subterms of that column's value.
fn collect_smaller(p: &Pattern, out: &mut HashSet<String>) {
	match p {
		Pattern::Constructor(_, payload) => all_vars(&payload.item, out),
		Pattern::Product(a, b) => {
			collect_smaller(&a.item, out);
			collect_smaller(&b.item, out);
		}
		Pattern::Left(a) | Pattern::Right(a) => collect_smaller(&a.item, out),
		_ => {}
	}
}

fn all_vars(p: &Pattern, out: &mut HashSet<String>) {
	match p {
		Pattern::Variable(v) => {
			out.insert(v.clone());
		}
		Pattern::Constructor(_, payload) => all_vars(&payload.item, out),
		Pattern::Product(a, b) => {
			all_vars(&a.item, out);
			all_vars(&b.item, out);
		}
		Pattern::Left(a) | Pattern::Right(a) => all_vars(&a.item, out),
		_ => {}
	}
}

fn is_self(name: &str, e: &Expr) -> bool {
	matches!(e, Expr::Qualified(q) if q.0.last().map(|s| s.as_str()) == Some(name))
}

fn find_calls(name: &str, e: &Spanned<Expr>, out: &mut Vec<Found>) {
	find_calls_expr_spanned(name, e, out)
}

fn find_calls_expr(name: &str, e: &Expr, out: &mut Vec<Found>) {
	// a spanless entry point: spans of the found calls are the placeholder of the root
	let root = Spanned {
		item: e.clone(),
		span: Span::synthetic(0),
	};
	find_calls_expr_spanned(name, &root, out)
}

fn find_calls_expr_spanned(name: &str, e: &Spanned<Expr>, out: &mut Vec<Found>) {
	match &e.item {
		Expr::App(..) => {
			// flatten `f a b c`
			let mut args: Vec<&Spanned<Expr>> = Vec::new();
			let mut cur = e;
			while let Expr::App(f, a) = &cur.item {
				args.push(a);
				cur = f;
			}
			args.reverse();
			if is_self(name, &cur.item) {
				out.push(Found {
					args: args
						.iter()
						.map(|a| match &a.item {
							Expr::Qualified(q) if q.0.len() == 1 => Some(q.0[0].clone()),
							_ => None,
						})
						.collect(),
					span: cur.span,
				});
			} else {
				find_calls_expr_spanned(name, cur, out);
			}
			for a in args {
				find_calls_expr_spanned(name, a, out);
			}
		}
		Expr::Qualified(_) if is_self(name, &e.item) => out.push(Found {
			args: Vec::new(),
			span: e.span,
		}),
		Expr::Fn(_, body) => find_calls_expr_spanned(name, body, out),
		Expr::Product(a, b) => {
			find_calls_expr_spanned(name, a, out);
			find_calls_expr_spanned(name, b, out);
		}
		Expr::Match(cases) => {
			for (_, body) in cases {
				find_calls_expr_spanned(name, body, out);
			}
		}
		_ => {}
	}
}
