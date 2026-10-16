// Optimization + partial evaluation of ANF IR

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::diag::Diagnostic;
use crate::ir::{
	count_arrows, display_ty, peel_fn, Arm, Atom, CasePat, Expr, Function, IrProgram, Name, Side,
	Value,
};
use crate::lang::{Intrinsic, Lang, LangItem};
use crate::lift_spec::{collect_fn_tys, lambda_lift, specialize_hof};
use crate::parser::Literal;
use crate::typechecker::Ty;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
static TRIED: AtomicUsize = AtomicUsize::new(0);
static ACCEPTED: AtomicUsize = AtomicUsize::new(0);
static WASTED: AtomicUsize = AtomicUsize::new(0);

type SubstMap = im::HashMap<String, Atom>;
type FactMap = im::HashMap<String, Fact>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
pub enum OptimizeMode {
	Off,
	// folding, copy propagation, CSE, DCE, known-case
	Standard,
	// standard + whole-program inlining, partial eval of calls to top-level known fns
	Aggressive,
}

pub fn optimize(program: &mut IrProgram, mode: OptimizeMode, lang: &Lang) {
	if mode == OptimizeMode::Off {
		return;
	}
	let externs: HashMap<String, (usize, Option<Intrinsic>)> = program
		.externs
		.iter()
		.map(|e| (e.name.clone(), (e.arity, e.intrinsic)))
		.collect();
	let counter = Cell::new(0u64);

	if mode == OptimizeMode::Aggressive {
		raise_arity(program, &externs, &counter);
	}
	run_sweeps(program, mode, lang, &externs, &counter, 2);

	if mode == OptimizeMode::Aggressive {
		// Closures that survived the sweeps (they escape into higher-order
		// functions or are join points) become top-level functions + paps.
		// recursive HOFs are then specialized on them. one more sweep inlines
		// the now-known functions into the specialized loops.
		for _round in 0..3 {
			let lifted = !disabled("lift") && lambda_lift(program, &counter);
			let specialized = !disabled("spec") && specialize_hof(program, &counter);
			if !lifted && !specialized {
				break;
			}
			run_sweeps(program, mode, lang, &externs, &counter, 1);
		}
	}

	if std::env::var_os("IOTA_OPT_STATS").is_some() {
		eprintln!(
			"[opt] inline attempts {}, accepted {}, wasted {}, fresh names {}",
			TRIED.load(Relaxed),
			ACCEPTED.load(Relaxed),
			WASTED.load(Relaxed),
			counter.get()
		);
	}
}

fn run_sweeps(
	program: &mut IrProgram,
	mode: OptimizeMode,
	lang: &Lang,
	externs: &HashMap<String, (usize, Option<Intrinsic>)>,
	counter: &Cell<u64>,
	sweeps: usize,
) {
	let recursive = recursive_set(program);
	let single = single_site_set(program, &recursive);
	let mut funcs: HashMap<String, Rc<Function>> = program
		.functions
		.iter()
		.map(|f| (f.name.clone(), Rc::new(f.clone())))
		.collect();
	let budget = Cell::new(0usize);

	for _ in 0..sweeps {
		for i in 0..program.functions.len() {
			let name = program.functions[i].name.clone();
			let current = funcs[&name].clone();
			let optimized = {
				let cx = Cx {
					funcs: &funcs,
					externs,
					lang,
					recursive: &recursive,
					single: &single,
					inline: mode == OptimizeMode::Aggressive,
					counter,
					budget: &budget,
					changed: Cell::new(false),
					in_try: Cell::new(0),
					var_tys: RefCell::new(HashMap::new()),
				};
				cx.optimize_function(&current)
			};
			funcs.insert(name, Rc::new(optimized));
		}
	}
	for f in &mut program.functions {
		*f = (*funcs[&f.name]).clone();
	}
}

fn recursive_set(program: &IrProgram) -> HashSet<String> {
	let calls: HashMap<&str, HashSet<String>> = program
		.functions
		.iter()
		.map(|f| (f.name.as_str(), referenced_globals(&f.body)))
		.collect();
	let mut rec = HashSet::new();
	for f in &program.functions {
		// f is recursive iff it can reach itself through its callees
		let mut seen: HashSet<&str> = HashSet::new();
		let mut stack: Vec<&str> = calls[f.name.as_str()].iter().map(|s| s.as_str()).collect();
		while let Some(n) = stack.pop() {
			if n == f.name {
				rec.insert(f.name.clone());
				break;
			}
			if !seen.insert(n) {
				continue;
			}
			if let Some(cs) = calls.get(n) {
				stack.extend(cs.iter().map(|s| s.as_str()));
			}
		}
	}
	rec
}

#[derive(Clone, Debug)]
enum Fact {
	Lit(Literal),
	Ctor(String, Option<Atom>),
	Tag(String), // only ctor is known (match)
	Pair(Atom, Atom),
	Pap(String, Vec<Atom>),
}

enum Folded {
	Lit(Literal),
	Ctor(String),
	Str(String),
}

struct Cx<'a> {
	funcs: &'a HashMap<String, Rc<Function>>,
	externs: &'a HashMap<String, (usize, Option<Intrinsic>)>,
	lang: &'a Lang,
	recursive: &'a HashSet<String>,
	inline: bool,
	counter: &'a Cell<u64>,
	budget: &'a Cell<usize>,
	changed: Cell<bool>,
	in_try: Cell<usize>,
	single: &'a HashSet<String>,
	var_tys: RefCell<HashMap<String, Ty>>,
}

const SMALL_INLINE: usize = 24;
const CONCRETE_INLINE: usize = 400;
const MAX_DEPTH: usize = 6;
const MAX_FUNCTION_SIZE: usize = 5_000;
const TAIL_INLINE_MAX: usize = 48;
const FUNCTION_BUDGET: usize = 6_000;
const MAX_DUP_ARMS: usize = 4;

type Binds = Vec<(Name, Ty, Value)>;

// name an expression returns, if it just returns a var
fn tail_var(e: &Expr) -> Option<&Name> {
	let mut cur = e;
	loop {
		match cur {
			Expr::Let(_, _, _, rest) => cur = &**rest,
			Expr::Halt(Atom::Var(n)) => return Some(n),
			_ => return None,
		}
	}
}

fn rename_var_atom(a: &mut Atom, from: &str, to: &str) {
	if let Atom::Var(n) = a {
		if n == from {
			*n = to.to_string();
		}
	}
}

fn rename_var_value(v: &mut Value, from: &str, to: &str) {
	match v {
		Value::Atom(a) | Value::Proj(a, _) | Value::Unwrap(a) => rename_var_atom(a, from, to),
		Value::App(a, b) | Value::Pair(a, b) => {
			rename_var_atom(a, from, to);
			rename_var_atom(b, from, to);
		}
		Value::Ctor(_, Some(a)) => rename_var_atom(a, from, to),
		Value::Ctor(_, None) | Value::Str(_) | Value::Fail(_) => {}
		Value::Lambda(_, _, body) => rename_var_in(body, from, to),
	}
}

// replace the free variable `from` by `to` (names are unique per function, so
// nothing can be captured)
fn rename_var_in(e: &mut Expr, from: &str, to: &str) {
	match e {
		Expr::Halt(a) => rename_var_atom(a, from, to),
		Expr::Case(s, arms) => {
			rename_var_atom(s, from, to);
			for arm in arms {
				rename_var_in(&mut arm.body, from, to);
			}
		}
		Expr::Let(_, _, v, rest) => {
			rename_var_value(v, from, to);
			rename_var_in(rest, from, to);
		}
	}
}

pub(crate) fn flatten(e: Expr) -> (Binds, Expr) {
	let mut binds = Vec::new();
	let mut cur = e;
	loop {
		match cur {
			Expr::Let(x, t, v, rest) => {
				binds.push((x, t, v));
				cur = *rest;
			}
			other => return (binds, other),
		}
	}
}

pub(crate) fn rebuild(binds: Binds, tail: Expr) -> Expr {
	let mut e = tail;
	for (x, t, v) in binds.into_iter().rev() {
		e = Expr::Let(x, t, v, Box::new(e));
	}
	e
}

fn resolve(subst: &SubstMap, a: &Atom) -> Atom {
	match a {
		Atom::Var(n) => subst.get(n).cloned().unwrap_or_else(|| a.clone()),
		_ => a.clone(),
	}
}

fn fact_of_atom(a: &Atom, facts: &FactMap) -> Option<Fact> {
	match a {
		Atom::Lit(l) => Some(Fact::Lit(l.clone())),
		Atom::Var(n) => facts.get(n).cloned(),
		Atom::Global(..) | Atom::Method(..) => None,
	}
}

fn record_fact(x: &str, v: &Value, facts: &mut FactMap) {
	match v {
		Value::Ctor(tag, p) => {
			facts.insert(x.to_string(), Fact::Ctor(tag.clone(), p.clone()));
		}
		Value::Pair(a, b) => {
			facts.insert(x.to_string(), Fact::Pair(a.clone(), b.clone()));
		}
		Value::Atom(Atom::Lit(l)) => {
			facts.insert(x.to_string(), Fact::Lit(l.clone()));
		}
		_ => {}
	}
}

fn values_equal(a: &Value, b: &Value) -> bool {
	match (a, b) {
		(Value::Atom(x), Value::Atom(y)) => x == y,
		(Value::App(f1, a1), Value::App(f2, a2)) => f1 == f2 && a1 == a2,
		(Value::Pair(a1, b1), Value::Pair(a2, b2)) => a1 == a2 && b1 == b2,
		(Value::Ctor(t1, p1), Value::Ctor(t2, p2)) => t1 == t2 && p1 == p2,
		(Value::Proj(a1, s1), Value::Proj(a2, s2)) => a1 == a2 && s1 == s2,
		(Value::Unwrap(a1), Value::Unwrap(a2)) => a1 == a2,
		(Value::Str(s1), Value::Str(s2)) => s1 == s2,
		_ => false,
	}
}

fn pick_arm(known_lit: Option<&Literal>, known_tag: Option<&str>, arms: &[Arm]) -> Option<Expr> {
	for arm in arms {
		let hit = match &arm.pat {
			CasePat::Wild => true,
			CasePat::Lit(l) => known_lit.map_or(false, |k| lit_eq(l, k)),
			CasePat::Ctor(t) => known_tag.map_or(false, |k| k == t),
		};
		if hit {
			return Some(arm.body.clone());
		}
	}
	None
}

fn lit_eq(a: &Literal, b: &Literal) -> bool {
	match (a, b) {
		(Literal::Int(x), Literal::Int(y)) => x == y,
		(Literal::Char(x), Literal::Char(y)) => x == y,
		(Literal::Float(x), Literal::Float(y)) => x.to_bits() == y.to_bits(),
		_ => false,
	}
}

fn atom_vars(a: &Atom, out: &mut HashSet<String>) {
	if let Atom::Var(n) = a {
		out.insert(n.clone());
	}
}

fn value_vars(v: &Value) -> HashSet<String> {
	let mut out = HashSet::new();
	match v {
		Value::Atom(a) | Value::Proj(a, _) | Value::Unwrap(a) => atom_vars(a, &mut out),
		Value::App(a, b) | Value::Pair(a, b) => {
			atom_vars(a, &mut out);
			atom_vars(b, &mut out);
		}
		Value::Ctor(_, Some(a)) => atom_vars(a, &mut out),
		Value::Ctor(_, None) | Value::Str(_) | Value::Fail(_) => {}
		Value::Lambda(p, _, body) => {
			out = expr_vars(body);
			out.remove(p);
		}
	}
	out
}

pub(crate) fn expr_vars(e: &Expr) -> HashSet<String> {
	match e {
		Expr::Halt(a) => {
			let mut s = HashSet::new();
			atom_vars(a, &mut s);
			s
		}
		Expr::Case(scrut, arms) => {
			let mut s = HashSet::new();
			atom_vars(scrut, &mut s);
			for arm in arms {
				s.extend(expr_vars(&arm.body));
			}
			s
		}
		Expr::Let(x, _, v, rest) => {
			let mut s = expr_vars(rest);
			s.remove(x);
			s.extend(value_vars(v));
			s
		}
	}
}

fn atom_globals(a: &Atom, out: &mut HashSet<String>) {
	if let Atom::Global(n, _) | Atom::Method(n, _) = a {
		out.insert(n.clone());
	}
}

pub fn referenced_globals(e: &Expr) -> HashSet<String> {
	let mut out = HashSet::new();
	fn go(e: &Expr, out: &mut HashSet<String>) {
		match e {
			Expr::Halt(a) => atom_globals(a, out),
			Expr::Case(s, arms) => {
				atom_globals(s, out);
				for arm in arms {
					go(&arm.body, out);
				}
			}
			Expr::Let(_, _, v, rest) => {
				match v {
					Value::Atom(a) | Value::Proj(a, _) | Value::Unwrap(a) => atom_globals(a, out),
					Value::App(a, b) | Value::Pair(a, b) => {
						atom_globals(a, out);
						atom_globals(b, out);
					}
					Value::Ctor(_, Some(a)) => atom_globals(a, out),
					Value::Lambda(_, _, body) => go(body, out),
					_ => {}
				}
				go(rest, out);
			}
		}
	}
	go(e, &mut out);
	out
}

fn ends_in_case(e: &Expr) -> bool {
	match e {
		Expr::Let(_, _, _, rest) => ends_in_case(rest),
		Expr::Case(..) => true,
		Expr::Halt(_) => false,
	}
}

pub(crate) fn expr_size(e: &Expr) -> usize {
	match e {
		Expr::Halt(_) => 0,
		Expr::Case(_, arms) => 1 + arms.iter().map(|a| expr_size(&a.body)).sum::<usize>(),
		Expr::Let(_, _, v, rest) => {
			1 + match v {
				Value::Lambda(_, _, b) => expr_size(b),
				_ => 0,
			} + expr_size(rest)
		}
	}
}

fn fold_intrinsic(op: Intrinsic, args: &[Atom], lang: &Lang) -> Option<Folded> {
	use Intrinsic::*;
	let lits: Vec<&Literal> = args
		.iter()
		.map(|a| match a {
			Atom::Lit(l) => Some(l),
			_ => None,
		})
		.collect::<Option<Vec<_>>>()?;
	let b = |v: bool| Folded::Ctor(lang.bool_ctor(v).to_string());
	match (op, lits.as_slice()) {
		(IAdd, [Literal::Int(a), Literal::Int(c)]) => {
			Some(Folded::Lit(Literal::Int(a.wrapping_add(*c))))
		}
		(ISub, [Literal::Int(a), Literal::Int(c)]) => {
			Some(Folded::Lit(Literal::Int(a.wrapping_sub(*c))))
		}
		(IMul, [Literal::Int(a), Literal::Int(c)]) => {
			Some(Folded::Lit(Literal::Int(a.wrapping_mul(*c))))
		}
		(IDiv, [Literal::Int(a), Literal::Int(c)]) if *c != 0 => {
			Some(Folded::Lit(Literal::Int(a.wrapping_div(*c))))
		}
		(IMod, [Literal::Int(a), Literal::Int(c)]) if *c != 0 => {
			Some(Folded::Lit(Literal::Int(a.wrapping_rem_euclid(*c))))
		}
		(ShowInt, [Literal::Int(a)]) => Some(Folded::Str(a.to_string())),
		(IEq, [Literal::Int(a), Literal::Int(c)]) => Some(b(a == c)),
		(INeq, [Literal::Int(a), Literal::Int(c)]) => Some(b(a != c)),
		(IGr, [Literal::Int(a), Literal::Int(c)]) => Some(b(a > c)),
		(IGre, [Literal::Int(a), Literal::Int(c)]) => Some(b(a >= c)),
		(ILs, [Literal::Int(a), Literal::Int(c)]) => Some(b(a < c)),
		(ILse, [Literal::Int(a), Literal::Int(c)]) => Some(b(a <= c)),
		(IEq, [Literal::Char(a), Literal::Char(c)]) => Some(b(a == c)),
		(INeq, [Literal::Char(a), Literal::Char(c)]) => Some(b(a != c)),
		(IGr, [Literal::Char(a), Literal::Char(c)]) => Some(b(a > c)),
		(IGre, [Literal::Char(a), Literal::Char(c)]) => Some(b(a >= c)),
		(ILs, [Literal::Char(a), Literal::Char(c)]) => Some(b(a < c)),
		(ILse, [Literal::Char(a), Literal::Char(c)]) => Some(b(a <= c)),
		(FAdd, [Literal::Float(a), Literal::Float(c)]) => Some(Folded::Lit(Literal::Float(a + c))),
		(FSub, [Literal::Float(a), Literal::Float(c)]) => Some(Folded::Lit(Literal::Float(a - c))),
		(FMul, [Literal::Float(a), Literal::Float(c)]) => Some(Folded::Lit(Literal::Float(a * c))),
		(FDiv, [Literal::Float(a), Literal::Float(c)]) => Some(Folded::Lit(Literal::Float(a / c))),
		(FEq, [Literal::Float(a), Literal::Float(c)]) => Some(b(a == c)),
		(FNeq, [Literal::Float(a), Literal::Float(c)]) => Some(b(a != c)),
		(FGr, [Literal::Float(a), Literal::Float(c)]) => Some(b(a > c)),
		(FGre, [Literal::Float(a), Literal::Float(c)]) => Some(b(a >= c)),
		(FLs, [Literal::Float(a), Literal::Float(c)]) => Some(b(a < c)),
		(FLse, [Literal::Float(a), Literal::Float(c)]) => Some(b(a <= c)),
		_ => None,
	}
}

fn can_reduce(callee: &Function, args: &[Atom], facts: &FactMap) -> bool {
	let mut unknown: HashSet<&str> = HashSet::new();
	for ((p, _), a) in callee.params.iter().zip(args) {
		if fact_of_atom(a, facts).is_none() {
			unknown.insert(p.as_str());
		}
	}
	if unknown.is_empty() {
		return true;
	}
	let mut e = &callee.body;
	loop {
		match e {
			Expr::Let(x, _, v, rest) => {
				let derived = match v {
					Value::Atom(Atom::Var(n))
					| Value::Proj(Atom::Var(n), _)
					| Value::Unwrap(Atom::Var(n)) => unknown.contains(n.as_str()),
					_ => false,
				};
				if derived {
					unknown.insert(x.as_str());
				} else {
					unknown.remove(x.as_str());
				}
				e = rest;
			}
			Expr::Case(Atom::Var(s), _) => return !unknown.contains(s.as_str()),
			Expr::Case(Atom::Lit(_), _) => return true,
			Expr::Case(..) => return false, // Global / Method scrutinee never resolved
			Expr::Halt(_) => return true,
		}
	}
}

fn cse_bucket(v: &Value) -> Option<String> {
	fn atom(x: &Atom, k: &mut String) {
		match x {
			Atom::Var(n) | Atom::Global(n, _) | Atom::Method(n, _) => k.push_str(n),
			Atom::Lit(_) => k.push('#'),
		}
		k.push('\u{1}');
	}
	let mut k = String::new();
	match v {
		Value::Atom(x) => {
			k.push('a');
			atom(x, &mut k);
		}
		Value::App(f, x) => {
			k.push('p');
			atom(f, &mut k);
			atom(x, &mut k);
		}
		Value::Pair(x, y) => {
			k.push('P');
			atom(x, &mut k);
			atom(y, &mut k);
		}
		Value::Ctor(t, p) => {
			k.push('C');
			k.push_str(t);
			k.push('\u{1}');
			if let Some(x) = p {
				atom(x, &mut k);
			}
		}
		Value::Proj(x, s) => {
			k.push(if *s == Side::Fst { 'f' } else { 's' });
			atom(x, &mut k);
		}
		Value::Unwrap(x) => {
			k.push('u');
			atom(x, &mut k);
		}
		Value::Str(s) => {
			k.push('S');
			k.push_str(s);
		}
		Value::Lambda(..) | Value::Fail(_) => return None,
	}
	Some(k)
}

fn returns_nullary_ctor(e: &Expr) -> Option<&str> {
	match e {
		Expr::Let(c, _, Value::Ctor(t, None), rest) => match &**rest {
			Expr::Halt(Atom::Var(r)) if r == c => Some(t.as_str()),
			_ => None,
		},
		_ => None,
	}
}

impl<'a> Cx<'a> {
	fn fresh(&self, base: &str) -> Name {
		self.counter.set(self.counter.get() + 1);
		let stem = base.split('~').next().unwrap_or(base);
		format!("{}~{}", stem, self.counter.get())
	}

	fn optimize_function(&self, f: &Function) -> Function {
		*self.var_tys.borrow_mut() = collect_fn_tys(f);
		self.budget.set(FUNCTION_BUDGET);
		let mut body = f.body.clone();
		let limit = MAX_FUNCTION_SIZE.max(expr_size(&body) * 4);
		for _ in 0..24 {
			self.changed.set(false);
			// only inlining can grow a function, so only keep a copy then
			let prev = self.inline.then(|| body.clone());
			body = self.simplify(body, &Default::default(), &Default::default(), 0, &f.name);
			if expr_size(&body) > limit {
				let safe = prev.unwrap_or_else(|| f.body.clone());
				return Function {
					body: safe,
					..f.clone()
				};
			}
			if !self.changed.get() {
				break;
			}
		}
		Function { body, ..f.clone() }
	}

	// true if `case scrut of arms` returns EXACTLY the Bool it scrutinises
	fn bool_identity(&self, scrut: &Atom, arms: &[Arm]) -> bool {
		if !matches!(scrut, Atom::Var(_)) {
			return false;
		}
		let t_name = self.lang.bool_ctor(true).to_string();
		let f_name = self.lang.bool_ctor(false).to_string();
		// what the first matching arm returns when the scrutinee is True / False
		let mut when_true: Option<bool> = None;
		let mut when_false: Option<bool> = None;
		for arm in arms {
			let Some(res) = returns_nullary_ctor(&arm.body) else {
				return false;
			};
			let res_true = if res == t_name {
				true
			} else if res == f_name {
				false
			} else {
				return false;
			};
			match &arm.pat {
				CasePat::Ctor(t) if *t == t_name => {
					when_true.get_or_insert(res_true);
				}
				CasePat::Ctor(t) if *t == f_name => {
					when_false.get_or_insert(res_true);
				}
				CasePat::Wild => {
					when_true.get_or_insert(res_true);
					when_false.get_or_insert(res_true);
				}
				_ => return false,
			}
		}
		when_true == Some(true) && when_false == Some(false)
	}

	fn subst_value(
		&self,
		v: Value,
		subst: &SubstMap,
		facts: &FactMap,
		depth: usize,
		owner: &str,
	) -> Value {
		let r = |a: &Atom| self.fold_global(resolve(subst, a));
		match v {
			Value::Atom(a) => Value::Atom(r(&a)),
			Value::App(f, a) => Value::App(r(&f), r(&a)),
			Value::Pair(a, b) => Value::Pair(r(&a), r(&b)),
			Value::Ctor(t, p) => Value::Ctor(t, p.map(|a| r(&a))),
			Value::Proj(a, s) => Value::Proj(r(&a), s),
			Value::Unwrap(a) => Value::Unwrap(r(&a)),
			Value::Lambda(p, t, body) => {
				let nb = self.simplify(*body, subst, facts, depth, owner);
				Value::Lambda(p, t, Box::new(nb))
			}
			other @ (Value::Str(_) | Value::Fail(_)) => other,
		}
	}

	fn simplify(
		&self,
		e: Expr,
		subst0: &SubstMap,
		facts0: &FactMap,
		depth: usize,
		owner: &str,
	) -> Expr {
		let (binds, tail) = flatten(e);
		let mut subst = subst0.clone();
		let mut facts = facts0.clone();
		let mut out: Binds = Vec::new();
		let mut cse: HashMap<String, Vec<usize>> = HashMap::new();
		let mut lams: HashMap<String, usize> = HashMap::new();

		for (x, ty, v) in binds {
			let v = self.subst_value(v, &subst, &facts, depth, owner);
			let first_new = out.len();
			self.step(
				x, ty, v, &mut subst, &mut facts, &mut out, &cse, &lams, depth, owner,
			);
			// index whatever `step` appended (a binding, or an inlined call's body)
			for i in first_new..out.len() {
				if let Some(k) = cse_bucket(&out[i].2) {
					cse.entry(k).or_default().push(i);
				}
				if matches!(out[i].2, Value::Lambda(..)) {
					lams.insert(out[i].0.clone(), i);
				}
			}
		}
		let tail = self.simplify_tail(tail, &subst, &facts, depth, owner);

		// dead code
		let mut live = expr_vars(&tail);
		let mut kept: Binds = Vec::new();
		for (x, t, v) in out.into_iter().rev() {
			if live.contains(&x) {
				live.extend(value_vars(&v));
				kept.push((x, t, v));
			} else {
				self.changed.set(true);
			}
		}
		kept.reverse();

		let mut tail = tail;
		if self.inline && self.in_try.get() == 0 {
			if let Some(inlined) = self.tail_inline(&mut kept, &tail, &facts, depth, owner) {
				let (more, new_tail) = flatten(inlined);
				kept.extend(more);
				tail = new_tail;
				self.changed.set(true);
			}
			self.case_of_case(&mut kept, &mut tail, &facts, depth, owner);
		}
		let (kept, tail) = self.float_in(kept, tail);

		rebuild(kept, tail)
	}

	// let r = f a b; r where f is small, no recursion w/ body ending in case: replace call w/ case
	fn tail_inline(
		&self,
		kept: &mut Binds,
		tail: &Expr,
		facts: &FactMap,
		depth: usize,
		owner: &str,
	) -> Option<Expr> {
		let Expr::Halt(Atom::Var(r)) = tail else {
			return None;
		};
		let (x, _, v) = kept.last()?;
		if x != r {
			return None;
		}
		let Value::App(f, a) = v else { return None };
		let (name, mut args): (String, Vec<Atom>) = match f {
			Atom::Global(n, _) => (n.clone(), Vec::new()),
			Atom::Var(p) => match facts.get(p) {
				Some(Fact::Pap(n, args)) => (n.clone(), args.clone()),
				_ => return None,
			},
			_ => return None,
		};
		args.push(a.clone());
		let callee = self.funcs.get(&name)?.clone();
		if depth >= MAX_DEPTH
			|| callee.params.len() != args.len()
			|| name == owner
			|| self.recursive.contains(&name)
			|| !ends_in_case(&callee.body)
		{
			return None;
		}
		let size = expr_size(&callee.body);
		if !self.single.contains(&name) {
			if size > TAIL_INLINE_MAX || self.budget.get() < size + 1 {
				return None;
			}
			self.budget.set(self.budget.get() - (size + 1));
		}

		let mut map = SubstMap::new();
		for ((p, _), a) in callee.params.iter().zip(args.iter()) {
			map.insert(p.clone(), a.clone());
		}
		let copy = self.rename_expr(&callee.body, &mut map);
		kept.pop();
		Some(self.simplify(copy, &Default::default(), facts, depth + 1, owner))
	}

	fn float_in(&self, mut kept: Binds, tail: Expr) -> (Binds, Expr) {
		let Expr::Case(scrut, mut arms) = tail else {
			return (kept, tail);
		};
		let mut scrut_vars = HashSet::new();
		atom_vars(&scrut, &mut scrut_vars);
		// free variables of each arm, kept current as bindings move in
		let mut arm_vars: Vec<HashSet<String>> = arms.iter().map(|a| expr_vars(&a.body)).collect();
		// variables used by the bindings after position i that stay in `kept`
		let mut later: HashSet<String> = HashSet::new();
		// operands of bindings that were copied into several arms
		let mut wanted: HashSet<String> = HashSet::new();
		let allow_dup = !disabled("dup");

		let mut i = kept.len();
		while i > 0 {
			i -= 1;
			let x = kept[i].0.clone();
			let mut targets: Vec<usize> = Vec::new();
			if !scrut_vars.contains(&x) && !later.contains(&x) {
				targets = arm_vars
					.iter()
					.enumerate()
					.filter(|(_, s)| s.contains(&x))
					.map(|(k, _)| k)
					.collect();
				if targets.len() > 1 {
					let dup_ok = allow_dup
						&& targets.len() <= MAX_DUP_ARMS
						&& !matches!(kept[i].2, Value::Lambda(..) | Value::Fail(_))
						&& (wanted.contains(&x)
							|| targets.iter().any(|&k| tail_var(&arms[k].body) == Some(&x)));
					if !dup_ok {
						targets.clear();
					}
				}
			}

			if targets.is_empty() {
				later.extend(value_vars(&kept[i].2));
				continue;
			}

			let (x, t, v) = kept.remove(i);
			let vv = value_vars(&v);
			if targets.len() > 1 {
				wanted.extend(vv.iter().cloned());
			}
			for (pos, &k) in targets.iter().enumerate() {
				let mut body =
					std::mem::replace(&mut arms[k].body, Expr::Halt(Atom::Lit(Literal::Int(0))));
				let name = if pos == 0 {
					x.clone()
				} else {
					let nm = self.fresh(&x);
					rename_var_in(&mut body, &x, &nm);
					self.var_tys.borrow_mut().insert(nm.clone(), t.clone());
					nm
				};
				arm_vars[k].remove(&x);
				arm_vars[k].extend(vv.iter().cloned());
				arms[k].body = Expr::Let(name, t.clone(), v.clone(), Box::new(body));
			}
			self.changed.set(true);
		}
		(kept, Expr::Case(scrut, arms))
	}

	#[allow(clippy::too_many_arguments)]
	fn step(
		&self,
		x: Name,
		ty: Ty,
		v: Value,
		subst: &mut SubstMap,
		facts: &mut FactMap,
		out: &mut Binds,
		cse: &HashMap<String, Vec<usize>>,
		lams: &HashMap<String, usize>,
		depth: usize,
		owner: &str,
	) {
		match &v {
			Value::Atom(a) => {
				if let Some(f) = fact_of_atom(a, facts) {
					facts.insert(x.clone(), f);
				}
				subst.insert(x, a.clone());
				self.changed.set(true);
				return;
			}
			Value::Proj(Atom::Var(n), side) => {
				if let Some(Fact::Pair(l, r)) = facts.get(n) {
					let picked = if *side == Side::Fst {
						l.clone()
					} else {
						r.clone()
					};
					if let Some(f) = fact_of_atom(&picked, facts) {
						facts.insert(x.clone(), f);
					}
					subst.insert(x, picked);
					self.changed.set(true);
					return;
				}
			}
			Value::Unwrap(Atom::Var(n)) => {
				if let Some(Fact::Ctor(_, Some(p))) = facts.get(n) {
					let picked = p.clone();
					if let Some(f) = fact_of_atom(&picked, facts) {
						facts.insert(x.clone(), f);
					}
					subst.insert(x, picked);
					self.changed.set(true);
					return;
				}
			}
			Value::App(f, a) => {
				if self.step_app(&x, &ty, f, a, subst, facts, out, depth, owner, lams) {
					return;
				}
			}
			_ => {}
		}

		record_fact(&x, &v, facts);

		if !matches!(v, Value::Lambda(..)) {
			let hit = cse_bucket(&v).and_then(|k| cse.get(&k)).and_then(|idxs| {
				idxs.iter()
					.map(|&i| &out[i])
					.find(|(_, t2, v2)| *t2 == ty && values_equal(v2, &v))
			});
			if let Some((y, _, _)) = hit {
				if let Some(f) = facts.get(y).cloned() {
					facts.insert(x.clone(), f);
				}
				subst.insert(x, Atom::Var(y.clone()));
				self.changed.set(true);
				return;
			}
		}
		out.push((x, ty, v));
	}

	#[allow(clippy::too_many_arguments)]
	fn step_app(
		&self,
		x: &Name,
		ty: &Ty,
		f: &Atom,
		a: &Atom,
		subst: &mut SubstMap,
		facts: &mut FactMap,
		out: &mut Binds,
		depth: usize,
		owner: &str,
		lams: &HashMap<String, usize>,
	) -> bool {
		let (name, mut args): (String, Vec<Atom>) = match f {
			Atom::Global(n, _) => (n.clone(), Vec::new()),
			Atom::Var(v) => match facts.get(v).cloned() {
				Some(Fact::Pap(n, args)) => (n, args),
				_ => return self.beta(x, f, a, subst, facts, out, lams, depth, owner),
			},
			Atom::Lit(_) | Atom::Method(..) => return false,
		};
		let arity = match self.funcs.get(&name) {
			Some(func) => func.params.len(),
			None => match self.externs.get(&name) {
				Some((n, _)) => *n,
				None => return false,
			},
		};
		args.push(a.clone());
		if args.len() < arity {
			facts.insert(x.clone(), Fact::Pap(name, args));
			return false;
		}
		if args.len() > arity {
			return false;
		}

		// saturated
		let folded = self
			.externs
			.get(&name)
			.and_then(|(_, i)| *i)
			.and_then(|op| fold_intrinsic(op, &args, self.lang));
		if let Some(folded) = folded {
			self.changed.set(true);
			match folded {
				Folded::Lit(l) => {
					facts.insert(x.clone(), Fact::Lit(l.clone()));
					subst.insert(x.clone(), Atom::Lit(l));
				}
				Folded::Ctor(tag) => {
					facts.insert(x.clone(), Fact::Ctor(tag.clone(), None));
					out.push((x.clone(), ty.clone(), Value::Ctor(tag, None)));
				}
				Folded::Str(s) => out.push((x.clone(), ty.clone(), Value::Str(s))),
			}
			return true;
		}
		if self.inline && self.funcs.contains_key(&name) {
			if let Some((binds, result)) = self.try_inline(&name, &args, facts, depth, owner) {
				for (n, _, v) in &binds {
					record_fact(n, v, facts);
				}
				if let Some(fact) = fact_of_atom(&result, facts) {
					facts.insert(x.clone(), fact);
				}
				out.extend(binds);
				subst.insert(x.clone(), result);
				self.changed.set(true);
				return true;
			}
		}
		false
	}

	fn is_concrete(a: &Atom, facts: &FactMap) -> bool {
		match a {
			Atom::Lit(_) => true,
			Atom::Var(n) => matches!(
				facts.get(n),
				Some(Fact::Lit(_))
					| Some(Fact::Ctor(..))
					| Some(Fact::Pair(..))
					| Some(Fact::Pap(..))
			),
			Atom::Global(..) | Atom::Method(..) => false,
		}
	}

	// if partial eval has no remaining case
	fn try_inline(
		&self,
		name: &str,
		args: &[Atom],
		facts: &FactMap,
		depth: usize,
		owner: &str,
	) -> Option<(Binds, Atom)> {
		if depth >= MAX_DEPTH {
			return None;
		}
		let callee = self.funcs.get(name)?.clone();
		if callee.params.len() != args.len() {
			return None;
		}
		let size = expr_size(&callee.body);
		let concrete = args.iter().any(|a| Self::is_concrete(a, facts));
		let recursive = self.recursive.contains(name);
		let all_concrete = args.iter().all(|a| Self::is_concrete(a, facts));
		let _ = all_concrete;

		let single = self.single.contains(name);
		let ok = !recursive
			&& name != owner
			&& (single || size <= SMALL_INLINE || (concrete && size <= CONCRETE_INLINE));
		if !ok || !can_reduce(&callee, args, facts) {
			return None;
		}
		if !single {
			if self.budget.get() < size + 1 {
				return None;
			}
			self.budget.set(self.budget.get() - (size + 1));
		}

		TRIED.fetch_add(1, Relaxed);

		let mut map = SubstMap::new();
		for ((p, _), a) in callee.params.iter().zip(args.iter()) {
			map.insert(p.clone(), a.clone());
		}
		let copy = self.rename_expr(&callee.body, &mut map);
		self.in_try.set(self.in_try.get() + 1);
		let simp = self.simplify(copy, &Default::default(), facts, depth + 1, owner);
		self.in_try.set(self.in_try.get() - 1);
		let (binds, tail) = flatten(simp);
		match tail {
			Expr::Halt(a) => {
				ACCEPTED.fetch_add(1, Relaxed);
				Some((binds, a))
			}
			_ => {
				WASTED.fetch_add(1, Relaxed);
				None
			}
		}
	}

	fn rn_atom(&self, a: &Atom, map: &SubstMap) -> Atom {
		match a {
			Atom::Var(n) => map.get(n).cloned().unwrap_or_else(|| a.clone()),
			other => other.clone(),
		}
	}

	fn rename_value(&self, v: &Value, map: &SubstMap) -> Value {
		let r = |a: &Atom| self.rn_atom(a, map);
		match v {
			Value::Atom(a) => Value::Atom(r(a)),
			Value::App(f, a) => Value::App(r(f), r(a)),
			Value::Pair(a, b) => Value::Pair(r(a), r(b)),
			Value::Ctor(t, p) => Value::Ctor(t.clone(), p.as_ref().map(r)),
			Value::Proj(a, s) => Value::Proj(r(a), *s),
			Value::Unwrap(a) => Value::Unwrap(r(a)),
			Value::Str(s) => Value::Str(s.clone()),
			Value::Fail(m) => Value::Fail(m.clone()),
			Value::Lambda(p, t, body) => {
				let np = self.fresh(p);
				self.var_tys.borrow_mut().insert(np.clone(), t.clone());
				let mut inner = map.clone();
				inner.insert(p.clone(), Atom::Var(np.clone()));
				let nb = self.rename_expr(body, &mut inner);
				Value::Lambda(np, t.clone(), Box::new(nb))
			}
		}
	}

	fn rename_expr(&self, e: &Expr, map: &mut SubstMap) -> Expr {
		match e {
			Expr::Let(x, t, v, rest) => {
				let nv = self.rename_value(v, map);
				let nx = self.fresh(x);
				self.var_tys.borrow_mut().insert(nx.clone(), t.clone());
				map.insert(x.clone(), Atom::Var(nx.clone()));
				let nrest = self.rename_expr(rest, map);
				Expr::Let(nx, t.clone(), nv, Box::new(nrest))
			}
			Expr::Halt(a) => Expr::Halt(self.rn_atom(a, map)),
			Expr::Case(a, arms) => Expr::Case(
				self.rn_atom(a, map),
				arms.iter()
					.map(|arm| Arm {
						pat: arm.pat.clone(),
						body: self.rename_expr(&arm.body, &mut map.clone()),
					})
					.collect(),
			),
		}
	}

	fn simplify_tail(
		&self,
		tail: Expr,
		subst: &SubstMap,
		facts: &FactMap,
		depth: usize,
		owner: &str,
	) -> Expr {
		match tail {
			Expr::Halt(a) => Expr::Halt(resolve(subst, &a)),
			Expr::Case(scrut, arms) => {
				let scrut = resolve(subst, &scrut);
				let (kl, kt): (Option<Literal>, Option<String>) = match &scrut {
					Atom::Lit(l) => (Some(l.clone()), None),
					Atom::Var(n) => match facts.get(n) {
						Some(Fact::Lit(l)) => (Some(l.clone()), None),
						Some(Fact::Ctor(t, _)) | Some(Fact::Tag(t)) => (None, Some(t.clone())),
						_ => (None, None),
					},
					Atom::Global(..) | Atom::Method(..) => (None, None),
				};
				if kl.is_some() || kt.is_some() {
					if let Some(chosen) = pick_arm(kl.as_ref(), kt.as_deref(), &arms) {
						self.changed.set(true);
						return self.simplify(chosen, subst, facts, depth, owner);
					}
				}
				let arms: Vec<Arm> = arms
					.into_iter()
					.map(|arm| {
						let mut f2 = facts.clone();
						if let Atom::Var(n) = &scrut {
							match &arm.pat {
								CasePat::Ctor(t) => {
									if !matches!(f2.get(n), Some(Fact::Ctor(..))) {
										f2.insert(n.clone(), Fact::Tag(t.clone()));
									}
								}
								CasePat::Lit(l) => {
									f2.insert(n.clone(), Fact::Lit(l.clone()));
								}
								CasePat::Wild => {}
							}
						}
						Arm {
							body: self.simplify(arm.body, subst, &f2, depth, owner),
							pat: arm.pat,
						}
					})
					.collect();
				if self.bool_identity(&scrut, &arms) {
					self.changed.set(true);
					return Expr::Halt(scrut);
				}
				Expr::Case(scrut, arms)
			}
			Expr::Let(..) => unreachable!("flatten never leaves a Let in tail position"),
		}
	}

	#[allow(clippy::too_many_arguments)]
	fn beta(
		&self,
		x: &Name,
		f: &Atom,
		a: &Atom,
		subst: &mut SubstMap,
		facts: &mut FactMap,
		out: &mut Binds,
		lams: &HashMap<String, usize>,
		depth: usize,
		owner: &str,
	) -> bool {
		if !self.inline || depth >= MAX_DEPTH {
			return false;
		}
		let Atom::Var(fv) = f else { return false };
		let Some(&i) = lams.get(fv) else { return false };
		let Value::Lambda(p, _, body) = &out[i].2 else {
			return false;
		};
		let size = expr_size(body);
		let concrete = Self::is_concrete(a, facts);
		if !(size <= SMALL_INLINE || (concrete && size <= CONCRETE_INLINE))
			|| self.budget.get() < size + 1
		{
			return false;
		}
		self.budget.set(self.budget.get() - (size + 1));

		let mut map = SubstMap::new();
		map.insert(p.clone(), a.clone());
		let copy = self.rename_expr(body, &mut map);

		self.in_try.set(self.in_try.get() + 1);
		let simp = self.simplify(copy, &Default::default(), facts, depth + 1, owner);
		self.in_try.set(self.in_try.get() - 1);

		let (binds, tail) = flatten(simp);
		let Expr::Halt(result) = tail else {
			return false;
		};
		for (n, _, v) in &binds {
			record_fact(n, v, facts);
		}
		if let Some(fact) = fact_of_atom(&result, facts) {
			facts.insert(x.clone(), fact);
		}
		out.extend(binds);
		subst.insert(x.clone(), result);
		self.changed.set(true);
		true
	}

	fn fold_global(&self, a: Atom) -> Atom {
		if let Atom::Global(n, _) = &a {
			if let Some(f) = self.funcs.get(n) {
				if f.params.is_empty() {
					if let Expr::Halt(Atom::Lit(l)) = &f.body {
						return Atom::Lit(l.clone());
					}
				}
			}
		}
		a
	}

	fn ty_of_atom(&self, a: &Atom) -> Option<Ty> {
		match a {
			Atom::Var(v) => self.var_tys.borrow().get(v).cloned(),
			Atom::Lit(Literal::Int(_)) => Some(Ty::Int),
			Atom::Lit(Literal::Float(_)) => Some(Ty::Float),
			Atom::Lit(Literal::Char(_)) => Some(Ty::Char),
			Atom::Lit(_) => None,
			Atom::Global(_, t) | Atom::Method(_, t) => Some(t.clone()),
		}
	}

	fn result_ty(&self, e: &Expr) -> Option<Ty> {
		let mut cur = e;
		loop {
			match cur {
				Expr::Let(_, _, _, rest) => cur = &**rest,
				Expr::Halt(a) => return self.ty_of_atom(a),
				Expr::Case(_, arms) => return arms.iter().find_map(|a| self.result_ty(&a.body)),
			}
		}
	}

	// outer arm `m` with the scrutinee replaced by the leaf value `a`
	fn coc_place(&self, c: &Coc, m: usize, a: &Atom) -> Expr {
		match &c.joins[m] {
			Some(j) => {
				let t = self.fresh("jmp");
				let ty = c.k_ty.expect("join point result type").clone();
				self.var_tys.borrow_mut().insert(t.clone(), ty.clone());
				Expr::Let(
					t.clone(),
					ty,
					Value::App(Atom::Var(j.clone()), a.clone()),
					Box::new(Expr::Halt(Atom::Var(t))),
				)
			}
			None => {
				let mut map = SubstMap::new();
				map.insert(c.x.clone(), a.clone());
				self.rename_expr(&c.arms[m].body, &mut map)
			}
		}
	}

	fn coc_dispatch(&self, c: &Coc, a: &Atom, fact: Option<Fact>) -> Expr {
		let known = match &fact {
			Some(Fact::Ctor(t, _)) | Some(Fact::Tag(t)) => {
				pick_arm_idx(None, Some(t.as_str()), c.arms)
			}
			Some(Fact::Lit(l)) => pick_arm_idx(Some(l), None, c.arms),
			_ => None,
		};
		if let Some(m) = known {
			return self.coc_place(c, m, a);
		}
		let arms = c
			.arms
			.iter()
			.enumerate()
			.map(|(m, arm)| Arm {
				pat: arm.pat.clone(),
				body: self.coc_place(c, m, a),
			})
			.collect();
		Expr::Case(a.clone(), arms)
	}

	// replace every leaf `Halt(a)` of `e` by the dispatch on `a`
	fn coc_replace(&self, e: Expr, facts: &FactMap, c: &Coc) -> Expr {
		let (binds, tail) = flatten(e);
		let mut local = facts.clone();
		for (x, _, v) in &binds {
			record_fact(x, v, &mut local);
		}
		let tail = match tail {
			Expr::Halt(a) => {
				let fact = fact_of_atom(&a, &local);
				self.coc_dispatch(c, &a, fact)
			}
			Expr::Case(s, arms) => Expr::Case(
				s,
				arms.into_iter()
					.map(|arm| Arm {
						pat: arm.pat,
						body: self.coc_replace(arm.body, &local, c),
					})
					.collect(),
			),
			Expr::Let(..) => unreachable!("flatten never leaves a Let in tail position"),
		};
		rebuild(binds, tail)
	}

	fn case_of_case(
		&self,
		kept: &mut Binds,
		tail: &mut Expr,
		facts: &FactMap,
		depth: usize,
		owner: &str,
	) -> bool {
		if disabled("coc") {
			return false;
		}
		let x = match &*tail {
			Expr::Case(Atom::Var(x), _) => x.clone(),
			_ => return false,
		};
		let Some(idx) = kept.iter().rposition(|(n, _, _)| *n == x) else {
			return false;
		};
		// the call's result must only feed the case
		if kept[idx + 1..]
			.iter()
			.any(|(_, _, v)| value_vars(v).contains(&x))
		{
			return false;
		}
		let (ty_x, f, a) = match &kept[idx] {
			(_, ty, Value::App(f, a)) => (ty.clone(), f.clone(), a.clone()),
			_ => return false,
		};
		let (name, mut args): (String, Vec<Atom>) = match &f {
			Atom::Global(n, _) => (n.clone(), Vec::new()),
			Atom::Var(p) => match facts.get(p) {
				Some(Fact::Pap(n, args)) => (n.clone(), args.clone()),
				_ => return false,
			},
			_ => return false,
		};
		args.push(a);
		let Some(callee) = self.funcs.get(&name).cloned() else {
			return false;
		};
		if depth >= MAX_DEPTH
			|| callee.params.len() != args.len()
			|| name == owner
			|| self.recursive.contains(&name)
			|| !ends_in_case(&callee.body)
			|| !has_known_leaf(&callee.body)
		{
			return false;
		}
		let size = expr_size(&callee.body);
		if (!self.single.contains(&name) && size > COC_CALLEE_MAX) || self.budget.get() < size + 1 {
			return false;
		}

		let arms_k: Vec<Arm> = match &*tail {
			Expr::Case(_, arms) => arms.clone(),
			_ => return false,
		};

		// inline and simplify a copy of the callee
		let mut map = SubstMap::new();
		for ((p, _), a) in callee.params.iter().zip(args.iter()) {
			map.insert(p.clone(), a.clone());
		}
		let copy = self.rename_expr(&callee.body, &mut map);
		self.budget.set(self.budget.get() - (size + 1));
		let simp = self.simplify(copy, &Default::default(), facts, depth + 1, owner);
		if !ends_in_case(&simp) {
			return false;
		}

		// what do the leaves look like? only want this if some outer arm gets resolved
		let mut leaf_facts: Vec<Option<Fact>> = Vec::new();
		collect_leaf_facts(&simp, facts, &mut leaf_facts);
		let known = leaf_facts
			.iter()
			.filter(|f| {
				matches!(
					f,
					Some(Fact::Ctor(..)) | Some(Fact::Tag(_)) | Some(Fact::Lit(_))
				)
			})
			.count();
		if leaf_facts.len() > COC_MAX_LEAVES || known == 0 {
			return false;
		}

		// how many leaves reach each outer arm
		let mut uses = vec![0usize; arms_k.len()];
		for fct in &leaf_facts {
			let target = match fct {
				Some(Fact::Ctor(t, _)) | Some(Fact::Tag(t)) => {
					pick_arm_idx(None, Some(t.as_str()), &arms_k)
				}
				Some(Fact::Lit(l)) => pick_arm_idx(Some(l), None, &arms_k),
				_ => None,
			};
			match target {
				Some(m) => uses[m] += 1,
				None => uses.iter_mut().for_each(|u| *u += 1),
			}
		}
		let join: Vec<bool> = arms_k
			.iter()
			.zip(uses.iter())
			.map(|(arm, &u)| u > 1 && expr_size(&arm.body) > COC_DUP_MAX)
			.collect();

		let k_ty = arms_k.iter().find_map(|arm| self.result_ty(&arm.body));
		if join.iter().any(|&j| j) && k_ty.is_none() {
			return false;
		}

		// join points: `let j = fn x' -> <arm> end`
		let mut join_names: Vec<Option<Name>> = vec![None; arms_k.len()];
		let mut join_lets: Binds = Vec::new();
		for (m, arm) in arms_k.iter().enumerate() {
			if !join[m] {
				continue;
			}
			let j = self.fresh("join");
			let param = self.fresh(&x);
			let mut pm = SubstMap::new();
			pm.insert(x.clone(), Atom::Var(param.clone()));
			let body = self.rename_expr(&arm.body, &mut pm);
			let jty = Ty::Fn(
				Box::new(ty_x.clone()),
				Box::new(k_ty.clone().expect("join point result type")),
			);
			{
				let mut vt = self.var_tys.borrow_mut();
				vt.insert(j.clone(), jty.clone());
				vt.insert(param.clone(), ty_x.clone());
			}
			join_lets.push((
				j.clone(),
				jty,
				Value::Lambda(param, ty_x.clone(), Box::new(body)),
			));
			join_names[m] = Some(j);
		}

		let ctx = Coc {
			x: &x,
			arms: &arms_k,
			joins: &join_names,
			k_ty: k_ty.as_ref(),
		};
		let new_inner = self.coc_replace(simp, facts, &ctx);

		kept.remove(idx);
		let (more, new_tail) = flatten(new_inner);
		kept.extend(join_lets);
		kept.extend(more);
		*tail = new_tail;
		self.changed.set(true);
		true
	}
}

fn is_valid_entry_type(ty: &Ty, lang: &Lang) -> bool {
	match ty {
		Ty::Unit | Ty::Int => true,
		Ty::App(f, a) => {
			matches!(f.as_ref(), Ty::Named(n) if n == lang.item(LangItem::IoType))
				&& matches!(a.as_ref(), Ty::Unit | Ty::Int)
		}
		_ => false,
	}
}

pub fn check_entry(program: &IrProgram, entry: &str, lang: &Lang) -> Result<(), Diagnostic> {
	let Some(f) = program.functions.iter().find(|f| f.name == entry) else {
		let known: Vec<&str> = program
			.functions
			.iter()
			.filter(|f| f.name.ends_with(":main"))
			.map(|f| f.name.as_str())
			.collect();
		let d = Diagnostic::error(format!("no top-level binding named `{}`", entry), None);
		return Err(if known.is_empty() {
			d.with_help(
				"define `let main : IO Unit = ... end` in your entry module, or pass --entry",
			)
		} else {
			d.with_help(format!(
				"did you mean one of: {}? (use --entry)",
				known.join(", ")
			))
		});
	};
	if !f.params.is_empty() {
		return Err(Diagnostic::error(
			format!("entry point `{}` must not take parameters", entry),
			Some(f.span),
		));
	}
	if !is_valid_entry_type(&f.ret, lang) {
		return Err(Diagnostic::error(
			format!(
				"entry point `{}` must have type Unit, Int, IO Unit or IO Int (found {})",
				entry,
				display_ty(&f.ret)
			),
			Some(f.span),
		));
	}
	Ok(())
}

pub fn prune_unreachable(program: &mut IrProgram, entry: &str) {
	let by_name: HashMap<&str, &Function> = program
		.functions
		.iter()
		.map(|f| (f.name.as_str(), f))
		.collect();
	let mut reachable: HashSet<String> = HashSet::new();
	let mut work = vec![entry.to_string()];
	reachable.insert(entry.to_string());
	while let Some(n) = work.pop() {
		if let Some(f) = by_name.get(n.as_str()) {
			for r in referenced_globals(&f.body) {
				if reachable.insert(r.clone()) {
					work.push(r);
				}
			}
		}
	}
	program.functions.retain(|f| reachable.contains(&f.name));
	program.externs.retain(|e| reachable.contains(&e.name));
}

// (global, args applied so far) if `a` is a global or a known partial application
fn pap_of(a: &Atom, paps: &HashMap<String, (String, usize)>) -> Option<(String, usize)> {
	match a {
		Atom::Global(g, _) => Some((g.clone(), 0)),
		Atom::Var(v) => paps.get(v).cloned(),
		_ => None,
	}
}

// Does evaluating `e` do nothing but allocate closures / paps,
// build values, project, and test ctors?
fn cheap_tail(
	e: &Expr,
	arity: &HashMap<String, usize>,
	paps: &mut HashMap<String, (String, usize)>,
) -> bool {
	let mut cur = e;
	loop {
		match cur {
			Expr::Halt(_) => return true,
			Expr::Case(_, arms) => {
				return arms
					.iter()
					.all(|arm| cheap_tail(&arm.body, arity, &mut paps.clone()));
			}
			Expr::Let(x, _, v, rest) => {
				let ok = match v {
					Value::Atom(a) => {
						if let Some(p) = pap_of(a, paps) {
							paps.insert(x.clone(), p);
						}
						true
					}
					// only a *partial* application is free; a saturated or
					// unknown-function application is real work
					Value::App(f, _) => match pap_of(f, paps) {
						Some((g, n)) => match arity.get(&g) {
							Some(&ar) if n + 1 < ar => {
								paps.insert(x.clone(), (g, n + 1));
								true
							}
							_ => false,
						},
						None => false,
					},
					Value::Lambda(..)
					| Value::Pair(..)
					| Value::Ctor(..)
					| Value::Proj(..)
					| Value::Unwrap(_)
					| Value::Fail(_) => true,
					// rebuilt on every call after expansion: not free
					Value::Str(_) => false,
				};
				if !ok {
					return false;
				}
				cur = &**rest;
			}
		}
	}
}

// Apply the new parameters to the result of every tail position of `e`.
// `fn_ty` is the function type of `e`'s result before expansion.
fn apply_in_tails(e: Expr, args: &[(Name, Ty)], fn_ty: &Ty, fresh: &dyn Fn(&str) -> Name) -> Expr {
	let (binds, tail) = flatten(e);
	let tail = match tail {
		Expr::Halt(a) => {
			let mut apps: Binds = Vec::new();
			let mut cur = a;
			let mut cur_ty = fn_ty.clone();
			for (name, _) in args {
				let res_ty = match &cur_ty {
					Ty::Fn(_, r) => (**r).clone(),
					other => other.clone(),
				};
				let t = fresh("eta");
				apps.push((
					t.clone(),
					res_ty.clone(),
					Value::App(cur, Atom::Var(name.clone())),
				));
				cur = Atom::Var(t);
				cur_ty = res_ty;
			}
			rebuild(apps, Expr::Halt(cur))
		}
		Expr::Case(s, arms) => Expr::Case(
			s,
			arms.into_iter()
				.map(|arm| Arm {
					pat: arm.pat,
					body: apply_in_tails(arm.body, args, fn_ty, fresh),
				})
				.collect(),
		),
		Expr::Let(..) => unreachable!("flatten never leaves a Let in tail position"),
	};
	rebuild(binds, tail)
}

fn eta_expand(f: &mut Function, k: usize, counter: &Cell<u64>) {
	let fresh = |base: &str| -> Name {
		counter.set(counter.get() + 1);
		format!("{}~{}", base, counter.get())
	};
	let (arg_tys, new_ret) = peel_fn(&f.ret, k);
	let extra: Vec<(Name, Ty)> = arg_tys.into_iter().map(|t| (fresh("eta"), t)).collect();
	let body = std::mem::replace(&mut f.body, Expr::Halt(Atom::Lit(Literal::Int(0))));
	f.body = apply_in_tails(body, &extra, &f.ret, &fresh);
	f.params.extend(extra);
	f.ret = new_ret;
	// `f.ty` (the full signature) unchanged
}

// Repeats until nothing changes, because raising one function (say an alias
// like `const$56`) is what makes its callers' bodies recognisably cheap.
// Each function is expanded at most once (afterwards its `ret` has no arrows),
// so this terminates.
fn raise_arity(
	program: &mut IrProgram,
	externs: &HashMap<String, (usize, Option<Intrinsic>)>,
	counter: &Cell<u64>,
) {
	loop {
		// stale within a round is fine: arities only grow, so a stale value
		// can only make `cheap_tail` more conservative, never wrong
		let arity: HashMap<String, usize> = program
			.functions
			.iter()
			.map(|f| (f.name.clone(), f.params.len()))
			.chain(externs.iter().map(|(n, (a, _))| (n.clone(), *a)))
			.collect();
		let mut changed = false;
		for f in program.functions.iter_mut() {
			let k = count_arrows(&f.ret);
			if k == 0 || !cheap_tail(&f.body, &arity, &mut HashMap::new()) {
				continue;
			}
			eta_expand(f, k, counter);
			changed = true;
		}
		if !changed {
			break;
		}
	}
}

fn disabled(feature: &str) -> bool {
	static OFF: std::sync::OnceLock<Vec<String>> = std::sync::OnceLock::new();
	OFF.get_or_init(|| {
		std::env::var("IOTA_OPT_DISABLE")
			.map(|v| v.split(',').map(|s| s.trim().to_string()).collect())
			.unwrap_or_default()
	})
	.iter()
	.any(|s| s == feature)
}

fn count_refs(e: &Expr, counts: &mut HashMap<String, usize>) {
	fn atom(a: &Atom, c: &mut HashMap<String, usize>) {
		if let Atom::Global(n, _) | Atom::Method(n, _) = a {
			*c.entry(n.clone()).or_insert(0) += 1;
		}
	}
	match e {
		Expr::Halt(a) => atom(a, counts),
		Expr::Case(s, arms) => {
			atom(s, counts);
			for arm in arms {
				count_refs(&arm.body, counts);
			}
		}
		Expr::Let(_, _, v, rest) => {
			match v {
				Value::Atom(a) | Value::Proj(a, _) | Value::Unwrap(a) => atom(a, counts),
				Value::App(a, b) | Value::Pair(a, b) => {
					atom(a, counts);
					atom(b, counts);
				}
				Value::Ctor(_, Some(a)) => atom(a, counts),
				Value::Lambda(_, _, body) => count_refs(body, counts),
				_ => {}
			}
			count_refs(rest, counts);
		}
	}
}

fn single_site_set(program: &IrProgram, recursive: &HashSet<String>) -> HashSet<String> {
	if disabled("single") {
		return HashSet::new();
	}
	let mut counts: HashMap<String, usize> = HashMap::new();
	for f in &program.functions {
		count_refs(&f.body, &mut counts);
	}
	counts
		.into_iter()
		.filter(|(n, c)| *c == 1 && !recursive.contains(n) && !n.contains("$lam"))
		.map(|(n, _)| n)
		.collect()
}

const COC_CALLEE_MAX: usize = 48; // size of inlined function
const COC_MAX_LEAVES: usize = 6; // leaves of inlined case tree
const COC_DUP_MAX: usize = 12; // outer arms up to this size are copied, not joined

struct Coc<'a> {
	x: &'a Name,
	arms: &'a [Arm],
	joins: &'a [Option<Name>],
	k_ty: Option<&'a Ty>,
}

fn pick_arm_idx(
	known_lit: Option<&Literal>,
	known_tag: Option<&str>,
	arms: &[Arm],
) -> Option<usize> {
	arms.iter().position(|arm| match &arm.pat {
		CasePat::Wild => true,
		CasePat::Lit(l) => known_lit.map_or(false, |k| lit_eq(l, k)),
		CasePat::Ctor(t) => known_tag.map_or(false, |k| k == t),
	})
}

// does some leaf of the (not yet simplified) body return a ctor or literal?
fn has_known_leaf(e: &Expr) -> bool {
	let mut known: HashSet<&str> = HashSet::new();
	let mut cur = e;
	loop {
		match cur {
			Expr::Let(x, _, v, rest) => {
				if matches!(v, Value::Ctor(..) | Value::Atom(Atom::Lit(_))) {
					known.insert(x.as_str());
				}
				cur = &**rest;
			}
			Expr::Halt(Atom::Lit(_)) => return true,
			Expr::Halt(Atom::Var(n)) => return known.contains(n.as_str()),
			Expr::Halt(_) => return false,
			Expr::Case(_, arms) => return arms.iter().any(|a| has_known_leaf(&a.body)),
		}
	}
}

// what each leaf of `e` is known to be (a ctor, a literal, or nothing)
fn collect_leaf_facts(e: &Expr, facts: &FactMap, out: &mut Vec<Option<Fact>>) {
	let mut local = facts.clone();
	let mut cur = e;
	loop {
		match cur {
			Expr::Let(x, _, v, rest) => {
				record_fact(x, v, &mut local);
				cur = &**rest;
			}
			Expr::Halt(a) => {
				out.push(fact_of_atom(a, &local));
				return;
			}
			Expr::Case(_, arms) => {
				for arm in arms {
					collect_leaf_facts(&arm.body, &local, out);
				}
				return;
			}
		}
	}
}
