// type-level queries used by spec and backend

use im::HashMap as ImHashMap;
use std::collections::HashMap;

use crate::typechecker::{ty_head_name, Scheme, Ty, TypeEnv};

pub struct TypeInfo {
	pub ctor_scheme: HashMap<String, Scheme>,
	pub type_ctors: HashMap<String, Vec<String>>, // name, ctor names (sorted)
	pub type_arity: ImHashMap<String, usize>,
	pub aliases: ImHashMap<String, Ty>,
}

/// App(App(f, a), b) -> (f, [a, b]).
pub fn spine(t: &Ty) -> (&Ty, Vec<&Ty>) {
	let mut args = Vec::new();
	let mut cur = t;
	while let Ty::App(f, a) = cur {
		args.push(&**a);
		cur = &**f;
	}
	args.reverse();
	(cur, args)
}

pub fn default_vars(t: &Ty) -> Ty {
	match t {
		Ty::Var(_) => Ty::Unit,
		Ty::Fn(a, b) => Ty::Fn(Box::new(default_vars(a)), Box::new(default_vars(b))),
		Ty::Product(a, b) => Ty::Product(Box::new(default_vars(a)), Box::new(default_vars(b))),
		Ty::Sum(a, b) => Ty::Sum(Box::new(default_vars(a)), Box::new(default_vars(b))),
		Ty::App(a, b) => Ty::App(Box::new(default_vars(a)), Box::new(default_vars(b))),
		o => o.clone(),
	}
}

pub fn has_vars(t: &Ty) -> bool {
	match t {
		Ty::Var(_) => true,
		Ty::Fn(a, b) | Ty::Product(a, b) | Ty::Sum(a, b) | Ty::App(a, b) => {
			has_vars(a) || has_vars(b)
		}
		_ => false,
	}
}

impl TypeInfo {
	pub fn new(env: &TypeEnv) -> Self {
		let mut ctor_scheme = HashMap::new();
		let mut type_ctors: HashMap<String, Vec<String>> = HashMap::new();
		for (key, scheme) in &env.data_ctors {
			if key.len() == 2 {
				ctor_scheme.insert(format!("{}:{}", key[0], key[1]), scheme.clone());
				type_ctors
					.entry(key[0].clone())
					.or_default()
					.push(key[1].clone());
			}
		}
		for v in type_ctors.values_mut() {
			v.sort();
			v.dedup();
		}
		let fake: Vec<String> = type_ctors
			.iter()
			.filter(|(n, cs)| {
				env.type_aliases.contains_key(*n)
					&& cs
						.iter()
						.any(|c| c != *n && env.type_ctors.contains_key(c.as_str()))
			})
			.map(|(n, _)| n.clone())
			.collect();
		for n in fake {
			type_ctors.remove(&n);
		}
		TypeInfo {
			ctor_scheme,
			type_ctors,
			type_arity: env.type_ctors.clone(),
			aliases: env.type_aliases.clone(),
		}
	}

	fn nominalize_sum(&self, t: &Ty) -> Option<Ty> {
		fn leaves(t: &Ty, out: &mut Vec<String>) -> bool {
			match t {
				Ty::Sum(a, b) => leaves(a, out) && leaves(b, out),
				Ty::Named(n) => {
					out.push(n.clone());
					true
				}
				Ty::App(..) => match spine(t).0 {
					Ty::Named(n) => {
						out.push(n.clone());
						true
					}
					_ => false,
				},
				_ => false,
			}
		}
		let mut ls = Vec::new();
		if !leaves(t, &mut ls) {
			return None;
		}
		ls.sort();
		ls.dedup();
		self.type_ctors
			.iter()
			.find(|(tn, cs)| self.type_arity.get(*tn).copied().unwrap_or(0) == 0 && **cs == ls)
			.map(|(tn, _)| Ty::Named(tn.clone()))
	}

	fn expand_head(&self, t: &Ty) -> Option<Ty> {
		match t {
			Ty::Named(n) if !self.type_ctors.contains_key(n) => self.aliases.get(n).cloned(),
			Ty::Sum(..) => self.nominalize_sum(t),
			_ => None,
		}
	}

	pub fn norm(&self, t: &Ty) -> Ty {
		let mut t = t.clone();
		for _ in 0..64 {
			match self.expand_head(&t) {
				Some(e) => t = e,
				None => break,
			}
		}
		match t {
			Ty::Fn(a, b) => Ty::Fn(Box::new(self.norm(&a)), Box::new(self.norm(&b))),
			Ty::Product(a, b) => Ty::Product(Box::new(self.norm(&a)), Box::new(self.norm(&b))),
			Ty::Sum(a, b) => Ty::Sum(Box::new(self.norm(&a)), Box::new(self.norm(&b))),
			Ty::App(a, b) => Ty::App(Box::new(self.norm(&a)), Box::new(self.norm(&b))),
			o => o,
		}
	}

	pub fn instance_head(&self, ty: &Ty) -> String {
		let t = self.norm(ty);
		match spine(&t).0 {
			Ty::Named(n) => n.clone(),
			_ => ty_head_name(&t),
		}
	}

	pub fn alias_heads(&self, head: &str) -> Vec<String> {
		let mut v: Vec<String> = self
			.aliases
			.iter()
			.filter(|(_, ty)| self.instance_head(ty) == head)
			.map(|(n, _)| n.clone())
			.collect();
		v.sort();
		v
	}
}
