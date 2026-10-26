// everything the compiler knows *by name* about the prelude
//
// everything read from the lang manifest in 2 tables:
//   [lang]         roles the compiler must be able to find (entry point, list and bool types + constructors, IO type, &c)
//   [intrinsics]   the prelude bindings the backend implements itself (math, comparisons, &c)

use std::collections::HashMap;

macro_rules! lang_items {
	($($variant:ident = $key:literal),* $(,)?) => {
		#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
		pub enum LangItem { $($variant),* }
		impl LangItem {
			pub const ALL: &'static [LangItem] = &[$(LangItem::$variant),*];
			pub fn key(self) -> &'static str {
				match self { $(LangItem::$variant => $key),* }
			}
			fn from_key(k: &str) -> Option<LangItem> {
				match k { $($key => Some(LangItem::$variant),)* _ => None }
			}
		}
	};
}

lang_items! {
	Entry     = "entry",
	IoType    = "io.type",
	ListType  = "list.type",
	ListNil   = "list.nil",
	ListCons  = "list.cons",
	BoolFalse = "bool.false",
	BoolTrue  = "bool.true",
	SumLeft   = "sum.left",
	SumRight  = "sum.right",
}

macro_rules! intrinsics {
	($($variant:ident = $key:literal),* $(,)?) => {
		#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
		pub enum Intrinsic {
			$($variant,)*
			/// An effectful runtime primitive from `rtprims::TABLE` (by index).
			Rt(u8),
		}
		#[allow(unused)]
		impl Intrinsic {
			pub fn key(self) -> &'static str {
				match self {
					$(Intrinsic::$variant => $key,)*
					Intrinsic::Rt(i) => crate::rtprims::get(i).key,
				}
			}
			fn from_key(k: &str) -> Option<Intrinsic> {
				match k {
					$($key => Some(Intrinsic::$variant),)*
					_ => crate::rtprims::by_key(k).map(Intrinsic::Rt),
				}
			}
		}
	};
}

intrinsics! {
	IAdd = "iadd", ISub = "isub", IMul = "imul", IDiv = "idiv", IMod = "imod",
	IEq = "ieq", INeq = "ineq", IGr = "igr", IGre = "igre", ILs = "ils", ILse = "ilse",
	FAdd = "fadd", FSub = "fsub", FMul = "fmul", FDiv = "fdiv",
	FEq = "feq", FNeq = "fneq", FGr = "fgr", FGre = "fgre", FLs = "fls", FLse = "flse",
	IAnd = "iand", IOr = "ior", IXor = "ixor", IShl = "ishl", IShr = "ishr", ISar = "isar",
	CharOrd = "ord", CharChr = "chr", IToF = "itof", FToI = "ftoi", UnitVal = "unit",
	ShowInt = "show_int", ShowFloat = "show_float", FloatRepr = "float_repr",
	Print = "print", Println = "println", GetLn = "getln",
	IoReturn = "io_return", IoBind = "io_bind",
	SumLeft = "sum_left", SumRight = "sum_right",
}

impl Intrinsic {
	/// Cheap, total and effect-free: safe to evaluate speculatively when the
	/// operands are already values (no thunk needed).
	pub fn is_cheap(self) -> bool {
		use Intrinsic::*;
		matches!(
			self,
			IAdd | ISub
				| IAnd | IOr | IXor
				| IShl | IShr
				| ISar | CharOrd
				| CharChr | IToF
				| IMul | IEq | INeq
				| IGr | IGre | ILs
				| ILse | FAdd
				| FSub | FMul
				| FDiv | FEq | FNeq
				| FGr | FGre | FLs
				| FLse
		)
	}
}

#[derive(Debug, Clone)]
pub struct Lang {
	items: HashMap<LangItem, String>,
	intrinsics: HashMap<String, Intrinsic>,
}

impl Lang {
	/// Parse a manifest. On failure returns one message per problem
	/// (`origin:line: ...`) for `main` to report.
	pub fn parse(text: &str, origin: &str) -> Result<Lang, Vec<String>> {
		let mut items = HashMap::new();
		let mut intrinsics = HashMap::new();
		let mut errors = Vec::new();
		let mut section = String::new();
		for (n, raw) in text.lines().enumerate() {
			let line = raw.split('#').next().unwrap_or("").trim();
			if line.is_empty() {
				continue;
			}
			let at = |msg: String| format!("{}:{}: {}", origin, n + 1, msg);
			if let Some(name) = line.strip_prefix('[').and_then(|l| l.strip_suffix(']')) {
				section = name.trim().to_string();
				if section != "lang" && section != "intrinsics" {
					errors.push(at(format!("unknown section `[{}]`", section)));
				}
				continue;
			}
			let Some((k, v)) = line.split_once('=') else {
				errors.push(at(format!("expected `key = value`, found `{}`", line)));
				continue;
			};
			let (k, v) = (k.trim(), v.trim());
			match section.as_str() {
				"lang" => match LangItem::from_key(k) {
					Some(item) => {
						items.insert(item, v.to_string());
					}
					None => errors.push(at(format!("unknown lang item `{}`", k))),
				},
				"intrinsics" => match Intrinsic::from_key(v) {
					Some(i) => {
						intrinsics.insert(k.to_string(), i);
					}
					None => errors.push(at(format!("unknown intrinsic `{}`", v))),
				},
				_ => errors.push(at("entry outside any section".to_string())),
			}
		}
		for item in LangItem::ALL {
			if !items.contains_key(item) {
				errors.push(format!("{}: missing lang item `{}`", origin, item.key()));
			}
		}
		if errors.is_empty() {
			Ok(Lang { items, intrinsics })
		} else {
			Err(errors)
		}
	}

	pub fn item(&self, i: LangItem) -> &str {
		&self.items[&i]
	}

	/// The prelude binding implemented by intrinsic `canonical`, if it is one.
	pub fn intrinsic(&self, canonical: &str) -> Option<Intrinsic> {
		self.intrinsics.get(canonical).copied()
	}

	pub fn bool_ctor(&self, b: bool) -> &str {
		self.item(if b {
			LangItem::BoolTrue
		} else {
			LangItem::BoolFalse
		})
	}
}

/// `"List:Cons"` -> `("List", "Cons")`.
pub fn split_ctor(canonical: &str) -> (&str, &str) {
	canonical.rsplit_once(':').unwrap_or(("", canonical))
}

/// The part after the last `:`.
pub fn bare(name: &str) -> &str {
	name.rsplit(':').next().unwrap_or(name)
}
