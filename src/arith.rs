// int semantics for values at compile time. used by:
//   - the optimizer's constant folder (`optimize.rs::fold_intrinsic`)
//   - the compile-time evaluator (`consteval.rs`, when it lands)
//   - conversion of values into type-level numbers
//
// runtime defines:
//   - 32 bit 2's comp. wrapping arithmetic
//   - euclidean div/mod
// anything disagreeing is a bug

#![allow(dead_code)]

pub fn iadd(a: i32, b: i32) -> i32 {
	a.wrapping_add(b)
}

pub fn isub(a: i32, b: i32) -> i32 {
	a.wrapping_sub(b)
}

pub fn imul(a: i32, b: i32) -> i32 {
	a.wrapping_mul(b)
}

pub fn idiv(a: i32, b: i32) -> Option<i32> {
	(b != 0).then(|| a.wrapping_div_euclid(b))
}

pub fn imod(a: i32, b: i32) -> Option<i32> {
	(b != 0).then(|| a.wrapping_rem_euclid(b))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatError {
	/// `Int -> Nat` of a negative number
	Negative(i32),
	/// A type-level number overflowed `u64`
	Overflow,
}

impl std::fmt::Display for NatError {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			NatError::Negative(n) => write!(f, "cannot convert negative number {} to a Nat", n),
			NatError::Overflow => write!(f, "type-level number is too large"),
		}
	}
}

/// Checked `Int -> Nat`: never wraps
pub fn int_to_nat(i: i32) -> Result<u64, NatError> {
	if i < 0 {
		Err(NatError::Negative(i))
	} else {
		Ok(i as u64)
	}
}

pub fn nat_add(a: u64, b: u64) -> Result<u64, NatError> {
	a.checked_add(b).ok_or(NatError::Overflow)
}

pub fn nat_mul(a: u64, b: u64) -> Result<u64, NatError> {
	a.checked_mul(b).ok_or(NatError::Overflow)
}

/// *NO truncated-at-zero subtraction*. type-level `Sub` only reduces when
/// `a >= b` is provable, so the caller has to check first.
pub fn nat_sub(a: u64, b: u64) -> Option<u64> {
	a.checked_sub(b)
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn wraps_like_the_runtime() {
		assert_eq!(iadd(i32::MAX, 1), i32::MIN);
		assert_eq!(isub(i32::MIN, 1), i32::MAX);
		assert_eq!(imul(i32::MAX, 2), -2);
	}

	// golden values for rt_idiv / rt_imod: Euclidean, remainder always >= 0
	#[test]
	fn euclidean_division() {
		assert_eq!(idiv(7, 2), Some(3));
		assert_eq!(imod(7, 2), Some(1));
		assert_eq!(idiv(-7, 2), Some(-4));
		assert_eq!(imod(-7, 2), Some(1));
		assert_eq!(idiv(7, -2), Some(-3));
		assert_eq!(imod(7, -2), Some(1));
		assert_eq!(idiv(-7, -2), Some(4));
		assert_eq!(imod(-7, -2), Some(1));
		assert_eq!(idiv(i32::MIN, -1), Some(i32::MIN));
		assert_eq!(imod(i32::MIN, -1), Some(0));
		assert_eq!(idiv(1, 0), None);
		assert_eq!(imod(1, 0), None);
	}

	// a direct port of rt_idiv / rt_imod from runtime/iota_rt.c (the b == 0 case is
	// excluded: the folder never folds it)
	fn c_idiv(a: i32, b: i32) -> i32 {
		if b == -1 {
			return (0u32.wrapping_sub(a as u32)) as i32;
		}
		let mut q = a.wrapping_div(b);
		let r = a.wrapping_rem(b);
		if r < 0 {
			q += if b < 0 { 1 } else { -1 };
		}
		q
	}
	fn c_imod(a: i32, b: i32) -> i32 {
		if b == -1 {
			return 0;
		}
		let mut r = a.wrapping_rem(b);
		if r < 0 {
			// the C code writes `-b`, which is signed overflow (UB) for b == INT_MIN;
			// it wraps on every targeted platform, so model that
			r = r.wrapping_add(if b < 0 { b.wrapping_neg() } else { b });
		}
		r
	}

	#[test]
	fn agrees_with_the_c_runtime() {
		let edge = [
			i32::MIN,
			i32::MIN + 1,
			-100,
			-7,
			-2,
			-1,
			0,
			1,
			2,
			7,
			100,
			i32::MAX,
		];
		for &a in &edge {
			for &b in edge.iter().filter(|b| **b != 0) {
				assert_eq!(idiv(a, b), Some(c_idiv(a, b)), "idiv {} {}", a, b);
				assert_eq!(imod(a, b), Some(c_imod(a, b)), "imod {} {}", a, b);
			}
		}
	}

	#[test]
	fn division_identity() {
		for a in -20..=20 {
			for b in (-5..=5).filter(|b| *b != 0) {
				let (q, r) = (idiv(a, b).unwrap(), imod(a, b).unwrap());
				assert!(r >= 0 && r < b.abs());
				assert_eq!(iadd(imul(q, b), r), a);
			}
		}
	}

	#[test]
	fn nat_conversion_is_checked() {
		assert_eq!(int_to_nat(0), Ok(0));
		assert_eq!(int_to_nat(80), Ok(80));
		assert_eq!(int_to_nat(-1), Err(NatError::Negative(-1)));
		assert_eq!(nat_add(u64::MAX, 1), Err(NatError::Overflow));
		assert_eq!(nat_mul(u64::MAX, 2), Err(NatError::Overflow));
		assert_eq!(nat_sub(3, 4), None);
		assert_eq!(nat_sub(4, 3), Some(1));
	}
}
