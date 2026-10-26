//! runtime primitives: effectful operations implemented in C
//! (`runtime/iota_rt.c`) and exposed to Iota as `IO` actions.
//!
//! Each row is the whole story for one primitive, so adding one never needs a
//! change to the lowering or the code generator:
//!
//!   1. a row here,
//!   2. the C function in `runtime/iota_rt.c`,
//!   3. a line in `prelude/lang.def` mapping a prelude binding to `key`,
//!   4. the `= undefined` binding in the prelude (or a std module).
//!
//! ### Calling convention
//!
//! The C function takes the arguments in order:
//!
//! | kind    | C parameter  | notes                                                          |
//! |---------|--------------|----------------------------------------------------------------|
//! | `Int`   | `int32_t`    | also used for `Char` and for flags                             |
//! | `Float` | `double`     |                                                                |
//! | `Str`   | `StrBuf *`   | the forced string; the callee owns it and must free it          |
//!
//! and returns, depending on `ret`:
//!
//! | kind    | C result                                                                     |
//! |---------|------------------------------------------------------------------------------|
//! | `Unit`  | `void`                                                                       |
//! | `Int`   | `int32_t`                                                                    |
//! | `Float` | `double`                                                                     |
//! | `Str`   | `uint32_t *` (from `rt_buf_alloc`), with an extra trailing `uint64_t *len`   |
//!
//! Fallible operations return a `Str` whose first code point is a status code
//! (0 = success) and whose remainder is the payload (or the error message);
//! `std/io.iota` decodes that into an `Either`. That keeps ADT construction out
//! of the code generator and avoids any hidden global `errno`.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
	Int,
	Float,
	Str,
	Unit,
}

pub struct RtPrim {
	/// The name used on the right-hand side of `prelude/lang.def`.
	pub key: &'static str,
	/// The C symbol in the runtime.
	pub c: &'static str,
	pub args: &'static [Kind],
	pub ret: Kind,
}

use Kind::{Float as F, Int as I, Str as S, Unit as U};

macro_rules! row {
	($key:literal, $c:literal, [$($a:expr),*], $ret:expr) => {
		RtPrim { key: $key, c: $c, args: &[$($a),*], ret: $ret }
	};
}

pub static TABLE: &[RtPrim] = &[
	// ---- file system: (path[, data], mode) -> status string ---------------
	// mode: bit 0 = bytes (each Char is one byte) instead of UTF-8, bit 1 = append
	row!("fs_read", "rt_fs_read", [S, I], S),
	row!("fs_write", "rt_fs_write", [S, S, I], S),
	row!("fs_kind", "rt_fs_kind", [S], I), // 0 missing, 1 file, 2 directory, 3 other
	row!("fs_stat", "rt_fs_stat", [S], S),
	row!("fs_remove", "rt_fs_remove", [S], S),
	row!("fs_mkdir", "rt_fs_mkdir", [S], S),
	row!("fs_list", "rt_fs_list", [S], S),
	row!("fs_rename", "rt_fs_rename", [S, S], S),
	row!("fs_cwd", "rt_fs_cwd", [], S),
	row!("fs_chdir", "rt_fs_chdir", [S], S),
	row!("fs_realpath", "rt_fs_realpath", [S], S),
	// ---- the process and its environment ----------------------------------
	row!("sys_args", "rt_sys_args", [], S),
	row!("sys_exit", "rt_sys_exit", [I], U),
	row!("sys_getenv", "rt_sys_getenv", [S], S),
	row!("sys_environ", "rt_sys_environ", [], S),
	row!("sys_pid", "rt_sys_pid", [], I),
	// ---- standard streams ---------------------------------------------------
	row!("io_flush", "rt_io_flush", [], U),
	row!("io_eprint", "rt_io_eprint", [S, I], U), // string, newline?
	row!("io_stdin_all", "rt_io_stdin_all", [], S),
	row!("io_getln_opt", "rt_io_getln_opt", [], S), // status 0 = a line, 1 = end of input
	// ---- time and randomness ----------------------------------------------
	row!("time_unix", "rt_time_unix", [], F),
	row!("time_mono", "rt_time_mono", [], F),
	row!("time_offset", "rt_time_offset", [F], I),
	row!("time_sleep", "rt_time_sleep", [I], U),
	row!("rng_seed", "rt_rng_seed", [], I),
	// ---- terminal -----------------------------------------------------------
	row!("term_is_tty", "rt_term_is_tty", [I], I),
	row!("term_raw", "rt_term_raw", [I], I),
	row!("term_key", "rt_term_key", [I], I),
	row!("term_cols", "rt_term_cols", [], I),
	row!("term_rows", "rt_term_rows", [], I),
	row!("term_resized", "rt_term_resized", [], I),
	// ---- child processes: (program\0arg\0..., stdin, mode) -> status string --
	row!("proc_run", "rt_proc_run", [S, S, I], S),
];

/// Index of the primitive called `key`, if there is one.
pub fn by_key(key: &str) -> Option<u8> {
	TABLE.iter().position(|p| p.key == key).map(|i| i as u8)
}

pub fn get(i: u8) -> &'static RtPrim {
	&TABLE[i as usize]
}
