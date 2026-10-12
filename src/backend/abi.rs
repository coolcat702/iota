//! The names generated code uses to talk to the C runtime (`runtime/iota_rt.c`).
//! They are spelled once, here; `codegen.rs` refers to the constants, and the C
//! file defines the same symbols.

pub const RT_ALLOC: &str = "rt_alloc";
pub const RT_FREE: &str = "rt_free";
pub const RT_FAIL: &str = "rt_fail";
pub const RT_IDIV: &str = "rt_idiv";
pub const RT_IMOD: &str = "rt_imod";
pub const RT_SHOW_INT: &str = "rt_show_int";
pub const RT_SHOW_FLOAT: &str = "rt_show_float";
pub const RT_GETLN: &str = "rt_getln";
pub const RT_SB_NEW: &str = "rt_sb_new";
pub const RT_SB_PUSH: &str = "rt_sb_push";
pub const RT_PRINT_SB: &str = "rt_print_sb";

/// The program entry the runtime's `main` calls.
pub const IOTA_MAIN: &str = "iota_main";

/// Helper functions the code generator emits into the module itself.
pub const FN_FROM_BUF: &str = "iota.from_buf";
pub const FN_PRINT_LIST: &str = "iota.print_list";

pub const MSG_BLACKHOLE: &str = "a value depends on itself (infinite loop)";
pub const MSG_NO_MATCH: &str = "non-exhaustive pattern match";
