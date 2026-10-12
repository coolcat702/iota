//! LLVM backend: typed monomorphic IR -> Core MIR -> lazy MIR -> reference
//! counted MIR -> LLVM IR.
//!
//! `main.rs` drives the stages one by one (so each can be inspected and reported
//! on separately); this module only exposes them.

pub mod abi;
pub mod check;
pub mod codegen;
pub mod lazy;
pub mod lower;
pub mod mir;
pub mod pack;
pub mod refcount;
