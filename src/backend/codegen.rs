// LLVM IR with inkwell
//
// Runtime representation:
//   Unit            {}
//   Int / Char      i32
//   Float           f64
//   Prod(a, b)      { ptr, ptr }                 a pair of suspensions
//   Data, all ctors nullary (Bool, ...)
//                   i8 tag only (i32 past 256 ctors)
//   other Data      ptr, tagged (types with <= 7 ctors):
//        bit 0 = 1       an immediate nullary constructor: ((tag+1) << 1) | 1
//        bit 0 = 0       a heap object at (value & ~15) with ((tag+1) << 1) in
//                        the low bits; tag+1 is never 0, so
//        bits 1..3 = 0   marks a *thunk* (see below)
//   Data, > 7 ctors the same, but the tag lives in the object header instead
//   Heap object     { i32 rc, [i32 tag,] field0, field1, ... }, sized for that
//                   constructor only; every field is a suspension word, and a
//                   pair payload is flattened into its two components
//   Fn(a, b)        ptr to { i32 rc, i32 state = 0, ptr code, ptr drop, captures... }
//
// Laziness
// A suspension `Susp(t)` is one pointer-sized word:
//   Imm    (Int/Char/enum/Unit)   bit 0 set: the evaluated value, `(v << 32) | 1`;
//                                 otherwise a pointer to a thunk object
//   Direct (closures, data)       the evaluated object itself, or a thunk object
//                                 (told apart by the tag nibble / header state)
//   Boxed  (Float, pairs)         always a pointer to a thunk object; a value that
//                                 is already evaluated gets a finished one
// A thunk object shares the closure header:
//   { i32 rc, i32 state, ptr code, ptr drop, payload }
//   state: UNEVAL | BLACKHOLE (being evaluated) | DONE; the payload holds the
//   captured variables until evaluation, then the result. `force_t` runs the code
//   once (the captures are *moved* into it), stores the result and flips the
//   state, so the thunk becomes an indirection. Re-entering a BLACKHOLE is an
//   infinite loop so it's reported.
//
// Calling convention
// Instances are `fastcc`; each param is a value or susp according to the strictness analysis,
// and a borrowed param stays owned by the caller. Results are owned values (WHNF). Closure code is
// `ret code(ptr clo, ptr susp_arg)`; the prologue moves captures out of a unique closure
// (freeing the shell) or dups them for a shared one.
//
// Dropping a recursive type loops on its last same-typed field, so releasing a long
// list takes constant stack. Reference counts are non-atomic because the runtime is single-threaded.

use std::collections::HashMap;
use std::path::Path;

use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, StructType};
use inkwell::values::{
	BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue,
};
use inkwell::{AddressSpace, FloatPredicate, IntPredicate};

use crate::diag::Diagnostic;
use crate::ir::Side;
use crate::lang::Intrinsic;

use super::abi::*;
use super::mir::*;

const FASTCC: u32 = 8;
const ST_UNEVAL: u64 = 0xFFFF_FFFD;
const ST_BLACKHOLE: u64 = 0xFFFF_FFFE;
const ST_DONE: u64 = 0xFFFF_FFFF;

macro_rules! ok {
	($e:expr) => {
		$e.expect("LLVM builder error")
	};
}

enum Job<'ctx> {
	Dup {
		f: FunctionValue<'ctx>,
		ty: MTy,
	},
	Drop {
		f: FunctionValue<'ctx>,
		ty: MTy,
	},
	Force {
		f: FunctionValue<'ctx>,
		ty: MTy,
	},
	Fields {
		f: FunctionValue<'ctx>,
		did: DataId,
	},
	CloDrop {
		f: FunctionValue<'ctx>,
		caps: Vec<MTy>,
	},
	ThunkDrop {
		f: FunctionValue<'ctx>,
		caps: Vec<MTy>,
		ret: MTy,
	},
	Lambda {
		f: FunctionValue<'ctx>,
		param: (Name, MTy),
		free: Vec<(Name, MTy)>,
		body: MExpr,
	},
	Thunk {
		f: FunctionValue<'ctx>,
		free: Vec<(Name, MTy)>,
		body: MExpr,
	},
	Pap {
		f: FunctionValue<'ctx>,
		func: String,
		k: usize,
	},
}

struct St<'ctx> {
	func: FunctionValue<'ctx>,
	vals: HashMap<Name, BasicValueEnum<'ctx>>,
	tys: HashMap<Name, MTy>,
}

pub struct CodeGen<'ctx, 'p> {
	ctx: &'ctx Context,
	m: Module<'ctx>,
	b: Builder<'ctx>,
	prog: &'p MProgram,
	facts: Facts<'p>,
	sigs: HashMap<String, (Vec<MTy>, Vec<bool>, MTy)>,
	fns: HashMap<String, FunctionValue<'ctx>>,
	glue: HashMap<(u8, MTy), FunctionValue<'ctx>>,
	forces: HashMap<MTy, FunctionValue<'ctx>>,
	fields_glue: HashMap<DataId, FunctionValue<'ctx>>,
	thunk_drops: HashMap<(Vec<MTy>, MTy), FunctionValue<'ctx>>,
	paps: HashMap<(String, usize), (FunctionValue<'ctx>, FunctionValue<'ctx>)>,
	jobs: Vec<Job<'ctx>>,
	counter: usize,
	helpers: Option<(FunctionValue<'ctx>, FunctionValue<'ctx>)>,
	to_sb_fn: Option<FunctionValue<'ctx>>,
}

impl<'ctx, 'p> CodeGen<'ctx, 'p> {
	pub fn new(ctx: &'ctx Context, prog: &'p MProgram) -> Self {
		let sigs = prog
			.funcs
			.iter()
			.map(|f| {
				(
					f.name.clone(),
					(
						f.params.iter().map(|p| p.1.clone()).collect(),
						f.borrowed.clone(),
						f.ret.clone(),
					),
				)
			})
			.collect();
		CodeGen {
			ctx,
			m: ctx.create_module("iota"),
			b: ctx.create_builder(),
			prog,
			facts: Facts { datas: &prog.datas },
			sigs,
			fns: HashMap::new(),
			glue: HashMap::new(),
			forces: HashMap::new(),
			fields_glue: HashMap::new(),
			thunk_drops: HashMap::new(),
			paps: HashMap::new(),
			jobs: Vec::new(),
			counter: 0,
			helpers: None,
			to_sb_fn: None,
		}
	}

	fn ptr_ty(&self) -> inkwell::types::PointerType<'ctx> {
		self.ctx.ptr_type(AddressSpace::default())
	}
	fn unit_ty(&self) -> StructType<'ctx> {
		self.ctx.struct_type(&[], false)
	}
	fn tag_ty(&self, n: usize) -> inkwell::types::IntType<'ctx> {
		if n <= 256 {
			self.ctx.i8_type()
		} else {
			self.ctx.i32_type()
		}
	}
	fn lty(&self, t: &MTy) -> BasicTypeEnum<'ctx> {
		match t {
			MTy::Unit => self.unit_ty().into(),
			MTy::Int | MTy::Char => self.ctx.i32_type().into(),
			MTy::Float => self.ctx.f64_type().into(),
			MTy::Fn(..) | MTy::Token | MTy::Susp(_) => self.ptr_ty().into(),
			MTy::Prod(..) => self
				.ctx
				.struct_type(&[self.ptr_ty().into(), self.ptr_ty().into()], false)
				.into(),
			MTy::Data(id) => {
				let d = &self.prog.datas[*id];
				if d.is_enum() {
					self.tag_ty(d.ctors.len()).into()
				} else {
					self.ptr_ty().into()
				}
			}
		}
	}
	fn meta(&self, t: &MTy) -> BasicMetadataTypeEnum<'ctx> {
		self.lty(t).into()
	}
	fn fn_ty(
		&self,
		params: &[BasicMetadataTypeEnum<'ctx>],
		ret: &MTy,
	) -> inkwell::types::FunctionType<'ctx> {
		self.lty(ret).fn_type(params, false)
	}
	fn wide(&self, did: DataId) -> bool {
		self.prog.datas[did].is_wide()
	}
	// idx of first payload field in a ctor obj
	fn base(&self, did: DataId) -> u32 {
		if self.wide(did) {
			2
		} else {
			1
		}
	}
	fn obj_ty(&self, did: DataId, ci: usize) -> StructType<'ctx> {
		let i = self.ctx.i32_type();
		let mut f: Vec<BasicTypeEnum<'ctx>> = vec![i.into()];
		if self.wide(did) {
			f.push(i.into());
		}
		for l in self.facts.stored_leaves(did, ci) {
			f.push(match l {
				MTy::Susp(_) => self.ptr_ty().into(),
				t => self.lty(&t),
			});
		}
		self.ctx.struct_type(&f, false)
	}
	fn clo_ty(&self, caps: &[MTy]) -> StructType<'ctx> {
		let i = self.ctx.i32_type();
		let p = self.ptr_ty();
		let mut f: Vec<BasicTypeEnum<'ctx>> = vec![i.into(), i.into(), p.into(), p.into()];
		for c in caps {
			f.push(self.lty(c));
		}
		self.ctx.struct_type(&f, false)
	}
	// Same object seen as `{ header, result }` once a thunk is evaluated
	fn res_ty(&self, ret: &MTy) -> StructType<'ctx> {
		self.clo_ty(std::slice::from_ref(ret))
	}
	// a thunk big enough for either its captures or result
	fn thunk_alloc_ty(&self, caps: &[MTy], ret: &MTy) -> StructType<'ctx> {
		let mut off = 0u64;
		for c in caps {
			let (s, a) = self.facts.val_size_align(c);
			off = off.div_ceil(a) * a + s;
		}
		let bytes = off.max(self.facts.val_size_align(ret).0);
		let words = bytes.div_ceil(8).max(1);
		let i = self.ctx.i32_type();
		let p = self.ptr_ty();
		let arr = self.ctx.i64_type().array_type(words as u32);
		self.ctx
			.struct_type(&[i.into(), i.into(), p.into(), p.into(), arr.into()], false)
	}

	fn rt(
		&self,
		name: &str,
		ret: Option<BasicTypeEnum<'ctx>>,
		params: &[BasicMetadataTypeEnum<'ctx>],
	) -> FunctionValue<'ctx> {
		if let Some(f) = self.m.get_function(name) {
			return f;
		}
		let ty = match ret {
			Some(r) => r.fn_type(params, false),
			None => self.ctx.void_type().fn_type(params, false),
		};
		self.m.add_function(name, ty, None)
	}
	fn call(
		&self,
		f: FunctionValue<'ctx>,
		args: &[BasicValueEnum<'ctx>],
	) -> Option<BasicValueEnum<'ctx>> {
		let a: Vec<BasicMetadataValueEnum<'ctx>> = args.iter().map(|v| (*v).into()).collect();
		ok!(self.b.build_call(f, &a, ""))
			.try_as_basic_value()
			.basic()
	}
	fn fast_call(
		&self,
		f: FunctionValue<'ctx>,
		args: &[BasicValueEnum<'ctx>],
	) -> Option<BasicValueEnum<'ctx>> {
		let a: Vec<BasicMetadataValueEnum<'ctx>> = args.iter().map(|v| (*v).into()).collect();
		let cs = ok!(self.b.build_call(f, &a, ""));
		cs.set_call_convention(FASTCC);
		cs.try_as_basic_value().basic()
	}
	fn alloc(&self, sty: StructType<'ctx>) -> PointerValue<'ctx> {
		let f = self.rt(
			RT_ALLOC,
			Some(self.ptr_ty().into()),
			&[self.ctx.i64_type().into()],
		);
		self.call(f, &[sty.size_of().expect("sized").into()])
			.unwrap()
			.into_pointer_value()
	}
	fn free(&self, p: PointerValue<'ctx>) {
		let f = self.rt(RT_FREE, None, &[self.ptr_ty().into()]);
		self.call(f, &[p.into()]);
	}
	fn gep(&self, sty: StructType<'ctx>, p: PointerValue<'ctx>, i: u32) -> PointerValue<'ctx> {
		ok!(self.b.build_struct_gep(sty, p, i, ""))
	}
	fn i32c(&self, n: u64) -> IntValue<'ctx> {
		self.ctx.i32_type().const_int(n, false)
	}
	fn i64c(&self, n: u64) -> IntValue<'ctx> {
		self.ctx.i64_type().const_int(n, false)
	}
	fn new_bb(&self, f: FunctionValue<'ctx>, n: &str) -> BasicBlock<'ctx> {
		self.ctx.append_basic_block(f, n)
	}
	fn zero(&self, t: &MTy) -> BasicValueEnum<'ctx> {
		self.lty(t).const_zero()
	}
	fn unit(&self) -> BasicValueEnum<'ctx> {
		self.unit_ty().const_zero().into()
	}
	fn fresh(&mut self) -> usize {
		self.counter += 1;
		self.counter
	}
	fn entry_alloca(&self, f: FunctionValue<'ctx>, t: BasicTypeEnum<'ctx>) -> PointerValue<'ctx> {
		let tb = self.ctx.create_builder();
		let entry = f
			.get_first_basic_block()
			.expect("function has an entry block");
		match entry.get_first_instruction() {
			Some(i) => tb.position_before(&i),
			None => tb.position_at_end(entry),
		}
		ok!(tb.build_alloca(t, "slot"))
	}
	fn p2i(&self, p: PointerValue<'ctx>) -> IntValue<'ctx> {
		ok!(self.b.build_ptr_to_int(p, self.ctx.i64_type(), ""))
	}
	fn i2p(&self, i: IntValue<'ctx>) -> PointerValue<'ctx> {
		ok!(self.b.build_int_to_ptr(i, self.ptr_ty(), ""))
	}
	fn fail_with(&self, msg: &str) {
		let gs = ok!(self.b.build_global_string_ptr(msg, "failmsg"));
		let f = self.rt(RT_FAIL, None, &[self.ptr_ty().into()]);
		self.call(f, &[gs.as_pointer_value().into()]);
	}

	// bit 0 of tagged word/susp
	fn is_imm(&self, p: PointerValue<'ctx>) -> IntValue<'ctx> {
		let low = ok!(self.b.build_and(self.p2i(p), self.i64c(1), ""));
		ok!(self
			.b
			.build_int_compare(IntPredicate::NE, low, self.ctx.i64_type().const_zero(), ""))
	}

	fn untag(&self, did: DataId, p: PointerValue<'ctx>) -> PointerValue<'ctx> {
		if self.wide(did) {
			return p;
		}
		self.i2p(ok!(self.b.build_and(self.p2i(p), self.i64c(!15u64), "")))
	}

	fn load_state(&self, obj: PointerValue<'ctx>) -> IntValue<'ctx> {
		ok!(self
			.b
			.build_load(self.ctx.i32_type(), self.gep(self.clo_ty(&[]), obj, 1), ""))
		.into_int_value()
	}
	fn store_state(&self, obj: PointerValue<'ctx>, st: u64) {
		ok!(self
			.b
			.build_store(self.gep(self.clo_ty(&[]), obj, 1), self.i32c(st)));
	}
	fn state_is_thunk(&self, st: IntValue<'ctx>) -> IntValue<'ctx> {
		ok!(self
			.b
			.build_int_compare(IntPredicate::UGE, st, self.i32c(ST_UNEVAL), ""))
	}

	// check if non-imm ptr of a `Direct` type is a thunk
	fn is_thunk_direct(
		&mut self,
		f: FunctionValue<'ctx>,
		inner: &MTy,
		p: PointerValue<'ctx>,
	) -> IntValue<'ctx> {
		let bool_t = self.ctx.bool_type();
		match inner {
			MTy::Data(d) if !self.wide(*d) => {
				let nib = ok!(self.b.build_and(
					ok!(self
						.b
						.build_right_shift(self.p2i(p), self.i64c(1), false, "")),
					self.i64c(7),
					""
				));
				ok!(self.b.build_int_compare(
					IntPredicate::EQ,
					nib,
					self.ctx.i64_type().const_zero(),
					""
				))
			}
			MTy::Data(_) => {
				// immediates are NEVER thunks. heap objs carry state in tag slot
				let bi = self.new_bb(f, "isth.imm");
				let bh = self.new_bb(f, "isth.heap");
				let bj = self.new_bb(f, "isth.join");
				ok!(self.b.build_conditional_branch(self.is_imm(p), bi, bh));
				self.b.position_at_end(bi);
				ok!(self.b.build_unconditional_branch(bj));
				self.b.position_at_end(bh);
				let r = self.state_is_thunk(self.load_state(p));
				let bh_end = self.b.get_insert_block().unwrap();
				ok!(self.b.build_unconditional_branch(bj));
				self.b.position_at_end(bj);
				let phi = ok!(self.b.build_phi(bool_t, ""));
				let f_val = bool_t.const_zero();
				phi.add_incoming(&[
					(&f_val as &dyn BasicValue, bi),
					(&r as &dyn BasicValue, bh_end),
				]);
				phi.as_basic_value().into_int_value()
			}
			_ => self.state_is_thunk(self.load_state(p)), // closures
		}
	}

	fn dup(&mut self, v: BasicValueEnum<'ctx>, t: &MTy) {
		if !self.facts.needs_rc(t) {
			return;
		}
		// `Direct` susp is a ptr to evaled obj OR a thunk, both keep count at offset 0 of ptr
		if let MTy::Susp(inner) = t {
			if self.facts.susp_kind(inner) == SuspKind::Direct {
				let inner = (**inner).clone();
				return self.dup(v, &inner);
			}
		}
		let g = self.glue_fn(false, t);
		self.call(g, &[v]);
	}
	fn drop_v(&mut self, v: BasicValueEnum<'ctx>, t: &MTy) {
		if !self.facts.needs_rc(t) {
			return;
		}
		let g = self.glue_fn(true, t);
		self.call(g, &[v]);
	}

	fn glue_fn(&mut self, drop: bool, t: &MTy) -> FunctionValue<'ctx> {
		let key = (drop as u8, t.clone());
		if let Some(f) = self.glue.get(&key) {
			return *f;
		}
		let n = self.fresh();
		let name = format!("{}${}", if drop { "drop" } else { "dup" }, n);
		let f = self.m.add_function(
			&name,
			self.ctx.void_type().fn_type(&[self.meta(t)], false),
			None,
		);
		self.glue.insert(key, f);
		self.jobs.push(if drop {
			Job::Drop { f, ty: t.clone() }
		} else {
			Job::Dup { f, ty: t.clone() }
		});
		f
	}

	fn force_fn(&mut self, inner: &MTy) -> FunctionValue<'ctx> {
		if let Some(f) = self.forces.get(inner) {
			return *f;
		}
		let n = self.fresh();
		let fty = self.fn_ty(&[self.ptr_ty().into()], inner);
		let f = self.m.add_function(&format!("force${}", n), fty, None);
		self.forces.insert(inner.clone(), f);
		self.jobs.push(Job::Force {
			f,
			ty: inner.clone(),
		});
		f
	}

	fn fields_fn(&mut self, did: DataId) -> FunctionValue<'ctx> {
		if let Some(f) = self.fields_glue.get(&did) {
			return *f;
		}
		let n = self.fresh();
		let f = self.m.add_function(
			&format!("fields${}", n),
			self.ctx.void_type().fn_type(&[self.ptr_ty().into()], false),
			None,
		);
		self.fields_glue.insert(did, f);
		self.jobs.push(Job::Fields { f, did });
		f
	}

	fn inc_rc(&self, obj: PointerValue<'ctx>) {
		let rc = ok!(self.b.build_load(self.ctx.i32_type(), obj, "")).into_int_value();
		ok!(self
			.b
			.build_store(obj, ok!(self.b.build_int_add(rc, self.i32c(1), ""))));
	}

	// `if rc == 1 { goto last } else { rc -= 1; return }`
	// leaves builder in `last`
	fn release_or_return(&self, f: FunctionValue<'ctx>, obj: PointerValue<'ctx>) {
		let rc = ok!(self.b.build_load(self.ctx.i32_type(), obj, "")).into_int_value();
		let last = self.new_bb(f, "last");
		let dec = self.new_bb(f, "dec");
		ok!(self.b.build_conditional_branch(
			ok!(self
				.b
				.build_int_compare(IntPredicate::EQ, rc, self.i32c(1), "")),
			last,
			dec
		));
		self.b.position_at_end(dec);
		ok!(self
			.b
			.build_store(obj, ok!(self.b.build_int_sub(rc, self.i32c(1), ""))));
		ok!(self.b.build_return(None));
		self.b.position_at_end(last);
	}

	fn release_obj(&self, f: FunctionValue<'ctx>, obj: PointerValue<'ctx>) {
		let rc = ok!(self.b.build_load(self.ctx.i32_type(), obj, "")).into_int_value();
		let last = self.new_bb(f, "rel.last");
		let dec = self.new_bb(f, "rel.dec");
		let join = self.new_bb(f, "rel.join");
		ok!(self.b.build_conditional_branch(
			ok!(self
				.b
				.build_int_compare(IntPredicate::EQ, rc, self.i32c(1), "")),
			last,
			dec
		));
		self.b.position_at_end(dec);
		ok!(self
			.b
			.build_store(obj, ok!(self.b.build_int_sub(rc, self.i32c(1), ""))));
		ok!(self.b.build_unconditional_branch(join));
		self.b.position_at_end(last);
		let dfn = ok!(self
			.b
			.build_load(self.ptr_ty(), self.gep(self.clo_ty(&[]), obj, 3), ""))
		.into_pointer_value();
		let ft = self.ctx.void_type().fn_type(&[self.ptr_ty().into()], false);
		ok!(self.b.build_indirect_call(ft, dfn, &[obj.into()], ""));
		ok!(self.b.build_unconditional_branch(join));
		self.b.position_at_end(join);
	}

	fn get_tag(
		&mut self,
		f: FunctionValue<'ctx>,
		did: DataId,
		v: BasicValueEnum<'ctx>,
	) -> IntValue<'ctx> {
		let i32t = self.ctx.i32_type();
		if self.prog.datas[did].is_enum() {
			return ok!(self
				.b
				.build_int_z_extend_or_bit_cast(v.into_int_value(), i32t, ""));
		}
		let p = v.into_pointer_value();
		if !self.wide(did) {
			let sh = ok!(self
				.b
				.build_right_shift(self.p2i(p), self.i64c(1), false, ""));
			let m = ok!(self.b.build_and(sh, self.i64c(7), ""));
			let t = ok!(self.b.build_int_truncate(m, i32t, ""));
			return ok!(self.b.build_int_sub(t, self.i32c(1), ""));
		}
		let bi = self.new_bb(f, "tag.imm");
		let bh = self.new_bb(f, "tag.heap");
		let bj = self.new_bb(f, "tag.join");
		ok!(self.b.build_conditional_branch(self.is_imm(p), bi, bh));
		self.b.position_at_end(bi);
		// an immediate holds `((tag + 1) << 1) | 1`
		let t1 = ok!(self.b.build_int_sub(
			ok!(self.b.build_int_truncate(
				ok!(self
					.b
					.build_right_shift(self.p2i(p), self.i64c(1), false, "")),
				i32t,
				""
			)),
			self.i32c(1),
			""
		));
		ok!(self.b.build_unconditional_branch(bj));
		self.b.position_at_end(bh);
		let t2 = self.load_state(p); // tag slot
		ok!(self.b.build_unconditional_branch(bj));
		self.b.position_at_end(bj);
		let phi = ok!(self.b.build_phi(i32t, ""));
		phi.add_incoming(&[(&t1 as &dyn BasicValue, bi), (&t2 as &dyn BasicValue, bh)]);
		phi.as_basic_value().into_int_value()
	}

	fn emit_dup(&mut self, f: FunctionValue<'ctx>, t: &MTy) {
		let e = self.new_bb(f, "entry");
		self.b.position_at_end(e);
		let arg = f.get_nth_param(0).unwrap();
		match t {
			MTy::Prod(a, bt) => {
				let sv = arg.into_struct_value();
				for (i, ct) in [(0u32, &**a), (1u32, &**bt)] {
					let c = ok!(self.b.build_extract_value(sv, i, ""));
					self.dup(c, &MTy::susp(ct.clone()));
				}
			}
			MTy::Fn(..) => self.inc_rc(arg.into_pointer_value()),
			MTy::Data(id) => {
				let p = arg.into_pointer_value();
				let heap = self.new_bb(f, "heap");
				let done = self.new_bb(f, "done");
				ok!(self.b.build_conditional_branch(self.is_imm(p), done, heap));
				self.b.position_at_end(heap);
				self.inc_rc(self.untag(*id, p));
				ok!(self.b.build_unconditional_branch(done));
				self.b.position_at_end(done);
			}
			MTy::Susp(inner) => {
				// imm needs nothing, boxed is always a thunk obj
				let p = arg.into_pointer_value();
				let heap = self.new_bb(f, "heap");
				let done = self.new_bb(f, "done");
				if self.facts.susp_kind(inner) == SuspKind::Imm {
					ok!(self.b.build_conditional_branch(self.is_imm(p), done, heap));
				} else {
					ok!(self.b.build_unconditional_branch(heap));
				}
				self.b.position_at_end(heap);
				self.inc_rc(p);
				ok!(self.b.build_unconditional_branch(done));
				self.b.position_at_end(done);
			}
			_ => {}
		}
		ok!(self.b.build_return(None));
	}

	fn emit_drop(&mut self, f: FunctionValue<'ctx>, t: &MTy) {
		let e = self.new_bb(f, "entry");
		self.b.position_at_end(e);
		let arg = f.get_nth_param(0).unwrap();
		match t {
			MTy::Prod(a, bt) => {
				let sv = arg.into_struct_value();
				for (i, ct) in [(0u32, &**a), (1u32, &**bt)] {
					let c = ok!(self.b.build_extract_value(sv, i, ""));
					self.drop_v(c, &MTy::susp(ct.clone()));
				}
				ok!(self.b.build_return(None));
			}
			MTy::Fn(..) => {
				let p = arg.into_pointer_value();
				self.release_or_return(f, p);
				let dfn =
					ok!(self
						.b
						.build_load(self.ptr_ty(), self.gep(self.clo_ty(&[]), p, 3), ""))
					.into_pointer_value();
				let ft = self.ctx.void_type().fn_type(&[self.ptr_ty().into()], false);
				ok!(self.b.build_indirect_call(ft, dfn, &[p.into()], ""));
				ok!(self.b.build_return(None));
			}
			MTy::Data(id) => self.emit_drop_data(f, *id, arg),
			MTy::Susp(inner) => {
				let p = arg.into_pointer_value();
				let thunk = self.new_bb(f, "thunk");
				let value = self.new_bb(f, "value");
				let done = self.new_bb(f, "done");
				match self.facts.susp_kind(inner) {
					SuspKind::Imm => {
						ok!(self.b.build_conditional_branch(self.is_imm(p), done, thunk));
					}
					SuspKind::Boxed => {
						ok!(self.b.build_unconditional_branch(thunk));
					}
					SuspKind::Direct => {
						let inner = (**inner).clone();
						let is_imm_p = self.is_imm(p);
						let nonimm = self.new_bb(f, "nonimm");
						ok!(self.b.build_conditional_branch(is_imm_p, value, nonimm));
						self.b.position_at_end(nonimm);
						let isth = self.is_thunk_direct(f, &inner, p);
						ok!(self.b.build_conditional_branch(isth, thunk, value));
					}
				}
				self.b.position_at_end(value);
				if let SuspKind::Direct = self.facts.susp_kind(inner) {
					let inner = (**inner).clone();
					self.drop_v(p.into(), &inner);
				}
				ok!(self.b.build_unconditional_branch(done));
				self.b.position_at_end(thunk);
				let obj = if let MTy::Data(d) = &**inner {
					self.untag(*d, p)
				} else {
					p
				};
				self.release_obj(f, obj);
				ok!(self.b.build_unconditional_branch(done));
				self.b.position_at_end(done);
				ok!(self.b.build_return(None));
			}
			_ => {
				ok!(self.b.build_return(None));
			}
		}
	}

	fn tail_leaf(&self, did: DataId, payload: &MTy) -> Option<usize> {
		self.facts
			.leaves(payload)
			.iter()
			.rposition(|l| matches!(l, MTy::Susp(t) if matches!(&**t, MTy::Data(d) if *d == did)))
	}

	fn emit_drop_data(&mut self, f: FunctionValue<'ctx>, did: DataId, arg: BasicValueEnum<'ctx>) {
		let ptr = self.ptr_ty();
		let cur = ok!(self.b.build_alloca(ptr, "cur"));
		ok!(self.b.build_store(cur, arg));
		let lp = self.new_bb(f, "loop");
		ok!(self.b.build_unconditional_branch(lp));
		self.b.position_at_end(lp);
		let v = ok!(self.b.build_load(ptr, cur, ""));
		let heap = self.new_bb(f, "heap");
		let done = self.new_bb(f, "done");
		ok!(self
			.b
			.build_conditional_branch(self.is_imm(v.into_pointer_value()), done, heap));
		self.b.position_at_end(done);
		ok!(self.b.build_return(None));
		self.b.position_at_end(heap);
		let obj = self.untag(did, v.into_pointer_value());
		self.release_or_return(f, obj);

		let tag = self.get_tag(f, did, v);
		let freeb = self.new_bb(f, "free");
		let def = self.prog.datas[did].clone();
		let mut cases = Vec::new();
		let mut bodies = Vec::new();
		for (i, c) in def.ctors.iter().enumerate() {
			if let Some(pt) = &c.payload {
				if !self.facts.leaves(pt).is_empty() {
					let bb = self.new_bb(f, "ctor");
					cases.push((self.i32c(i as u64), bb));
					bodies.push((bb, i, pt.clone()));
				}
			}
		}
		ok!(self.b.build_switch(tag, freeb, &cases));
		for (bb, ci, pt) in bodies {
			self.b.position_at_end(bb);
			let oty = self.obj_ty(did, ci);
			let leaves = self.facts.leaves(&pt);
			let tail = self.tail_leaf(did, &pt);
			let base = self.base(did);
			for (i, l) in leaves.iter().enumerate() {
				if Some(i) != tail && !self.facts.is_packed(did, ci, i) {
					let fv = ok!(self
						.b
						.build_load(ptr, self.gep(oty, obj, base + i as u32), ""));
					self.drop_v(fv, l);
				}
			}
			match tail {
				Some(ti) => {
					let nv = ok!(self
						.b
						.build_load(ptr, self.gep(oty, obj, base + ti as u32), ""))
					.into_pointer_value();
					self.free(obj);
					// tail is a susp, continue only if it's an evaled cell
					let cont = self.new_bb(f, "tail.cell");
					let other = self.new_bb(f, "tail.other");
					let nonimm = self.new_bb(f, "tail.nonimm");
					ok!(self
						.b
						.build_conditional_branch(self.is_imm(nv), cont, nonimm));
					self.b.position_at_end(nonimm);
					let isth = self.is_thunk_direct(f, &MTy::Data(did), nv);
					ok!(self.b.build_conditional_branch(isth, other, cont));
					self.b.position_at_end(other);
					self.drop_v(nv.into(), &MTy::susp(MTy::Data(did)));
					ok!(self.b.build_return(None));
					self.b.position_at_end(cont);
					ok!(self.b.build_store(cur, nv));
					ok!(self.b.build_unconditional_branch(lp));
				}
				None => {
					ok!(self.b.build_unconditional_branch(freeb));
				}
			}
		}
		self.b.position_at_end(freeb);
		self.free(obj);
		ok!(self.b.build_return(None));
	}

	fn emit_fields(&mut self, f: FunctionValue<'ctx>, did: DataId) {
		let e = self.new_bb(f, "entry");
		self.b.position_at_end(e);
		let v = f.get_nth_param(0).unwrap();
		let obj = self.untag(did, v.into_pointer_value());
		let tag = self.get_tag(f, did, v);
		let done = self.new_bb(f, "done");
		let def = self.prog.datas[did].clone();
		let mut cases = Vec::new();
		let mut bodies = Vec::new();
		for (i, c) in def.ctors.iter().enumerate() {
			if let Some(pt) = &c.payload {
				if !self.facts.leaves(pt).is_empty() {
					let bb = self.new_bb(f, "ctor");
					cases.push((self.i32c(i as u64), bb));
					bodies.push((bb, i, pt.clone()));
				}
			}
		}
		ok!(self.b.build_switch(tag, done, &cases));
		for (bb, ci, pt) in bodies {
			self.b.position_at_end(bb);
			let oty = self.obj_ty(did, ci);
			let base = self.base(did);
			for (i, l) in self.facts.leaves(&pt).iter().enumerate() {
				if self.facts.is_packed(did, ci, i) {
					continue;
				}
				let fv =
					ok!(self
						.b
						.build_load(self.ptr_ty(), self.gep(oty, obj, base + i as u32), ""));
				self.drop_v(fv, l);
			}
			ok!(self.b.build_unconditional_branch(done));
		}
		self.b.position_at_end(done);
		ok!(self.b.build_return(None));
	}

	fn imm_encode(&self, v: BasicValueEnum<'ctx>, t: &MTy) -> PointerValue<'ctx> {
		let word = match t {
			MTy::Unit => self.i64c(1),
			_ => {
				let z = ok!(self.b.build_int_z_extend_or_bit_cast(
					v.into_int_value(),
					self.ctx.i64_type(),
					""
				));
				let sh = ok!(self.b.build_left_shift(z, self.i64c(32), ""));
				ok!(self.b.build_or(sh, self.i64c(1), ""))
			}
		};
		self.i2p(word)
	}

	fn imm_decode(&self, w: PointerValue<'ctx>, t: &MTy) -> BasicValueEnum<'ctx> {
		match t {
			MTy::Unit => self.unit(),
			_ => {
				let sh = ok!(self
					.b
					.build_right_shift(self.p2i(w), self.i64c(32), false, ""));
				ok!(self
					.b
					.build_int_truncate_or_bit_cast(sh, self.lty(t).into_int_type(), ""))
				.into()
			}
		}
	}

	fn wrap(&mut self, v: BasicValueEnum<'ctx>, t: &MTy) -> BasicValueEnum<'ctx> {
		match self.facts.susp_kind(t) {
			SuspKind::Imm => self.imm_encode(v, t).into(),
			SuspKind::Direct => v,
			SuspKind::Boxed => {
				// a finished thunk obj holding the value
				let drop = self.thunk_drop_fn(vec![], t.clone());
				let aty = self.thunk_alloc_ty(&[], t);
				let obj = self.alloc(aty);
				let cty = self.clo_ty(&[]);
				ok!(self.b.build_store(self.gep(cty, obj, 0), self.i32c(1)));
				self.store_state(obj, ST_DONE);
				ok!(self
					.b
					.build_store(self.gep(cty, obj, 2), self.ptr_ty().const_null()));
				ok!(self.b.build_store(
					self.gep(cty, obj, 3),
					drop.as_global_value().as_pointer_value()
				));
				ok!(self.b.build_store(self.gep(self.res_ty(t), obj, 4), v));
				obj.into()
			}
		}
	}

	// `force$t(susp) -> t`
	// evaluate a suspension to a value.
	fn emit_force(&mut self, f: FunctionValue<'ctx>, t: &MTy) {
		let e = self.new_bb(f, "entry");
		self.b.position_at_end(e);
		let p = f.get_nth_param(0).unwrap().into_pointer_value();
		let thunk = self.new_bb(f, "thunk");
		let kind = self.facts.susp_kind(t);
		match kind {
			SuspKind::Imm => {
				let imm = self.new_bb(f, "imm");
				ok!(self.b.build_conditional_branch(self.is_imm(p), imm, thunk));
				self.b.position_at_end(imm);
				let v = self.imm_decode(p, t);
				ok!(self.b.build_return(Some(&v)));
			}
			SuspKind::Direct => {
				let value = self.new_bb(f, "value");
				let nonimm = self.new_bb(f, "nonimm");
				ok!(self
					.b
					.build_conditional_branch(self.is_imm(p), value, nonimm));
				self.b.position_at_end(nonimm);
				let isth = self.is_thunk_direct(f, t, p);
				ok!(self.b.build_conditional_branch(isth, thunk, value));
				self.b.position_at_end(value);
				ok!(self.b.build_return(Some(&p.as_basic_value_enum())));
			}
			SuspKind::Boxed => {
				ok!(self.b.build_unconditional_branch(thunk));
			}
		}

		self.b.position_at_end(thunk);
		let obj = if let MTy::Data(d) = t {
			self.untag(*d, p)
		} else {
			p
		};
		let st = self.load_state(obj);
		let done_bb = self.new_bb(f, "done");
		let eval_bb = self.new_bb(f, "eval");
		let loop_bb = self.new_bb(f, "blackhole");
		ok!(self.b.build_switch(
			st,
			eval_bb,
			&[
				(self.i32c(ST_DONE), done_bb),
				(self.i32c(ST_BLACKHOLE), loop_bb)
			]
		));
		let rty = self.res_ty(t);

		self.b.position_at_end(loop_bb);
		self.fail_with(MSG_BLACKHOLE);
		ok!(self.b.build_unreachable());

		self.b.position_at_end(done_bb);
		let v = ok!(self.b.build_load(self.lty(t), self.gep(rty, obj, 4), ""));
		self.dup(v, t);
		self.release_obj(f, obj);
		ok!(self.b.build_return(Some(&v)));

		self.b.position_at_end(eval_bb);
		self.store_state(obj, ST_BLACKHOLE);
		let code = ok!(self
			.b
			.build_load(self.ptr_ty(), self.gep(self.clo_ty(&[]), obj, 2), ""))
		.into_pointer_value();
		let ft = self.fn_ty(&[self.ptr_ty().into()], t);
		let cs = ok!(self.b.build_indirect_call(ft, code, &[obj.into()], ""));
		cs.set_call_convention(FASTCC);
		let v = cs
			.try_as_basic_value()
			.basic()
			.unwrap_or_else(|| self.unit());
		self.dup(v, t); // thunk keeps one reference to its result
		ok!(self.b.build_store(self.gep(rty, obj, 4), v));
		self.store_state(obj, ST_DONE);
		self.release_obj(f, obj);
		ok!(self.b.build_return(Some(&v)));
	}

	fn thunk_drop_fn(&mut self, caps: Vec<MTy>, ret: MTy) -> FunctionValue<'ctx> {
		let key = (caps.clone(), ret.clone());
		if let Some(f) = self.thunk_drops.get(&key) {
			return *f;
		}
		let n = self.fresh();
		let f = self.m.add_function(
			&format!("thunkdrop${}", n),
			self.ctx.void_type().fn_type(&[self.ptr_ty().into()], false),
			None,
		);
		self.thunk_drops.insert(key, f);
		self.jobs.push(Job::ThunkDrop { f, caps, ret });
		f
	}

	fn emit_thunk_drop(&mut self, f: FunctionValue<'ctx>, caps: &[MTy], ret: &MTy) {
		let e = self.new_bb(f, "entry");
		self.b.position_at_end(e);
		let obj = f.get_nth_param(0).unwrap().into_pointer_value();
		let st = self.load_state(obj);
		let uneval = self.new_bb(f, "uneval");
		let done = self.new_bb(f, "done");
		let fin = self.new_bb(f, "free");
		ok!(self.b.build_switch(
			st,
			fin,
			&[(self.i32c(ST_UNEVAL), uneval), (self.i32c(ST_DONE), done)]
		));
		self.b.position_at_end(uneval);
		let cty = self.clo_ty(caps);
		for (i, t) in caps.iter().enumerate() {
			if self.facts.needs_rc(t) {
				let v = ok!(self
					.b
					.build_load(self.lty(t), self.gep(cty, obj, 4 + i as u32), ""));
				self.drop_v(v, t);
			}
		}
		ok!(self.b.build_unconditional_branch(fin));
		self.b.position_at_end(done);
		if self.facts.needs_rc(ret) {
			let v = ok!(self
				.b
				.build_load(self.lty(ret), self.gep(self.res_ty(ret), obj, 4), ""));
			self.drop_v(v, ret);
		}
		ok!(self.b.build_unconditional_branch(fin));
		self.b.position_at_end(fin);
		self.free(obj);
		ok!(self.b.build_return(None));
	}

	fn ctor_pty(&self, did: DataId, ci: usize) -> MTy {
		self.prog.datas[did].ctors[ci]
			.payload
			.clone()
			.unwrap_or(MTy::Unit)
	}

	fn store_leaf(
		&self,
		oty: StructType<'ctx>,
		obj: PointerValue<'ctx>,
		idx: u32,
		packed: Option<&MTy>,
		w: BasicValueEnum<'ctx>,
	) {
		let v = match packed {
			Some(t) => self.imm_decode(w.into_pointer_value(), t),
			None => w,
		};
		ok!(self.b.build_store(self.gep(oty, obj, idx), v));
	}

	fn load_leaf(
		&self,
		oty: StructType<'ctx>,
		obj: PointerValue<'ctx>,
		idx: u32,
		packed: Option<&MTy>,
	) -> BasicValueEnum<'ctx> {
		match packed {
			Some(t) => {
				let v = ok!(self.b.build_load(self.lty(t), self.gep(oty, obj, idx), ""));
				self.imm_encode(v, t).into()
			}
			None => ok!(self
				.b
				.build_load(self.ptr_ty(), self.gep(oty, obj, idx), "")),
		}
	}

	fn packed_ty(&self, did: DataId, ci: usize, i: usize) -> Option<MTy> {
		if self.facts.is_packed(did, ci, i) {
			Some(self.facts.stored_leaves(did, ci)[i].clone())
		} else {
			None
		}
	}

	fn store_payload(
		&self,
		did: DataId,
		ci: usize,
		obj: PointerValue<'ctx>,
		v: BasicValueEnum<'ctx>,
	) {
		let oty = self.obj_ty(did, ci);
		let base = self.base(did);
		match self.ctor_pty(did, ci) {
			MTy::Unit => {}
			MTy::Prod(..) => {
				let sv = v.into_struct_value();
				for i in 0..2u32 {
					let w = ok!(self.b.build_extract_value(sv, i, ""));
					self.store_leaf(
						oty,
						obj,
						base + i,
						self.packed_ty(did, ci, i as usize).as_ref(),
						w,
					);
				}
			}
			_ => self.store_leaf(oty, obj, base, self.packed_ty(did, ci, 0).as_ref(), v),
		}
	}

	fn load_payload(
		&self,
		did: DataId,
		ci: usize,
		obj: PointerValue<'ctx>,
	) -> BasicValueEnum<'ctx> {
		let oty = self.obj_ty(did, ci);
		let base = self.base(did);
		let payload = self.ctor_pty(did, ci);
		match &payload {
			MTy::Unit => self.imm_encode(self.unit(), &MTy::Unit).into(),
			MTy::Prod(..) => {
				let a = self.load_leaf(oty, obj, base, self.packed_ty(did, ci, 0).as_ref());
				let b = self.load_leaf(oty, obj, base + 1, self.packed_ty(did, ci, 1).as_ref());
				let mut s = self.lty(&payload).into_struct_type().get_undef();
				s = ok!(self.b.build_insert_value(s, a, 0, "")).into_struct_value();
				s = ok!(self.b.build_insert_value(s, b, 1, "")).into_struct_value();
				s.into()
			}
			_ => self.load_leaf(oty, obj, base, self.packed_ty(did, ci, 0).as_ref()),
		}
	}

	fn init_ctor(
		&mut self,
		did: DataId,
		tag: u64,
		obj: PointerValue<'ctx>,
		pv: BasicValueEnum<'ctx>,
	) -> BasicValueEnum<'ctx> {
		let oty = self.obj_ty(did, tag as usize);
		ok!(self.b.build_store(self.gep(oty, obj, 0), self.i32c(1)));
		if self.wide(did) {
			ok!(self.b.build_store(self.gep(oty, obj, 1), self.i32c(tag)));
		}
		self.store_payload(did, tag as usize, obj, pv);
		if self.wide(did) {
			obj.into()
		} else {
			let t = ok!(self
				.b
				.build_or(self.p2i(obj), self.i64c((tag + 1) << 1), ""));
			self.i2p(t).into()
		}
	}

	fn build_ctor(
		&mut self,
		did: DataId,
		ctor: &str,
		payload: Option<BasicValueEnum<'ctx>>,
	) -> BasicValueEnum<'ctx> {
		let d = self.prog.datas[did].clone();
		let tag = d
			.tag_of(ctor)
			.unwrap_or_else(|| panic!("no constructor {} in {}", ctor, d.name)) as u64;
		if d.is_enum() {
			return self.tag_ty(d.ctors.len()).const_int(tag, false).into();
		}
		match (payload, &d.ctors[tag as usize].payload) {
			(Some(pv), Some(_)) => {
				let obj = self.alloc(self.obj_ty(did, tag as usize));
				self.init_ctor(did, tag, obj, pv)
			}
			_ => self.i2p(self.i64c(((tag + 1) << 1) | 1)).into(),
		}
	}

	fn list_info(&self) -> ListInfo {
		self.prog
			.list
			.expect("program uses strings but the prelude defines no list type")
	}

	/// `iota.to_sb(list) -> StrBuf*`: see `list_helpers`.
	fn to_sb_helper(&mut self) -> FunctionValue<'ctx> {
		self.list_helpers();
		self.to_sb_fn.expect("list_helpers builds to_sb")
	}

	// `(from_buf(ptr buf, i64 len) -> List Char, print_list(List Char, i32 newline) -> void)`
	fn list_helpers(&mut self) -> (FunctionValue<'ctx>, FunctionValue<'ctx>) {
		if let Some(h) = self.helpers {
			return h;
		}
		let li = self.list_info();
		let did = li.data;
		let i32t = self.ctx.i32_type();
		let i64t = self.ctx.i64_type();
		let ptr = self.ptr_ty();
		let cons_pty = self.prog.datas[did].ctors[li.cons].payload.clone().unwrap();
		let saved = self.b.get_insert_block();

		// from_buf: build a fully evaled list from a u32 buffer (+ free)
		let from_f = self.m.add_function(
			FN_FROM_BUF,
			ptr.fn_type(&[ptr.into(), i64t.into()], false),
			None,
		);
		{
			let e = self.new_bb(from_f, "entry");
			let lp = self.new_bb(from_f, "loop");
			let body = self.new_bb(from_f, "body");
			let done = self.new_bb(from_f, "done");
			self.b.position_at_end(e);
			let buf = from_f.get_nth_param(0).unwrap().into_pointer_value();
			let len = from_f.get_nth_param(1).unwrap().into_int_value();
			let acc = ok!(self.b.build_alloca(ptr, "acc"));
			let idx = ok!(self.b.build_alloca(i64t, "i"));
			let nil_name = self.prog.datas[did].ctors[li.nil].name.clone();
			let nil = self.build_ctor(did, &nil_name, None);
			ok!(self.b.build_store(acc, nil));
			ok!(self.b.build_store(idx, len));
			ok!(self.b.build_unconditional_branch(lp));
			self.b.position_at_end(lp);
			let i = ok!(self.b.build_load(i64t, idx, "")).into_int_value();
			ok!(self.b.build_conditional_branch(
				ok!(self
					.b
					.build_int_compare(IntPredicate::EQ, i, i64t.const_zero(), "")),
				done,
				body
			));
			self.b.position_at_end(body);
			let i1 = ok!(self.b.build_int_sub(i, self.i64c(1), ""));
			ok!(self.b.build_store(idx, i1));
			let cp = unsafe { ok!(self.b.build_gep(i32t, buf, &[i1], "")) };
			let ch = ok!(self.b.build_load(i32t, cp, ""));
			let head = self.imm_encode(ch, &MTy::Char);
			let tail = ok!(self.b.build_load(ptr, acc, ""));
			let mut cell = self.lty(&cons_pty).into_struct_type().get_undef();
			cell = ok!(self.b.build_insert_value(cell, head, 0, "")).into_struct_value();
			cell = ok!(self.b.build_insert_value(cell, tail, 1, "")).into_struct_value();
			let cname = self.prog.datas[did].ctors[li.cons].name.clone();
			let c = self.build_ctor(did, &cname, Some(cell.into()));
			ok!(self.b.build_store(acc, c));
			ok!(self.b.build_unconditional_branch(lp));
			self.b.position_at_end(done);
			self.free(buf);
			let r = ok!(self.b.build_load(ptr, acc, ""));
			ok!(self.b.build_return(Some(&r)));
		}

		// to_sb: force the list cell-by-cell into a fresh StrBuf and return it. Consumes the
		// list. (Nothing is observable until the whole list has been forced, so an error while
		// evaluating the tail leaves no half-done effect behind.)
		let to_sb_f = self
			.m
			.add_function(FN_TO_SB, ptr.fn_type(&[ptr.into()], false), None);
		{
			let e = self.new_bb(to_sb_f, "entry");
			let lp = self.new_bb(to_sb_f, "loop");
			let cell = self.new_bb(to_sb_f, "cell");
			let done = self.new_bb(to_sb_f, "done");
			self.b.position_at_end(e);
			let list = to_sb_f.get_nth_param(0).unwrap();
			let sb_new = self.rt(RT_SB_NEW, Some(ptr.into()), &[]);
			let sb = self.call(sb_new, &[]).unwrap();
			let cur = ok!(self.b.build_alloca(ptr, "cur"));
			ok!(self.b.build_store(cur, list));
			ok!(self.b.build_unconditional_branch(lp));
			self.b.position_at_end(lp);
			let p = ok!(self.b.build_load(ptr, cur, "")).into_pointer_value();
			ok!(self.b.build_conditional_branch(self.is_imm(p), done, cell));
			self.b.position_at_end(cell);
			let obj = self.untag(did, p);
			let payload = self.load_payload(did, li.cons, obj).into_struct_value();
			let head = ok!(self.b.build_extract_value(payload, 0, ""));
			let tail = ok!(self.b.build_extract_value(payload, 1, ""));
			self.dup(head, &MTy::susp(MTy::Char));
			self.dup(tail, &MTy::susp(MTy::Data(did)));
			let fc = self.force_fn(&MTy::Char);
			let ch = self.call(fc, &[head]).unwrap();
			let push = self.rt(RT_SB_PUSH, None, &[ptr.into(), i32t.into()]);
			self.call(push, &[sb, ch]);
			let fl = self.force_fn(&MTy::Data(did));
			let next = self.call(fl, &[tail]).unwrap();
			self.drop_v(p.into(), &MTy::Data(did)); // reference to this cell
			ok!(self.b.build_store(cur, next));
			ok!(self.b.build_unconditional_branch(lp));
			self.b.position_at_end(done);
			ok!(self.b.build_return(Some(&sb)));
		}

		// print_list: force the list, then print it
		let print_f = self.m.add_function(
			FN_PRINT_LIST,
			self.ctx
				.void_type()
				.fn_type(&[ptr.into(), i32t.into()], false),
			None,
		);
		{
			let e = self.new_bb(print_f, "entry");
			self.b.position_at_end(e);
			let list = print_f.get_nth_param(0).unwrap();
			let nl = print_f.get_nth_param(1).unwrap();
			let sb = self.call(to_sb_f, &[list]).unwrap();
			let pr = self.rt(RT_PRINT_SB, None, &[ptr.into(), i32t.into()]);
			self.call(pr, &[sb, nl]);
			ok!(self.b.build_return(None));
		}
		if let Some(bb) = saved {
			self.b.position_at_end(bb);
		}
		self.to_sb_fn = Some(to_sb_f);
		self.helpers = Some((from_f, print_f));
		(from_f, print_f)
	}

	fn closure_prologue(
		&mut self,
		f: FunctionValue<'ctx>,
		clo: PointerValue<'ctx>,
		caps: &[MTy],
	) -> Vec<BasicValueEnum<'ctx>> {
		let cty = self.clo_ty(caps);
		let mut vals = Vec::new();
		for (i, t) in caps.iter().enumerate() {
			vals.push(ok!(self.b.build_load(
				self.lty(t),
				self.gep(cty, clo, 4 + i as u32),
				""
			)));
		}
		let rc = ok!(self.b.build_load(self.ctx.i32_type(), clo, "")).into_int_value();
		let uniq = ok!(self
			.b
			.build_int_compare(IntPredicate::EQ, rc, self.i32c(1), ""));
		let bu = self.new_bb(f, "clo.unique");
		let bs = self.new_bb(f, "clo.shared");
		let bj = self.new_bb(f, "clo.go");
		ok!(self.b.build_conditional_branch(uniq, bu, bs));
		self.b.position_at_end(bu);
		self.free(clo);
		ok!(self.b.build_unconditional_branch(bj));
		self.b.position_at_end(bs);
		for (v, t) in vals.clone().into_iter().zip(caps) {
			self.dup(v, t);
		}
		ok!(self
			.b
			.build_store(clo, ok!(self.b.build_int_sub(rc, self.i32c(1), ""))));
		ok!(self.b.build_unconditional_branch(bj));
		self.b.position_at_end(bj);
		vals
	}

	fn new_closure(
		&mut self,
		code: FunctionValue<'ctx>,
		drop: FunctionValue<'ctx>,
		caps: &[(BasicValueEnum<'ctx>, MTy)],
	) -> PointerValue<'ctx> {
		let tys: Vec<MTy> = caps.iter().map(|c| c.1.clone()).collect();
		let cty = self.clo_ty(&tys);
		let p = self.alloc(cty);
		ok!(self.b.build_store(self.gep(cty, p, 0), self.i32c(1)));
		self.store_state(p, 0);
		ok!(self.b.build_store(
			self.gep(cty, p, 2),
			code.as_global_value().as_pointer_value()
		));
		ok!(self.b.build_store(
			self.gep(cty, p, 3),
			drop.as_global_value().as_pointer_value()
		));
		for (i, (v, _)) in caps.iter().enumerate() {
			ok!(self.b.build_store(self.gep(cty, p, 4 + i as u32), *v));
		}
		p
	}

	fn new_clo_drop(&mut self, caps: Vec<MTy>) -> FunctionValue<'ctx> {
		let n = self.fresh();
		let f = self.m.add_function(
			&format!("clodrop${}", n),
			self.ctx.void_type().fn_type(&[self.ptr_ty().into()], false),
			None,
		);
		self.jobs.push(Job::CloDrop { f, caps });
		f
	}

	fn susp_cap_tys(&self, ptys: &[MTy]) -> Vec<MTy> {
		ptys.iter().map(|t| MTy::susp(t.inner().clone())).collect()
	}

	fn pap_fns(&mut self, func: &str, k: usize) -> (FunctionValue<'ctx>, FunctionValue<'ctx>) {
		let key = (func.to_string(), k);
		if let Some(x) = self.paps.get(&key) {
			return *x;
		}
		let (ptys, _, ret) = self.sigs[func].clone();
		let n = self.fresh();
		let res = if k + 1 == ptys.len() {
			ret
		} else {
			MTy::Fn(Box::new(MTy::Unit), Box::new(MTy::Unit))
		};
		let fty = self.fn_ty(&[self.ptr_ty().into(), self.ptr_ty().into()], &res);
		let code = self.m.add_function(&format!("pap${}${}", n, k), fty, None);
		code.set_call_conventions(FASTCC);
		let drop = self.new_clo_drop(self.susp_cap_tys(&ptys[..k]));
		self.paps.insert(key, (code, drop));
		self.jobs.push(Job::Pap {
			f: code,
			func: func.to_string(),
			k,
		});
		(code, drop)
	}

	fn make_pap(&mut self, func: &str, args: &[BasicValueEnum<'ctx>]) -> BasicValueEnum<'ctx> {
		let (ptys, _, _) = self.sigs[func].clone();
		let k = args.len();
		let (code, drop) = self.pap_fns(func, k);
		let tys = self.susp_cap_tys(&ptys[..k]);
		let caps: Vec<(BasicValueEnum<'ctx>, MTy)> = args.iter().cloned().zip(tys).collect();
		self.new_closure(code, drop, &caps).into()
	}

	fn apply_closure(
		&mut self,
		clo: PointerValue<'ctx>,
		arg: BasicValueEnum<'ctx>,
		rt: &MTy,
	) -> BasicValueEnum<'ctx> {
		let code = ok!(self
			.b
			.build_load(self.ptr_ty(), self.gep(self.clo_ty(&[]), clo, 2), ""))
		.into_pointer_value();
		let fty = self.fn_ty(&[self.ptr_ty().into(), self.ptr_ty().into()], rt);
		let cs = ok!(self
			.b
			.build_indirect_call(fty, code, &[clo.into(), arg.into()], ""));
		cs.set_call_convention(FASTCC);
		cs.try_as_basic_value()
			.basic()
			.unwrap_or_else(|| self.unit())
	}

	fn atom(&self, st: &St<'ctx>, a: &MAtom) -> BasicValueEnum<'ctx> {
		match a {
			MAtom::Var(n) => *st
				.vals
				.get(n)
				.unwrap_or_else(|| panic!("codegen: unbound variable `{}`", n)),
			MAtom::Unit => self.unit(),
			MAtom::Int(n) => self.ctx.i32_type().const_int(*n as i64 as u64, true).into(),
			MAtom::Float(x) => self.ctx.f64_type().const_float(*x).into(),
			MAtom::Char(c) => self.ctx.i32_type().const_int(*c as u64, false).into(),
		}
	}

	fn atom_ty(&self, st: &St<'ctx>, a: &MAtom) -> MTy {
		match a {
			MAtom::Var(n) => st.tys[n].clone(),
			MAtom::Unit => MTy::Unit,
			MAtom::Int(_) => MTy::Int,
			MAtom::Float(_) => MTy::Float,
			MAtom::Char(_) => MTy::Char,
		}
	}

	fn data_id(t: &MTy) -> DataId {
		match t {
			MTy::Data(id) => *id,
			other => panic!("codegen: expected a data type, got {:?}", other),
		}
	}

	fn value(&mut self, st: &mut St<'ctx>, ty: &MTy, v: &MValue) -> BasicValueEnum<'ctx> {
		match v {
			MValue::Atom(a) => self.atom(st, a),
			MValue::Fail(msg) => {
				self.fail_with(msg);
				self.zero(ty)
			}
			MValue::Str(s) => {
				let li = self.list_info();
				let did = li.data;
				let (nil_name, cons_name) = (
					self.prog.datas[did].ctors[li.nil].name.clone(),
					self.prog.datas[did].ctors[li.cons].name.clone(),
				);
				let cons_pty = self.prog.datas[did].ctors[li.cons].payload.clone().unwrap();
				let cell_ty = self.lty(&cons_pty).into_struct_type();
				let mut acc = self.build_ctor(did, &nil_name, None);
				for ch in s.chars().rev() {
					let mut cell = cell_ty.get_undef();
					let head = self.imm_encode(self.i32c(ch as u64).into(), &MTy::Char);
					cell = ok!(self.b.build_insert_value(cell, head, 0, "")).into_struct_value();
					cell = ok!(self.b.build_insert_value(cell, acc, 1, "")).into_struct_value();
					acc = self.build_ctor(did, &cons_name, Some(cell.into()));
				}
				acc
			}
			MValue::Pair(a, b) => {
				let sty = self.lty(ty).into_struct_type();
				let mut s = sty.get_undef();
				s = ok!(self.b.build_insert_value(s, self.atom(st, a), 0, "")).into_struct_value();
				s = ok!(self.b.build_insert_value(s, self.atom(st, b), 1, "")).into_struct_value();
				s.into()
			}
			MValue::Ctor { ctor, payload } => {
				let did = Self::data_id(ty);
				let pv = payload.as_ref().map(|p| self.atom(st, p));
				self.build_ctor(did, ctor, pv)
			}
			MValue::CtorReuse {
				token,
				ctor,
				payload,
			} => {
				let did = Self::data_id(ty);
				let tag = self.prog.datas[did].tag_of(ctor).unwrap() as u64;
				let oty = self.obj_ty(did, tag as usize);
				let tok = st.vals[token].into_pointer_value();
				let isnull = ok!(self.b.build_int_compare(
					IntPredicate::EQ,
					self.p2i(tok),
					self.ctx.i64_type().const_zero(),
					""
				));
				let f = st.func;
				let balloc = self.new_bb(f, "reuse.alloc");
				let bjoin = self.new_bb(f, "reuse.join");
				let bfrom = self.b.get_insert_block().unwrap();
				ok!(self.b.build_conditional_branch(isnull, balloc, bjoin));
				self.b.position_at_end(balloc);
				let fresh = self.alloc(oty);
				let balloc_end = self.b.get_insert_block().unwrap();
				ok!(self.b.build_unconditional_branch(bjoin));
				self.b.position_at_end(bjoin);
				let phi = ok!(self.b.build_phi(self.ptr_ty(), ""));
				phi.add_incoming(&[
					(&tok as &dyn BasicValue, bfrom),
					(&fresh as &dyn BasicValue, balloc_end),
				]);
				let obj = phi.as_basic_value().into_pointer_value();
				let pv = self.atom(st, payload);
				self.init_ctor(did, tag, obj, pv)
			}
			MValue::Proj(a, side) => {
				let sv = self.atom(st, a).into_struct_value();
				let r = ok!(self.b.build_extract_value(
					sv,
					if matches!(side, Side::Fst) { 0 } else { 1 },
					""
				));
				self.dup(r, ty);
				r
			}
			MValue::Unwrap(a, ctor) => {
				let at = self.atom_ty(st, a);
				let did = Self::data_id(&at);
				let ci = self.prog.datas[did].tag_of(ctor).unwrap();
				let obj = self.untag(did, self.atom(st, a).into_pointer_value());
				let r = self.load_payload(did, ci, obj);
				self.dup(r, ty);
				r
			}
			MValue::Field(a, ctor, i) => {
				let at = self.atom_ty(st, a);
				let did = Self::data_id(&at);
				let ci = self.prog.datas[did].tag_of(ctor).unwrap();
				let obj = self.untag(did, self.atom(st, a).into_pointer_value());
				let oty = self.obj_ty(did, ci);
				let packed = self.packed_ty(did, ci, *i);
				let r = self.load_leaf(oty, obj, self.base(did) + *i as u32, packed.as_ref());
				if packed.is_none() {
					self.dup(r, ty);
				}
				r
			}
			MValue::Lambda { param, body, free } => {
				let n = self.fresh();
				let ret = match ty {
					MTy::Fn(_, r) => (**r).clone(),
					_ => unreachable!("lambda with non-function type"),
				};
				let fty = self.fn_ty(&[self.ptr_ty().into(), self.ptr_ty().into()], &ret);
				let code = self.m.add_function(&format!("lam${}", n), fty, None);
				code.set_call_conventions(FASTCC);
				let drop = self.new_clo_drop(free.iter().map(|f| f.1.clone()).collect());
				self.jobs.push(Job::Lambda {
					f: code,
					param: param.clone(),
					free: free.clone(),
					body: (**body).clone(),
				});
				let caps: Vec<(BasicValueEnum<'ctx>, MTy)> =
					free.iter().map(|(n, t)| (st.vals[n], t.clone())).collect();
				self.new_closure(code, drop, &caps).into()
			}
			MValue::Delay { body, free } => {
				let n = self.fresh();
				let ret = ty.inner().clone();
				let fty = self.fn_ty(&[self.ptr_ty().into()], &ret);
				let code = self.m.add_function(&format!("thunk${}", n), fty, None);
				code.set_call_conventions(FASTCC);
				let cap_tys: Vec<MTy> = free.iter().map(|f| f.1.clone()).collect();
				let drop = self.thunk_drop_fn(cap_tys.clone(), ret.clone());
				self.jobs.push(Job::Thunk {
					f: code,
					free: free.clone(),
					body: (**body).clone(),
				});
				let obj = self.alloc(self.thunk_alloc_ty(&cap_tys, &ret));
				let cty = self.clo_ty(&cap_tys);
				ok!(self.b.build_store(self.gep(cty, obj, 0), self.i32c(1)));
				self.store_state(obj, ST_UNEVAL);
				ok!(self.b.build_store(
					self.gep(cty, obj, 2),
					code.as_global_value().as_pointer_value()
				));
				ok!(self.b.build_store(
					self.gep(cty, obj, 3),
					drop.as_global_value().as_pointer_value()
				));
				for (i, (n, _)) in free.iter().enumerate() {
					ok!(self
						.b
						.build_store(self.gep(cty, obj, 4 + i as u32), st.vals[n]));
				}
				obj.into()
			}
			MValue::Call { func, args } => {
				let f = *self
					.fns
					.get(func)
					.unwrap_or_else(|| panic!("codegen: no instance `{}`", func));
				let vals: Vec<_> = args.iter().map(|x| self.atom(st, x)).collect();
				self.fast_call(f, &vals).unwrap_or_else(|| self.unit())
			}
			MValue::MakePap { func, args } => {
				let vals: Vec<_> = args.iter().map(|x| self.atom(st, x)).collect();
				self.make_pap(func, &vals)
			}
			MValue::Apply(f, a) => {
				let rt = match self.atom_ty(st, f).inner() {
					MTy::Fn(_, r) => (**r).clone(),
					other => panic!("codegen: apply of non-function {:?}", other),
				};
				let clo = self.atom(st, f).into_pointer_value();
				let arg = self.atom(st, a);
				self.apply_closure(clo, arg, &rt)
			}
			MValue::Prim(p, args) => self.prim(st, ty, *p, args),
			MValue::Force(a) => {
				let inner = self.atom_ty(st, a).inner().clone();
				let fg = self.force_fn(&inner);
				let s = self.atom(st, a);
				self.call(fg, &[s]).unwrap_or_else(|| self.unit())
			}
			MValue::Wrap(a) => {
				let t = self.atom_ty(st, a);
				let v = self.atom(st, a);
				self.wrap(v, &t)
			}
		}
	}

	fn prim(
		&mut self,
		st: &mut St<'ctx>,
		ty: &MTy,
		p: Intrinsic,
		args: &[MAtom],
	) -> BasicValueEnum<'ctx> {
		use Intrinsic::*;
		let i32t = self.ctx.i32_type();
		let i64t = self.ctx.i64_type();
		let ptr = self.ptr_ty();
		let a: Vec<BasicValueEnum<'ctx>> = args.iter().map(|x| self.atom(st, x)).collect();
		let bool_result = |this: &Self, c: IntValue<'ctx>| -> BasicValueEnum<'ctx> {
			let bi = this
				.prog
				.bool_ty
				.expect("a comparison needs the bool type from the lang manifest");
			let it = this.lty(ty).into_int_type();
			ok!(this.b.build_select(
				c,
				it.const_int(bi.true_tag as u64, false),
				it.const_int(bi.false_tag as u64, false),
				""
			))
			.into()
		};
		match p {
			IAdd => ok!(self
				.b
				.build_int_add(a[0].into_int_value(), a[1].into_int_value(), ""))
			.into(),
			ISub => ok!(self
				.b
				.build_int_sub(a[0].into_int_value(), a[1].into_int_value(), ""))
			.into(),
			IMul => ok!(self
				.b
				.build_int_mul(a[0].into_int_value(), a[1].into_int_value(), ""))
			.into(),
			IDiv | IMod => {
				let f = self.rt(
					if p == IDiv { RT_IDIV } else { RT_IMOD },
					Some(i32t.into()),
					&[i32t.into(), i32t.into()],
				);
				self.call(f, &[a[0], a[1]]).unwrap()
			}
			IEq | INeq | IGr | IGre | ILs | ILse => {
				let pred = match p {
					IEq => IntPredicate::EQ,
					INeq => IntPredicate::NE,
					IGr => IntPredicate::SGT,
					IGre => IntPredicate::SGE,
					ILs => IntPredicate::SLT,
					_ => IntPredicate::SLE,
				};
				let c = ok!(self.b.build_int_compare(
					pred,
					a[0].into_int_value(),
					a[1].into_int_value(),
					""
				));
				bool_result(self, c)
			}
			FAdd => {
				ok!(self
					.b
					.build_float_add(a[0].into_float_value(), a[1].into_float_value(), ""))
				.into()
			}
			FSub => {
				ok!(self
					.b
					.build_float_sub(a[0].into_float_value(), a[1].into_float_value(), ""))
				.into()
			}
			FMul => {
				ok!(self
					.b
					.build_float_mul(a[0].into_float_value(), a[1].into_float_value(), ""))
				.into()
			}
			FDiv => {
				ok!(self
					.b
					.build_float_div(a[0].into_float_value(), a[1].into_float_value(), ""))
				.into()
			}
			FEq | FNeq | FGr | FGre | FLs | FLse => {
				let pred = match p {
					FEq => FloatPredicate::OEQ,
					FNeq => FloatPredicate::UNE,
					FGr => FloatPredicate::OGT,
					FGre => FloatPredicate::OGE,
					FLs => FloatPredicate::OLT,
					_ => FloatPredicate::OLE,
				};
				let c = ok!(self.b.build_float_compare(
					pred,
					a[0].into_float_value(),
					a[1].into_float_value(),
					""
				));
				bool_result(self, c)
			}
			ShowInt | ShowFloat | FloatRepr => {
				let len = self.entry_alloca(st.func, i64t.into());
				let (name, pty): (&str, BasicMetadataTypeEnum<'ctx>) = match p {
					ShowInt => (RT_SHOW_INT, i32t.into()),
					ShowFloat => (RT_SHOW_FLOAT, self.ctx.f64_type().into()),
					_ => (RT_FLOAT_REPR, self.ctx.f64_type().into()),
				};
				let f = self.rt(name, Some(ptr.into()), &[pty, ptr.into()]);
				let buf = self.call(f, &[a[0], len.into()]).unwrap();
				let n = ok!(self.b.build_load(i64t, len, ""));
				let (from_f, _) = self.list_helpers();
				self.call(from_f, &[buf, n]).unwrap()
			}
			IAnd => ok!(self
				.b
				.build_and(a[0].into_int_value(), a[1].into_int_value(), ""))
			.into(),
			IOr => ok!(self
				.b
				.build_or(a[0].into_int_value(), a[1].into_int_value(), ""))
			.into(),
			IXor => ok!(self
				.b
				.build_xor(a[0].into_int_value(), a[1].into_int_value(), ""))
			.into(),
			// the shift amount is taken mod 32 (LLVM makes an oversized shift poison)
			IShl | IShr | ISar => {
				let n = ok!(self
					.b
					.build_and(a[1].into_int_value(), i32t.const_int(31, false), ""));
				let x = a[0].into_int_value();
				match p {
					IShl => ok!(self.b.build_left_shift(x, n, "")).into(),
					IShr => ok!(self.b.build_right_shift(x, n, false, "")).into(),
					_ => ok!(self.b.build_right_shift(x, n, true, "")).into(),
				}
			}
			// Char and Int are both i32
			CharOrd | CharChr => a[0],
			IToF => ok!(self.b.build_signed_int_to_float(
				a[0].into_int_value(),
				self.ctx.f64_type(),
				""
			))
			.into(),
			FToI => {
				let f = self.rt(RT_FTOI, Some(i32t.into()), &[self.ctx.f64_type().into()]);
				self.call(f, &[a[0]]).unwrap()
			}
			Rt(i) => {
				use crate::rtprims::{self, Kind};
				let sig = rtprims::get(i);
				let f64t = self.ctx.f64_type();
				let mut cargs: Vec<BasicValueEnum<'ctx>> = Vec::new();
				let mut ptys: Vec<BasicMetadataTypeEnum<'ctx>> = Vec::new();
				for (k, kind) in sig.args.iter().enumerate() {
					match kind {
						Kind::Int => {
							cargs.push(a[k]);
							ptys.push(i32t.into());
						}
						Kind::Float => {
							cargs.push(a[k]);
							ptys.push(f64t.into());
						}
						Kind::Str => {
							// force the whole list into a StrBuf; the C function owns it
							let to_sb = self.to_sb_helper();
							let sb = self.call(to_sb, &[a[k]]).unwrap();
							cargs.push(sb);
							ptys.push(ptr.into());
						}
						Kind::Unit => unreachable!("`{}`: Unit is only a result kind", sig.key),
					}
				}
				match sig.ret {
					Kind::Unit => {
						let f = self.rt(sig.c, None, &ptys);
						self.call(f, &cargs);
						// `exit` is typed `IO a`: it never returns, so any value will do
						match ty {
							MTy::Unit => self.unit(),
							t => self.lty(t).const_zero(),
						}
					}
					Kind::Int => {
						let f = self.rt(sig.c, Some(i32t.into()), &ptys);
						self.call(f, &cargs).unwrap()
					}
					Kind::Float => {
						let f = self.rt(sig.c, Some(f64t.into()), &ptys);
						self.call(f, &cargs).unwrap()
					}
					Kind::Str => {
						let len = self.entry_alloca(st.func, i64t.into());
						cargs.push(len.into());
						ptys.push(ptr.into());
						let f = self.rt(sig.c, Some(ptr.into()), &ptys);
						let buf = self.call(f, &cargs).unwrap();
						let n = ok!(self.b.build_load(i64t, len, ""));
						let (from_f, _) = self.list_helpers();
						self.call(from_f, &[buf, n]).unwrap()
					}
				}
			}
			Print | Println => {
				let (_, print_f) = self.list_helpers();
				self.call(print_f, &[a[0], self.i32c((p == Println) as u64).into()]); // consumes the list
				self.unit()
			}
			GetLn => {
				let len = self.entry_alloca(st.func, i64t.into());
				let f = self.rt(RT_GETLN, Some(ptr.into()), &[ptr.into()]);
				let buf = self.call(f, &[len.into()]).unwrap();
				let n = ok!(self.b.build_load(i64t, len, ""));
				let (from_f, _) = self.list_helpers();
				self.call(from_f, &[buf, n]).unwrap()
			}
			IoReturn | IoBind | SumLeft | SumRight | UnitVal => {
				unreachable!("{:?} is synthesized by lower.rs, not a primitive", p)
			}
		}
	}

	// emit in a loop instead of recursion in case a function has a really long let chain
	fn expr(&mut self, st: &mut St<'ctx>, e: &MExpr) {
		let mut e = e;
		loop {
			match e {
				MExpr::Let(x, ty, v, rest) => {
					let val = self.value(st, ty, v);
					st.vals.insert(x.clone(), val);
					st.tys.insert(x.clone(), ty.clone());
					e = &**rest;
				}
				MExpr::Dup(n, r) => {
					let (v, t) = (st.vals[n], st.tys[n].clone());
					self.dup(v, &t);
					e = &**r;
				}
				MExpr::Drop(n, r) => {
					let (v, t) = (st.vals[n], st.tys[n].clone());
					self.drop_v(v, &t);
					e = &**r;
				}
				_ => break,
			}
		}
		self.expr_term(st, e);
	}

	fn expr_term(&mut self, st: &mut St<'ctx>, e: &MExpr) {
		match e {
			MExpr::Let(..) | MExpr::Dup(..) | MExpr::Drop(..) => unreachable!("handled by `expr`"),
			MExpr::Ret(a) => {
				let v = self.atom(st, a);
				ok!(self.b.build_return(Some(&v)));
			}
			MExpr::Take {
				binds,
				from,
				ctor,
				token,
				rest,
			} => {
				let (v, t) = (st.vals[from], st.tys[from].clone());
				let did = Self::data_id(&t);
				let ci = self.prog.datas[did].tag_of(ctor).unwrap();
				let f = st.func;
				let obj = self.untag(did, v.into_pointer_value());
				let oty = self.obj_ty(did, ci);
				let base = self.base(did);
				let leaves = self.facts.leaves(&self.ctor_pty(did, ci));
				// read every leaf before branching, the path may free the cell
				let words: Vec<BasicValueEnum<'ctx>> = (0..leaves.len())
					.map(|i| {
						self.load_leaf(
							oty,
							obj,
							base + i as u32,
							self.packed_ty(did, ci, i).as_ref(),
						)
					})
					.collect();
				let bound = |i: usize| binds.iter().any(|b| b.2 == i);
				let rc = ok!(self.b.build_load(self.ctx.i32_type(), obj, "")).into_int_value();
				let uniq = ok!(self
					.b
					.build_int_compare(IntPredicate::EQ, rc, self.i32c(1), ""));
				let bu = self.new_bb(f, "take.unique");
				let bs = self.new_bb(f, "take.shared");
				let bj = self.new_bb(f, "take.join");
				ok!(self.b.build_conditional_branch(uniq, bu, bs));
				self.b.position_at_end(bu);
				for (i, l) in leaves.iter().enumerate() {
					if !bound(i) && !self.facts.is_packed(did, ci, i) {
						self.drop_v(words[i], l);
					}
				}
				if token.is_none() {
					self.free(obj);
				}
				let bu_end = self.b.get_insert_block().unwrap();
				ok!(self.b.build_unconditional_branch(bj));
				self.b.position_at_end(bs);
				for (i, l) in leaves.iter().enumerate() {
					if bound(i) && !self.facts.is_packed(did, ci, i) {
						self.dup(words[i], l);
					}
				}
				ok!(self
					.b
					.build_store(obj, ok!(self.b.build_int_sub(rc, self.i32c(1), ""))));
				ok!(self.b.build_unconditional_branch(bj));
				self.b.position_at_end(bj);
				if let Some(tok) = token {
					let null = self.ptr_ty().const_null();
					let phi = ok!(self.b.build_phi(self.ptr_ty(), ""));
					phi.add_incoming(&[
						(&obj as &dyn BasicValue, bu_end),
						(&null as &dyn BasicValue, bs),
					]);
					st.vals.insert(tok.clone(), phi.as_basic_value());
					st.tys.insert(tok.clone(), MTy::Token);
				}
				for (n, ty, i) in binds {
					st.vals.insert(n.clone(), words[*i]);
					st.tys.insert(n.clone(), ty.clone());
				}
				self.expr(st, rest);
			}
			MExpr::DropReuse(tok, x, r) => {
				let (v, t) = (st.vals[x], st.tys[x].clone());
				let did = Self::data_id(&t);
				let f = st.func;
				let obj = self.untag(did, v.into_pointer_value());
				let rc = ok!(self.b.build_load(self.ctx.i32_type(), obj, "")).into_int_value();
				let uniq = ok!(self
					.b
					.build_int_compare(IntPredicate::EQ, rc, self.i32c(1), ""));
				let bu = self.new_bb(f, "dr.unique");
				let bs = self.new_bb(f, "dr.shared");
				let bj = self.new_bb(f, "dr.join");
				ok!(self.b.build_conditional_branch(uniq, bu, bs));
				self.b.position_at_end(bu);
				let fg = self.fields_fn(did);
				self.call(fg, &[v]);
				let bu_end = self.b.get_insert_block().unwrap();
				ok!(self.b.build_unconditional_branch(bj));
				self.b.position_at_end(bs);
				ok!(self
					.b
					.build_store(obj, ok!(self.b.build_int_sub(rc, self.i32c(1), ""))));
				let null = self.ptr_ty().const_null();
				ok!(self.b.build_unconditional_branch(bj));
				self.b.position_at_end(bj);
				let phi = ok!(self.b.build_phi(self.ptr_ty(), ""));
				phi.add_incoming(&[
					(&obj as &dyn BasicValue, bu_end),
					(&null as &dyn BasicValue, bs),
				]);
				st.vals.insert(tok.clone(), phi.as_basic_value());
				st.tys.insert(tok.clone(), MTy::Token);
				self.expr(st, r);
			}
			MExpr::Case(a, arms) => self.case(st, a, arms),
		}
	}

	fn arm_body(&mut self, st: &St<'ctx>, bb: BasicBlock<'ctx>, body: &MExpr) {
		self.b.position_at_end(bb);
		let mut st2 = St {
			func: st.func,
			vals: st.vals.clone(),
			tys: st.tys.clone(),
		};
		self.expr(&mut st2, body);
	}

	fn case(&mut self, st: &mut St<'ctx>, a: &MAtom, arms: &[MArm]) {
		let f = st.func;
		let sty = self.atom_ty(st, a);
		let sv = self.atom(st, a);
		let fail_bb = self.new_bb(f, "nomatch");
		let wild = arms.iter().position(|m| matches!(m.pat, MPat::Wild));
		let blocks: Vec<BasicBlock<'ctx>> = arms.iter().map(|_| self.new_bb(f, "arm")).collect();
		let default_bb = wild.map(|i| blocks[i]).unwrap_or(fail_bb);
		match &sty {
			MTy::Data(id) => {
				let tag = self.get_tag(f, *id, sv);
				let mut cases = Vec::new();
				for (i, m) in arms.iter().enumerate() {
					if let MPat::Ctor(c) = &m.pat {
						// let t = self.prog.datas[*id]
						// 	.tag_of(c)
						// 	.expect("unknown ctor in case");
						let t = self.prog.datas[*id].tag_of(c).unwrap_or_else(|| {
							panic!(
        "unknown ctor `{}` in case on `{:?}` : data `{}` (id {}) in fn `{}`; ctors = {:?}",
        c, a,
        self.prog.datas[*id].name, id,
        f.get_name().to_string_lossy(),
        self.prog.datas[*id].ctors.iter().map(|c| &c.name).collect::<Vec<_>>()
    )
						});
						cases.push((self.i32c(t as u64), blocks[i]));
					}
				}
				ok!(self.b.build_switch(tag, default_bb, &cases));
			}
			MTy::Int | MTy::Char => {
				let mut cases = Vec::new();
				for (i, m) in arms.iter().enumerate() {
					match &m.pat {
						MPat::Int(n) => cases.push((
							self.ctx.i32_type().const_int(*n as i64 as u64, true),
							blocks[i],
						)),
						MPat::Char(c) => cases.push((self.i32c(*c as u64), blocks[i])),
						_ => {}
					}
				}
				ok!(self.b.build_switch(sv.into_int_value(), default_bb, &cases));
			}
			MTy::Float => {
				for (i, m) in arms.iter().enumerate() {
					if let MPat::Float(x) = &m.pat {
						let c = ok!(self.b.build_float_compare(
							FloatPredicate::OEQ,
							sv.into_float_value(),
							self.ctx.f64_type().const_float(*x),
							""
						));
						let next = self.new_bb(f, "fcmp");
						ok!(self.b.build_conditional_branch(c, blocks[i], next));
						self.b.position_at_end(next);
					}
				}
				ok!(self.b.build_unconditional_branch(default_bb));
			}
			_ => {
				ok!(self.b.build_unconditional_branch(default_bb));
			}
		}
		for (i, m) in arms.iter().enumerate() {
			self.arm_body(st, blocks[i], &m.body);
		}
		self.b.position_at_end(fail_bb);
		self.fail_with(MSG_NO_MATCH);
		ok!(self.b.build_unreachable());
	}

	fn drain(&mut self) {
		while let Some(job) = self.jobs.pop() {
			match job {
				Job::Dup { f, ty } => self.emit_dup(f, &ty),
				Job::Drop { f, ty } => self.emit_drop(f, &ty),
				Job::Force { f, ty } => self.emit_force(f, &ty),
				Job::Fields { f, did } => self.emit_fields(f, did),
				Job::ThunkDrop { f, caps, ret } => self.emit_thunk_drop(f, &caps, &ret),
				Job::CloDrop { f, caps } => {
					let e = self.new_bb(f, "entry");
					self.b.position_at_end(e);
					let clo = f.get_nth_param(0).unwrap().into_pointer_value();
					let cty = self.clo_ty(&caps);
					for (i, t) in caps.iter().enumerate() {
						if self.facts.needs_rc(t) {
							let v = ok!(self.b.build_load(
								self.lty(t),
								self.gep(cty, clo, 4 + i as u32),
								""
							));
							self.drop_v(v, t);
						}
					}
					self.free(clo);
					ok!(self.b.build_return(None));
				}
				Job::Lambda {
					f,
					param,
					free,
					body,
				} => {
					let e = self.new_bb(f, "entry");
					self.b.position_at_end(e);
					let clo = f.get_nth_param(0).unwrap().into_pointer_value();
					let arg = f.get_nth_param(1).unwrap();
					let caps: Vec<MTy> = free.iter().map(|x| x.1.clone()).collect();
					let vals = self.closure_prologue(f, clo, &caps);
					let mut st = St {
						func: f,
						vals: HashMap::new(),
						tys: HashMap::new(),
					};
					for ((n, t), v) in free.iter().zip(vals) {
						st.vals.insert(n.clone(), v);
						st.tys.insert(n.clone(), t.clone());
					}
					st.vals.insert(param.0.clone(), arg);
					st.tys.insert(param.0.clone(), param.1.clone());
					self.expr(&mut st, &body);
				}
				Job::Thunk { f, free, body } => {
					// a thunk never runs twice, so move out captures and keep obj for result
					let e = self.new_bb(f, "entry");
					self.b.position_at_end(e);
					let obj = f.get_nth_param(0).unwrap().into_pointer_value();
					let caps: Vec<MTy> = free.iter().map(|x| x.1.clone()).collect();
					let cty = self.clo_ty(&caps);
					let mut st = St {
						func: f,
						vals: HashMap::new(),
						tys: HashMap::new(),
					};
					for (i, (n, t)) in free.iter().enumerate() {
						let v = ok!(self.b.build_load(
							self.lty(t),
							self.gep(cty, obj, 4 + i as u32),
							""
						));
						st.vals.insert(n.clone(), v);
						st.tys.insert(n.clone(), t.clone());
					}
					self.expr(&mut st, &body);
				}
				Job::Pap { f, func, k } => {
					let e = self.new_bb(f, "entry");
					self.b.position_at_end(e);
					let clo = f.get_nth_param(0).unwrap().into_pointer_value();
					let arg = f.get_nth_param(1).unwrap();
					let (ptys, borrowed, _) = self.sigs[&func].clone();
					let cap_tys = self.susp_cap_tys(&ptys[..k]);
					let mut vals = self.closure_prologue(f, clo, &cap_tys);
					vals.push(arg);
					if k + 1 == ptys.len() {
						let target = self.fns[&func];
						// every stored arg is a susp, strict param wants value
						let mut call_args = Vec::new();
						for (i, v) in vals.iter().enumerate() {
							if ptys[i].is_susp() {
								call_args.push(*v);
							} else {
								let fg = self.force_fn(&ptys[i]);
								call_args.push(self.call(fg, &[*v]).unwrap_or_else(|| self.unit()));
							}
						}
						let r = self
							.fast_call(target, &call_args)
							.unwrap_or_else(|| self.unit());
						// wrapper owns args, borrowed param's callee leaves it to this
						for (i, v) in call_args.iter().enumerate() {
							if borrowed[i] {
								self.drop_v(*v, &ptys[i]);
							}
						}
						ok!(self.b.build_return(Some(&r)));
					} else {
						let r = self.make_pap(&func, &vals);
						ok!(self.b.build_return(Some(&r)));
					}
				}
			}
		}
	}

	fn emit_body(&mut self, fv: FunctionValue<'ctx>, f: &MFunc) {
		let e = self.new_bb(fv, "entry");
		self.b.position_at_end(e);
		let mut st = St {
			func: fv,
			vals: HashMap::new(),
			tys: HashMap::new(),
		};
		for (i, (n, t)) in f.params.iter().enumerate() {
			st.vals
				.insert(n.clone(), fv.get_nth_param(i as u32).unwrap());
			st.tys.insert(n.clone(), t.clone());
		}
		self.expr(&mut st, &f.body);
	}

	pub fn generate(mut self) -> Module<'ctx> {
		let prog = self.prog;
		for f in &prog.funcs {
			let ps: Vec<BasicMetadataTypeEnum<'ctx>> =
				f.params.iter().map(|p| self.meta(&p.1)).collect();
			let fv = self.m.add_function(&f.name, self.fn_ty(&ps, &f.ret), None);
			fv.set_call_conventions(FASTCC);
			self.fns.insert(f.name.clone(), fv);
		}
		for f in &prog.funcs {
			let fv = self.fns[&f.name];
			if !f.caf {
				self.emit_body(fv, f);
				self.drain();
				continue;
			}
			// constants evaled at most once then cached
			let rty = self.lty(&f.ret);
			let init =
				self.m
					.add_function(&format!("{}.init", f.name), self.fn_ty(&[], &f.ret), None);
			init.set_call_conventions(FASTCC);
			self.emit_body(init, f);
			self.drain();
			let cache = self.m.add_global(rty, None, &format!("{}.cache", f.name));
			cache.set_initializer(&rty.const_zero());
			let done = self
				.m
				.add_global(self.ctx.i8_type(), None, &format!("{}.done", f.name));
			done.set_initializer(&self.ctx.i8_type().const_zero());
			let e = self.new_bb(fv, "entry");
			let compute = self.new_bb(fv, "compute");
			let load = self.new_bb(fv, "load");
			self.b.position_at_end(e);
			let flag = ok!(self
				.b
				.build_load(self.ctx.i8_type(), done.as_pointer_value(), ""))
			.into_int_value();
			let is_done = ok!(self.b.build_int_compare(
				IntPredicate::NE,
				flag,
				self.ctx.i8_type().const_zero(),
				""
			));
			ok!(self.b.build_conditional_branch(is_done, load, compute));
			self.b.position_at_end(compute);
			let v = self.fast_call(init, &[]).unwrap_or_else(|| self.unit());
			ok!(self.b.build_store(cache.as_pointer_value(), v));
			ok!(self.b.build_store(
				done.as_pointer_value(),
				self.ctx.i8_type().const_int(1, false)
			));
			ok!(self.b.build_unconditional_branch(load));
			self.b.position_at_end(load);
			let r = ok!(self.b.build_load(rty, cache.as_pointer_value(), ""));
			let rt = f.ret.clone();
			self.dup(r, &rt); // cache keeps its own permanent reference
			ok!(self.b.build_return(Some(&r)));
			self.drain();
		}

		// i32 iota_main(void)
		let i32t = self.ctx.i32_type();
		let main = self
			.m
			.add_function(IOTA_MAIN, i32t.fn_type(&[], false), None);
		let e = self.new_bb(main, "entry");
		self.b.position_at_end(e);
		let entry = self.fns[&prog.entry];
		let mut r = self.fast_call(entry, &[]).unwrap_or_else(|| self.unit());
		if prog.entry_kind == EntryKind::Action {
			let res = prog.entry_ret.clone();
			let world = self.imm_encode(self.unit(), &MTy::Unit);
			r = self.apply_closure(r.into_pointer_value(), world.into(), &res);
		}
		let exit: IntValue<'ctx> = match &prog.entry_ret {
			MTy::Int => r.into_int_value(),
			other => {
				let t = other.clone();
				self.drop_v(r, &t);
				i32t.const_zero()
			}
		};
		ok!(self.b.build_return(Some(&exit)));
		self.drain();
		self.m
	}
}

pub fn write_ll(prog: &MProgram, out: &Path) -> Result<(), Diagnostic> {
	let ctx = Context::create();
	let module = CodeGen::new(&ctx, prog).generate();
	module.verify().map_err(|e| {
		Diagnostic::error(format!("LLVM rejected the generated module: {}", e), None)
			.with_help("this is a bug in the Iota backend -- You didn't fuck up, I did")
	})?;
	module
		.print_to_file(out)
		.map_err(|e| Diagnostic::error(format!("writing {}: {}", out.display(), e), None))
}
