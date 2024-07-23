use std::path::PathBuf;

use color_eyre::{
    eyre::{eyre, Context as _},
    Result,
};
use hashbrown::{HashMap, HashSet};
use inkwell::{
    attributes::{Attribute, AttributeLoc},
    basic_block::BasicBlock,
    builder::Builder,
    context::Context as InkwellContext,
    module::{Linkage, Module},
    passes::{PassManager, PassManagerBuilder},
    targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine},
    types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, IntType},
    values::{BasicValueEnum, FunctionValue, IntMathValue, IntValue, PointerValue},
    AddressSpace, IntPredicate, OptimizationLevel,
};
use intcast::IntCast;
use lasso::Spur;
use tracing::{debug, debug_span, trace, trace_span};

use crate::{
    context::{Context as MflContext, ItemId, ItemKind},
    ir::{Arithmetic, Basic, Compare, Control, IntKind, Memory, OpCode, Stack, TypeResolvedOp},
    pass_manager::static_analysis::{Analyzer, ValueId},
    stores::{
        interner::Interner,
        ops::Op,
        source::SourceStore,
        types::{BuiltinTypes, IntWidth, Signedness, TypeId, TypeKind, TypeStore},
    },
    Args, Stores,
};

mod arithmetic;
mod control;
mod memory;
mod stack;

const BOOTSTRAP_OBJ: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/bootstrap.o"));
const SYSCALLS: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/syscalls.o"));

const CALL_CONV_COLD: u32 = 9;

type InkwellResult<T = ()> = Result<T, inkwell::builder::BuilderError>;
type BuilderArithFunc<'ctx, T> = fn(&'_ Builder<'ctx>, T, T, &'_ str) -> InkwellResult<T>;

impl IntWidth {
    fn get_int_type(self, ctx: &InkwellContext) -> IntType<'_> {
        match self {
            IntWidth::I8 => ctx.i8_type(),
            IntWidth::I16 => ctx.i16_type(),
            IntWidth::I32 => ctx.i32_type(),
            IntWidth::I64 => ctx.i64_type(),
        }
    }
}

impl OpCode<TypeResolvedOp> {
    fn get_arith_fn<'ctx, T: IntMathValue<'ctx>>(&self) -> BuilderArithFunc<'ctx, T> {
        let OpCode::Basic(Basic::Arithmetic(arith_op)) = self else {
            panic!("ICE: Called get_arith_fn on non-arith opcode");
        };
        match arith_op {
            Arithmetic::Add => Builder::build_int_add,
            Arithmetic::BitAnd => Builder::build_and,
            Arithmetic::BitOr => Builder::build_or,
            Arithmetic::BitXor => Builder::build_xor,
            Arithmetic::Multiply => Builder::build_int_mul,
            Arithmetic::Subtract => Builder::build_int_sub,

            Arithmetic::BitNot
            | Arithmetic::Div
            | Arithmetic::Rem
            | Arithmetic::ShiftLeft
            | Arithmetic::ShiftRight => panic!("ICE: Called get_arith_fn for non-trivial op"),
        }
    }

    fn get_div_rem_fn<'ctx, T: IntMathValue<'ctx>>(
        &self,
        signed: Signedness,
    ) -> BuilderArithFunc<'ctx, T> {
        let OpCode::Basic(Basic::Arithmetic(arith_op)) = self else {
            panic!("ICE: Called get_div_rem_fn on non-arith opcode");
        };
        match (arith_op, signed) {
            (Arithmetic::Div, Signedness::Signed) => Builder::build_int_signed_div,
            (Arithmetic::Div, Signedness::Unsigned) => Builder::build_int_unsigned_div,
            (Arithmetic::Rem, Signedness::Signed) => Builder::build_int_signed_rem,
            (Arithmetic::Rem, Signedness::Unsigned) => Builder::build_int_unsigned_rem,
            _ => panic!("ICE: Called get_div_rem_fn on non-div-rem opcode"),
        }
    }

    fn get_predicate(&self, signed: Signedness) -> IntPredicate {
        let OpCode::Basic(Basic::Compare(cmp_op)) = self else {
            panic!("ICE: Called get_predicate on non-compare opcode");
        };

        match (cmp_op, signed) {
            (Compare::Equal, _) => IntPredicate::EQ,
            (Compare::Less, Signedness::Unsigned) => IntPredicate::ULT,
            (Compare::LessEqual, Signedness::Unsigned) => IntPredicate::ULE,
            (Compare::Greater, Signedness::Unsigned) => IntPredicate::UGT,
            (Compare::GreaterEqual, Signedness::Unsigned) => IntPredicate::UGE,
            (Compare::Less, Signedness::Signed) => IntPredicate::SLT,
            (Compare::LessEqual, Signedness::Signed) => IntPredicate::SLE,
            (Compare::Greater, Signedness::Signed) => IntPredicate::SGT,
            (Compare::GreaterEqual, Signedness::Signed) => IntPredicate::SGE,
            (Compare::NotEq, _) => IntPredicate::NE,
            _ => panic!("ICE: Called get_predicate on non-predicate opcode"),
        }
    }
}

struct DataStore<'a> {
    context: &'a MflContext,
    interner: &'a mut Interner,
    analyzer: &'a Analyzer,
    type_store: &'a mut TypeStore,
    source_store: &'a SourceStore,
}

#[derive(Debug)]
struct ValueStore<'ctx> {
    value_map: HashMap<ValueId, BasicValueEnum<'ctx>>,
    variable_map: HashMap<ItemId, PointerValue<'ctx>>,
    string_map: HashMap<Spur, PointerValue<'ctx>>,
    merge_pair_map: HashMap<ValueId, PointerValue<'ctx>>,
    alloca_temp_store: HashMap<TypeId, Vec<PointerValue<'ctx>>>,
    alloca_prelude_block: BasicBlock<'ctx>,
}

impl<'ctx> ValueStore<'ctx> {
    fn new(prelude_block: BasicBlock<'ctx>) -> Self {
        Self {
            value_map: Default::default(),
            variable_map: Default::default(),
            string_map: Default::default(),
            merge_pair_map: Default::default(),
            alloca_temp_store: Default::default(),
            alloca_prelude_block: prelude_block,
        }
    }

    fn get_temp_alloca(
        &mut self,
        cg: &mut CodeGen<'ctx>,
        type_store: &mut TypeStore,
        type_id: TypeId,
    ) -> InkwellResult<PointerValue<'ctx>> {
        let slot = self
            .alloca_temp_store
            .get_mut(&type_id)
            .and_then(|v| v.pop());

        if let Some(s) = slot {
            Ok(s)
        } else {
            let cur_block = cg.builder.get_insert_block().unwrap();
            cg.builder.position_at_end(self.alloca_prelude_block);
            let llvm_type = cg.get_type(type_store, type_id);
            let alloc = cg.builder.build_alloca(llvm_type, "");
            cg.builder.position_at_end(cur_block);
            alloc
        }
    }

    fn release_temp_alloca(&mut self, type_id: TypeId, pv: PointerValue<'ctx>) {
        self.alloca_temp_store.entry(type_id).or_default().push(pv);
    }

    fn get_string_literal(
        &mut self,
        cg: &CodeGen<'ctx>,
        interner: &Interner,
        id: Spur,
    ) -> InkwellResult<PointerValue<'ctx>> {
        match self.string_map.get(&id) {
            Some(&ptr) => Ok(ptr),
            None => {
                let string = interner.resolve(id);
                let name = format!("SId{}", id.into_inner());
                let global = cg.builder.build_global_string_ptr(string, &name)?;

                let ptr = global
                    .as_pointer_value()
                    .const_cast(cg.ctx.i8_type().ptr_type(AddressSpace::default()));
                self.string_map.insert(id, ptr);

                Ok(ptr)
            }
        }
    }

    fn load_value(
        &mut self,
        cg: &mut CodeGen<'ctx>,
        id: ValueId,
        ds: &mut DataStore,
    ) -> InkwellResult<BasicValueEnum<'ctx>> {
        if let Some(&ptr) = self.merge_pair_map.get(&id) {
            let name = ptr.get_name().to_str().unwrap();
            trace!(name, "Fetching variable {id:?}");
            let [ty_id] = ds.analyzer.value_types([id]).unwrap();
            let val_type = cg.get_type(ds.type_store, ty_id);
            cg.builder.build_load(val_type, ptr, name)
        } else {
            trace!("Fetching live value {id:?}");
            Ok(self.value_map[&id])
        }
    }

    fn store_value(
        &mut self,
        cg: &CodeGen<'ctx>,
        id: ValueId,
        value: BasicValueEnum<'ctx>,
    ) -> InkwellResult {
        if let Some(&ptr) = self.merge_pair_map.get(&id) {
            trace!(
                name = ptr.get_name().to_str().unwrap(),
                "Storing variable {id:?}",
            );
            cg.builder.build_store(ptr, value)?;
        } else {
            trace!("Stored live value {id:?}");
            self.value_map.insert(id, value);
        }

        Ok(())
    }
}

struct CodeGen<'ctx> {
    ctx: &'ctx InkwellContext,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    pass_manager: PassManager<Module<'ctx>>,

    function_queue: Vec<ItemId>,
    processed_functions: HashSet<ItemId>,
    item_function_map: HashMap<ItemId, FunctionValue<'ctx>>,
    syscall_wrappers: Vec<FunctionValue<'ctx>>,
    oob_handler: FunctionValue<'ctx>,
    type_map: HashMap<TypeId, BasicTypeEnum<'ctx>>,

    attrib_align_stack: Attribute,
}

impl<'ctx> CodeGen<'ctx> {
    fn from_context(ctx: &'ctx InkwellContext, opt_level: OptimizationLevel) -> Self {
        let module = ctx.create_module("mfl_module");
        let builder = ctx.create_builder();

        let pm_builder = PassManagerBuilder::create();
        pm_builder.set_optimization_level(opt_level);
        pm_builder.set_inliner_with_threshold(23);
        let pass_manager = PassManager::create(());
        pm_builder.populate_module_pass_manager(&pass_manager);

        const ATTRIBUTE_ALIGNSTACK: u32 = 81;

        let attrib_align_stack = ctx.create_enum_attribute(ATTRIBUTE_ALIGNSTACK, 32);

        let oob_sig = ctx.void_type().fn_type(&[], false);
        let oob_handler = module.add_function("_oob", oob_sig, Some(Linkage::Private));

        Self {
            ctx,
            module,
            builder,
            pass_manager,
            function_queue: Vec::new(),
            processed_functions: HashSet::new(),
            item_function_map: HashMap::new(),
            syscall_wrappers: Vec::new(),
            oob_handler,
            type_map: HashMap::new(),
            attrib_align_stack,
        }
    }

    fn enqueue_function(&mut self, item: ItemId) {
        if !self.processed_functions.contains(&item) {
            trace!(name = ?item, "Enqueing function");
            self.function_queue.push(item);
            self.processed_functions.insert(item);
        }
    }

    fn build_function_prototypes(
        &mut self,
        program: &MflContext,
        interner: &mut Interner,
        type_store: &mut TypeStore,
    ) {
        let _span = debug_span!(stringify!(CodeGen::build_function_prototypes)).entered();

        let proto_span = debug_span!("building prototypes").entered();
        for item in program.get_all_items() {
            if item.kind != ItemKind::Function {
                continue;
            }
            let item_sig = program.trir().get_item_signature(item.id);

            let name = interner.get_symbol_name(program, item.id);
            trace!(name, "Building prototype");

            let entry_stack: Vec<BasicMetadataTypeEnum> = item_sig
                .entry
                .iter()
                .map(|t| self.get_type(type_store, *t).into())
                .collect();

            let function_type = if item_sig.exit.is_empty() {
                self.ctx.void_type().fn_type(&entry_stack, false)
            } else {
                let exit_stack: Vec<_> = item_sig
                    .exit
                    .iter()
                    .map(|t| self.get_type(type_store, *t))
                    .collect();
                self.ctx
                    .struct_type(&exit_stack, false)
                    .fn_type(entry_stack.as_slice(), false)
            };

            let function = self
                .module
                .add_function(name, function_type, Some(Linkage::Private));
            function.add_attribute(AttributeLoc::Function, self.attrib_align_stack);
            if name == "builtins$oob_handler" {
                self.oob_handler = function;
                // Because the OoB handle isn't called like a regular function, we'll enqueue it here.
                self.enqueue_function(item.id);
                function.set_call_conventions(CALL_CONV_COLD);
            }
            self.item_function_map.insert(item.id, function);
        }
        proto_span.exit();

        let _syscall_span = debug_span!("defining syscalls").entered();
        let args: Vec<BasicMetadataTypeEnum> =
            (1..=7).map(|_| self.ctx.i64_type().into()).collect();
        for i in 0..7 {
            let args = &args[..=i];
            let func_sig = self.ctx.i64_type().fn_type(args, false);
            let function = self.module.add_function(
                &(format!("_syscall{}", i + 1)),
                func_sig,
                Some(Linkage::External),
            );
            self.syscall_wrappers.push(function);
        }
    }

    fn cast_int(
        &mut self,
        v: IntValue<'ctx>,
        target_type: IntType<'ctx>,
        from_signedness: Signedness,
    ) -> InkwellResult<IntValue<'ctx>> {
        use std::cmp::Ordering;
        let name = v.get_name().to_str().unwrap(); // Our name came from us, so should be valid.
        let widened = match v
            .get_type()
            .get_bit_width()
            .cmp(&target_type.get_bit_width())
        {
            Ordering::Less => match from_signedness {
                Signedness::Signed => {
                    self.builder
                        .build_int_s_extend_or_bit_cast(v, target_type, name)?
                }
                Signedness::Unsigned => {
                    self.builder
                        .build_int_z_extend_or_bit_cast(v, target_type, name)?
                }
            },
            Ordering::Equal => v,
            Ordering::Greater => {
                self.builder
                    .build_int_truncate_or_bit_cast(v, target_type, name)?
            }
        };

        Ok(widened)
    }

    fn get_type(&mut self, type_store: &mut TypeStore, kind: TypeId) -> BasicTypeEnum<'ctx> {
        if let Some(tp) = self.type_map.get(&kind) {
            return *tp;
        }

        let tp = match type_store.get_type_info(kind).kind {
            TypeKind::Integer(int) => match int.width {
                IntWidth::I8 => self.ctx.i8_type().into(),
                IntWidth::I16 => self.ctx.i16_type().into(),
                IntWidth::I32 => self.ctx.i32_type().into(),
                IntWidth::I64 => self.ctx.i64_type().into(),
            },
            TypeKind::Bool => self.ctx.bool_type().into(),
            TypeKind::Pointer(sub_to_kind) => self
                .get_type(type_store, sub_to_kind)
                .ptr_type(AddressSpace::default())
                .into(),
            TypeKind::Array { type_id, length } => self
                .get_type(type_store, type_id)
                .array_type(length.to_u32().unwrap())
                .into(),
            TypeKind::Struct(_) | TypeKind::GenericStructInstance(_) => {
                let struct_def = type_store.get_struct_def(kind);

                if struct_def.is_union {
                    let size = type_store.get_size_info(kind);
                    let size = match size.byte_width % 8 {
                        0 => size.byte_width / 8,
                        _ => (size.byte_width / 8) + 1,
                    };
                    self.ctx
                        .i64_type()
                        .array_type(size.to_u32().unwrap())
                        .into()
                } else {
                    let fields: Vec<BasicTypeEnum> = struct_def
                        .clone()
                        .fields
                        .iter()
                        .map(|f| self.get_type(type_store, f.kind))
                        .collect();

                    self.ctx.struct_type(&fields, false).into()
                }
            }
            TypeKind::GenericStructBase(_) => unreachable!(),
        };

        self.type_map.insert(kind, tp);

        tp
    }

    fn compile_block(
        &mut self,
        ds: &mut DataStore,
        value_store: &mut ValueStore<'ctx>,
        id: ItemId,
        block: &[Op<TypeResolvedOp>],
        function: FunctionValue<'ctx>,
    ) -> InkwellResult {
        for op in block {
            match op.code {
                OpCode::Basic(Basic::Stack(Stack::Swap { count })) => {
                    trace!(?op.id, count.inner, "Swap")
                }
                OpCode::Basic(Basic::Stack(Stack::Dup { count })) => {
                    trace!(?op.id, count.inner, "Dup" )
                }
                OpCode::Basic(Basic::Stack(Stack::Drop { count })) => {
                    trace!(?op.id, count.inner, "Drop")
                }
                OpCode::Basic(Basic::Stack(Stack::Over { depth })) => {
                    trace!(?op.id, depth.inner, "Over")
                }
                OpCode::Basic(Basic::Stack(Stack::Reverse { count })) => {
                    trace!(?op.id, count.inner, "Rev")
                }
                OpCode::Basic(Basic::Stack(Stack::Rotate {
                    item_count,
                    direction,
                    shift_count,
                })) => trace!(item_count.inner, ?direction, shift_count.inner, "Rot"),
                OpCode::Complex(TypeResolvedOp::Memory { id, is_global }) => {
                    trace!(?op.id, ?id, is_global, "Memory")
                }
                OpCode::Complex(TypeResolvedOp::If(_)) => trace!(?op.id, "If"),
                OpCode::Complex(TypeResolvedOp::While(_)) => trace!(?op.id, "While"),
                _ => trace!(?op.id, "{:?}", op.code),
            }

            match &op.code {
                OpCode::Basic(Basic::Arithmetic(arith_op)) => match arith_op {
                    Arithmetic::Add | Arithmetic::Subtract => {
                        self.build_add_sub(ds, value_store, op)?
                    }
                    Arithmetic::BitAnd
                    | Arithmetic::BitOr
                    | Arithmetic::BitXor
                    | Arithmetic::Multiply => {
                        self.build_multiply_and_or_xor(ds, value_store, op)?
                    }

                    Arithmetic::BitNot => self.build_bit_not(ds, value_store, op)?,

                    Arithmetic::Div | Arithmetic::Rem => self.build_div_rem(ds, value_store, op)?,
                    Arithmetic::ShiftLeft | Arithmetic::ShiftRight => {
                        self.build_shift_left_right(ds, value_store, op)?
                    }
                },

                OpCode::Basic(Basic::Compare(cmp_op)) => match cmp_op {
                    Compare::Equal
                    | Compare::Less
                    | Compare::LessEqual
                    | Compare::Greater
                    | Compare::GreaterEqual
                    | Compare::NotEq => self.build_compare(ds, value_store, op)?,

                    Compare::IsNull => self.build_is_null(ds, value_store, op)?,
                },

                OpCode::Basic(Basic::Control(cnt_op)) => match cnt_op {
                    Control::Epilogue | Control::Return => {
                        self.build_epilogue_return(ds, value_store, id, op)?;
                        break;
                    }
                    Control::Exit => {
                        self.build_exit()?;
                        break;
                    }
                    Control::Prologue => self.build_prologue(ds, value_store, op, function)?,
                    Control::SysCall { arg_count } => {
                        self.build_syscall(ds, value_store, op, *arg_count)?
                    }
                },

                OpCode::Basic(Basic::Memory(mem_op)) => match mem_op {
                    Memory::ExtractArray { emit_array } => {
                        self.build_extract_array(ds, value_store, function, op, *emit_array)?
                    }
                    Memory::ExtractStruct {
                        emit_struct,
                        field_name,
                    } => {
                        self.build_extract_struct(ds, value_store, op, *field_name, *emit_struct)?
                    }
                    Memory::InsertArray { emit_array } => {
                        self.build_insert_array(ds, value_store, function, op, *emit_array)?
                    }
                    Memory::InsertStruct {
                        emit_struct,
                        field_name,
                    } => {
                        self.build_insert_struct(ds, value_store, op, *field_name, *emit_struct)?
                    }
                    Memory::Load => self.build_load(ds, value_store, op)?,
                    Memory::PackArray { .. } => self.build_pack(ds, value_store, op)?,
                    Memory::Store => self.build_store(ds, value_store, op)?,
                    Memory::Unpack => self.build_unpack(ds, value_store, op)?,
                },

                OpCode::Basic(Basic::Stack(stk_op)) => match stk_op {
                    Stack::Dup { .. } | Stack::Over { .. } => {
                        self.build_dup_over(ds, value_store, op)?
                    }

                    // These do nothing in codegen
                    Stack::Drop { .. }
                    | Stack::Emit { .. }
                    | Stack::Reverse { .. }
                    | Stack::Rotate { .. }
                    | Stack::Swap { .. } => {
                        continue;
                    }
                },

                OpCode::Basic(Basic::PushBool(val)) => {
                    self.build_push_bool(ds, value_store, op, *val)?
                }
                OpCode::Basic(Basic::PushInt { width, value }) => {
                    self.build_push_int(ds, value_store, op, *width, *value)?
                }
                OpCode::Basic(Basic::PushStr { id, is_c_str }) => {
                    self.build_push_str(ds, value_store, op, *id, *is_c_str)?
                }

                OpCode::Complex(cmp_op) => match cmp_op {
                    TypeResolvedOp::Cast { id } => self.build_cast(ds, value_store, op, *id)?,
                    TypeResolvedOp::CallFunction { id: callee_id } => {
                        self.build_function_call(ds, value_store, op, *callee_id)?
                    }
                    TypeResolvedOp::If(if_op) => {
                        self.build_if(ds, value_store, function, id, op, if_op)?;
                        if if_op.else_block.is_terminal && if_op.then_block.is_terminal {
                            // Nothing else to codegen here.
                            break;
                        }
                    }
                    TypeResolvedOp::Const { id } => self.build_const(ds, value_store, op, *id)?,
                    TypeResolvedOp::PackStruct { .. } => self.build_pack(ds, value_store, op)?,
                    TypeResolvedOp::Memory {
                        id,
                        is_global: false,
                    } => self.build_memory_local(ds, value_store, op, *id)?,
                    TypeResolvedOp::Memory {
                        id: _,
                        is_global: true,
                    } => todo!(),
                    TypeResolvedOp::SizeOf { id: kind } => {
                        let size_info = ds.type_store.get_size_info(*kind);
                        self.build_push_int(
                            ds,
                            value_store,
                            op,
                            IntWidth::I64,
                            IntKind::Unsigned(size_info.byte_width),
                        )?;
                    }
                    TypeResolvedOp::While(while_op) => {
                        self.build_while(ds, value_store, function, id, op, while_op)?
                    }
                },
            }
        }

        Ok(())
    }

    fn build_merge_variables(
        &mut self,
        block: &[Op<TypeResolvedOp>],
        analyzer: &Analyzer,
        type_store: &mut TypeStore,
        merge_pair_map: &mut HashMap<ValueId, PointerValue<'ctx>>,
    ) -> InkwellResult {
        fn make_variable<'ctx>(
            value_id: ValueId,
            cg: &mut CodeGen<'ctx>,
            analyzer: &Analyzer,
            type_store: &mut TypeStore,
            merge_pair_map: &mut HashMap<ValueId, PointerValue<'ctx>>,
        ) -> InkwellResult {
            if merge_pair_map.contains_key(&value_id) {
                trace!("        Variable already exists for `{value_id:?}`");
                return Ok(());
            }
            let type_id = analyzer.value_types([value_id]).unwrap()[0];
            let typ = cg.get_type(type_store, type_id);
            let name = format!("{value_id}_var");
            trace!("        Defining variable `{name}`");

            let var = cg.builder.build_alloca(typ, &name)?;
            merge_pair_map.insert(value_id, var);

            Ok(())
        }

        for op in block {
            match &op.code {
                OpCode::Complex(TypeResolvedOp::If(if_op)) => {
                    let Some(op_merges) = analyzer.get_if_merges(op.id) else {
                        panic!("ICE: If block doesn't have merge info");
                    };
                    for merge in op_merges {
                        make_variable(
                            merge.output_value,
                            self,
                            analyzer,
                            type_store,
                            merge_pair_map,
                        )?;
                    }

                    self.build_merge_variables(
                        &if_op.then_block.block,
                        analyzer,
                        type_store,
                        merge_pair_map,
                    )?;
                    self.build_merge_variables(
                        &if_op.else_block.block,
                        analyzer,
                        type_store,
                        merge_pair_map,
                    )?;
                }
                OpCode::Complex(TypeResolvedOp::While(while_op)) => {
                    let Some(op_merges) = analyzer.get_while_merges(op.id) else {
                        panic!("ICE: While block doesn't have merge info");
                    };
                    for merge in &op_merges.condition {
                        make_variable(merge.pre_value, self, analyzer, type_store, merge_pair_map)?;
                    }

                    for merge in &op_merges.body {
                        make_variable(merge.pre_value, self, analyzer, type_store, merge_pair_map)?;
                    }

                    self.build_merge_variables(
                        &while_op.condition.block,
                        analyzer,
                        type_store,
                        merge_pair_map,
                    )?;
                    self.build_merge_variables(
                        &while_op.body_block.block,
                        analyzer,
                        type_store,
                        merge_pair_map,
                    )?;
                }

                _ => continue,
            };
        }

        Ok(())
    }

    fn compile_procedure(
        &mut self,
        program: &MflContext,
        id: ItemId,
        function: FunctionValue<'ctx>,
        source_store: &SourceStore,
        interner: &mut Interner,
        type_store: &mut TypeStore,
    ) -> InkwellResult {
        let name = interner.get_symbol_name(program, id);
        let _span = debug_span!(stringify!(CodeGen::compile_procedure), name).entered();

        let mut value_store = ValueStore::new(self.ctx.append_basic_block(function, "allocs"));

        let entry_block = self.ctx.append_basic_block(function, "entry");
        self.builder.position_at_end(entry_block);

        trace!("Defining local allocations");
        let scope = program.nrir().get_scope(id);
        for &item_id in scope.get_child_items().values() {
            let item_id = item_id.inner;
            let item_header = program.get_item_header(item_id);
            if item_header.kind != ItemKind::Memory {
                continue;
            }

            let alloc_type_id = program.trir().get_memory_type(item_id);
            let (store_type_id, alloc_size, is_array) = match type_store
                .get_type_info(alloc_type_id)
                .kind
            {
                TypeKind::Array { type_id, length } => (type_id, length.to_u32().unwrap(), true),
                TypeKind::Integer { .. }
                | TypeKind::Pointer(_)
                | TypeKind::Bool
                | TypeKind::Struct(_)
                | TypeKind::GenericStructBase(_)
                | TypeKind::GenericStructInstance(_) => (alloc_type_id, 1, false),
            };

            let mem_type = self.get_type(type_store, store_type_id);
            let array_type = mem_type.array_type(alloc_size);
            let name = interner.get_symbol_name(program, item_id).to_owned() + "_";
            let variable = self.builder.build_alloca(array_type, &name)?;

            self.builder
                .build_store(variable, array_type.const_zero())?;

            let variable = if !is_array {
                self.builder.build_pointer_cast(
                    variable,
                    mem_type.ptr_type(AddressSpace::default()),
                    &name,
                )?
            } else {
                variable
            };

            value_store.variable_map.insert(item_id, variable);
        }

        trace!("Defining merge variables");
        self.build_merge_variables(
            program.trir().get_item_body(id),
            program.get_analyzer(id),
            type_store,
            &mut value_store.merge_pair_map,
        )?;

        {
            let mut data_store = DataStore {
                context: program,
                interner,
                analyzer: program.get_analyzer(id),
                type_store,
                source_store,
            };

            let _span = trace_span!("compile_block").entered();
            self.compile_block(
                &mut data_store,
                &mut value_store,
                id,
                program.trir().get_item_body(id),
                function,
            )?;

            self.builder
                .position_at_end(value_store.alloca_prelude_block);
            self.builder.build_unconditional_branch(entry_block)?;
        }

        {
            let _span = trace_span!("verifying").entered();
            if !function.verify(true) {
                eprintln!();
                function.print_to_stderr();
            }
        }

        Ok(())
    }

    fn build(
        &mut self,
        program: &MflContext,
        source_store: &SourceStore,
        interner: &mut Interner,
        type_store: &mut TypeStore,
    ) -> InkwellResult {
        let _span = debug_span!(stringify!(CodeGen::build)).entered();
        while let Some(item_id) = self.function_queue.pop() {
            let function = self.item_function_map[&item_id];
            self.compile_procedure(
                program,
                item_id,
                function,
                source_store,
                interner,
                type_store,
            )?;
        }

        self.pass_manager.run_on(&self.module);

        Ok(())
    }

    fn build_entry(
        &mut self,
        program: &MflContext,
        interner: &mut Interner,
        type_store: &mut TypeStore,
        entry_id: ItemId,
    ) -> InkwellResult {
        let u64_type_id = type_store.get_builtin(BuiltinTypes::U64).id;
        let argc_type = self.get_type(type_store, u64_type_id);

        let u8_ptr_type_id = type_store.get_builtin_ptr(BuiltinTypes::U8).id;
        let argv_type_id = type_store.get_pointer(interner, u8_ptr_type_id).id;
        let argv_type = self.get_type(type_store, argv_type_id);

        let function_type = self
            .ctx
            .void_type()
            .fn_type(&[argc_type.into(), argv_type.into()], false);

        let entry_func = self
            .module
            .add_function("entry", function_type, Some(Linkage::External));
        entry_func.add_attribute(AttributeLoc::Function, self.attrib_align_stack);

        let block = self.ctx.append_basic_block(entry_func, "entry");
        self.builder.position_at_end(block);

        let entry_sig = program.trir().get_item_signature(entry_id);
        let args = if entry_sig.entry.is_empty() {
            Vec::new()
        } else {
            entry_func.get_param_iter().map(Into::into).collect()
        };

        let user_entry = self.item_function_map[&entry_id];
        self.builder
            .build_call(user_entry, &args, "call_user_entry")?;

        self.builder.build_return(None)?;

        Ok(())
    }

    fn module(&self) -> &Module<'ctx> {
        &self.module
    }
}

pub(crate) fn compile(
    program: &MflContext,
    stores: &mut Stores,
    top_level_items: &[ItemId],
    args: &Args,
) -> Result<Vec<PathBuf>> {
    let _span = debug_span!(stringify!(backend_llvm::compile)).entered();

    if !args.obj_dir.exists() {
        std::fs::create_dir_all(&args.obj_dir)
            .with_context(|| eyre!("failed to create directory `{:?}`", args.obj_dir))?;
    } else if !args.obj_dir.is_dir() {
        return Err(eyre!("obj path is not a directory"));
    }

    let mut output_obj = args.obj_dir.clone();
    output_obj.push(args.file.file_stem().unwrap());
    output_obj.set_extension("o");
    let mut bootstrap_obj = args.obj_dir.clone();
    bootstrap_obj.push("bootstrap.o");
    let mut syscalls_obj = args.obj_dir.clone();
    syscalls_obj.push("syscalls.o");

    let mut output_llir = args.obj_dir.clone();
    output_llir.push(args.file.file_stem().unwrap());
    output_llir.set_extension("llir");

    let mut output_asm = args.obj_dir.clone();
    output_asm.push(args.file.file_stem().unwrap());
    output_asm.set_extension("s");

    debug!("Compiling with LLVM codegen to {}", output_obj.display());

    trace!("Creating LLVM machinary");
    let opt_level = if !args.optimize {
        OptimizationLevel::None
    } else {
        OptimizationLevel::Aggressive
    };

    Target::initialize_x86(&InitializationConfig::default());
    let target_triple = TargetMachine::get_default_triple();
    trace!("    Triple: {target_triple}");
    let target =
        Target::from_triple(&target_triple).map_err(|e| eyre!("Error creating target: `{e}`"))?;
    let target_machine = target
        .create_target_machine(
            &target_triple,
            "x86-64",
            "",
            opt_level,
            RelocMode::PIC,
            CodeModel::Default,
        )
        .ok_or_else(|| eyre!("Error creating target machine"))?;

    let context = InkwellContext::create();
    let mut codegen = CodeGen::from_context(&context, opt_level);

    top_level_items
        .iter()
        .for_each(|&id| codegen.enqueue_function(id));
    codegen.build_function_prototypes(program, &mut stores.strings, &mut stores.types);
    if !args.is_library {
        codegen.build_entry(
            program,
            &mut stores.strings,
            &mut stores.types,
            top_level_items[0],
        )?;
    } else {
        // Top level items clearly need to be external symbols if we're a library.
        // Pretty naff library if they're not.
        top_level_items
            .iter()
            .for_each(|id| codegen.item_function_map[id].set_linkage(Linkage::External));
    }
    codegen.build(
        program,
        &stores.source,
        &mut stores.strings,
        &mut stores.types,
    )?;

    {
        let _span = trace_span!("Writing object file").entered();
        target_machine
            .write_to_file(codegen.module(), FileType::Object, &output_obj)
            .map_err(|e| eyre!("Error writing object: {e}"))?;
    }

    if args.emit_asm {
        let _span = trace_span!("Writing assembly file").entered();
        target_machine
            .write_to_file(codegen.module(), FileType::Assembly, &output_asm)
            .map_err(|e| eyre!("Error writing object: {e}"))?;
    }

    if args.emit_llir {
        let _span = trace_span!("Writing LLIR file").entered();
        codegen
            .module()
            .print_to_file(&output_llir)
            .map_err(|e| eyre!("Error writing object: {e}"))?;
    }

    if !args.is_library {
        let _span = trace_span!("Writing bootstrap").entered();
        std::fs::write(&bootstrap_obj, BOOTSTRAP_OBJ)
            .map_err(|e| eyre!("Error writing bootstrap: {e}"))?;
    }

    {
        let _span = trace_span!("Writing syscalls").entered();
        std::fs::write(&syscalls_obj, SYSCALLS)
            .map_err(|e| eyre!("Error writing syscall wrappers: {e}"))?;
    }

    Ok(vec![bootstrap_obj, output_obj, syscalls_obj])
}
