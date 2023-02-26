use std::{
    path::{Path, PathBuf},
    process::Command,
};

use color_eyre::{
    eyre::{eyre, Context as _},
    Result,
};
use hashbrown::{HashMap, HashSet};
use inkwell::{
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    passes::{PassManager, PassManagerBuilder},
    targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine},
    types::{BasicMetadataTypeEnum, BasicType, IntType},
    values::{BasicValueEnum, FunctionValue, IntMathValue, IntValue, PointerValue},
    AddressSpace, IntPredicate, OptimizationLevel,
};
use intcast::IntCast;
use lasso::Spur;
use tracing::{debug, debug_span, trace, trace_span};

use crate::{
    interners::Interners,
    opcode::{IntKind, Op, OpCode},
    program::{
        static_analysis::{Analyzer, ConstVal, PtrId, ValueId},
        type_store::{IntWidth, Signedness, TypeKind, TypeStore},
        ItemId, ItemKind, Program,
    },
};

mod arithmetic;
mod control;
mod memory;
mod stack;

type BuilderArithFunc<'ctx, T> = fn(&'_ Builder<'ctx>, T, T, &'_ str) -> T;

impl IntWidth {
    fn get_int_type(self, ctx: &Context) -> IntType<'_> {
        match self {
            IntWidth::I8 => ctx.i8_type(),
            IntWidth::I16 => ctx.i16_type(),
            IntWidth::I32 => ctx.i32_type(),
            IntWidth::I64 => ctx.i64_type(),
        }
    }
}

impl OpCode {
    fn get_arith_fn<'ctx, T: IntMathValue<'ctx>>(
        &self,
    ) -> (BuilderArithFunc<'ctx, T>, &'static str) {
        match self {
            OpCode::Add => (Builder::build_int_add, "add"),
            OpCode::BitAnd => (Builder::build_and, "and"),
            OpCode::BitOr => (Builder::build_or, "or"),
            OpCode::Multiply => (Builder::build_int_mul, "mul"),
            OpCode::Subtract => (Builder::build_int_sub, "sub"),
            _ => panic!("ICE: Called get_arid_fn on non-arith opcode"),
        }
    }

    fn get_predicate(&self, signed: Signedness) -> (IntPredicate, &'static str) {
        match (self, signed) {
            (OpCode::Equal, _) => (IntPredicate::EQ, "equal"),
            (OpCode::Less, Signedness::Unsigned) => (IntPredicate::ULT, "less"),
            (OpCode::LessEqual, Signedness::Unsigned) => (IntPredicate::ULE, "less-equal"),
            (OpCode::Greater, Signedness::Unsigned) => (IntPredicate::UGT, "greater"),
            (OpCode::GreaterEqual, Signedness::Unsigned) => (IntPredicate::UGE, "greater-equal"),
            (OpCode::Less, Signedness::Signed) => (IntPredicate::SLT, "less"),
            (OpCode::LessEqual, Signedness::Signed) => (IntPredicate::SLE, "less-equal"),
            (OpCode::Greater, Signedness::Signed) => (IntPredicate::SGT, "greater"),
            (OpCode::GreaterEqual, Signedness::Signed) => (IntPredicate::SGE, "greater-equal"),
            (OpCode::NotEq, _) => (IntPredicate::NE, "not-equal"),
            _ => panic!("ICE: Called get_predicate on non-predicate opcode"),
        }
    }
}

fn is_fully_const(id: ValueId, analyzer: &Analyzer) -> bool {
    let Some([const_val]) = analyzer.value_consts([id]) else {
            return false;
        };

    matches!(
        const_val,
        ConstVal::Int(_)
            | ConstVal::Bool(_)
            | ConstVal::Ptr {
                offset: Some(_),
                ..
            }
    )
}

#[derive(Debug, Default)]
struct ValueStore<'ctx> {
    value_map: HashMap<ValueId, BasicValueEnum<'ctx>>,
    variable_map: HashMap<ItemId, PointerValue<'ctx>>,
    string_map: HashMap<Spur, PointerValue<'ctx>>,
    merge_pair_map: HashMap<ValueId, PointerValue<'ctx>>,
}

impl<'ctx> ValueStore<'ctx> {
    fn get_string_literal(
        &mut self,
        cg: &CodeGen<'ctx>,
        interner: &mut Interners,
        id: Spur,
    ) -> PointerValue<'ctx> {
        match self.string_map.get(&id) {
            Some(&ptr) => ptr,
            None => {
                let string = interner.resolve_literal(id);
                let global = cg.builder.build_global_string_ptr(string, "global_string");

                let ptr = global
                    .as_pointer_value()
                    .const_cast(cg.ctx.i8_type().ptr_type(AddressSpace::default()));
                self.string_map.insert(id, ptr);
                ptr
            }
        }
    }

    fn load_const_value(
        &mut self,
        cg: &CodeGen<'ctx>,
        id: ValueId,
        const_val: ConstVal,
        analyzer: &Analyzer,
        type_store: &TypeStore,
        interner: &mut Interners,
    ) -> BasicValueEnum<'ctx> {
        trace!("Fetching const {id:?}");
        match const_val {
            ConstVal::Int(val) => {
                let [type_id] = analyzer.value_types([id]).unwrap();
                let type_info = type_store.get_type_info(type_id);
                let TypeKind::Integer{ width: target_width, .. } = type_info.kind else {
                    panic!("ICE: ConstInt for non-int type");
                };
                let target_type = target_width.get_int_type(cg.ctx);
                match val {
                    IntKind::Signed(val) => target_type
                        .const_int(val as u64, false)
                        .const_cast(target_type, true)
                        .into(),
                    IntKind::Unsigned(val) => target_type
                        .const_int(val, false)
                        .const_cast(target_type, false)
                        .into(),
                }
            }
            ConstVal::Bool(val) => cg.ctx.bool_type().const_int(val as u64, false).into(),
            ConstVal::Ptr { id, offset, .. } => {
                let ptr = match id {
                    PtrId::Mem(id) => self.variable_map[&id],
                    PtrId::Str(id) => self.get_string_literal(cg, interner, id),
                };

                if let Some(offset) = offset {
                    let offset = cg.ctx.i64_type().const_int(offset, false);
                    unsafe { cg.builder.build_gep(ptr, &[offset], "ptr offset") }.into()
                } else {
                    ptr.into()
                }
            }
        }
    }

    fn load_value(
        &mut self,
        cg: &CodeGen<'ctx>,
        id: ValueId,
        analyzer: &Analyzer,
        type_store: &TypeStore,
        interner: &mut Interners,
    ) -> BasicValueEnum<'ctx> {
        match analyzer.value_consts([id]) {
            Some([const_val]) => {
                self.load_const_value(cg, id, const_val, analyzer, type_store, interner)
            }
            _ => {
                if let Some(&ptr) = self.merge_pair_map.get(&id) {
                    trace!(
                        name = ptr.get_name().to_str().unwrap(),
                        "Fetching variable {id:?}"
                    );
                    cg.builder.build_load(ptr, "load_var")
                } else {
                    trace!("Fetching live value {id:?}");
                    self.value_map[&id]
                }
            }
        }
    }

    fn store_value(&mut self, cg: &CodeGen<'ctx>, id: ValueId, value: BasicValueEnum<'ctx>) {
        if let Some(&ptr) = self.merge_pair_map.get(&id) {
            trace!(
                name = ptr.get_name().to_str().unwrap(),
                "Storing variable {id:?}",
            );
            cg.builder.build_store(ptr, value);
        } else {
            trace!("Stored live value {id:?}");
            self.value_map.insert(id, value);
        }
    }
}

struct CodeGen<'ctx> {
    ctx: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    pass_manager: PassManager<Module<'ctx>>,

    function_queue: Vec<ItemId>,
    processed_functions: HashSet<ItemId>,
    item_function_map: HashMap<ItemId, FunctionValue<'ctx>>,
    syscall_wrappers: Vec<FunctionValue<'ctx>>,
}

impl<'ctx> CodeGen<'ctx> {
    fn from_context(ctx: &'ctx Context, opt_level: OptimizationLevel) -> Self {
        let module = ctx.create_module("porth_module");
        let builder = ctx.create_builder();

        let pm_builder = PassManagerBuilder::create();
        pm_builder.set_optimization_level(opt_level);
        pm_builder.set_inliner_with_threshold(23);
        let pass_manager = PassManager::create(());
        pm_builder.populate_module_pass_manager(&pass_manager);

        Self {
            ctx,
            module,
            builder,
            pass_manager,
            function_queue: Vec::new(),
            processed_functions: HashSet::new(),
            item_function_map: HashMap::new(),
            syscall_wrappers: Vec::new(),
        }
    }

    fn enqueue_function(&mut self, item: ItemId) {
        if !self.processed_functions.contains(&item) {
            trace!(name = ?item, "Enqueing function");
            self.function_queue.push(item);
            self.processed_functions.insert(item);
        }
    }

    fn build_function_prototypes(&mut self, program: &Program, interner: &mut Interners) {
        let _span = debug_span!(stringify!(CodeGen::build_function_prototypes)).entered();

        let proto_span = debug_span!("building prototypes").entered();
        for (id, item) in program.get_all_items() {
            if item.kind() != ItemKind::Function {
                continue;
            }
            let item_sig = program.get_item_signature_resolved(id);

            let name = interner.get_symbol_name(program, id);
            trace!(name, "Building prototype");

            let entry_stack: Vec<BasicMetadataTypeEnum> = item_sig
                .entry_stack()
                .iter()
                .map(|t| {
                    let type_info = program.get_type_store().get_type_info(*t);
                    match type_info.kind {
                        TypeKind::Integer { width, .. } => width.get_int_type(self.ctx).into(),
                        TypeKind::Pointer => {
                            self.ctx.i8_type().ptr_type(AddressSpace::default()).into()
                        }
                        TypeKind::Bool => self.ctx.bool_type().into(),
                    }
                })
                .collect();

            let function_type = if item_sig.exit_stack().is_empty() {
                self.ctx.void_type().fn_type(&entry_stack, false)
            } else {
                let exit_stack: Vec<_> = item_sig
                    .exit_stack()
                    .iter()
                    .map(|t| {
                        let type_info = program.get_type_store().get_type_info(*t);
                        match type_info.kind {
                            TypeKind::Integer { width, .. } => {
                                width.get_int_type(self.ctx).as_basic_type_enum()
                            }
                            TypeKind::Pointer => self
                                .ctx
                                .i8_type()
                                .ptr_type(AddressSpace::default())
                                .as_basic_type_enum(),
                            TypeKind::Bool => self.ctx.bool_type().as_basic_type_enum(),
                        }
                    })
                    .collect();
                self.ctx
                    .struct_type(&exit_stack, false)
                    .fn_type(entry_stack.as_slice(), false)
            };

            let function = self
                .module
                .add_function(name, function_type, Some(Linkage::Private));
            self.item_function_map.insert(id, function);
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
        to_signedness: Signedness,
    ) -> IntValue<'ctx> {
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
                        .build_int_s_extend_or_bit_cast(v, target_type, name)
                }
                Signedness::Unsigned => {
                    self.builder
                        .build_int_z_extend_or_bit_cast(v, target_type, name)
                }
            },
            Ordering::Equal => v,
            Ordering::Greater => self
                .builder
                .build_int_truncate_or_bit_cast(v, target_type, name),
        };

        self.builder.build_int_cast_sign_flag(
            widened,
            target_type,
            to_signedness == Signedness::Signed,
            name,
        )
    }

    fn compile_block(
        &mut self,
        program: &Program,
        value_store: &mut ValueStore<'ctx>,
        id: ItemId,
        block: &[Op],
        function: FunctionValue<'ctx>,
        interner: &mut Interners,
    ) {
        let analyzer = program.get_analyzer(id);
        let type_store = program.get_type_store();

        for op in block {
            match op.code {
                OpCode::If(_) => trace!(?op.id, "If"),
                OpCode::While(_) => trace!(?op.id, "While"),
                OpCode::Swap { count, .. } => trace!(?op.id, count, "Swap"),
                OpCode::Dup { count, .. } => trace!(?op.id, count, "Dup" ),
                OpCode::Drop { count, .. } => trace!(?op.id, count, "Drop"),
                OpCode::Over { depth, .. } => trace!(?op.id, depth, "Over"),
                OpCode::Memory {
                    item_id, global, ..
                } => trace!(?op.id, ?item_id, global, "Memory"),
                OpCode::Rot {
                    item_count,
                    direction,
                    shift_count,
                    ..
                } => trace!(item_count, ?direction, shift_count, "Rot"),
                _ => trace!(?op.id, "{:?}", op.code),
            }

            // These do nothing in codegen
            if let OpCode::Swap { .. } | OpCode::Rot { .. } = &op.code {
                continue;
            }

            let op_io = analyzer.get_op_io(op.id);

            if !op_io.outputs().is_empty()
                && op_io
                    .outputs()
                    .iter()
                    .all(|id| is_fully_const(*id, analyzer))
            {
                op_io.outputs().iter().for_each(|id| trace!("{id:?}"));
                trace!("Op is fully const");
                continue;
            }

            match &op.code {
                OpCode::Add | OpCode::Subtract => {
                    self.build_add_sub(interner, analyzer, value_store, type_store, op)
                }
                OpCode::Multiply | OpCode::BitAnd | OpCode::BitOr => {
                    self.build_multiply_and_or(interner, analyzer, value_store, type_store, op)
                }
                OpCode::DivMod => {
                    self.build_divmod(interner, analyzer, value_store, type_store, op)
                }

                OpCode::Equal
                | OpCode::NotEq
                | OpCode::Greater
                | OpCode::GreaterEqual
                | OpCode::Less
                | OpCode::LessEqual => {
                    self.build_compare(interner, analyzer, value_store, type_store, op)
                }

                OpCode::ShiftLeft | OpCode::ShiftRight => {
                    self.build_shift_left_right(interner, analyzer, value_store, type_store, op)
                }
                OpCode::BitNot => {
                    self.build_bit_not(interner, analyzer, value_store, type_store, op)
                }

                OpCode::ArgC => todo!(),
                OpCode::ArgV => todo!(),
                OpCode::CallFunction {
                    item_id: callee_id, ..
                } => self.build_function_call(
                    program,
                    interner,
                    analyzer,
                    value_store,
                    type_store,
                    op,
                    *callee_id,
                ),

                OpCode::ResolvedCast { id: type_id } => self.build_cast(
                    program,
                    interner,
                    analyzer,
                    value_store,
                    type_store,
                    op,
                    *type_id,
                ),

                OpCode::Dup { .. } | OpCode::Over { .. } => {
                    self.build_dup_over(program, interner, analyzer, value_store, op)
                }

                OpCode::Epilogue | OpCode::Return => {
                    self.build_epilogue_return(program, interner, analyzer, value_store, op)
                }

                OpCode::If(if_op) => self.build_if(
                    program,
                    interner,
                    analyzer,
                    value_store,
                    function,
                    id,
                    op,
                    if_op,
                ),
                OpCode::While(while_op) => self.build_while(
                    program,
                    interner,
                    analyzer,
                    value_store,
                    function,
                    id,
                    op,
                    while_op,
                ),

                OpCode::ResolvedLoad { id: type_id } => self.build_load(
                    program,
                    interner,
                    analyzer,
                    value_store,
                    type_store,
                    op,
                    *type_id,
                ),
                OpCode::ResolvedStore { id: type_id } => self.build_store(
                    program,
                    interner,
                    analyzer,
                    value_store,
                    type_store,
                    op,
                    *type_id,
                ),
                OpCode::Memory {
                    item_id,
                    global: false,
                    ..
                } => self.build_memory_local(analyzer, value_store, op, *item_id),
                OpCode::Memory {
                    module_id,
                    item_id,
                    offset,
                    global: true,
                } => todo!(),
                OpCode::Prologue => self.build_prologue(analyzer, value_store, op, function),

                OpCode::PushBool(val) => self.build_push_bool(analyzer, value_store, op, *val),
                OpCode::PushInt { width, value } => {
                    self.build_push_int(analyzer, value_store, op, *width, *value)
                }
                OpCode::PushStr { id, is_c_str } => {
                    todo!()
                }

                OpCode::SysCall { arg_count, .. } => self.build_syscall(
                    program,
                    interner,
                    analyzer,
                    value_store,
                    type_store,
                    op,
                    *arg_count,
                ),

                // These are no-ops as far as codegen is concerned.
                OpCode::Drop { .. } | OpCode::Rot { .. } | OpCode::Swap { .. } => continue,

                OpCode::ResolvedIdent { .. } => {
                    panic!("ICE: Encountered resolved ident during codegen")
                }
                OpCode::UnresolvedCast { .. } => {
                    panic!("ICE: Encountered unresolved cast during codegen")
                }
                OpCode::UnresolvedLoad { .. } => {
                    panic!("ICE: Encountered unresolved load during codegen")
                }
                OpCode::UnresolvedStore { .. } => {
                    panic!("ICE: Encountered unresolved store during codegen")
                }
                OpCode::UnresolvedIdent { .. } => {
                    panic!("ICE: Encountered unresolved ident during codegen")
                }
            }
        }
    }

    fn build_merge_variables(
        &mut self,
        block: &[Op],
        analyzer: &Analyzer,
        type_store: &TypeStore,
        merge_pair_map: &mut HashMap<ValueId, PointerValue<'ctx>>,
    ) {
        fn make_variable<'ctx>(
            value_id: ValueId,
            cg: &CodeGen<'ctx>,
            analyzer: &Analyzer,
            type_store: &TypeStore,
            merge_pair_map: &mut HashMap<ValueId, PointerValue<'ctx>>,
        ) {
            if merge_pair_map.contains_key(&value_id) {
                trace!("        Variable already exists for `{value_id:?}`");
                return;
            }
            let type_id = analyzer.value_types([value_id]).unwrap()[0];
            let type_info = type_store.get_type_info(type_id);
            let typ = match type_info.kind {
                TypeKind::Integer { width, .. } => width.get_int_type(cg.ctx).as_basic_type_enum(),
                TypeKind::Bool => cg.ctx.bool_type().as_basic_type_enum(),
                TypeKind::Pointer => cg
                    .ctx
                    .i8_type()
                    .ptr_type(AddressSpace::default())
                    .as_basic_type_enum(),
            };
            let name = format!("{value_id:?}_var");
            trace!("        Defining variable `{name}`");

            let var = cg.builder.build_alloca(typ, &name);
            merge_pair_map.insert(value_id, var);
        }

        for op in block {
            match &op.code {
                OpCode::If(if_op) => {
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
                        );
                    }

                    self.build_merge_variables(
                        &if_op.then_block,
                        analyzer,
                        type_store,
                        merge_pair_map,
                    );
                    self.build_merge_variables(
                        &if_op.else_block,
                        analyzer,
                        type_store,
                        merge_pair_map,
                    );
                }
                OpCode::While(while_op) => {
                    let Some(op_merges) = analyzer.get_while_merges(op.id) else {
                        panic!("ICE: While block doesn't have merge info");
                    };
                    for merge in &op_merges.condition {
                        make_variable(merge.pre_value, self, analyzer, type_store, merge_pair_map);
                    }

                    for merge in &op_merges.body {
                        make_variable(merge.pre_value, self, analyzer, type_store, merge_pair_map);
                    }

                    self.build_merge_variables(
                        &while_op.condition,
                        analyzer,
                        type_store,
                        merge_pair_map,
                    );
                    self.build_merge_variables(
                        &while_op.body_block,
                        analyzer,
                        type_store,
                        merge_pair_map,
                    );
                }

                _ => continue,
            };
        }
    }

    fn compile_procedure(
        &mut self,
        program: &Program,
        id: ItemId,
        function: FunctionValue<'ctx>,
        interner: &mut Interners,
    ) {
        let mut value_store = ValueStore::default();
        let name = interner.get_symbol_name(program, id);
        let _span = debug_span!(stringify!(CodeGen::compile_procedure), name).entered();

        let entry_block = self.ctx.append_basic_block(function, "entry");
        self.builder.position_at_end(entry_block);

        trace!("Defining local allocations");
        let function_data = program.get_function_data(id);
        for (&item_id, alloc_size) in &function_data.alloc_sizes {
            let variable = self.builder.build_alloca(
                self.ctx.i8_type().array_type(alloc_size.to_u32().unwrap()),
                interner.get_symbol_name(program, item_id),
            );
            let variable = self.builder.build_pointer_cast(
                variable,
                self.ctx.i8_type().ptr_type(AddressSpace::default()),
                "ptr_cast",
            );

            value_store.variable_map.insert(item_id, variable);
        }

        trace!("Defining merge variables");
        self.build_merge_variables(
            program.get_item_body(id),
            program.get_analyzer(id),
            program.get_type_store(),
            &mut value_store.merge_pair_map,
        );

        {
            let _span = trace_span!("compile_block").entered();
            self.compile_block(
                program,
                &mut value_store,
                id,
                program.get_item_body(id),
                function,
                interner,
            );
        }

        {
            let _span = trace_span!("verifying").entered();
            if !function.verify(true) {
                eprintln!();
                function.print_to_stderr();
            }
        }
    }

    fn build(&mut self, program: &Program, interner: &mut Interners) {
        let _span = debug_span!(stringify!(CodeGen::build)).entered();
        while let Some(item_id) = self.function_queue.pop() {
            let function = self.item_function_map[&item_id];
            self.compile_procedure(program, item_id, function, interner);
        }

        self.pass_manager.run_on(&self.module);
    }

    fn build_entry(&mut self, entry_id: ItemId) {
        let function_type = self.ctx.void_type().fn_type(&[], false);
        let entry_func = self
            .module
            .add_function("entry", function_type, Some(Linkage::External));
        let block = self.ctx.append_basic_block(entry_func, "entry");
        self.builder.position_at_end(block);
        let user_entry = self.item_function_map[&entry_id];
        self.builder.build_call(user_entry, &[], "call_user_entry");
        self.builder.build_return(None);
    }

    fn module(&self) -> &Module<'ctx> {
        &self.module
    }
}

pub(crate) fn compile(
    program: &Program,
    entry_function: ItemId,
    interner: &mut Interners,
    file: &str,
    opt_level: u8,
) -> Result<Vec<PathBuf>> {
    let _span = debug_span!(stringify!(backend_llvm::compile)).entered();

    let mut output_obj = Path::new(&file).to_path_buf();
    output_obj.set_extension("o");
    let mut bootstrap_obj = Path::new(&file).to_path_buf();
    bootstrap_obj.set_file_name("bootstrap.o");

    let mut output_asm = Path::new(&file).to_path_buf();
    output_asm.set_extension("s");

    debug!("Compiling with LLVM codegen to {}", output_obj.display());

    trace!("Creating LLVM machinary");
    let opt_level = match opt_level {
        0 => OptimizationLevel::None,
        1 => OptimizationLevel::Less,
        2 => OptimizationLevel::Default,
        3.. => OptimizationLevel::Aggressive,
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
            RelocMode::Default,
            CodeModel::Default,
        )
        .ok_or_else(|| eyre!("Error creating target machine"))?;

    let context = Context::create();
    let mut codegen = CodeGen::from_context(&context, opt_level);

    codegen.enqueue_function(entry_function);
    codegen.build_function_prototypes(program, interner);
    codegen.build_entry(entry_function);
    codegen.build(program, interner);

    {
        let _span = trace_span!("Writing object file").entered();
        target_machine
            .write_to_file(codegen.module(), FileType::Object, &output_obj)
            .map_err(|e| eyre!("Error writing object: {e}"))?;
    }

    {
        let _span = trace_span!("Writing assembly file").entered();
        target_machine
            .write_to_file(codegen.module(), FileType::Assembly, &output_asm)
            .map_err(|e| eyre!("Error writing object: {e}"))?;
    }

    let nasm = {
        let _span = trace_span!("Assembling bootstrap").entered();
        trace!("Assembling... bootstrap.s to {}", bootstrap_obj.display());
        Command::new("nasm")
            .arg("-felf64")
            .arg("./std/bootstrap.s")
            .arg("-o")
            .arg(&bootstrap_obj)
            .status()
            .with_context(|| eyre!("Failed to execute nasm"))?
    };

    if !nasm.success() {
        std::process::exit(-2);
    }

    Ok(vec![bootstrap_obj, output_obj])
}
