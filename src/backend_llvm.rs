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
    values::{
        BasicMetadataValueEnum, BasicValueEnum, FunctionValue, IntMathValue, IntValue, PointerValue,
    },
    AddressSpace, IntPredicate, OptimizationLevel,
};
use intcast::IntCast;
use lasso::Spur;
use tracing::{debug, debug_span, trace, trace_span};

use crate::{
    interners::Interners,
    n_ops::SliceNOps,
    opcode::{ConditionalBlock, Op, OpCode},
    program::{
        static_analysis::{Analyzer, ConstVal, IntWidth, PorthTypeKind, PtrId, ValueId},
        Procedure, ProcedureId, ProcedureKind, Program,
    },
    source_file::SourceStorage,
};

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

    fn get_predicate(&self) -> (IntPredicate, &'static str) {
        match self {
            OpCode::Equal => (IntPredicate::EQ, "equal"),
            OpCode::Less => (IntPredicate::ULT, "less"),
            OpCode::LessEqual => (IntPredicate::ULE, "less-equal"),
            OpCode::Greater => (IntPredicate::UGT, "greater"),
            OpCode::GreaterEqual => (IntPredicate::UGE, "greater-equal"),
            OpCode::NotEq => (IntPredicate::NE, "not-equal"),
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
    variable_map: HashMap<ProcedureId, PointerValue<'ctx>>,
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
        interner: &mut Interners,
    ) -> BasicValueEnum<'ctx> {
        trace!("Fetching const {id:?}");
        match const_val {
            ConstVal::Int(val) => {
                let Some([PorthTypeKind::Int(target_width)]) = analyzer.value_types([id]) else {
                            panic!("ICE: ConstInt for non-int type");
                        };
                let target_type = target_width.get_int_type(cg.ctx);
                target_type
                    .const_int(val, false)
                    .const_cast(target_type, false)
                    .into()
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
        interner: &mut Interners,
    ) -> BasicValueEnum<'ctx> {
        match analyzer.value_consts([id]) {
            Some([const_val]) => self.load_const_value(cg, id, const_val, analyzer, interner),
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

    function_queue: Vec<ProcedureId>,
    processed_functions: HashSet<ProcedureId>,
    proc_function_map: HashMap<ProcedureId, FunctionValue<'ctx>>,
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
            proc_function_map: HashMap::new(),
            syscall_wrappers: Vec::new(),
        }
    }

    fn enqueue_function(&mut self, proc: ProcedureId) {
        if !self.processed_functions.contains(&proc) {
            trace!(name = ?proc, "Enqueing function");
            self.function_queue.push(proc);
            self.processed_functions.insert(proc);
        }
    }

    fn build_function_prototypes(&mut self, program: &Program, interner: &mut Interners) {
        let _span = debug_span!(stringify!(CodeGen::build_function_prototypes)).entered();

        let proto_span = debug_span!("building prototypes").entered();
        for (id, proc) in program.get_all_procedures() {
            let ProcedureKind::Function(_) = proc.kind() else { continue };

            let name = interner.get_symbol_name(program, id);
            trace!(name, "Building prototype");

            let entry_stack: Vec<BasicMetadataTypeEnum> = proc
                .entry_stack()
                .iter()
                .map(|t| match t.kind {
                    PorthTypeKind::Int(width) => width.get_int_type(self.ctx).into(),
                    PorthTypeKind::Ptr => {
                        self.ctx.i8_type().ptr_type(AddressSpace::default()).into()
                    }
                    PorthTypeKind::Bool => self.ctx.bool_type().into(),
                })
                .collect();

            let function_type = if proc.exit_stack().is_empty() {
                self.ctx.void_type().fn_type(&entry_stack, false)
            } else {
                let exit_stack: Vec<_> = proc
                    .exit_stack()
                    .iter()
                    .map(|t| match t.kind {
                        PorthTypeKind::Int(width) => {
                            width.get_int_type(self.ctx).as_basic_type_enum()
                        }
                        PorthTypeKind::Ptr => self
                            .ctx
                            .i8_type()
                            .ptr_type(AddressSpace::default())
                            .as_basic_type_enum(),
                        PorthTypeKind::Bool => self.ctx.bool_type().as_basic_type_enum(),
                    })
                    .collect();
                self.ctx
                    .struct_type(&exit_stack, false)
                    .fn_type(entry_stack.as_slice(), false)
            };

            let function = self
                .module
                .add_function(name, function_type, Some(Linkage::Private));
            self.proc_function_map.insert(id, function);
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

    fn resize_int(&mut self, v: IntValue<'ctx>, target_type: IntType<'ctx>) -> IntValue<'ctx> {
        use std::cmp::Ordering;
        match v
            .get_type()
            .get_bit_width()
            .cmp(&target_type.get_bit_width())
        {
            Ordering::Less => {
                let name = v.get_name().to_str().unwrap(); // Our name came from us, so should be valid.
                self.builder
                    .build_int_z_extend_or_bit_cast(v, target_type, name)
            }
            Ordering::Equal => v,
            Ordering::Greater => {
                let name = v.get_name().to_str().unwrap(); // Our name came from us, so should be valid.
                self.builder
                    .build_int_truncate_or_bit_cast(v, target_type, name)
            }
        }
    }

    fn compile_block(
        &mut self,
        program: &Program,
        value_store: &mut ValueStore<'ctx>,
        id: ProcedureId,
        procedure: &Procedure,
        block: &[Op],
        function: FunctionValue<'ctx>,
        source_storage: &SourceStorage,
        interner: &mut Interners,
    ) {
        let analyzer = procedure.analyzer();

        for op in block {
            match op.code {
                OpCode::If { .. } => trace!(?op.id, "If"),
                OpCode::While { .. } => trace!(?op.id, "While"),
                OpCode::Swap { count, .. } => trace!(?op.id, count, "Swap"),
                OpCode::Dup { count, .. } => trace!(?op.id, count, "Dup" ),
                OpCode::Drop { count, .. } => trace!(?op.id, count, "Drop"),
                OpCode::Over { depth, .. } => trace!(?op.id, depth, "Over"),
                OpCode::Cast { kind, .. } => trace!(?op.id, ?kind, "Cast"),
                OpCode::Memory {
                    proc_id, global, ..
                } => trace!(?op.id, ?proc_id, global, "Memory"),
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
                    let [a, b] = *op_io.inputs().as_arr();
                    let [a_type, b_type] = analyzer.value_types([a, b]).unwrap();

                    let res: BasicValueEnum = match [a_type, b_type] {
                        [PorthTypeKind::Int(_), PorthTypeKind::Int(_)] => {
                            let [PorthTypeKind::Int(width)] = analyzer.value_types([op_io.outputs()[0]]).unwrap() else {
                                panic!("ICE: Non-int output of int-int arithmetic");
                            };

                            let a_val = value_store
                                .load_value(self, a, analyzer, interner)
                                .into_int_value();
                            let b_val = value_store
                                .load_value(self, b, analyzer, interner)
                                .into_int_value();

                            let target_type = width.get_int_type(self.ctx);
                            let a_val = self.resize_int(a_val, target_type);
                            let b_val = self.resize_int(b_val, target_type);

                            let (func, name) = op.code.get_arith_fn();
                            func(&self.builder, a_val, b_val, name).into()
                        }
                        [PorthTypeKind::Int(_), PorthTypeKind::Ptr] => {
                            assert!(matches!(op.code, OpCode::Add));
                            let offset = value_store
                                .load_value(self, a, analyzer, interner)
                                .into_int_value();

                            let offset = self.resize_int(offset, self.ctx.i64_type());
                            let ptr = value_store
                                .load_value(self, b, analyzer, interner)
                                .into_pointer_value();

                            unsafe { self.builder.build_gep(ptr, &[offset], "ptr_offset") }.into()
                        }
                        [PorthTypeKind::Ptr, PorthTypeKind::Int(_)] => {
                            let offset = value_store
                                .load_value(self, b, analyzer, interner)
                                .into_int_value();

                            let offset = self.resize_int(offset, self.ctx.i64_type());
                            let ptr = value_store
                                .load_value(self, a, analyzer, interner)
                                .into_pointer_value();

                            // If we're subtracting, then we need to negate the offset.
                            let offset = if let OpCode::Subtract = &op.code {
                                self.builder.build_int_neg(offset, "neg")
                            } else {
                                offset
                            };

                            unsafe { self.builder.build_gep(ptr, &[offset], "ptr_offset") }.into()
                        }
                        [PorthTypeKind::Ptr, PorthTypeKind::Ptr] => {
                            assert!(matches!(op.code, OpCode::Subtract));

                            let lhs = value_store
                                .load_value(self, a, analyzer, interner)
                                .into_pointer_value();
                            let rhs = value_store
                                .load_value(self, b, analyzer, interner)
                                .into_pointer_value();
                            let diff = self.builder.build_ptr_diff(lhs, rhs, "ptr_diff");
                            self.builder
                                .build_int_cast(diff, self.ctx.i64_type(), "wide_diff")
                                .into()
                        }
                        _ => panic!("ICE: Unexpected types"),
                    };

                    value_store.store_value(self, op_io.outputs()[0], res);
                }
                OpCode::Multiply | OpCode::BitAnd | OpCode::BitOr => {
                    let [a, b] = *op_io.inputs().as_arr();
                    let [output_type] = analyzer.value_types([op_io.outputs()[0]]).unwrap();

                    let a_val = value_store
                        .load_value(self, a, analyzer, interner)
                        .into_int_value();
                    let b_val = value_store
                        .load_value(self, b, analyzer, interner)
                        .into_int_value();

                    let (a_val, b_val) = if let PorthTypeKind::Int(width) = output_type {
                        let target_type = width.get_int_type(self.ctx);
                        let a_val = self.resize_int(a_val, target_type);
                        let b_val = self.resize_int(b_val, target_type);

                        (a_val, b_val)
                    } else {
                        (a_val, b_val)
                    };

                    let (func, name) = op.code.get_arith_fn();
                    let sum = func(&self.builder, a_val, b_val, name);
                    value_store.store_value(self, op_io.outputs()[0], sum.into());
                }
                OpCode::DivMod => {
                    let [a, b] = *op_io.inputs().as_arr();

                    let [PorthTypeKind::Int(output_width)] = analyzer.value_types([op_io.outputs()[0]]).unwrap() else {
                        panic!("ICE: Non-int output of int-int arithmetic");
                    };

                    let a_val = value_store
                        .load_value(self, a, analyzer, interner)
                        .into_int_value();
                    let b_val = value_store
                        .load_value(self, b, analyzer, interner)
                        .into_int_value();

                    let target_type = output_width.get_int_type(self.ctx);
                    let a_val = self.resize_int(a_val, target_type);
                    let b_val = self.resize_int(b_val, target_type);

                    let rem_res = self.builder.build_int_unsigned_rem(a_val, b_val, "rem");
                    let quot_res = self.builder.build_int_unsigned_div(a_val, b_val, "div");

                    let [quot_val, rem_val] = *op_io.outputs().as_arr();
                    value_store.store_value(self, quot_val, quot_res.into());
                    value_store.store_value(self, rem_val, rem_res.into());
                }

                OpCode::Equal
                | OpCode::NotEq
                | OpCode::Greater
                | OpCode::GreaterEqual
                | OpCode::Less
                | OpCode::LessEqual => {
                    let [a, b] = *op_io.inputs().as_arr();
                    let input_types = analyzer.value_types([a, b]).unwrap();

                    let a_val = value_store
                        .load_value(self, a, analyzer, interner)
                        .into_int_value();
                    let b_val = value_store
                        .load_value(self, b, analyzer, interner)
                        .into_int_value();

                    let (a_val, b_val) = match input_types {
                        [PorthTypeKind::Int(a_width), PorthTypeKind::Int(b_width)] => {
                            let target_type = a_width.max(b_width).get_int_type(self.ctx);
                            let a_val = self.resize_int(a_val, target_type);
                            let b_val = self.resize_int(b_val, target_type);
                            (a_val, b_val)
                        }
                        [PorthTypeKind::Ptr, PorthTypeKind::Ptr] => todo!(),
                        [PorthTypeKind::Bool, PorthTypeKind::Bool] => (a_val, b_val),
                        _ => unreachable!(),
                    };

                    let (pred, name) = op.code.get_predicate();
                    let res = self.builder.build_int_compare(pred, a_val, b_val, name);
                    value_store.store_value(self, op_io.outputs()[0], res.into());
                }

                OpCode::ShiftLeft | OpCode::ShiftRight => {
                    let [a, b] = *op_io.inputs().as_arr();

                    let [PorthTypeKind::Int(width)] = analyzer.value_types([op_io.outputs()[0]]).unwrap() else {
                        panic!("ICE: Non-int output of int-int arithmetic");
                    };

                    let a_val = value_store
                        .load_value(self, a, analyzer, interner)
                        .into_int_value();
                    let b_val = value_store
                        .load_value(self, b, analyzer, interner)
                        .into_int_value();

                    let target_type = width.get_int_type(self.ctx);
                    let a_val = self.resize_int(a_val, target_type);
                    let b_val = self.resize_int(b_val, target_type);

                    let res = match &op.code {
                        OpCode::ShiftLeft => self.builder.build_left_shift(a_val, b_val, "shl"),
                        OpCode::ShiftRight => {
                            self.builder.build_right_shift(a_val, b_val, false, "shr")
                        }
                        _ => unreachable!(),
                    };
                    value_store.store_value(self, op_io.outputs()[0], res.into());
                }
                OpCode::BitNot => {
                    let a = op_io.inputs()[0];
                    let a_val = value_store
                        .load_value(self, a, analyzer, interner)
                        .into_int_value();

                    let res = self.builder.build_not(a_val, "not");
                    value_store.store_value(self, op_io.outputs()[0], res.into());
                }

                OpCode::ArgC => todo!(),
                OpCode::ArgV => todo!(),
                OpCode::CallProc {
                    proc_id: callee_id, ..
                } => {
                    let args: Vec<BasicMetadataValueEnum> = op_io
                        .inputs()
                        .iter()
                        .map(|id| value_store.load_value(self, *id, analyzer, interner))
                        .map(Into::into)
                        .collect();

                    let callee_name = interner.get_symbol_name(program, *callee_id);
                    let callee_value = self.proc_function_map[callee_id];

                    let result = self.builder.build_call(
                        callee_value,
                        &args,
                        &format!("calling {callee_name}"),
                    );

                    self.enqueue_function(*callee_id);

                    let Some(BasicValueEnum::StructValue(result)) = result.try_as_basic_value().left()  else {
                            // It was a void-type, so nothing to do.
                            continue;
                        };

                    for (&id, idx) in op_io.outputs().iter().zip(0..) {
                        let value = self
                            .builder
                            .build_extract_value(result, idx, "callproc_ret")
                            .unwrap();

                        value_store.store_value(self, id, value);
                    }
                }
                OpCode::Cast {
                    kind: PorthTypeKind::Int(output_width),
                    ..
                } => {
                    let input_id = op_io.inputs()[0];
                    let input_type = analyzer.value_types([input_id]).unwrap()[0];
                    let input_data = value_store.load_value(self, input_id, analyzer, interner);

                    let output = match input_type {
                        PorthTypeKind::Int(_) => {
                            let val = input_data.into_int_value();
                            let target_type = output_width.get_int_type(self.ctx);
                            self.resize_int(val, target_type)
                        }
                        PorthTypeKind::Bool => {
                            let val = input_data.into_int_value();
                            let target_type = output_width.get_int_type(self.ctx);

                            self.resize_int(val, target_type)
                        }
                        PorthTypeKind::Ptr => self.builder.build_ptr_to_int(
                            input_data.into_pointer_value(),
                            self.ctx.i64_type(),
                            "cast_ptr",
                        ),
                    };

                    value_store.store_value(self, op_io.outputs()[0], output.into());
                }
                OpCode::Cast {
                    kind: PorthTypeKind::Ptr,
                    ..
                } => {
                    let input_id = op_io.inputs()[0];
                    let input_type = analyzer.value_types([input_id]).unwrap()[0];
                    let input_data = value_store.load_value(self, input_id, analyzer, interner);

                    let output = match input_type {
                        PorthTypeKind::Int(_) | PorthTypeKind::Bool => {
                            self.builder.build_int_to_ptr(
                                input_data.into_int_value(),
                                self.ctx.i8_type().ptr_type(AddressSpace::default()),
                                "cast_int",
                            )
                        }
                        PorthTypeKind::Ptr => input_data.into_pointer_value(),
                    };

                    value_store.store_value(self, op_io.outputs()[0], output.into());
                }
                OpCode::Cast {
                    kind: PorthTypeKind::Bool,
                    ..
                } => {
                    unreachable!()
                }

                OpCode::Dup { .. } | OpCode::Over { .. } => {
                    for (&input_id, &output_id) in op_io.inputs().iter().zip(op_io.outputs()) {
                        let value = value_store.load_value(self, input_id, analyzer, interner);
                        value_store.store_value(self, output_id, value);
                    }
                }

                OpCode::Epilogue | OpCode::Return => {
                    if op_io.inputs().is_empty() {
                        self.builder.build_return(None);
                        continue;
                    }

                    let return_values: Vec<BasicValueEnum> = op_io
                        .inputs()
                        .iter()
                        .map(|id| value_store.load_value(self, *id, analyzer, interner))
                        .collect();
                    self.builder.build_aggregate_return(&return_values);
                }

                OpCode::If {
                    condition:
                        ConditionalBlock {
                            condition: condition_block,
                            block: then_block,
                            ..
                        },
                    else_block,
                    ..
                } => {
                    let current_block = self.builder.get_insert_block().unwrap();

                    // Generate new blocks for Then, Else, and Post.
                    let then_basic_block = self
                        .ctx
                        .append_basic_block(function, &format!("{:?}_then", op.id));
                    let else_basic_block = self
                        .ctx
                        .append_basic_block(function, &format!("{:?}_else", op.id));
                    let post_basic_block = self
                        .ctx
                        .append_basic_block(function, &format!("{:?}_post", op.id));

                    self.builder.position_at_end(current_block);
                    // Compile condition
                    trace!("Compiling condition for {:?}", op.id);
                    self.compile_block(
                        program,
                        value_store,
                        id,
                        procedure,
                        condition_block,
                        function,
                        source_storage,
                        interner,
                    );

                    trace!("Compiling jump for {:?}", op.id);
                    // Make conditional jump.
                    let op_io = analyzer.get_op_io(op.id);
                    self.builder.build_conditional_branch(
                        value_store
                            .load_value(self, op_io.inputs()[0], analyzer, interner)
                            .into_int_value(),
                        then_basic_block,
                        else_basic_block,
                    );

                    // Compile Then
                    self.builder.position_at_end(then_basic_block);
                    trace!("Compiling then-block for {:?}", op.id);
                    self.compile_block(
                        program,
                        value_store,
                        id,
                        procedure,
                        then_block,
                        function,
                        source_storage,
                        interner,
                    );

                    trace!("Transfering to merge vars for {:?}", op.id);
                    {
                        let Some(merges) = analyzer.get_if_merges(op.id) else {
                                panic!("ICE: If block doesn't have merges");
                            };
                        for merge in merges {
                            let data =
                                value_store.load_value(self, merge.then_value, analyzer, interner);
                            value_store.store_value(self, merge.output_value, data);
                        }
                    }

                    self.builder.build_unconditional_branch(post_basic_block);

                    // Compile Else
                    self.builder.position_at_end(else_basic_block);
                    trace!("Compiling else-block for {:?}", op.id);
                    self.compile_block(
                        program,
                        value_store,
                        id,
                        procedure,
                        else_block,
                        function,
                        source_storage,
                        interner,
                    );

                    trace!("Transfering to merge vars for {:?}", op.id);
                    {
                        let Some(merges) = analyzer.get_if_merges(op.id) else {
                                panic!("ICE: If block doesn't have merges");
                            };
                        for merge in merges {
                            let data =
                                value_store.load_value(self, merge.else_value, analyzer, interner);
                            value_store.store_value(self, merge.output_value, data);
                        }
                    }
                    self.builder.build_unconditional_branch(post_basic_block);

                    // Build our jumps
                    self.builder.position_at_end(post_basic_block);
                }
                OpCode::While { body } => {
                    let current_block = self.builder.get_insert_block().unwrap();
                    let condition_block = self
                        .ctx
                        .append_basic_block(function, &format!("{:?}_condition", op.id));
                    let body_block = self
                        .ctx
                        .append_basic_block(function, &format!("{:?}_body", op.id));
                    let post_block = self
                        .ctx
                        .append_basic_block(function, &format!("{:?}_post", op.id));

                    self.builder.position_at_end(current_block);
                    self.builder.build_unconditional_branch(condition_block);

                    trace!("Compiling condition for {:?}", op.id);
                    self.builder.position_at_end(condition_block);
                    self.compile_block(
                        program,
                        value_store,
                        id,
                        procedure,
                        &body.condition,
                        function,
                        source_storage,
                        interner,
                    );

                    trace!("Transfering to merge vars for {:?}", op.id);
                    {
                        let Some(merges) = analyzer.get_while_merges(op.id) else {
                                panic!("ICE: While block doesn't have merges");
                            };
                        for merge in &merges.condition {
                            let data = value_store.load_value(
                                self,
                                merge.condition_value,
                                analyzer,
                                interner,
                            );
                            value_store.store_value(self, merge.pre_value, data);
                        }
                    }

                    trace!("Compiling jump for {:?}", op.id);
                    // Make conditional jump.
                    let op_io = analyzer.get_op_io(op.id);
                    self.builder.build_conditional_branch(
                        value_store
                            .load_value(self, op_io.inputs()[0], analyzer, interner)
                            .into_int_value(),
                        body_block,
                        post_block,
                    );

                    // Compile body
                    self.builder.position_at_end(body_block);
                    trace!("Compiling body-block for {:?}", op.id);
                    self.compile_block(
                        program,
                        value_store,
                        id,
                        procedure,
                        &body.block,
                        function,
                        source_storage,
                        interner,
                    );

                    trace!("Transfering to merge vars for {:?}", op.id);
                    {
                        let Some(merges) = analyzer.get_while_merges(op.id) else {
                                panic!("ICE: While block doesn't have merges");
                            };
                        for merge in &merges.body {
                            let data = value_store.load_value(
                                self,
                                merge.condition_value,
                                analyzer,
                                interner,
                            );
                            value_store.store_value(self, merge.pre_value, data);
                        }
                    }

                    self.builder.build_unconditional_branch(condition_block);

                    self.builder.position_at_end(post_block);
                }

                OpCode::Load { kind } => {
                    let ptr_value_id = op_io.inputs()[0];
                    let ptr = value_store
                        .load_value(self, ptr_value_id, analyzer, interner)
                        .into_pointer_value();

                    let cast_ptr = match kind {
                        PorthTypeKind::Int(width) => {
                            let ptr_type = width
                                .get_int_type(self.ctx)
                                .ptr_type(AddressSpace::default());
                            self.builder.build_pointer_cast(ptr, ptr_type, "cast_ptr")
                        }
                        PorthTypeKind::Ptr => {
                            let ptr_type = self
                                .ctx
                                .i8_type()
                                .ptr_type(AddressSpace::default())
                                .ptr_type(AddressSpace::default());

                            self.builder.build_pointer_cast(ptr, ptr_type, "cast_ptr")
                        }
                        PorthTypeKind::Bool => {
                            let ptr_type = self.ctx.bool_type().ptr_type(AddressSpace::default());
                            self.builder.build_pointer_cast(ptr, ptr_type, "cast_ptr")
                        }
                    };

                    let value = self.builder.build_load(cast_ptr, "load");
                    value_store.store_value(self, op_io.outputs()[0], value);
                }
                OpCode::Store { kind } => {
                    let [data, ptr] = *op_io.inputs().as_arr();
                    let data = value_store.load_value(self, data, analyzer, interner);
                    let ptr = value_store
                        .load_value(self, ptr, analyzer, interner)
                        .into_pointer_value();

                    let cast_ptr = match kind {
                        PorthTypeKind::Int(width) => {
                            let ptr_type = width
                                .get_int_type(self.ctx)
                                .ptr_type(AddressSpace::default());
                            self.builder.build_pointer_cast(ptr, ptr_type, "cast_ptr")
                        }
                        PorthTypeKind::Ptr => {
                            let ptr_type = self
                                .ctx
                                .i8_type()
                                .ptr_type(AddressSpace::default())
                                .ptr_type(AddressSpace::default());

                            self.builder.build_pointer_cast(ptr, ptr_type, "cast_ptr")
                        }
                        PorthTypeKind::Bool => {
                            let ptr_type = self.ctx.bool_type().ptr_type(AddressSpace::default());
                            self.builder.build_pointer_cast(ptr, ptr_type, "cast_ptr")
                        }
                    };

                    self.builder.build_store(cast_ptr, data);
                }

                OpCode::Memory {
                    proc_id,
                    global: false,
                    ..
                } => {
                    let ptr = value_store.variable_map[proc_id];
                    value_store.store_value(self, op_io.outputs()[0], ptr.into());
                }
                OpCode::Memory {
                    module_id,
                    proc_id,
                    offset,
                    global: true,
                } => todo!(),
                OpCode::Prologue => {
                    let params = function.get_param_iter();
                    for (id, param) in op_io.outputs().iter().zip(params) {
                        value_store.store_value(self, *id, param);
                    }
                }

                OpCode::PushBool(val) => {
                    let value = self.ctx.bool_type().const_int(*val as _, false).into();
                    value_store.store_value(self, op_io.outputs()[0], value);
                }
                OpCode::PushInt { width, value } => {
                    let int_type = width.get_int_type(self.ctx);
                    let value = int_type
                        .const_int(*value, false)
                        .const_cast(int_type, false)
                        .into();
                    value_store.store_value(self, op_io.outputs()[0], value);
                }
                OpCode::PushStr { id, is_c_str } => {
                    todo!()
                }

                OpCode::SysCall { arg_count, .. } => {
                    let callee_value = self.syscall_wrappers[*arg_count - 1];

                    let args: Vec<BasicMetadataValueEnum> =
                        op_io
                            .inputs()
                            .iter()
                            .map(
                                |id| match value_store.load_value(self, *id, analyzer, interner) {
                                    BasicValueEnum::PointerValue(v) => self
                                        .builder
                                        .build_ptr_to_int(v, self.ctx.i64_type(), "ptr_cast"),
                                    BasicValueEnum::IntValue(i) => {
                                        self.resize_int(i, self.ctx.i64_type())
                                    }
                                    t => panic!("ICE: Unexected type: {t:?}"),
                                },
                            )
                            .map(Into::into)
                            .collect();

                    let result = self.builder.build_call(
                        callee_value,
                        &args,
                        &format!("calling syscall{arg_count}"),
                    );

                    let Some(BasicValueEnum::IntValue(ret_val)) = result.try_as_basic_value().left() else {
                        panic!("ICE: All syscalls return a value");
                    };

                    value_store.store_value(self, op_io.outputs()[0], ret_val.into());
                }

                // These are no-ops as far as codegen is concerned.
                OpCode::Drop { .. } | OpCode::Rot { .. } | OpCode::Swap { .. } => continue,

                OpCode::ResolvedIdent { .. } => {
                    panic!("ICE: Encountered resolved ident during codegen")
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
        merge_pair_map: &mut HashMap<ValueId, PointerValue<'ctx>>,
    ) {
        fn make_variable<'ctx>(
            value_id: ValueId,
            cg: &CodeGen<'ctx>,
            analyzer: &Analyzer,
            merge_pair_map: &mut HashMap<ValueId, PointerValue<'ctx>>,
        ) {
            if merge_pair_map.contains_key(&value_id) {
                trace!("        Variable already exists for `{value_id:?}`");
                return;
            }

            let typ = match analyzer.value_types([value_id]).unwrap()[0] {
                PorthTypeKind::Int(width) => width.get_int_type(cg.ctx).as_basic_type_enum(),
                PorthTypeKind::Bool => cg.ctx.bool_type().as_basic_type_enum(),
                PorthTypeKind::Ptr => cg
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
                OpCode::If {
                    condition,
                    else_block,
                    ..
                } => {
                    let Some(op_merges) = analyzer.get_if_merges(op.id) else {
                        panic!("ICE: If block doesn't have merge info");
                    };
                    for merge in op_merges {
                        make_variable(merge.output_value, self, analyzer, merge_pair_map);
                    }

                    self.build_merge_variables(&condition.block, analyzer, merge_pair_map);
                    self.build_merge_variables(else_block, analyzer, merge_pair_map);
                }
                OpCode::While { body } => {
                    let Some(op_merges) = analyzer.get_while_merges(op.id) else {
                        panic!("ICE: While block doesn't have merge info");
                    };
                    for merge in &op_merges.condition {
                        make_variable(merge.pre_value, self, analyzer, merge_pair_map);
                    }

                    for merge in &op_merges.body {
                        make_variable(merge.pre_value, self, analyzer, merge_pair_map);
                    }

                    self.build_merge_variables(&body.condition, analyzer, merge_pair_map);
                    self.build_merge_variables(&body.block, analyzer, merge_pair_map);
                }

                _ => continue,
            };
        }
    }

    fn compile_procedure(
        &mut self,
        program: &Program,
        id: ProcedureId,
        procedure: &Procedure,
        function: FunctionValue<'ctx>,
        source_storage: &SourceStorage,
        interner: &mut Interners,
    ) {
        let mut value_store = ValueStore::default();
        let name = interner.get_symbol_name(program, id);
        let _span = debug_span!(stringify!(CodeGen::compile_procedure), name).entered();

        let entry_block = self.ctx.append_basic_block(function, "entry");
        self.builder.position_at_end(entry_block);

        trace!("Defining local allocations");
        let proc_data = procedure.kind().get_proc_data();
        for (&proc_id, alloc_size) in &proc_data.alloc_sizes {
            let variable = self.builder.build_alloca(
                self.ctx.i8_type().array_type(alloc_size.to_u32().unwrap()),
                interner.get_symbol_name(program, proc_id),
            );
            let variable = self.builder.build_pointer_cast(
                variable,
                self.ctx.i8_type().ptr_type(AddressSpace::default()),
                "ptr_cast",
            );

            value_store.variable_map.insert(proc_id, variable);
        }

        trace!("Defining merge variables");
        self.build_merge_variables(
            procedure.body(),
            procedure.analyzer(),
            &mut value_store.merge_pair_map,
        );

        {
            let _span = trace_span!("compile_block").entered();
            self.compile_block(
                program,
                &mut value_store,
                id,
                procedure,
                procedure.body(),
                function,
                source_storage,
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

    fn build(
        &mut self,
        program: &Program,
        source_storage: &SourceStorage,
        interner: &mut Interners,
    ) {
        let _span = debug_span!(stringify!(CodeGen::build)).entered();
        while let Some(proc_id) = self.function_queue.pop() {
            let proc = program.get_proc(proc_id);
            let function = self.proc_function_map[&proc_id];
            self.compile_procedure(program, proc_id, proc, function, source_storage, interner);
        }

        self.pass_manager.run_on(&self.module);
    }

    fn build_entry(&mut self, entry_id: ProcedureId) {
        let function_type = self.ctx.void_type().fn_type(&[], false);
        let entry_func = self
            .module
            .add_function("entry", function_type, Some(Linkage::External));
        let block = self.ctx.append_basic_block(entry_func, "entry");
        self.builder.position_at_end(block);
        let user_entry = self.proc_function_map[&entry_id];
        self.builder.build_call(user_entry, &[], "call_user_entry");
        self.builder.build_return(None);
    }

    fn module(&self) -> &Module<'ctx> {
        &self.module
    }
}

pub(crate) fn compile(
    program: &Program,
    entry_function: ProcedureId,
    source_storage: &SourceStorage,
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
    codegen.build(program, source_storage, interner);

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
