use std::path::{Path, PathBuf};

use color_eyre::{eyre::eyre, Result};
use hashbrown::{HashMap, HashSet};
use inkwell::{
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    passes::{PassManager, PassManagerBuilder},
    targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine},
    types::{BasicMetadataTypeEnum, BasicType},
    values::{BasicMetadataValueEnum, BasicValueEnum, FunctionValue, IntMathValue, PointerValue},
    AddressSpace, IntPredicate, OptimizationLevel,
};
use log::{debug, trace};

use crate::{
    interners::Interners,
    n_ops::SliceNOps,
    opcode::{ConditionalBlock, Op, OpCode},
    program::{
        static_analysis::{Analyzer, ConstVal, PorthTypeKind, PtrId, ValueId},
        Procedure, ProcedureId, ProcedureKind, Program,
    },
    source_file::SourceStorage,
};

type BuilderArithFunc<'ctx, T> = fn(&'_ Builder<'ctx>, T, T, &'_ str) -> T;

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

struct CodeGen<'ctx> {
    ctx: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    pass_manager: PassManager<Module<'ctx>>,

    function_queue: Vec<ProcedureId>,
    processed_functions: HashSet<ProcedureId>,
    proc_function_map: HashMap<ProcedureId, FunctionValue<'ctx>>,
}

impl<'ctx> CodeGen<'ctx> {
    fn from_context(ctx: &'ctx Context, opt_level: OptimizationLevel) -> Self {
        let module = ctx.create_module("porth_module");
        let builder = ctx.create_builder();

        let pm_builder = PassManagerBuilder::create();
        pm_builder.set_optimization_level(opt_level);
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
        }
    }

    fn enqueue_function(&mut self, proc: ProcedureId) {
        if !self.processed_functions.contains(&proc) {
            self.function_queue.push(proc);
        }
    }

    fn build_function_prototypes(&mut self, program: &Program, interner: &mut Interners) {
        debug!("Building function prototypes..");
        for (id, proc) in program.get_all_procedures() {
            let ProcedureKind::Function(_) = proc.kind() else { continue };

            let name = interner.get_symbol_name(program, id);
            trace!("    Building prototype for {name}");

            let entry_stack: Vec<BasicMetadataTypeEnum> = proc
                .entry_stack()
                .iter()
                .map(|t| match t.kind {
                    PorthTypeKind::Int => self.ctx.i64_type().into(),
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
                        PorthTypeKind::Int => self.ctx.i64_type().as_basic_type_enum(),
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

        debug!("    Finished");
    }

    fn load_value(
        &self,
        id: ValueId,
        value_map: &mut HashMap<ValueId, BasicValueEnum<'ctx>>,
        variable_map: &HashMap<ProcedureId, PointerValue<'ctx>>,
        merge_pair_map: &HashMap<ValueId, PointerValue<'ctx>>,
        analyzer: &Analyzer,
    ) -> BasicValueEnum<'ctx> {
        match analyzer.value_consts([id]) {
            Some([const_val]) => {
                trace!("      Fetching const {id:?}");
                match const_val {
                    ConstVal::Int(val) => self.ctx.i64_type().const_int(val, true).into(),
                    ConstVal::Bool(val) => self.ctx.bool_type().const_int(val as u64, false).into(),
                    ConstVal::Ptr { id, offset, .. } => {
                        let ptr = match id {
                            PtrId::Mem(id) => variable_map[&id],
                            PtrId::Str(_) => todo!(),
                        };

                        if let Some(offset) = offset {
                            let offset = self.ctx.i64_type().const_int(offset, false);
                            unsafe { self.builder.build_gep(ptr, &[offset], "ptr offset") }.into()
                        } else {
                            ptr.into()
                        }
                    }
                }
            }
            _ => {
                if let Some(&ptr) = merge_pair_map.get(&id) {
                    trace!(
                        "      Fetching {id:?} from variable at {}",
                        ptr.get_name().to_str().unwrap()
                    );
                    self.builder.build_load(ptr, "load_var")
                } else {
                    trace!("      Fetching from value map at {id:?}");
                    value_map[&id]
                }
            }
        }
    }

    fn store_value(
        &self,
        id: ValueId,
        value: BasicValueEnum<'ctx>,
        value_map: &mut HashMap<ValueId, BasicValueEnum<'ctx>>,
        merge_pair_map: &HashMap<ValueId, PointerValue<'ctx>>,
    ) {
        if let Some(&ptr) = merge_pair_map.get(&id) {
            trace!(
                "      Stored {id:?} in variable at {}",
                ptr.get_name().to_str().unwrap()
            );
            self.builder.build_store(ptr, value);
        } else {
            trace!("      Stored in value map at {id:?}");
            value_map.insert(id, value);
        }
    }

    fn compile_block(
        &mut self,
        program: &Program,
        id: ProcedureId,
        procedure: &Procedure,
        block: &[Op],
        function: FunctionValue<'ctx>,
        value_map: &mut HashMap<ValueId, BasicValueEnum<'ctx>>,
        variable_map: &HashMap<ProcedureId, PointerValue<'ctx>>,
        merge_pair_map: &HashMap<ValueId, PointerValue<'ctx>>,
        source_storage: &SourceStorage,
        interner: &mut Interners,
    ) {
        let analyzer = procedure.analyzer();

        for op in block {
            match op.code {
                OpCode::If { .. } => trace!("    {:?}: If", op.id),
                OpCode::While { .. } => trace!("    {:?}: While", op.id),
                _ => trace!("    {:?}: {:?}", op.id, op.code),
            }

            // These do nothing in codegen
            match &op.code {
                OpCode::Swap | OpCode::Rot => continue,
                _ => {}
            }

            let op_io = analyzer.get_op_io(op.id);

            if !op_io.outputs().is_empty()
                && op_io
                    .outputs()
                    .iter()
                    .all(|id| is_fully_const(*id, analyzer))
            {
                trace!("      .. is fully const");
                continue;
            }

            match &op.code {
                OpCode::Add | OpCode::Subtract => {
                    let [a, b] = *op_io.inputs().as_arr();
                    let [a_type, b_type] = analyzer.value_types([a, b]).unwrap();

                    let res: BasicValueEnum = match [a_type, b_type] {
                        [PorthTypeKind::Int, PorthTypeKind::Int] => {
                            let a_val = self
                                .load_value(a, value_map, variable_map, merge_pair_map, analyzer)
                                .into_int_value();
                            let b_val = self
                                .load_value(b, value_map, variable_map, merge_pair_map, analyzer)
                                .into_int_value();
                            let (func, name) = op.code.get_arith_fn();
                            func(&self.builder, a_val, b_val, name).into()
                        }
                        [PorthTypeKind::Int, PorthTypeKind::Ptr] => {
                            assert!(matches!(op.code, OpCode::Add));
                            let offset = self
                                .load_value(a, value_map, variable_map, merge_pair_map, analyzer)
                                .into_int_value();
                            let ptr = self
                                .load_value(b, value_map, variable_map, merge_pair_map, analyzer)
                                .into_pointer_value();

                            unsafe { self.builder.build_gep(ptr, &[offset], "ptr_offset") }.into()
                        }
                        [PorthTypeKind::Ptr, PorthTypeKind::Int] => {
                            let offset = self
                                .load_value(b, value_map, variable_map, merge_pair_map, analyzer)
                                .into_int_value();
                            let ptr = self
                                .load_value(a, value_map, variable_map, merge_pair_map, analyzer)
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

                            let lhs = self
                                .load_value(a, value_map, variable_map, merge_pair_map, analyzer)
                                .into_pointer_value();
                            let rhs = self
                                .load_value(b, value_map, variable_map, merge_pair_map, analyzer)
                                .into_pointer_value();
                            self.builder.build_ptr_diff(lhs, rhs, "ptr_diff").into()
                        }
                        _ => panic!("ICE: Unexpected types"),
                    };

                    self.store_value(op_io.outputs()[0], res, value_map, merge_pair_map);
                }
                OpCode::Multiply | OpCode::BitAnd | OpCode::BitOr => {
                    let [a, b] = *op_io.inputs().as_arr();
                    let a_val = self
                        .load_value(a, value_map, variable_map, merge_pair_map, analyzer)
                        .into_int_value();
                    let b_val = self
                        .load_value(b, value_map, variable_map, merge_pair_map, analyzer)
                        .into_int_value();

                    let (func, name) = op.code.get_arith_fn();
                    let sum = func(&self.builder, a_val, b_val, name);
                    self.store_value(op_io.outputs()[0], sum.into(), value_map, merge_pair_map);
                }
                OpCode::DivMod => {
                    let [a, b] = *op_io.inputs().as_arr();
                    let a_val = self
                        .load_value(a, value_map, variable_map, merge_pair_map, analyzer)
                        .into_int_value();
                    let b_val = self
                        .load_value(b, value_map, variable_map, merge_pair_map, analyzer)
                        .into_int_value();

                    let rem_res = self.builder.build_int_unsigned_rem(a_val, b_val, "rem");
                    let quot_res = self.builder.build_int_unsigned_div(a_val, b_val, "div");

                    let [quot_val, rem_val] = *op_io.outputs().as_arr();
                    self.store_value(quot_val, quot_res.into(), value_map, merge_pair_map);
                    self.store_value(rem_val, rem_res.into(), value_map, merge_pair_map);
                }

                OpCode::Equal
                | OpCode::NotEq
                | OpCode::Greater
                | OpCode::GreaterEqual
                | OpCode::Less
                | OpCode::LessEqual => {
                    let [a, b] = *op_io.inputs().as_arr();
                    let a_val = self
                        .load_value(a, value_map, variable_map, merge_pair_map, analyzer)
                        .into_int_value();
                    let b_val = self
                        .load_value(b, value_map, variable_map, merge_pair_map, analyzer)
                        .into_int_value();

                    let (pred, name) = op.code.get_predicate();
                    let res = self.builder.build_int_compare(pred, a_val, b_val, name);
                    self.store_value(op_io.outputs()[0], res.into(), value_map, merge_pair_map);
                }

                OpCode::ShiftLeft => {
                    let [a, b] = *op_io.inputs().as_arr();
                    let a_val = self
                        .load_value(a, value_map, variable_map, merge_pair_map, analyzer)
                        .into_int_value();
                    let b_val = self
                        .load_value(b, value_map, variable_map, merge_pair_map, analyzer)
                        .into_int_value();

                    let res = self.builder.build_left_shift(a_val, b_val, "shl");
                    self.store_value(op_io.outputs()[0], res.into(), value_map, merge_pair_map);
                }
                OpCode::ShiftRight => {
                    let [a, b] = *op_io.inputs().as_arr();
                    let a_val = self
                        .load_value(a, value_map, variable_map, merge_pair_map, analyzer)
                        .into_int_value();
                    let b_val = self
                        .load_value(b, value_map, variable_map, merge_pair_map, analyzer)
                        .into_int_value();

                    let res = self.builder.build_right_shift(a_val, b_val, false, "shr");
                    self.store_value(op_io.outputs()[0], res.into(), value_map, merge_pair_map);
                }
                OpCode::BitNot => {
                    let a = op_io.inputs()[0];
                    let a_val = self
                        .load_value(a, value_map, variable_map, merge_pair_map, analyzer)
                        .into_int_value();

                    let res = self.builder.build_not(a_val, "not");
                    self.store_value(op_io.outputs()[0], res.into(), value_map, merge_pair_map);
                }

                OpCode::ArgC => todo!(),
                OpCode::ArgV => todo!(),
                OpCode::CallProc {
                    proc_id: callee_id, ..
                } => {
                    let args: Vec<BasicMetadataValueEnum> = op_io
                        .inputs()
                        .iter()
                        .map(|id| {
                            self.load_value(*id, value_map, variable_map, merge_pair_map, analyzer)
                        })
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

                        self.store_value(id, value, value_map, merge_pair_map);
                    }
                }
                OpCode::CastBool => todo!(),
                OpCode::CastInt => todo!(),
                OpCode::CastPtr => todo!(),

                OpCode::Dup { .. } => {
                    let input = op_io.inputs()[0];
                    let output = op_io.outputs()[0];
                    let value =
                        self.load_value(input, value_map, variable_map, merge_pair_map, analyzer);
                    self.store_value(output, value, value_map, merge_pair_map);
                }

                OpCode::Epilogue | OpCode::Return => {
                    for var in variable_map.values() {
                        self.builder.build_free(*var);
                    }

                    if op_io.inputs().is_empty() {
                        self.builder.build_return(None);
                        continue;
                    }

                    let return_values: Vec<BasicValueEnum> = op_io
                        .inputs()
                        .iter()
                        .map(|id| {
                            self.load_value(*id, value_map, variable_map, merge_pair_map, analyzer)
                        })
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
                    trace!("    Compiling condition for {:?}", op.id);
                    self.compile_block(
                        program,
                        id,
                        procedure,
                        condition_block,
                        function,
                        value_map,
                        variable_map,
                        merge_pair_map,
                        source_storage,
                        interner,
                    );

                    trace!("    Compiling jump for {:?}", op.id);
                    // Make conditional jump.
                    let op_io = analyzer.get_op_io(op.id);
                    self.builder.build_conditional_branch(
                        self.load_value(
                            op_io.inputs()[0],
                            value_map,
                            variable_map,
                            merge_pair_map,
                            analyzer,
                        )
                        .into_int_value(),
                        then_basic_block,
                        else_basic_block,
                    );

                    // Compile Then
                    self.builder.position_at_end(then_basic_block);
                    trace!("");
                    trace!("    Compiling then-block for {:?}", op.id);
                    self.compile_block(
                        program,
                        id,
                        procedure,
                        then_block,
                        function,
                        value_map,
                        variable_map,
                        merge_pair_map,
                        source_storage,
                        interner,
                    );

                    trace!("");
                    trace!("    Transfering to merge vars for {:?}", op.id);
                    {
                        let Some(merges) = analyzer.get_if_merges(op.id) else {
                            panic!("ICE: If block doesn't have merges");
                        };
                        for merge in merges {
                            let data = self.load_value(
                                merge.then_value,
                                value_map,
                                variable_map,
                                merge_pair_map,
                                analyzer,
                            );
                            self.store_value(merge.output_value, data, value_map, merge_pair_map);
                        }
                    }

                    self.builder.build_unconditional_branch(post_basic_block);

                    // Compile Else
                    self.builder.position_at_end(else_basic_block);
                    trace!("");
                    trace!("    Compiling else-block for {:?}", op.id);
                    self.compile_block(
                        program,
                        id,
                        procedure,
                        else_block,
                        function,
                        value_map,
                        variable_map,
                        merge_pair_map,
                        source_storage,
                        interner,
                    );

                    trace!("");
                    trace!("    Transfering to merge vars for {:?}", op.id);
                    {
                        let Some(merges) = analyzer.get_if_merges(op.id) else {
                            panic!("ICE: If block doesn't have merges");
                        };
                        for merge in merges {
                            let data = self.load_value(
                                merge.else_value,
                                value_map,
                                variable_map,
                                merge_pair_map,
                                analyzer,
                            );
                            self.store_value(merge.output_value, data, value_map, merge_pair_map);
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

                    trace!("");
                    trace!("    Compiling condition for {:?}", op.id);
                    self.builder.position_at_end(condition_block);
                    self.compile_block(
                        program,
                        id,
                        procedure,
                        &body.condition,
                        function,
                        value_map,
                        variable_map,
                        merge_pair_map,
                        source_storage,
                        interner,
                    );

                    trace!("");
                    trace!("    Transfering to merge vars for {:?}", op.id);
                    {
                        let Some(merges) = analyzer.get_while_merges(op.id) else {
                            panic!("ICE: While block doesn't have merges");
                        };
                        for merge in &merges.condition {
                            let data = self.load_value(
                                merge.condition_value,
                                value_map,
                                variable_map,
                                merge_pair_map,
                                analyzer,
                            );
                            self.store_value(merge.pre_value, data, value_map, merge_pair_map);
                        }
                    }

                    trace!("    Compiling jump for {:?}", op.id);
                    // Make conditional jump.
                    let op_io = analyzer.get_op_io(op.id);
                    self.builder.build_conditional_branch(
                        self.load_value(
                            op_io.inputs()[0],
                            value_map,
                            variable_map,
                            merge_pair_map,
                            analyzer,
                        )
                        .into_int_value(),
                        body_block,
                        post_block,
                    );

                    // Compile body
                    self.builder.position_at_end(body_block);
                    trace!("");
                    trace!("    Compiling body-block for {:?}", op.id);
                    self.compile_block(
                        program,
                        id,
                        procedure,
                        &body.block,
                        function,
                        value_map,
                        variable_map,
                        merge_pair_map,
                        source_storage,
                        interner,
                    );

                    trace!("");
                    trace!("    Transfering to merge vars for {:?}", op.id);
                    {
                        let Some(merges) = analyzer.get_while_merges(op.id) else {
                            panic!("ICE: While block doesn't have merges");
                        };
                        for merge in &merges.body {
                            let data = self.load_value(
                                merge.condition_value,
                                value_map,
                                variable_map,
                                merge_pair_map,
                                analyzer,
                            );
                            self.store_value(merge.pre_value, data, value_map, merge_pair_map);
                        }
                    }

                    self.builder.build_unconditional_branch(condition_block);

                    self.builder.position_at_end(post_block);
                }

                OpCode::Load { width, kind } => todo!(),
                OpCode::Store { width, kind } => {
                    log::error!("STORE not implemented correctly");
                    let [data, ptr] = *op_io.inputs().as_arr();
                    let data =
                        self.load_value(data, value_map, variable_map, merge_pair_map, analyzer);
                    let ptr = self
                        .load_value(ptr, value_map, variable_map, merge_pair_map, analyzer)
                        .into_pointer_value();

                    self.builder.build_store(ptr, data);
                }

                OpCode::Memory {
                    proc_id,
                    global: false,
                    ..
                } => {
                    let ptr = variable_map[proc_id];

                    self.store_value(op_io.outputs()[0], ptr.into(), value_map, merge_pair_map);
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
                        self.store_value(*id, param, value_map, merge_pair_map);
                    }
                }

                OpCode::PushBool(val) => {
                    let value = self.ctx.bool_type().const_int(*val as _, false).into();
                    self.store_value(op_io.outputs()[0], value, value_map, merge_pair_map);
                }
                OpCode::PushInt(val) => {
                    let value = self.ctx.bool_type().const_int(*val, false).into();
                    self.store_value(op_io.outputs()[0], value, value_map, merge_pair_map);
                }
                OpCode::PushStr { id, is_c_str } => {
                    todo!()
                }

                OpCode::SysCall(_) => todo!(),

                // These are no-ops as far as codegen is concerned.
                OpCode::Drop | OpCode::Rot | OpCode::Swap => continue,

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
                PorthTypeKind::Int => cg.ctx.i64_type().as_basic_type_enum(),
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
                    self.build_merge_variables(&condition.block, analyzer, merge_pair_map);
                    self.build_merge_variables(else_block, analyzer, merge_pair_map);

                    let Some(op_merges) = analyzer.get_if_merges(op.id) else {
                        panic!("ICE: If block doesn't have merge info");
                    };
                    for merge in op_merges {
                        make_variable(merge.output_value, self, analyzer, merge_pair_map);
                    }
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
        let mut value_map = HashMap::new();
        let mut variable_map = HashMap::new();
        let mut merge_pair_map = HashMap::new();
        let name = interner.get_symbol_name(program, id);
        debug!("Compiling {name}...");

        let entry_block = self.ctx.append_basic_block(function, "entry");
        self.builder.position_at_end(entry_block);

        let proc_data = procedure.kind().get_proc_data();
        for (&proc_id, alloc_data) in &proc_data.alloc_size_and_offsets {
            let variable = self.builder.build_alloca(
                self.ctx.i8_type().array_type(alloc_data.size as _),
                interner.get_symbol_name(program, proc_id),
            );

            variable_map.insert(proc_id, variable);
        }

        trace!("      Defining merge variables");
        self.build_merge_variables(procedure.body(), procedure.analyzer(), &mut merge_pair_map);

        self.compile_block(
            program,
            id,
            procedure,
            procedure.body(),
            function,
            &mut value_map,
            &variable_map,
            &merge_pair_map,
            source_storage,
            interner,
        );
    }

    fn build(
        &mut self,
        program: &Program,
        source_storage: &SourceStorage,
        interner: &mut Interners,
    ) {
        while let Some(proc_id) = self.function_queue.pop() {
            let proc = program.get_proc(proc_id);
            let function = self.proc_function_map[&proc_id];
            self.compile_procedure(program, proc_id, proc, function, source_storage, interner);
        }

        self.pass_manager.run_on(&self.module);
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
    let mut entry_asm_filename = Path::new(&file)
        .file_stem()
        .unwrap()
        .to_str()
        .unwrap()
        .to_owned();
    entry_asm_filename.push_str("_entry.asm");

    let mut entry_asm = Path::new(&file).to_path_buf();
    entry_asm.set_file_name(&entry_asm_filename);

    let mut output_obj = Path::new(&file).to_path_buf();
    output_obj.set_extension("o");

    debug!(
        "Compiling with LLVM codegen to {} and {}",
        entry_asm.display(),
        output_obj.display()
    );

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
    codegen.proc_function_map[&entry_function].set_linkage(Linkage::External);
    codegen.build(program, source_storage, interner);

    target_machine
        .write_to_file(codegen.module(), FileType::Assembly, &output_obj)
        .map_err(|e| eyre!("Error writing object: {e}"))?;

    Ok(vec![output_obj])
}
