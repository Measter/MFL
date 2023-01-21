use std::path::{Path, PathBuf};

use color_eyre::{eyre::eyre, Result};
use hashbrown::{HashMap, HashSet};
use inkwell::{
    builder::Builder,
    context::Context,
    module::Module,
    passes::{PassManager, PassManagerBuilder},
    targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine},
    types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum},
    values::{BasicMetadataValueEnum, BasicValueEnum, FunctionValue},
    AddressSpace, OptimizationLevel,
};
use log::{debug, trace};

use crate::{
    interners::Interners,
    n_ops::SliceNOps,
    opcode::{Op, OpCode},
    program::{
        static_analysis::{Analyzer, ConstVal, PorthTypeKind, ValueId},
        Procedure, ProcedureId, ProcedureKind, Program,
    },
    source_file::SourceStorage,
};

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

            let function = self.module.add_function(name, function_type, None);
            self.proc_function_map.insert(id, function);
        }

        debug!("    Finished");
    }

    fn value_or_const(
        &self,
        id: ValueId,
        value_map: &mut HashMap<ValueId, BasicValueEnum<'ctx>>,
        analyzer: &Analyzer,
    ) -> BasicValueEnum<'ctx> {
        match analyzer.value_consts([id]) {
            Some([const_val]) => match const_val {
                ConstVal::Int(val) => self.ctx.i64_type().const_int(val, true).into(),
                ConstVal::Bool(val) => self.ctx.bool_type().const_int(val as u64, false).into(),
                ConstVal::Ptr {
                    id,
                    src_op_loc,
                    offset,
                } => todo!(),
            },
            _ => value_map[&id],
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
        source_storage: &SourceStorage,
        interner: &mut Interners,
    ) {
        let analyzer = procedure.analyzer();

        for op in procedure.body() {
            let op_io = analyzer.get_op_io(op.id);

            match &op.code {
                OpCode::Add => {
                    let [a, b] = *op_io.inputs().as_arr();
                    let a_val = self.value_or_const(a, value_map, analyzer).into_int_value();
                    let b_val = self.value_or_const(b, value_map, analyzer).into_int_value();

                    let sum = self.builder.build_int_add(a_val, b_val, "add");
                    value_map.insert(op_io.outputs()[0], sum.into());
                }
                OpCode::ArgC => todo!(),
                OpCode::ArgV => todo!(),
                OpCode::BitAnd => todo!(),
                OpCode::BitNot => todo!(),
                OpCode::BitOr => todo!(),
                OpCode::CallProc {
                    proc_id: callee_id, ..
                } => {
                    let args: Vec<BasicMetadataValueEnum> = op_io
                        .inputs()
                        .iter()
                        .map(|id| self.value_or_const(*id, value_map, analyzer))
                        .map(Into::into)
                        .collect();

                    let callee_name = interner.get_symbol_name(program, *callee_id);
                    let callee_value = self.proc_function_map[callee_id];

                    self.builder
                        .build_call(callee_value, &args, &format!("calling {callee_name}"));

                    self.enqueue_function(*callee_id);
                }
                OpCode::CastBool => todo!(),
                OpCode::CastInt => todo!(),
                OpCode::CastPtr => todo!(),
                OpCode::DivMod => todo!(),
                OpCode::Dup { depth } => todo!(),
                OpCode::DupPair => todo!(),
                OpCode::Drop => {
                    // We only have to update the value map, and we don't care whether it
                    // actually existed (e.g. due to const elision).
                    value_map.remove(&op_io.inputs()[0]);
                }
                OpCode::Epilogue => {
                    if op_io.inputs().is_empty() {
                        self.builder.build_return(None);
                        continue;
                    }

                    let return_values: Vec<BasicValueEnum> = op_io
                        .inputs()
                        .iter()
                        .map(|id| self.value_or_const(*id, value_map, analyzer))
                        .collect();
                    self.builder.build_aggregate_return(&return_values);
                }
                OpCode::Equal => todo!(),
                OpCode::If {
                    open_token,
                    condition,
                    else_block,
                    end_token,
                } => todo!(),
                OpCode::Less => todo!(),
                OpCode::LessEqual => todo!(),
                OpCode::Load { width, kind } => todo!(),
                OpCode::Greater => todo!(),
                OpCode::GreaterEqual => todo!(),
                OpCode::Memory {
                    module_id,
                    proc_id,
                    offset,
                    global,
                } => todo!(),
                OpCode::Multiply => todo!(),
                OpCode::NotEq => todo!(),
                OpCode::Prologue => {
                    let params = function.get_param_iter();
                    for (id, param) in op_io.outputs().iter().zip(params) {
                        value_map.insert(*id, param);
                    }
                }
                OpCode::PushBool(_) => todo!(),
                OpCode::PushInt(v) => {
                    // This is always const, there's nothing to do.
                    continue;
                }
                OpCode::PushStr { id, is_c_str } => todo!(),
                OpCode::ResolvedIdent { module, proc_id } => todo!(),
                OpCode::Return => todo!(),
                OpCode::Rot => todo!(),
                OpCode::ShiftLeft => todo!(),
                OpCode::ShiftRight => todo!(),
                OpCode::Store { width, kind } => todo!(),
                OpCode::Subtract => todo!(),
                OpCode::Swap => todo!(),
                OpCode::SysCall(_) => todo!(),
                OpCode::UnresolvedIdent { module, proc } => todo!(),
                OpCode::While { body } => todo!(),
            }
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
        let name = interner.get_symbol_name(program, id);
        debug!("Compiling {name}...");

        let entry_block = self.ctx.append_basic_block(function, "entry");
        self.builder.position_at_end(entry_block);

        self.compile_block(
            program,
            id,
            procedure,
            procedure.body(),
            function,
            &mut value_map,
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
    codegen.build(program, source_storage, interner);

    target_machine
        .write_to_file(codegen.module(), FileType::Assembly, &output_obj)
        .map_err(|e| eyre!("Error writing object: {e}"))?;

    Ok(vec![output_obj])
}
