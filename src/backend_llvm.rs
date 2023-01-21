use std::path::{Path, PathBuf};

use color_eyre::{eyre::eyre, Result};
use hashbrown::HashMap;
use inkwell::{
    builder::Builder,
    context::Context,
    module::Module,
    passes::{PassManager, PassManagerBuilder},
    targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine},
    types::{BasicMetadataTypeEnum, BasicType},
    values::FunctionValue,
    AddressSpace, OptimizationLevel,
};
use log::{debug, trace};

use crate::{
    interners::Interners,
    program::{static_analysis::PorthTypeKind, ProcedureId, ProcedureKind, Program},
    source_file::SourceStorage,
};

struct CodeGen<'ctx> {
    ctx: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    pass_manager: PassManager<Module<'ctx>>,

    function_queue: Vec<ProcedureId>,
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
            proc_function_map: HashMap::new(),
        }
    }

    fn enqueue_function(&mut self, proc: ProcedureId) {
        self.function_queue.push(proc);
    }

    fn build_function_prototypes(&mut self, program: &Program, interner: &mut Interners) {
        debug!("Building function prototypes..");
        for (id, proc) in program.get_all_procedures() {
            let ProcedureKind::Function(_) = proc.kind() else { continue };

            let name = interner.get_symbol_name(program, id);
            trace!("    Building prototype for {name}");

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
            let return_type = self.ctx.struct_type(&exit_stack, false);

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

            let function_type = return_type.fn_type(&entry_stack, false);

            let function = self.module.add_function(name, function_type, None);
            self.proc_function_map.insert(id, function);
        }

        debug!("finished");
    }

    fn build(
        &mut self,
        program: &Program,
        source_storage: &SourceStorage,
        interner: &mut Interners,
    ) {
        todo!()
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
        .write_to_file(codegen.module(), FileType::Object, &output_obj)
        .map_err(|e| eyre!("Error writing object: {e}"))?;

    todo!()
}
