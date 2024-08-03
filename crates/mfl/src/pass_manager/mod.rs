use std::collections::VecDeque;

use ariadne::{Color, Label};
use color_eyre::{eyre::eyre, Result};
use flagset::{flags, FlagSet};
use hashbrown::HashMap;
use prettytable::{row, Table};
use tracing::{debug_span, trace};

use crate::{
    diagnostics,
    error_signal::ErrorSignal,
    option::OptionExt,
    simulate::{simulate_execute_program, SimulatorValue},
    stores::{
        item::{ItemHeader, ItemId, ItemKind, LangItem},
        types::TypeKind,
    },
    Stores,
};

mod passes;
pub mod static_analysis;

flags! {
    pub(crate) enum PassState: u16 {
        BuildNames,
        CheckAsserts,
        ConstPropBody,
        CyclicRefCheckBody,

        DeclareStructs,
        DefineStructs,
        EvaluatedConstsAsserts,
        IdentResolvedBody,

        IdentResolvedSignature,
        PartiallyTypeResolved,
        SelfContainingStruct,
        StackAndTypeCheckedBody,

        TerminalBlockCheckBody,
        TypeResolvedBody,
        TypeResolvedSignature,
        ValidAttributes,
    }
}

impl PassState {
    fn get_function(self) -> fn(&mut PassManager, &mut Stores, ItemId) -> Result<(), ()> {
        match self {
            PassState::IdentResolvedSignature => PassManager::ensure_ident_resolved_signature,
            PassState::IdentResolvedBody => PassManager::ensure_ident_resolved_body,
            PassState::DeclareStructs => PassManager::ensure_declare_structs,
            PassState::DefineStructs => PassManager::ensure_define_structs,
            PassState::SelfContainingStruct => PassManager::ensure_self_containing_structs,
            PassState::TypeResolvedSignature => PassManager::ensure_type_resolved_signature,
            PassState::TypeResolvedBody => PassManager::ensure_type_resolved_body,
            PassState::BuildNames => PassManager::ensure_build_names,
            PassState::CyclicRefCheckBody => PassManager::ensure_cyclic_ref_check_body,
            PassState::TerminalBlockCheckBody => PassManager::ensure_terminal_block_check_body,
            PassState::StackAndTypeCheckedBody => PassManager::ensure_stack_and_type_checked_body,
            PassState::ConstPropBody => PassManager::ensure_const_prop_body,
            PassState::EvaluatedConstsAsserts => PassManager::ensure_evaluated_consts_asserts,
            PassState::CheckAsserts => PassManager::ensure_check_asserts,
            PassState::PartiallyTypeResolved => PassManager::ensure_partially_resolve_types,
            PassState::ValidAttributes => PassManager::ensure_valid_attributes,
        }
    }

    fn get_deps(self) -> &'static [PassState] {
        use PassState::*;
        match self {
            BuildNames
            | IdentResolvedBody
            | IdentResolvedSignature
            | TerminalBlockCheckBody
            | ValidAttributes => &[],
            ConstPropBody => &[StackAndTypeCheckedBody],
            CheckAsserts => &[EvaluatedConstsAsserts],
            CyclicRefCheckBody | TypeResolvedBody => &[IdentResolvedBody],
            DeclareStructs | SelfContainingStruct | TypeResolvedSignature => {
                &[IdentResolvedSignature]
            }
            DefineStructs => &[DeclareStructs],
            EvaluatedConstsAsserts => &[CyclicRefCheckBody, ConstPropBody],
            PartiallyTypeResolved => &[IdentResolvedBody, IdentResolvedSignature],
            StackAndTypeCheckedBody => &[
                TypeResolvedSignature,
                TypeResolvedBody,
                TerminalBlockCheckBody,
            ],
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct ItemState {
    passed: FlagSet<PassState>,
    errored: FlagSet<PassState>,
}

impl ItemState {
    fn new() -> Self {
        Self {
            passed: FlagSet::default(),
            errored: FlagSet::default(),
        }
    }
}

pub struct PassManager {
    states: HashMap<ItemId, ItemState>,
    queue: VecDeque<ItemId>,
    defined_generic_structs: bool,
    stack_stats_table: Table,
}

impl PassManager {
    fn new(i: impl Iterator<Item = ItemHeader>) -> Self {
        let (states, queue) = i.map(|i| ((i.id, ItemState::new()), i.id)).unzip();
        Self {
            states,
            queue,
            defined_generic_structs: false,
            stack_stats_table: Table::new(),
        }
    }

    fn set_error(&mut self, cur_item: ItemId, state: PassState) {
        let cur_item_state = self.states.get_mut(&cur_item).unwrap();
        cur_item_state.errored |= state;
    }

    fn set_passed(&mut self, cur_item: ItemId, state: PassState) {
        let cur_item_state = self.states.get_mut(&cur_item).unwrap();
        cur_item_state.passed |= state;
    }

    pub fn add_new_item(&mut self, id: ItemId, base_id: ItemId, new_state: FlagSet<PassState>) {
        self.queue.push_back(id);
        let mut new_state_info = self.states[&base_id];
        new_state_info.passed = new_state;
        self.states
            .insert(id, new_state_info)
            .expect_none("ICE: Re-added state for item");
    }

    pub fn enqueue(&mut self, id: ItemId) {
        self.queue.push_back(id);
    }

    fn next_item(&mut self) -> Option<ItemId> {
        self.queue.pop_front()
    }
}

macro_rules! ensure_state_deps {
    ($self:expr, $stores:expr, $cur_item:expr, $this_state:expr) => {
        let cur_item_state = $self.states[&$cur_item];
        if cur_item_state.passed.contains($this_state) {
            return Ok(());
        }
        let dep_list = $this_state.get_deps();
        let mut had_error = false;
        for &dep in dep_list {
            let cur_item_state = $self.states[&$cur_item];
            if cur_item_state.passed.contains(dep) {
                continue;
            }
            if cur_item_state.errored.contains(dep) {
                had_error = true;
                continue;
            }

            dep.get_function()($self, $stores, $cur_item)?;
        }
        if had_error {
            $self.set_error($cur_item, $this_state);
            return Err(());
        }
    };
}

impl PassManager {
    pub fn ensure_build_names(&mut self, stores: &mut Stores, cur_item: ItemId) -> Result<(), ()> {
        const STATE: PassState = PassState::BuildNames;
        ensure_state_deps!(self, stores, cur_item, STATE);

        let _span = debug_span!("BuildNames").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        stores.build_friendly_name(self, cur_item);
        stores.build_mangled_name(self, cur_item);
        self.set_passed(cur_item, STATE);
        Ok(())
    }

    fn ensure_check_asserts(&mut self, stores: &mut Stores, cur_item: ItemId) -> Result<(), ()> {
        const STATE: PassState = PassState::CheckAsserts;
        ensure_state_deps!(self, stores, cur_item, STATE);

        let _span = debug_span!("CheckAsserts").entered();
        trace!(
            name = stores.get_symbol_name( cur_item),
            id = ?cur_item,
        );

        // Type check and const prop ensure this value exists.
        let Some([SimulatorValue::Bool(assert_is_true)]) = stores.items.get_consts(cur_item) else {
            unreachable!()
        };

        if !assert_is_true {
            let item_header = stores.items.get_item_header(cur_item);
            diagnostics::emit_error(
                stores,
                item_header.name.location,
                "assert failure",
                [Label::new(item_header.name.location)
                    .with_color(Color::Red)
                    .with_message("evaluated to false")],
                None,
            );

            self.set_error(cur_item, STATE);
            Err(())
        } else {
            self.set_passed(cur_item, STATE);
            Ok(())
        }
    }

    fn ensure_const_prop_body(&mut self, stores: &mut Stores, cur_item: ItemId) -> Result<(), ()> {
        const STATE: PassState = PassState::ConstPropBody;
        ensure_state_deps!(self, stores, cur_item, PassState::ConstPropBody);

        let _span = debug_span!("ConstProp").entered();
        trace!(
            name = stores.get_symbol_name( cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::const_prop::analyze_item(stores, self, &mut had_error, cur_item);

        if had_error.into_bool() {
            self.set_error(cur_item, STATE);
            Err(())
        } else {
            self.set_passed(cur_item, STATE);
            Ok(())
        }
    }

    fn ensure_cyclic_ref_check_body(
        &mut self,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        const STATE: PassState = PassState::CyclicRefCheckBody;
        ensure_state_deps!(self, stores, cur_item, STATE);

        let _span = debug_span!("CycleCheck").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::cycles::check_invalid_cycles(stores, self, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item, STATE);
            Err(())
        } else {
            self.set_passed(cur_item, STATE);
            Ok(())
        }
    }

    pub fn ensure_declare_structs(
        &mut self,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        const STATE: PassState = PassState::DeclareStructs;
        ensure_state_deps!(self, stores, cur_item, STATE);

        let _span = debug_span!("DeclStruct").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::structs::declare_struct(stores, self, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item, STATE);
            Err(())
        } else {
            self.set_passed(cur_item, STATE);
            Ok(())
        }
    }

    fn ensure_define_structs(&mut self, stores: &mut Stores, cur_item: ItemId) -> Result<(), ()> {
        const STATE: PassState = PassState::DefineStructs;
        ensure_state_deps!(self, stores, cur_item, STATE);

        let _span = debug_span!("DefStruct").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        // Non-generic structs require the generic structs to be defined, incase any of them depend on a generic struct.
        // TODO: Make this use the pass manager to avoid this bit.
        let struct_def = stores.sigs.nrir.get_struct(cur_item);
        if struct_def.generic_params.is_empty() && !self.defined_generic_structs {
            let all_generic_structs = stores.items.get_generic_structs().to_owned();
            for gsi in all_generic_structs {
                if self.ensure_define_structs(stores, gsi).is_err() {
                    had_error.set();
                }
            }
            self.defined_generic_structs = true;
        }

        if had_error.into_bool() {
            self.set_error(cur_item, STATE);
            return Err(());
        }

        let mut had_error = ErrorSignal::new();
        passes::structs::define_struct(stores, self, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item, STATE);
            Err(())
        } else {
            self.set_passed(cur_item, STATE);
            Ok(())
        }
    }

    pub fn ensure_evaluated_consts_asserts(
        &mut self,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        const STATE: PassState = PassState::EvaluatedConstsAsserts;
        ensure_state_deps!(self, stores, cur_item, STATE);

        let _span = debug_span!("EvaluateConstAsserts").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let result = simulate_execute_program(stores, self, cur_item);
        match result {
            Ok(stack) => {
                let type_sig = stores.sigs.trir.get_item_signature(cur_item);
                let const_vals = stack
                    .into_iter()
                    .zip(&type_sig.exit)
                    .map(|(val, ty)| {
                        let expected_type = stores.types.get_type_info(*ty);
                        // Implicit casting the integer.
                        match val {
                            SimulatorValue::Int { kind, .. } => {
                                let TypeKind::Integer(int) = expected_type.kind else {
                                    unreachable!()
                                };
                                SimulatorValue::Int {
                                    width: int.width,
                                    kind: kind.cast(int),
                                }
                            }
                            SimulatorValue::Bool(_) => val,
                        }
                    })
                    .collect();

                stores.items.set_consts(cur_item, const_vals);

                self.set_passed(cur_item, STATE);
                Ok(())
            }
            Err(_) => {
                self.set_error(cur_item, STATE);
                Err(())
            }
        }
    }

    pub fn ensure_ident_resolved_body(
        &mut self,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        const STATE: PassState = PassState::IdentResolvedBody;
        ensure_state_deps!(self, stores, cur_item, STATE);

        let _span = debug_span!("IdentBody").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::ident_resolution::resolve_body(stores, self, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item, STATE);
            Err(())
        } else {
            self.set_passed(cur_item, STATE);
            Ok(())
        }
    }

    pub fn ensure_ident_resolved_signature(
        &mut self,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        const STATE: PassState = PassState::IdentResolvedSignature;
        ensure_state_deps!(self, stores, cur_item, STATE);

        let _span = debug_span!("IdentSig").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::ident_resolution::resolve_signature(stores, self, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item, STATE);
            Err(())
        } else {
            self.set_passed(cur_item, STATE);
            Ok(())
        }
    }

    pub fn ensure_partially_resolve_types(
        &mut self,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        const STATE: PassState = PassState::PartiallyTypeResolved;
        ensure_state_deps!(self, stores, cur_item, STATE);

        let _span = debug_span!("PartialType").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::type_resolution::resolve_signature(stores, self, &mut had_error, cur_item);
        passes::type_resolution::resolve_body(stores, self, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item, STATE);
            Err(())
        } else {
            self.set_passed(cur_item, STATE);
            Ok(())
        }
    }

    fn ensure_self_containing_structs(
        &mut self,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        const STATE: PassState = PassState::SelfContainingStruct;
        ensure_state_deps!(self, stores, cur_item, STATE);

        let _span = debug_span!("SelfContainingStruct").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::cycles::check_invalid_cycles(stores, self, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item, STATE);
            Err(())
        } else {
            self.set_passed(cur_item, STATE);
            Ok(())
        }
    }

    fn ensure_stack_and_type_checked_body(
        &mut self,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        const STATE: PassState = PassState::StackAndTypeCheckedBody;
        ensure_state_deps!(self, stores, cur_item, STATE);

        let _span = debug_span!("StackTypeCheck").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        let stats = passes::stack_type_check::analyze_item(stores, self, &mut had_error, cur_item);

        self.stack_stats_table.add_row(row![
            stores.get_symbol_name(cur_item),
            stats.max_stack_depth,
            stats.unique_item_count
        ]);
        if had_error.into_bool() {
            self.set_error(cur_item, STATE);
            Err(())
        } else {
            self.set_passed(cur_item, STATE);
            Ok(())
        }
    }

    fn ensure_terminal_block_check_body(
        &mut self,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        const STATE: PassState = PassState::TerminalBlockCheckBody;
        ensure_state_deps!(self, stores, cur_item, STATE);

        let _span = debug_span!("TerminalCheck").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        passes::terminal::determine_terminal_blocks(stores, cur_item);
        self.set_passed(cur_item, STATE);
        Ok(())
    }

    fn ensure_type_resolved_body(
        &mut self,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        const STATE: PassState = PassState::TypeResolvedBody;
        ensure_state_deps!(self, stores, cur_item, STATE);

        let _span = debug_span!("TypeBody").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::type_resolution::resolve_body(stores, self, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item, STATE);
            Err(())
        } else {
            self.set_passed(cur_item, STATE);
            Ok(())
        }
    }

    pub fn ensure_type_resolved_signature(
        &mut self,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        const STATE: PassState = PassState::TypeResolvedSignature;
        ensure_state_deps!(self, stores, cur_item, STATE);

        let _span = debug_span!("TypeSig").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::type_resolution::resolve_signature(stores, self, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item, STATE);
            Err(())
        } else {
            self.set_passed(cur_item, STATE);
            Ok(())
        }
    }

    pub fn ensure_valid_attributes(
        &mut self,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        const STATE: PassState = PassState::ValidAttributes;
        ensure_state_deps!(self, stores, cur_item, STATE);

        let _span = debug_span!("ValidAttrib").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::attributes::validate_attributes(stores, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item, STATE);
            Err(())
        } else {
            self.set_passed(cur_item, STATE);
            Ok(())
        }
    }

    fn ensure_done(&mut self, stores: &mut Stores, cur_item: ItemId) -> Result<(), ()> {
        let needed_states = match stores.items.get_item_header(cur_item).kind {
            ItemKind::Module => [
                PassState::BuildNames,
                PassState::ValidAttributes,
                PassState::IdentResolvedSignature,
            ]
            .as_slice(),
            ItemKind::StructDef => &[
                PassState::ValidAttributes,
                PassState::SelfContainingStruct,
                PassState::DefineStructs,
            ],
            ItemKind::Variable | ItemKind::FunctionDecl => &[
                PassState::BuildNames,
                PassState::ValidAttributes,
                PassState::TypeResolvedSignature,
            ],
            // Type resolution happens after the generic function is instantiated.
            ItemKind::GenericFunction => {
                &[PassState::ValidAttributes, PassState::PartiallyTypeResolved]
            }
            ItemKind::Assert => &[PassState::ValidAttributes, PassState::CheckAsserts],
            ItemKind::Const => &[
                PassState::ValidAttributes,
                PassState::EvaluatedConstsAsserts,
            ],
            ItemKind::Function { .. } => &[
                PassState::BuildNames,
                PassState::ValidAttributes,
                PassState::ConstPropBody,
            ],
        };

        let as_flags = needed_states.iter().fold(FlagSet::default(), |a, b| a | *b);
        let cur_state = self.states[&cur_item];
        if cur_state.passed.contains(as_flags) {
            return Ok(());
        }
        if !cur_state.errored.is_empty() {
            return Err(());
        }

        for state in needed_states {
            state.get_function()(self, stores, cur_item)?;
        }

        Ok(())
    }
}

pub fn run(stores: &mut Stores, print_stack_stats: bool) -> Result<()> {
    let _span = debug_span!(stringify!(pass_manager)).entered();
    let mut pass_manager = PassManager::new(stores.items.get_all_items());
    let mut had_error = ErrorSignal::new();

    // Need to make sure the String type is declared before anything else.
    let string_id = stores.items.get_lang_items()[&LangItem::String];
    if pass_manager
        .ensure_declare_structs(stores, string_id)
        .is_err()
    {
        panic!("ICE: Failed to declared String type");
    };

    while let Some(cur_item_id) = pass_manager.next_item() {
        if pass_manager.ensure_done(stores, cur_item_id).is_err() {
            had_error.set();
        }
    }

    if print_stack_stats {
        println!("\n{}", pass_manager.stack_stats_table);
    }

    if had_error.into_bool() {
        Err(eyre!("Error during static analysis"))
    } else {
        Ok(())
    }
}
