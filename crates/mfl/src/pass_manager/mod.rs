use std::collections::VecDeque;

use color_eyre::{eyre::eyre, Result};
use flagset::{flags, FlagSet};
use hashbrown::HashMap;
use prettytable::{row, Table};
use stores::items::ItemId;
use tracing::{debug_span, trace};

use crate::{
    error_signal::ErrorSignal,
    option::OptionExt,
    simulate::{simulate_execute_program, SimulatorValue},
    stores::{
        diagnostics::Diagnostic,
        item::{ItemHeader, ItemKind, LangItem},
        types::TypeKind,
    },
    Stores,
};

mod passes;
pub mod static_analysis;

flags! {
    pub(crate) enum PassState: u32 {
        BuildNames,
        CheckAsserts,
        ConstPropBody,
        DeclareEnums,

        DeclareStructs,
        DefineStructs,
        EvaluatedConstsAsserts,
        IdentResolvedBody,

        IdentResolvedScope,
        IdentResolvedSignature,
        PartiallyTypeResolved,
        StackAndTypeCheckedBody,

        TerminalBlockCheckBody,
        TypeResolvedBody,
        TypeResolvedSignature,
        ValidityCheck,
    }
}

impl PassState {
    fn get_function(self) -> fn(&mut PassManager, &mut Stores, ItemId) -> Result<(), ()> {
        match self {
            PassState::IdentResolvedScope => PassManager::ensure_ident_resolved_scope,
            PassState::IdentResolvedSignature => PassManager::ensure_ident_resolved_signature,
            PassState::IdentResolvedBody => PassManager::ensure_ident_resolved_body,
            PassState::DeclareStructs => PassManager::ensure_declare_structs,
            PassState::DefineStructs => PassManager::ensure_define_structs,
            PassState::DeclareEnums => PassManager::ensure_declare_enums,
            PassState::TypeResolvedSignature => PassManager::ensure_type_resolved_signature,
            PassState::TypeResolvedBody => PassManager::ensure_type_resolved_body,
            PassState::BuildNames => PassManager::ensure_build_names,
            PassState::TerminalBlockCheckBody => PassManager::ensure_terminal_block_check_body,
            PassState::StackAndTypeCheckedBody => PassManager::ensure_stack_and_type_checked_body,
            PassState::ConstPropBody => PassManager::ensure_const_prop_body,
            PassState::EvaluatedConstsAsserts => PassManager::ensure_evaluated_consts_asserts,
            PassState::CheckAsserts => PassManager::ensure_check_asserts,
            PassState::PartiallyTypeResolved => PassManager::ensure_partially_resolve_types,
            PassState::ValidityCheck => PassManager::ensure_validity_check,
        }
    }

    fn get_deps(self) -> &'static [PassState] {
        use PassState::*;
        match self {
            BuildNames | IdentResolvedScope | TerminalBlockCheckBody | ValidityCheck => &[],
            IdentResolvedBody | IdentResolvedSignature => &[IdentResolvedScope],
            ConstPropBody => &[StackAndTypeCheckedBody],
            CheckAsserts => &[EvaluatedConstsAsserts],
            TypeResolvedBody => &[IdentResolvedBody],
            DeclareEnums => &[BuildNames],
            DeclareStructs => &[BuildNames, IdentResolvedSignature],
            TypeResolvedSignature => &[IdentResolvedSignature],
            DefineStructs => &[DeclareStructs],
            EvaluatedConstsAsserts => &[ValidityCheck, ConstPropBody],
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
        let mut stack_stats_table = Table::new();
        stack_stats_table.set_titles(row!["Item", "Stack Depth", "No. Values"]);
        Self {
            states,
            queue,
            defined_generic_structs: false,
            stack_stats_table,
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

    pub fn add_new_generic_item(
        &mut self,
        id: ItemId,
        base_id: ItemId,
        new_state: FlagSet<PassState>,
    ) {
        self.queue.push_back(id);
        let mut new_state_info = self.states[&base_id];
        new_state_info.passed = new_state;
        self.states
            .insert(id, new_state_info)
            .expect_none("ICE: Re-added state for item");
    }

    fn next_item(&mut self) -> Option<ItemId> {
        self.queue.pop_front()
    }
}

enum NeedsWork {
    Yes,
    No,
}

impl NeedsWork {
    fn done(self) -> bool {
        matches!(self, NeedsWork::No)
    }
}

impl PassManager {
    fn ensure_state_deps(
        &mut self,
        stores: &mut Stores,
        cur_item: ItemId,
        this_state: PassState,
    ) -> Result<NeedsWork, ()> {
        let cur_item_state = self.states[&cur_item];
        if cur_item_state.passed.contains(this_state) {
            return Ok(NeedsWork::No);
        } else if cur_item_state.errored.contains(this_state) {
            return Err(());
        }
        let dep_list = this_state.get_deps();
        let mut had_error = false;
        for &dep in dep_list {
            let cur_item_state = self.states[&cur_item];
            if cur_item_state.passed.contains(dep) {
                continue;
            }
            if cur_item_state.errored.contains(dep) {
                had_error = true;
                continue;
            }

            had_error |= dep.get_function()(self, stores, cur_item).is_err();
        }
        if had_error {
            self.set_error(cur_item, this_state);
            return Err(());
        }
        Ok(NeedsWork::Yes)
    }

    pub fn ensure_build_names(&mut self, stores: &mut Stores, cur_item: ItemId) -> Result<(), ()> {
        const STATE: PassState = PassState::BuildNames;
        if self.ensure_state_deps(stores, cur_item, STATE)?.done() {
            return Ok(());
        };

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
        if self.ensure_state_deps(stores, cur_item, STATE)?.done() {
            return Ok(());
        };

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
            Diagnostic::error(item_header.name.location, "assert failure")
                .primary_label_message("evaluated to false")
                .attached(stores.diags, cur_item);

            self.set_error(cur_item, STATE);
            Err(())
        } else {
            self.set_passed(cur_item, STATE);
            Ok(())
        }
    }

    fn ensure_const_prop_body(&mut self, stores: &mut Stores, cur_item: ItemId) -> Result<(), ()> {
        const STATE: PassState = PassState::ConstPropBody;
        if self.ensure_state_deps(stores, cur_item, STATE)?.done() {
            return Ok(());
        };

        let _span = debug_span!("ConstProp").entered();
        trace!(
            name = stores.get_symbol_name( cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::const_prop::analyze_item(stores, self, &mut had_error, cur_item);

        if had_error.into_err() {
            self.set_error(cur_item, STATE);
            Err(())
        } else {
            self.set_passed(cur_item, STATE);
            Ok(())
        }
    }

    fn ensure_declare_enums(&mut self, stores: &mut Stores, cur_item: ItemId) -> Result<(), ()> {
        const STATE: PassState = PassState::DeclareEnums;
        if self.ensure_state_deps(stores, cur_item, STATE)?.done() {
            return Ok(());
        };

        let _span = debug_span!("DeclEnum").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        passes::types::declare_enum(stores, cur_item);
        self.set_passed(cur_item, STATE);
        Ok(())
    }

    pub fn ensure_declare_structs(
        &mut self,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        const STATE: PassState = PassState::DeclareStructs;
        if self.ensure_state_deps(stores, cur_item, STATE)?.done() {
            return Ok(());
        };

        let _span = debug_span!("DeclStruct").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::types::declare_struct(stores, &mut had_error, cur_item);
        if had_error.into_err() {
            self.set_error(cur_item, STATE);
            Err(())
        } else {
            self.set_passed(cur_item, STATE);
            Ok(())
        }
    }

    fn ensure_define_structs(&mut self, stores: &mut Stores, cur_item: ItemId) -> Result<(), ()> {
        const STATE: PassState = PassState::DefineStructs;
        if self.ensure_state_deps(stores, cur_item, STATE)?.done() {
            return Ok(());
        };

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

        if had_error.into_err() {
            self.set_error(cur_item, STATE);
            return Err(());
        }

        let mut had_error = ErrorSignal::new();
        passes::types::define_struct(stores, self, &mut had_error, cur_item);
        if had_error.into_err() {
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
        if self.ensure_state_deps(stores, cur_item, STATE)?.done() {
            return Ok(());
        };

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
                            SimulatorValue::Bool(_) | SimulatorValue::EnumValue { .. } => val,
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
        if self.ensure_state_deps(stores, cur_item, STATE)?.done() {
            return Ok(());
        };

        let _span = debug_span!("IdentBody").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::ident_resolution::resolve_body(stores, self, &mut had_error, cur_item);
        if had_error.into_err() {
            self.set_error(cur_item, STATE);
            Err(())
        } else {
            self.set_passed(cur_item, STATE);
            Ok(())
        }
    }

    pub fn ensure_ident_resolved_scope(
        &mut self,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        const STATE: PassState = PassState::IdentResolvedScope;
        if self.ensure_state_deps(stores, cur_item, STATE)?.done() {
            return Ok(());
        };

        let _span = debug_span!("IdentScope").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::ident_resolution::resolve_idents_in_scope(stores, self, &mut had_error, cur_item);
        if had_error.into_err() {
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
        if self.ensure_state_deps(stores, cur_item, STATE)?.done() {
            return Ok(());
        };

        let _span = debug_span!("IdentSig").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::ident_resolution::resolve_signature(stores, self, &mut had_error, cur_item);
        if had_error.into_err() {
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
        if self.ensure_state_deps(stores, cur_item, STATE)?.done() {
            return Ok(());
        };

        let _span = debug_span!("PartialType").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::type_resolution::resolve_signature(stores, self, &mut had_error, cur_item);
        passes::type_resolution::resolve_body(stores, self, &mut had_error, cur_item);
        if had_error.into_err() {
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
        if self.ensure_state_deps(stores, cur_item, STATE)?.done() {
            return Ok(());
        };

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
        if had_error.into_err() {
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
        if self.ensure_state_deps(stores, cur_item, STATE)?.done() {
            return Ok(());
        };

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
        if self.ensure_state_deps(stores, cur_item, STATE)?.done() {
            return Ok(());
        };

        let _span = debug_span!("TypeBody").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::type_resolution::resolve_body(stores, self, &mut had_error, cur_item);
        if had_error.into_err() {
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
        if self.ensure_state_deps(stores, cur_item, STATE)?.done() {
            return Ok(());
        };

        let _span = debug_span!("TypeSig").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::type_resolution::resolve_signature(stores, self, &mut had_error, cur_item);
        if had_error.into_err() {
            self.set_error(cur_item, STATE);
            Err(())
        } else {
            self.set_passed(cur_item, STATE);
            Ok(())
        }
    }

    fn ensure_validity_check(&mut self, stores: &mut Stores, cur_item: ItemId) -> Result<(), ()> {
        const STATE: PassState = PassState::ValidityCheck;
        if self.ensure_state_deps(stores, cur_item, STATE)?.done() {
            return Ok(());
        };

        let _span = debug_span!("ValidityCheck").entered();
        trace!(
            name = stores.get_symbol_name(cur_item),
            id = ?cur_item,
        );

        let mut had_error = ErrorSignal::new();
        passes::validity::validity_check(stores, self, &mut had_error, cur_item);
        if had_error.into_err() {
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
                PassState::ValidityCheck,
                PassState::IdentResolvedScope,
            ]
            .as_slice(),
            ItemKind::StructDef => &[
                PassState::ValidityCheck,
                PassState::IdentResolvedScope,
                PassState::DefineStructs,
            ],
            ItemKind::Enum => &[
                PassState::ValidityCheck,
                PassState::IdentResolvedScope,
                PassState::DeclareEnums,
            ],
            ItemKind::Variable | ItemKind::FunctionDecl => &[
                PassState::BuildNames,
                PassState::ValidityCheck,
                PassState::TypeResolvedSignature,
            ],
            // Type resolution happens after the generic function is instantiated.
            ItemKind::GenericFunction => {
                &[PassState::ValidityCheck, PassState::PartiallyTypeResolved]
            }
            ItemKind::Assert => &[PassState::ValidityCheck, PassState::CheckAsserts],
            ItemKind::Const => &[PassState::ValidityCheck, PassState::EvaluatedConstsAsserts],
            ItemKind::Function { .. } => &[
                PassState::BuildNames,
                PassState::ValidityCheck,
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

    if had_error.into_err() {
        Err(eyre!("Error during static analysis"))
    } else {
        Ok(())
    }
}
