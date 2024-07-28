use std::collections::VecDeque;

use ariadne::{Color, Label};
use color_eyre::{eyre::eyre, Result};
use flagset::{flags, FlagSet};
use hashbrown::HashMap;
use prettytable::{row, Table};
use tracing::{debug_span, trace};

use crate::{
    context::{Context, ItemHeader, ItemId, ItemKind, LangItem},
    diagnostics,
    error_signal::ErrorSignal,
    option::OptionExt,
    simulate::{simulate_execute_program, SimulatorValue},
    stores::types::TypeKind,
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
    }
}

impl PassState {
    fn get_function(
        self,
    ) -> fn(&mut PassContext, &mut Context, &mut Stores, ItemId) -> Result<(), ()> {
        match self {
            PassState::IdentResolvedSignature => PassContext::ensure_ident_resolved_signature,
            PassState::IdentResolvedBody => PassContext::ensure_ident_resolved_body,
            PassState::DeclareStructs => PassContext::ensure_declare_structs,
            PassState::DefineStructs => PassContext::ensure_define_structs,
            PassState::SelfContainingStruct => PassContext::ensure_self_containing_structs,
            PassState::TypeResolvedSignature => PassContext::ensure_type_resolved_signature,
            PassState::TypeResolvedBody => PassContext::ensure_type_resolved_body,
            PassState::BuildNames => PassContext::ensure_build_names,
            PassState::CyclicRefCheckBody => PassContext::ensure_cyclic_ref_check_body,
            PassState::TerminalBlockCheckBody => PassContext::ensure_terminal_block_check_body,
            PassState::StackAndTypeCheckedBody => PassContext::ensure_stack_and_type_checked_body,
            PassState::ConstPropBody => PassContext::ensure_const_prop_body,
            PassState::EvaluatedConstsAsserts => PassContext::ensure_evaluated_consts_asserts,
            PassState::CheckAsserts => PassContext::ensure_check_asserts,
            PassState::PartiallyTypeResolved => PassContext::ensure_partially_resolve_types,
        }
    }

    fn get_deps(self) -> (FlagSet<PassState>, &'static [PassState]) {
        use PassState::*;
        match self {
            IdentResolvedSignature | IdentResolvedBody | TerminalBlockCheckBody | BuildNames => {
                (FlagSet::default(), &[])
            }
            SelfContainingStruct | DeclareStructs | TypeResolvedSignature => {
                (IdentResolvedSignature.into(), &[IdentResolvedSignature])
            }
            PartiallyTypeResolved => (
                IdentResolvedBody | IdentResolvedSignature,
                &[IdentResolvedBody, IdentResolvedSignature],
            ),
            DefineStructs => (DeclareStructs.into(), &[DeclareStructs]),
            TypeResolvedBody | CyclicRefCheckBody => {
                (IdentResolvedBody.into(), &[IdentResolvedBody])
            }
            StackAndTypeCheckedBody => (
                TypeResolvedSignature | TypeResolvedBody | TerminalBlockCheckBody,
                &[
                    TypeResolvedSignature,
                    TypeResolvedBody,
                    TerminalBlockCheckBody,
                ],
            ),
            ConstPropBody => (StackAndTypeCheckedBody.into(), &[StackAndTypeCheckedBody]),
            EvaluatedConstsAsserts => (
                CyclicRefCheckBody | ConstPropBody,
                &[CyclicRefCheckBody, ConstPropBody],
            ),
            CheckAsserts => (EvaluatedConstsAsserts.into(), &[EvaluatedConstsAsserts]),
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct ItemState {
    state: FlagSet<PassState>,
    had_error: bool,
}

impl ItemState {
    fn new() -> Self {
        Self {
            state: FlagSet::default(),
            had_error: false,
        }
    }
}

pub struct PassContext {
    states: HashMap<ItemId, ItemState>,
    queue: VecDeque<ItemId>,
    defined_generic_structs: bool,
    stack_stats_table: Table,
}

impl PassContext {
    fn new(i: impl Iterator<Item = ItemHeader>) -> Self {
        let (states, queue) = i.map(|i| ((i.id, ItemState::new()), i.id)).unzip();
        Self {
            states,
            queue,
            defined_generic_structs: false,
            stack_stats_table: Table::new(),
        }
    }

    fn set_error(&mut self, cur_item: ItemId) {
        self.states.get_mut(&cur_item).unwrap().had_error = true;
    }

    fn set_state(&mut self, cur_item: ItemId, new_state: PassState) {
        let cur_item_state = self.states.get_mut(&cur_item).unwrap();
        cur_item_state.state |= new_state;
    }

    pub fn add_new_item(&mut self, id: ItemId, base_id: ItemId, new_state: FlagSet<PassState>) {
        self.queue.push_back(id);
        let mut new_state_info = self.states[&base_id];
        new_state_info.state = new_state;
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
    ($self:expr, $ctx:expr, $stores:expr, $cur_item:expr, $this_state:expr) => {
        let cur_item_state = $self.states[&$cur_item];
        if cur_item_state.state.contains($this_state) {
            return Ok(());
        }
        let (dep_flags, mut dep_list) = $this_state.get_deps();
        loop {
            let cur_item_state = $self.states[&$cur_item];
            if cur_item_state.state.contains(dep_flags) {
                break;
            }
            if cur_item_state.had_error {
                return Err(());
            }

            let [first, rest @ ..] = dep_list else { break };
            dep_list = rest;
            first.get_function()($self, $ctx, $stores, $cur_item)?;
        }
    };
}

impl PassContext {
    pub fn ensure_ident_resolved_signature(
        &mut self,
        ctx: &mut Context,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        ensure_state_deps!(
            self,
            ctx,
            stores,
            cur_item,
            PassState::IdentResolvedSignature
        );

        let _span = debug_span!(stringify!(ensure_ident_resolved_signature));
        trace!(
            name = stores.strings.get_symbol_name(ctx, cur_item),
            id = ?cur_item,
            "IdentSig"
        );

        let mut had_error = ErrorSignal::new();
        passes::ident_resolution::resolve_signature(ctx, stores, self, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item);
            Err(())
        } else {
            self.set_state(cur_item, PassState::IdentResolvedSignature);
            Ok(())
        }
    }

    pub fn ensure_declare_structs(
        &mut self,
        ctx: &mut Context,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        ensure_state_deps!(self, ctx, stores, cur_item, PassState::DeclareStructs);

        let _span = debug_span!(stringify!(ensure_declare_structs));
        trace!(
            name = stores.strings.get_symbol_name(ctx, cur_item),
            id = ?cur_item,
            "DeclStruct",
        );

        let mut had_error = ErrorSignal::new();
        passes::structs::declare_struct(ctx, stores, self, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item);
            Err(())
        } else {
            self.set_state(cur_item, PassState::DeclareStructs);
            Ok(())
        }
    }

    fn ensure_define_structs(
        &mut self,
        ctx: &mut Context,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        ensure_state_deps!(self, ctx, stores, cur_item, PassState::DefineStructs);

        let _span = debug_span!(stringify!(ensure_define_structs));
        trace!(
            name = stores.strings.get_symbol_name(ctx, cur_item),
            id = ?cur_item,
            "DefStruct",
        );

        let mut had_error = ErrorSignal::new();
        // Non-generic structs require the generic structs to be defined, incase any of them depend on a generic struct.
        // TODO: Make this use the pass manager to avoid this bit.
        let struct_def = ctx.nrir().get_struct(cur_item);
        if struct_def.generic_params.is_empty() && !self.defined_generic_structs {
            let all_generic_structs = ctx.get_generic_structs().to_owned();
            for gsi in all_generic_structs {
                if self.ensure_define_structs(ctx, stores, gsi).is_err() {
                    had_error.set();
                }
            }
            self.defined_generic_structs = true;
        }

        if had_error.into_bool() {
            self.set_error(cur_item);
            return Err(());
        }

        let mut had_error = ErrorSignal::new();
        passes::structs::define_struct(ctx, stores, self, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item);
            Err(())
        } else {
            self.set_state(cur_item, PassState::DefineStructs);
            Ok(())
        }
    }

    fn ensure_self_containing_structs(
        &mut self,
        ctx: &mut Context,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        ensure_state_deps!(self, ctx, stores, cur_item, PassState::SelfContainingStruct);

        let _span = debug_span!(stringify!(ensure_self_containing_structs));
        trace!(
            name = stores.strings.get_symbol_name(ctx, cur_item),
            id = ?cur_item,
            "SelfContainingStruct",
        );

        let mut had_error = ErrorSignal::new();
        passes::cycles::check_invalid_cycles(ctx, stores, self, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item);
            Err(())
        } else {
            self.set_state(cur_item, PassState::SelfContainingStruct);
            Ok(())
        }
    }

    pub fn ensure_ident_resolved_body(
        &mut self,
        ctx: &mut Context,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        ensure_state_deps!(self, ctx, stores, cur_item, PassState::IdentResolvedBody);

        let _span = debug_span!(stringify!(ensure_ident_resolved_body));
        trace!(
            name = stores.strings.get_symbol_name(ctx, cur_item),
            id = ?cur_item,
            "IdentBody",
        );

        let mut had_error = ErrorSignal::new();
        passes::ident_resolution::resolve_body(ctx, stores, self, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item);
            Err(())
        } else {
            self.set_state(cur_item, PassState::IdentResolvedBody);
            Ok(())
        }
    }

    pub fn ensure_partially_resolve_types(
        &mut self,
        ctx: &mut Context,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        ensure_state_deps!(
            self,
            ctx,
            stores,
            cur_item,
            PassState::PartiallyTypeResolved
        );

        let _span = debug_span!(stringify!(ensure_partially_resolve_types));
        trace!(
            name = stores.strings.get_symbol_name(ctx, cur_item),
            id = ?cur_item,
            "PartialType",
        );

        let mut had_error = ErrorSignal::new();
        passes::type_resolution::resolve_signature(ctx, stores, self, &mut had_error, cur_item);
        passes::type_resolution::resolve_body(ctx, stores, self, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item);
            Err(())
        } else {
            self.set_state(cur_item, PassState::PartiallyTypeResolved);
            Ok(())
        }
    }
    pub fn ensure_type_resolved_signature(
        &mut self,
        ctx: &mut Context,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        ensure_state_deps!(
            self,
            ctx,
            stores,
            cur_item,
            PassState::TypeResolvedSignature
        );

        let _span = debug_span!(stringify!(ensure_ident_resolved_body));
        trace!(
            name = stores.strings.get_symbol_name(ctx, cur_item),
            id = ?cur_item,
            "TypeSig",
        );

        let mut had_error = ErrorSignal::new();
        passes::type_resolution::resolve_signature(ctx, stores, self, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item);
            Err(())
        } else {
            self.set_state(cur_item, PassState::TypeResolvedSignature);
            Ok(())
        }
    }

    pub fn ensure_build_names(
        &mut self,
        ctx: &mut Context,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        ensure_state_deps!(self, ctx, stores, cur_item, PassState::BuildNames);

        let _span = debug_span!(stringify!(ensure_build_names));
        trace!(
            name = stores.strings.get_symbol_name(ctx, cur_item),
            id = ?cur_item,
            "BuildNames",
        );

        stores.build_friendly_name(ctx, self, cur_item);
        stores.build_mangled_name(ctx, self, cur_item);
        self.set_state(cur_item, PassState::BuildNames);
        Ok(())
    }

    fn ensure_type_resolved_body(
        &mut self,
        ctx: &mut Context,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        ensure_state_deps!(self, ctx, stores, cur_item, PassState::TypeResolvedBody);

        let _span = debug_span!(stringify!(ensure_ident_resolved_body));
        trace!(
            name = stores.strings.get_symbol_name(ctx, cur_item),
            id = ?cur_item,
            "TypeBody",
        );

        let mut had_error = ErrorSignal::new();
        passes::type_resolution::resolve_body(ctx, stores, self, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item);
            Err(())
        } else {
            self.set_state(cur_item, PassState::TypeResolvedBody);
            Ok(())
        }
    }

    fn ensure_cyclic_ref_check_body(
        &mut self,
        ctx: &mut Context,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        ensure_state_deps!(self, ctx, stores, cur_item, PassState::CyclicRefCheckBody);

        let _span = debug_span!(stringify!(ensure_ident_resolved_body));
        trace!(
            name = stores.strings.get_symbol_name(ctx, cur_item),
            id = ?cur_item,
            "CycleCheck",
        );

        let mut had_error = ErrorSignal::new();
        passes::cycles::check_invalid_cycles(ctx, stores, self, &mut had_error, cur_item);
        if had_error.into_bool() {
            self.set_error(cur_item);
            Err(())
        } else {
            self.set_state(cur_item, PassState::CyclicRefCheckBody);
            Ok(())
        }
    }

    fn ensure_terminal_block_check_body(
        &mut self,
        ctx: &mut Context,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        ensure_state_deps!(
            self,
            ctx,
            stores,
            cur_item,
            PassState::TerminalBlockCheckBody
        );

        let _span = debug_span!(stringify!(ensure_ident_resolved_body));
        trace!(
            name = stores.strings.get_symbol_name(ctx, cur_item),
            id = ?cur_item,
            "TerminalCheck",
        );

        passes::terminal::determine_terminal_blocks(ctx, stores, cur_item);
        self.set_state(cur_item, PassState::TerminalBlockCheckBody);
        Ok(())
    }

    fn ensure_stack_and_type_checked_body(
        &mut self,
        ctx: &mut Context,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        ensure_state_deps!(
            self,
            ctx,
            stores,
            cur_item,
            PassState::StackAndTypeCheckedBody
        );

        let _span = debug_span!(stringify!(ensure_ident_resolved_body));
        trace!(
            name = stores.strings.get_symbol_name(ctx, cur_item),
            id = ?cur_item,
            "StackTypeCheck",
        );

        let mut had_error = ErrorSignal::new();
        let stats =
            passes::stack_type_check::analyze_item(ctx, stores, self, &mut had_error, cur_item);

        self.stack_stats_table.add_row(row![
            stores.strings.get_symbol_name(ctx, cur_item),
            stats.max_stack_depth,
            stats.unique_item_count
        ]);
        if had_error.into_bool() {
            self.set_error(cur_item);
            Err(())
        } else {
            self.set_state(cur_item, PassState::StackAndTypeCheckedBody);
            Ok(())
        }
    }

    fn ensure_const_prop_body(
        &mut self,
        ctx: &mut Context,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        ensure_state_deps!(self, ctx, stores, cur_item, PassState::ConstPropBody);

        let _span = debug_span!(stringify!(ensure_ident_resolved_body));
        trace!(
            name = stores.strings.get_symbol_name(ctx, cur_item),
            id = ?cur_item,
            "ConstProp",
        );

        let mut had_error = ErrorSignal::new();
        passes::const_prop::analyze_item(ctx, stores, self, &mut had_error, cur_item);

        if had_error.into_bool() {
            self.set_error(cur_item);
            Err(())
        } else {
            self.set_state(cur_item, PassState::ConstPropBody);
            Ok(())
        }
    }

    pub fn ensure_evaluated_consts_asserts(
        &mut self,
        ctx: &mut Context,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        ensure_state_deps!(
            self,
            ctx,
            stores,
            cur_item,
            PassState::EvaluatedConstsAsserts
        );

        let _span = debug_span!(stringify!(ensure_ident_resolved_body));
        trace!(
            name = stores.strings.get_symbol_name(ctx, cur_item),
            id = ?cur_item,
            "EvaluateConstAsserts",
        );

        let result = simulate_execute_program(ctx, stores, self, cur_item);
        match result {
            Ok(stack) => {
                let type_sig = ctx.trir().get_item_signature(cur_item);
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

                ctx.set_consts(cur_item, const_vals);

                self.set_state(cur_item, PassState::EvaluatedConstsAsserts);
                Ok(())
            }
            Err(_) => {
                self.set_error(cur_item);
                Err(())
            }
        }
    }

    fn ensure_check_asserts(
        &mut self,
        ctx: &mut Context,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        ensure_state_deps!(self, ctx, stores, cur_item, PassState::CheckAsserts);

        let _span = debug_span!(stringify!(ensure_check_asserts));
        trace!(
            name = stores.strings.get_symbol_name(ctx, cur_item),
            id = ?cur_item,
            "CheckAsserts",
        );

        // Type check and const prop ensure this value exists.
        let Some([SimulatorValue::Bool(assert_is_true)]) = ctx.get_consts(cur_item) else {
            unreachable!()
        };

        if !assert_is_true {
            let item_header = ctx.get_item_header(cur_item);
            diagnostics::emit_error(
                stores,
                item_header.name.location,
                "assert failure",
                [Label::new(item_header.name.location)
                    .with_color(Color::Red)
                    .with_message("evaluated to false")],
                None,
            );

            self.set_error(cur_item);
            Err(())
        } else {
            self.set_state(cur_item, PassState::CheckAsserts);
            Ok(())
        }
    }

    fn ensure_done(
        &mut self,
        ctx: &mut Context,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        let needed_states = match ctx.get_item_header(cur_item).kind {
            ItemKind::Module => [PassState::IdentResolvedSignature].as_slice(),
            ItemKind::StructDef => &[PassState::SelfContainingStruct, PassState::DefineStructs],
            ItemKind::Variable => &[PassState::BuildNames, PassState::TypeResolvedSignature],
            // Type resolution happens after the generic function is instantiated.
            ItemKind::GenericFunction => &[
                PassState::PartiallyTypeResolved,
                PassState::IdentResolvedBody,
            ],
            ItemKind::Assert => &[PassState::CheckAsserts],
            ItemKind::Const => &[PassState::EvaluatedConstsAsserts],
            ItemKind::Function => &[PassState::BuildNames, PassState::ConstPropBody],
        };

        let as_flags = needed_states.iter().fold(FlagSet::default(), |a, b| a | *b);
        let cur_state = self.states[&cur_item];
        if cur_state.state.contains(as_flags) {
            return Ok(());
        }
        if cur_state.had_error {
            return Err(());
        }

        for state in needed_states {
            state.get_function()(self, ctx, stores, cur_item)?;
        }

        Ok(())
    }
}

pub fn run(ctx: &mut Context, stores: &mut Stores, print_stack_stats: bool) -> Result<()> {
    let _span = debug_span!(stringify!(pass_manager)).entered();
    let mut pass_ctx = PassContext::new(ctx.get_all_items());
    let mut had_error = ErrorSignal::new();

    // Need to make sure the String type is declared before anything else.
    let string_id = ctx.get_lang_items()[&LangItem::String];
    if pass_ctx
        .ensure_declare_structs(ctx, stores, string_id)
        .is_err()
    {
        panic!("ICE: Failed to declared String type");
    };

    while let Some(cur_item_id) = pass_ctx.next_item() {
        if pass_ctx.ensure_done(ctx, stores, cur_item_id).is_err() {
            had_error.set();
        }
    }

    if print_stack_stats {
        println!("\n{}", pass_ctx.stack_stats_table);
    }

    if had_error.into_bool() {
        Err(eyre!("Error during static analysis"))
    } else {
        Ok(())
    }
}
