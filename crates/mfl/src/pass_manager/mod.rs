use std::collections::VecDeque;

use color_eyre::{eyre::eyre, Result};
use flagset::{flags, FlagSet};
use hashbrown::HashMap;
use tracing::{debug_span, trace};

use crate::{
    context::{Context, ItemHeader, ItemId, ItemKind},
    option::OptionExt,
    Stores,
};

mod passes;
pub mod static_analysis;

flags! {
    enum PassState: u8 {
        IdentResolvedSignature,
        IdentResolvedBody,
        DeclareStructs,
        DefineStructs,
        TypeResolvedSignature,
        TypeResolvedBody,
        CyclicRefCheckBody,
        TerminalBlockCheckBody,
        StackAndTypeCheckedBody,
        ConstPropBody,
        EvaluatedConstsAsserts,
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
            PassState::TypeResolvedSignature => PassContext::ensure_type_resolved_signature,
            PassState::TypeResolvedBody => PassContext::ensure_type_resolved_body,
            PassState::CyclicRefCheckBody => PassContext::ensure_cyclic_ref_check_body,
            PassState::TerminalBlockCheckBody => PassContext::ensure_terminal_block_check_body,
            PassState::StackAndTypeCheckedBody => PassContext::ensure_stack_and_type_checked_body,
            PassState::ConstPropBody => PassContext::ensure_const_prop_body,
            PassState::EvaluatedConstsAsserts => PassContext::ensure_evaluated_consts_asserts,
        }
    }

    fn get_deps(self) -> (FlagSet<PassState>, &'static [PassState]) {
        use PassState::*;
        match self {
            IdentResolvedSignature => (FlagSet::default(), &[]),
            IdentResolvedBody => (FlagSet::default(), &[]),
            DeclareStructs => (IdentResolvedSignature.into(), &[IdentResolvedSignature]),
            DefineStructs => (DeclareStructs.into(), &[DeclareStructs]),
            TypeResolvedSignature => (IdentResolvedSignature.into(), &[IdentResolvedSignature]),
            TypeResolvedBody => (IdentResolvedBody.into(), &[IdentResolvedBody]),
            CyclicRefCheckBody => (IdentResolvedBody.into(), &[IdentResolvedBody]),
            // Technically, this is only needed because the block terminal flags are in the AST.
            TerminalBlockCheckBody => (TypeResolvedBody.into(), &[TypeResolvedBody]),
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
}

impl PassContext {
    fn new(i: impl Iterator<Item = ItemHeader>) -> Self {
        let (states, queue) = i.map(|i| ((i.id, ItemState::new()), i.id)).unzip();
        Self {
            states,
            queue,
            defined_generic_structs: false,
        }
    }

    fn set_error(&mut self, cur_item: ItemId) {
        self.states.get_mut(&cur_item).unwrap().had_error = true;
    }

    fn set_state(&mut self, cur_item: ItemId, new_state: PassState) {
        let cur_item_state = self.states.get_mut(&cur_item).unwrap();
        cur_item_state.state |= new_state;
    }

    pub fn add_new_item(&mut self, id: ItemId, base_id: ItemId) {
        let new_state_info = self.states[&base_id];
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
    fn ensure_ident_resolved_signature(
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

        let mut had_error = false;
        passes::ident_resolution::resolve_signature(ctx, stores, &mut had_error, cur_item);
        if !had_error {
            self.set_state(cur_item, PassState::IdentResolvedSignature);
            Ok(())
        } else {
            self.set_error(cur_item);
            Err(())
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

        let mut had_error = false;
        passes::structs::declare_struct(ctx, stores, &mut had_error, cur_item);
        if !had_error {
            self.set_state(cur_item, PassState::DeclareStructs);
            Ok(())
        } else {
            self.set_error(cur_item);
            Err(())
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

        let mut had_error = false;
        // Non-generic structs require the generic structs to be defined, incase any of them depend on a generic struct.
        // TODO: Make this use the pass manager to avoid this bit.
        let struct_def = ctx.nrir().get_struct(cur_item);
        if struct_def.generic_params.is_none() && !self.defined_generic_structs {
            let all_generic_structs = ctx.get_generic_structs().to_owned();
            for gsi in all_generic_structs {
                had_error |= self.ensure_define_structs(ctx, stores, gsi).is_err();
            }
            self.defined_generic_structs = true;
        }

        if had_error {
            self.set_error(cur_item);
            return Err(());
        }

        passes::structs::define_struct(ctx, stores, &mut had_error, cur_item);
        if !had_error {
            self.set_state(cur_item, PassState::DefineStructs);
            Ok(())
        } else {
            self.set_error(cur_item);
            Err(())
        }
    }

    fn ensure_ident_resolved_body(
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

        let mut had_error = false;
        passes::ident_resolution::resolve_body(ctx, stores, &mut had_error, cur_item);
        if !had_error {
            self.set_state(cur_item, PassState::IdentResolvedBody);
            Ok(())
        } else {
            self.set_error(cur_item);
            Err(())
        }
    }

    fn ensure_type_resolved_signature(
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

        let mut had_error = false;
        passes::type_resolution::resolve_signature(ctx, stores, self, &mut had_error, cur_item);
        if !had_error {
            self.set_state(cur_item, PassState::TypeResolvedSignature);
            Ok(())
        } else {
            self.set_error(cur_item);
            Err(())
        }
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

        let mut had_error = false;
        passes::type_resolution::resolve_body(ctx, stores, self, &mut had_error, cur_item);
        if !had_error {
            self.set_state(cur_item, PassState::TypeResolvedBody);
            Ok(())
        } else {
            self.set_error(cur_item);
            Err(())
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

        let mut had_error = false;
        passes::cycles::check_invalid_cycles(ctx, stores, self, &mut had_error, cur_item);
        if !had_error {
            self.set_state(cur_item, PassState::CyclicRefCheckBody);
            Ok(())
        } else {
            self.set_error(cur_item);
            Err(())
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

        passes::terminal::determine_terminal_blocks(ctx, cur_item);
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

        let mut had_error = false;
        passes::stack_type_check::analyze_item(ctx, stores, self, &mut had_error, cur_item);
        if !had_error {
            self.set_state(cur_item, PassState::StackAndTypeCheckedBody);
            Ok(())
        } else {
            self.set_error(cur_item);
            Err(())
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

        todo!();
        self.set_state(cur_item, PassState::ConstPropBody);
        Ok(())
    }

    fn ensure_evaluated_consts_asserts(
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

        todo!();
        self.set_state(cur_item, PassState::EvaluatedConstsAsserts);
        Ok(())
    }

    fn ensure_done(
        &mut self,
        ctx: &mut Context,
        stores: &mut Stores,
        cur_item: ItemId,
    ) -> Result<(), ()> {
        let needed_states = match ctx.get_item_header(cur_item).kind {
            ItemKind::Module => [PassState::IdentResolvedSignature].as_slice(),
            ItemKind::StructDef => &[PassState::DefineStructs],
            ItemKind::Memory => &[PassState::TypeResolvedSignature],
            // Type resolution happens after the generic function is instantiated.
            ItemKind::GenericFunction => &[
                PassState::IdentResolvedSignature,
                PassState::IdentResolvedBody,
            ],
            ItemKind::Assert | ItemKind::Const => &[PassState::EvaluatedConstsAsserts],
            ItemKind::Function => &[PassState::ConstPropBody],
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

pub fn run(ctx: &mut Context, stores: &mut Stores) -> Result<()> {
    let _span = debug_span!(stringify!(pass_manager)).entered();
    let mut pass_ctx = PassContext::new(ctx.get_all_items());
    let mut had_error = false;

    while let Some(cur_item_id) = pass_ctx.next_item() {
        had_error |= pass_ctx.ensure_done(ctx, stores, cur_item_id).is_err();
    }

    if had_error {
        Err(eyre!("Error during static analysis"))
    } else {
        Ok(())
    }
}