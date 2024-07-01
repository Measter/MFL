use std::collections::VecDeque;

use color_eyre::{eyre::eyre, Result};
use hashbrown::HashMap;

use crate::{
    context::{Context, ItemHeader, ItemId, ItemKind},
    option::OptionExt,
    Stores,
};

mod passes;
pub mod static_analysis;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PassState {
    Initial,
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
    Done,
}

#[derive(Debug, Clone, Copy)]
struct ItemState {
    state: PassState,
    had_error: bool,
}

impl ItemState {
    fn new() -> Self {
        Self {
            state: PassState::Initial,
            had_error: false,
        }
    }
}

pub struct PassContext {
    states: HashMap<ItemId, ItemState>,
    queue: VecDeque<ItemId>,
}

impl PassContext {
    fn new(i: impl Iterator<Item = ItemHeader>) -> Self {
        let (states, queue) = i.map(|i| ((i.id, ItemState::new()), i.id)).unzip();
        Self { states, queue }
    }

    fn get_state(&self, cur_item: ItemId) -> PassState {
        self.states[&cur_item].state
    }

    fn set_error(&mut self, cur_item: ItemId) {
        self.states.get_mut(&cur_item).unwrap().had_error = true;
    }

    fn set_state(&mut self, cur_item: ItemId, new_state: PassState) {
        let cur_item_state = self.states.get_mut(&cur_item).unwrap();
        cur_item_state.state = new_state;
    }

    pub fn add_new_item(&mut self, id: ItemId, initial_state: PassState, base_id: ItemId) {
        let mut new_state_info = self.states[&base_id].clone();
        new_state_info.state = initial_state;
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

macro_rules! state_check {
    ($self:expr, $expected_state:expr, $prev_function:ident, $ctx: expr, $cur_item:expr) => {
        let cur_state = $self.states[&$cur_item];
        if cur_state.state >= $expected_state {
            return true;
        }
        if cur_state.had_error || !$self.$prev_function($ctx, $cur_item) {
            return false;
        }
    };
}

impl PassContext {
    fn ensure_initial(&mut self, _: &mut Context, _: ItemId) -> bool {
        // This is just here to keep the pattern going.
        true
    }

    fn ensure_declare_structs(&mut self, ctx: &mut Context, cur_item: ItemId) -> bool {
        state_check!(
            self,
            PassState::DeclareStructs,
            ensure_ident_resolved_signature,
            ctx,
            cur_item
        );

        todo!();
        self.set_state(cur_item, PassState::DeclareStructs);
        true
    }

    fn ensure_define_structs(&mut self, ctx: &mut Context, cur_item: ItemId) -> bool {
        state_check!(
            self,
            PassState::DefineStructs,
            ensure_declare_structs,
            ctx,
            cur_item
        );

        todo!();
        self.set_state(cur_item, PassState::DefineStructs);
        true
    }

    fn ensure_ident_resolved_signature(&mut self, ctx: &mut Context, cur_item: ItemId) -> bool {
        state_check!(
            self,
            PassState::IdentResolvedSignature,
            ensure_initial,
            ctx,
            cur_item
        );

        todo!();
        self.set_state(cur_item, PassState::IdentResolvedSignature);
        true
    }

    fn ensure_ident_resolved_body(&mut self, ctx: &mut Context, cur_item: ItemId) -> bool {
        state_check!(
            self,
            PassState::IdentResolvedBody,
            ensure_ident_resolved_signature,
            ctx,
            cur_item
        );

        todo!();
        self.set_state(cur_item, PassState::IdentResolvedBody);
        true
    }

    fn ensure_type_resolved_signature(&mut self, ctx: &mut Context, cur_item: ItemId) -> bool {
        state_check!(
            self,
            PassState::TypeResolvedSignature,
            ensure_ident_resolved_body,
            ctx,
            cur_item
        );

        todo!();
        self.set_state(cur_item, PassState::TypeResolvedSignature);
        true
    }

    fn ensure_type_resolved_body(&mut self, ctx: &mut Context, cur_item: ItemId) -> bool {
        state_check!(
            self,
            PassState::TypeResolvedBody,
            ensure_type_resolved_signature,
            ctx,
            cur_item
        );

        todo!();
        self.set_state(cur_item, PassState::TypeResolvedBody);
        true
    }

    fn ensure_cyclic_ref_check_body(&mut self, ctx: &mut Context, cur_item: ItemId) -> bool {
        state_check!(
            self,
            PassState::CyclicRefCheckBody,
            ensure_type_resolved_body,
            ctx,
            cur_item
        );

        todo!();
        self.set_state(cur_item, PassState::CyclicRefCheckBody);
        true
    }

    fn ensure_terminal_block_check_body(&mut self, ctx: &mut Context, cur_item: ItemId) -> bool {
        state_check!(
            self,
            PassState::TerminalBlockCheckBody,
            ensure_cyclic_ref_check_body,
            ctx,
            cur_item
        );

        todo!();
        self.set_state(cur_item, PassState::TerminalBlockCheckBody);
        true
    }

    fn ensure_stack_and_type_checked_body(&mut self, ctx: &mut Context, cur_item: ItemId) -> bool {
        state_check!(
            self,
            PassState::StackAndTypeCheckedBody,
            ensure_terminal_block_check_body,
            ctx,
            cur_item
        );

        todo!();
        self.set_state(cur_item, PassState::StackAndTypeCheckedBody);
        true
    }

    fn ensure_const_prop_body(&mut self, ctx: &mut Context, cur_item: ItemId) -> bool {
        state_check!(
            self,
            PassState::ConstPropBody,
            ensure_stack_and_type_checked_body,
            ctx,
            cur_item
        );

        todo!();
        self.set_state(cur_item, PassState::ConstPropBody);
        true
    }

    fn ensure_evaluated_consts_asserts(&mut self, ctx: &mut Context, cur_item: ItemId) -> bool {
        state_check!(
            self,
            PassState::EvaluatedConstsAsserts,
            ensure_const_prop_body,
            ctx,
            cur_item
        );

        todo!();

        self.set_state(cur_item, PassState::EvaluatedConstsAsserts);
        true
    }

    fn ensure_done(&mut self, ctx: &mut Context, cur_item: ItemId) -> bool {
        let cur_state = self.states[&cur_item];
        if cur_state.state >= PassState::Done {
            return true;
        }
        if cur_state.had_error {
            return false;
        }

        // Let's just short-circuit to the specific previous state for this one.
        let needed_prev_state = match ctx.get_item_header(cur_item).kind {
            ItemKind::Module => PassState::IdentResolvedSignature,
            ItemKind::StructDef => PassState::DefineStructs,
            ItemKind::Memory => PassState::TypeResolvedSignature,
            ItemKind::Function | ItemKind::GenericFunction | ItemKind::Assert | ItemKind::Const => {
                PassState::EvaluatedConstsAsserts
            }
        };

        let prev_function: fn(&mut PassContext, &mut Context, ItemId) -> bool =
            match needed_prev_state {
                PassState::IdentResolvedSignature => PassContext::ensure_ident_resolved_signature,
                PassState::DefineStructs => PassContext::ensure_define_structs,
                PassState::TypeResolvedSignature => PassContext::ensure_type_resolved_signature,
                PassState::ConstPropBody => PassContext::ensure_const_prop_body,
                PassState::EvaluatedConstsAsserts => PassContext::ensure_evaluated_consts_asserts,

                _ => panic!("ICE: unexpected previous state: {needed_prev_state:?}"),
            };

        prev_function(self, ctx, cur_item);

        // no actual work to be done in this one.
        self.set_state(cur_item, PassState::Done);

        true
    }
}

pub fn run(ctx: &mut Context, stores: &mut Stores) -> Result<()> {
    let mut pass_ctx = PassContext::new(ctx.get_all_items());
    let mut had_error = false;

    while let Some(cur_item_id) = pass_ctx.next_item() {
        had_error |= pass_ctx.ensure_done(ctx, cur_item_id);

        // match pass_ctx.can_progress(cur_item_id) {
        //     CanProgress::No => {
        //         // We're still waiting on something else to progress.
        //         pass_ctx.enqueue(cur_item_id);
        //     }
        //     CanProgress::Error => {
        //         // Whatever we were waiting for had an error before it could get to the
        //         // stage we required. We need to propagate the error flag so our dependencies
        //         // know we can't progress.
        //         pass_ctx.set_had_error(cur_item_id);
        //     }
        //     CanProgress::Yes => {
        //         let cur_item_state = pass_ctx.get_state(cur_item_id);
        //         let pass_func = match cur_item_state {
        //             PassState::IdentResolvedSignature => {
        //                 passes::ident_resolution::resolve_signature
        //             }
        //             PassState::IdentResolvedBody => passes::ident_resolution::resolve_body,

        //             PassState::DeclareStructs => passes::structs::declare_struct,
        //             PassState::DefineStructs => passes::structs::define_struct,

        //             PassState::TypeResolvedSignature => passes::type_resolution::resolve_signature,
        //             PassState::TypeResolvedBody => passes::type_resolution::resolve_body,

        //             PassState::CyclicRefCheckBody => todo!(),
        //             PassState::TerminalBlockCheckBody => todo!(),

        //             PassState::StackAndTypeCheckedBody => todo!(),
        //             PassState::ConstPropBody => todo!(),

        //             PassState::EvaluatedConstsAsserts => todo!(),

        //             PassState::Done => {
        //                 continue;
        //             }
        //         };

        //         match pass_func(ctx, stores, &mut pass_ctx, &mut had_error, cur_item_id) {
        //             PassResult::Progress(next) => pass_ctx.progress_state(cur_item_id, next),
        //             PassResult::Waiting => {}
        //             PassResult::Error => {
        //                 pass_ctx.set_had_error(cur_item_id);
        //                 continue;
        //             }
        //         }

        //         pass_ctx.enqueue(cur_item_id);
        //     }
        // }
    }

    if had_error {
        Err(eyre!("Error during static analysis"))
    } else {
        Ok(())
    }
}
