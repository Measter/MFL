use std::{collections::VecDeque, ops::ControlFlow};

use color_eyre::{eyre::eyre, Result};
use hashbrown::HashMap;

use crate::{
    context::{Context, ItemId},
    Stores,
};

mod passes;
pub mod static_analysis;

#[derive(Debug, Clone, Copy)]
enum PassResult {
    // We can progress to the next state
    Progress,
    // Failed because we're waiting on something else to progress
    // Don't progress our state, reinsert on to back of queue.
    Waiting,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum PassState {
    Unanalyzed,
    IdentResolvedSignature,
    IdentResolvedBody,
    TypeResolvedSignature,
    TypeResolvedBody,
    CyclicRefCheckBody,
    TerminalBlockCheckBody,
    StackAndTypeCheckedBody,
    ConstPropBody,
    EvaluatedConstsAsserts,
}

fn action(state: PassState, res: PassResult) -> (PassState, fn(&mut VecDeque<ItemId>, ItemId)) {
    let next_state = match state {
        PassState::Unanalyzed => PassState::IdentResolvedSignature,
        PassState::IdentResolvedSignature => PassState::IdentResolvedBody,
        PassState::IdentResolvedBody => PassState::TypeResolvedSignature,
        PassState::TypeResolvedSignature => PassState::TypeResolvedBody,
        PassState::TypeResolvedBody => PassState::CyclicRefCheckBody,
        PassState::CyclicRefCheckBody => PassState::TerminalBlockCheckBody,
        PassState::TerminalBlockCheckBody => PassState::StackAndTypeCheckedBody,
        PassState::StackAndTypeCheckedBody => PassState::ConstPropBody,
        PassState::ConstPropBody => PassState::EvaluatedConstsAsserts,
        PassState::EvaluatedConstsAsserts => state,
    };
    match res {
        PassResult::Progress => (next_state, VecDeque::push_front),
        PassResult::Waiting => (state, VecDeque::push_back),
    }
}

pub fn run(ctx: &mut Context, stores: &mut Stores) -> Result<()> {
    let mut states: HashMap<_, _> = ctx
        .get_all_items()
        .map(|i| (i.id, PassState::Unanalyzed))
        .collect();

    let mut queue: VecDeque<_> = ctx.get_all_items().map(|i| i.id).collect();
    let mut had_error = false;

    while let Some(cur_item_id) = queue.pop_front() {
        let cur_item_state = states[&cur_item_id];
        let (next_state, queue_func) = match cur_item_state {
            PassState::Unanalyzed => {
                match passes::ident_resolution::resolve_signature(
                    ctx,
                    stores,
                    &mut had_error,
                    cur_item_id,
                ) {
                    ControlFlow::Continue(st) => action(cur_item_state, st),
                    ControlFlow::Break(()) => continue,
                }
            }
            PassState::IdentResolvedSignature => {
                match passes::ident_resolution::resolve_body(
                    ctx,
                    stores,
                    &mut had_error,
                    cur_item_id,
                ) {
                    ControlFlow::Continue(st) => action(cur_item_state, st),
                    ControlFlow::Break(()) => continue,
                }
            }
            PassState::TypeResolvedSignature => todo!(),
            PassState::IdentResolvedBody => todo!(),
            PassState::TypeResolvedBody => todo!(),
            PassState::CyclicRefCheckBody => todo!(),
            PassState::TerminalBlockCheckBody => todo!(),
            PassState::StackAndTypeCheckedBody => todo!(),
            PassState::ConstPropBody => todo!(),
            PassState::EvaluatedConstsAsserts => todo!(),
        };

        states.insert(cur_item_id, next_state);
        queue_func(&mut queue, cur_item_id);
    }

    if had_error {
        Err(eyre!("Error during static analysis"))
    } else {
        Ok(())
    }
}
