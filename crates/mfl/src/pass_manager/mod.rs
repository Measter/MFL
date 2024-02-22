use std::collections::VecDeque;

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
    Progress(PassState),
    // Failed because we're waiting on something else to progress
    // Don't progress our state, reinsert on to back of queue.
    Waiting,
    // Failed and we can't progress.
    Error,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum PassState {
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

pub fn run(ctx: &mut Context, stores: &mut Stores) -> Result<()> {
    let mut states: HashMap<_, _> = ctx
        .get_all_items()
        .map(|i| (i.id, PassState::IdentResolvedSignature))
        .collect();

    let mut queue: VecDeque<_> = ctx.get_all_items().map(|i| i.id).collect();
    let mut had_error = false;

    while let Some(cur_item_id) = queue.pop_front() {
        let cur_item_state = states[&cur_item_id];
        let (next_state, queue_func): (_, fn(&mut VecDeque<_>, ItemId)) = match cur_item_state {
            PassState::IdentResolvedSignature => {
                match passes::ident_resolution::resolve_signature(
                    ctx,
                    stores,
                    &mut had_error,
                    cur_item_id,
                ) {
                    PassResult::Progress(next) => (next, VecDeque::push_front),
                    PassResult::Waiting => (cur_item_state, VecDeque::push_back),
                    PassResult::Error => continue,
                }
            }
            PassState::IdentResolvedBody => {
                match passes::ident_resolution::resolve_body(
                    ctx,
                    stores,
                    &mut had_error,
                    cur_item_id,
                ) {
                    PassResult::Progress(next) => (next, VecDeque::push_front),
                    PassResult::Waiting => (cur_item_state, VecDeque::push_back),
                    PassResult::Error => continue,
                }
            }

            PassState::DeclareStructs => todo!(),
            PassState::DefineStructs => todo!(),

            PassState::TypeResolvedSignature => todo!(),
            PassState::TypeResolvedBody => todo!(),

            PassState::CyclicRefCheckBody => todo!(),
            PassState::TerminalBlockCheckBody => todo!(),

            PassState::StackAndTypeCheckedBody => todo!(),
            PassState::ConstPropBody => todo!(),

            PassState::EvaluatedConstsAsserts => todo!(),

            PassState::Done => {
                continue;
            }
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
