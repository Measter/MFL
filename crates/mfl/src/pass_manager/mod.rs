use std::collections::VecDeque;

use color_eyre::{eyre::eyre, Result};
use hashbrown::HashMap;

use crate::{
    context::{Context, ItemHeader, ItemId},
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

struct ItemState {
    deps: Vec<Vec<(ItemId, PassState)>>,
    state: PassState,
    had_error: bool,
}

impl ItemState {
    fn new() -> Self {
        Self {
            deps: (0..PassState::Done as usize).map(|_| Vec::new()).collect(),
            state: PassState::IdentResolvedSignature,
            had_error: false,
        }
    }
}

enum CanProgress {
    Yes,
    No,
    Error,
}

struct PassContext {
    states: HashMap<ItemId, ItemState>,
}

impl PassContext {
    fn new(i: impl Iterator<Item = ItemHeader>) -> Self {
        Self {
            states: i.map(|i| (i.id, ItemState::new())).collect(),
        }
    }

    fn can_progress(&self, cur_item: ItemId) -> CanProgress {
        let cur_item_info = &self.states[&cur_item];
        for (dep_id, required_dep_state) in &cur_item_info.deps[cur_item_info.state as usize] {
            let dep_state = &self.states[dep_id];
            if dep_state.state > *required_dep_state {
                continue;
            }
            if dep_state.had_error {
                return CanProgress::Error;
            }
            return CanProgress::No;
        }

        CanProgress::Yes
    }

    fn get_state(&self, cur_item: ItemId) -> PassState {
        self.states[&cur_item].state
    }

    fn set_had_error(&mut self, cur_item: ItemId) {
        self.states.get_mut(&cur_item).unwrap().had_error = true;
    }

    fn add_dependency(
        &mut self,
        item: ItemId,
        for_item_state: PassState,
        dep_id: ItemId,
        dep_state: PassState,
    ) {
        let cur_item_state = self.states.get_mut(&item).unwrap();
        cur_item_state.deps[for_item_state as usize].push((dep_id, dep_state));
    }

    fn progress_state(&mut self, cur_item: ItemId, new_state: PassState) {
        let cur_item_state = self.states.get_mut(&cur_item).unwrap();
        cur_item_state.state = new_state;
    }
}

pub fn run(ctx: &mut Context, stores: &mut Stores) -> Result<()> {
    let mut pass_ctx = PassContext::new(ctx.get_all_items());

    let mut queue: VecDeque<_> = ctx.get_all_items().map(|i| i.id).collect();
    let mut had_error = false;

    while let Some(cur_item_id) = queue.pop_front() {
        match pass_ctx.can_progress(cur_item_id) {
            CanProgress::No => {
                // We're still waiting on something else to progress.
                queue.push_back(cur_item_id);
            }
            CanProgress::Error => {
                // Whatever we were waiting for had an error before it could get to the
                // stage we required. We need to propagate the error flag so our dependencies
                // know we can't progress.
                pass_ctx.set_had_error(cur_item_id);
            }
            CanProgress::Yes => {
                let cur_item_state = pass_ctx.get_state(cur_item_id);
                let pass_func = match cur_item_state {
                    PassState::IdentResolvedSignature => {
                        passes::ident_resolution::resolve_signature
                    }
                    PassState::IdentResolvedBody => passes::ident_resolution::resolve_body,

                    PassState::DeclareStructs => passes::structs::declare_struct,
                    PassState::DefineStructs => passes::structs::define_struct,

                    PassState::TypeResolvedSignature => passes::type_resolution::resolve_signature,
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

                match pass_func(ctx, stores, &mut pass_ctx, &mut had_error, cur_item_id) {
                    PassResult::Progress(next) => pass_ctx.progress_state(cur_item_id, next),
                    PassResult::Waiting => {}
                    PassResult::Error => {
                        pass_ctx.set_had_error(cur_item_id);
                        continue;
                    }
                }

                queue.push_back(cur_item_id);
            }
        }
    }

    if had_error {
        Err(eyre!("Error during static analysis"))
    } else {
        Ok(())
    }
}
