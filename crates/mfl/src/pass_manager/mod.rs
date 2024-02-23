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

struct DepInfo {
    deps: Vec<Vec<(ItemId, PassState)>>,
}

impl DepInfo {
    fn new() -> Self {
        Self {
            deps: (0..PassState::Done as usize).map(|_| Vec::new()).collect(),
        }
    }
}

struct PassContext {
    // Keeps track of what Items and what stage they need to be in for the item to progress.
    waiting_info: HashMap<ItemId, DepInfo>,
    state: HashMap<ItemId, PassState>,
}

impl PassContext {
    fn new(i: impl Iterator<Item = ItemHeader>) -> Self {
        let (waiting_info, state) = i
            .map(|i| {
                (
                    (i.id, DepInfo::new()),
                    (i.id, PassState::IdentResolvedSignature),
                )
            })
            .unzip();

        Self {
            waiting_info,
            state,
        }
    }

    fn can_progress(&self, cur_item: ItemId) -> bool {
        let cur_state = self.get_state(cur_item);
        let dep_info = &self.waiting_info[&cur_item];
        let cur_state_deps = &dep_info.deps[cur_state as usize];
        cur_state_deps
            .iter()
            .all(|(dep_id, dep_state)| self.state[dep_id] > *dep_state)
    }

    fn get_state(&self, cur_item: ItemId) -> PassState {
        self.state[&cur_item]
    }

    fn add_dependency(
        &mut self,
        item: ItemId,
        for_item_state: PassState,
        dep_id: ItemId,
        dep_state: PassState,
    ) {
        let cur_item_deps = self.waiting_info.get_mut(&item).unwrap();
        cur_item_deps.deps[for_item_state as usize].push((dep_id, dep_state));
    }

    fn progress_state(&mut self, cur_item: ItemId, new_state: PassState) {
        self.state.insert(cur_item, new_state);
    }
}

pub fn run(ctx: &mut Context, stores: &mut Stores) -> Result<()> {
    let mut pass_ctx = PassContext::new(ctx.get_all_items());

    let mut queue: VecDeque<_> = ctx.get_all_items().map(|i| i.id).collect();
    let mut had_error = false;

    while let Some(cur_item_id) = queue.pop_front() {
        if !pass_ctx.can_progress(cur_item_id) {
            queue.push_back(cur_item_id);
            continue;
        }

        let cur_item_state = pass_ctx.get_state(cur_item_id);
        let pass_func = match cur_item_state {
            PassState::IdentResolvedSignature => passes::ident_resolution::resolve_signature,
            PassState::IdentResolvedBody => passes::ident_resolution::resolve_body,

            PassState::DeclareStructs => passes::structs::declare_struct,
            PassState::DefineStructs => passes::structs::define_struct,

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

        match pass_func(ctx, stores, &mut pass_ctx, &mut had_error, cur_item_id) {
            PassResult::Progress(next) => pass_ctx.progress_state(cur_item_id, next),
            PassResult::Waiting => {}
            PassResult::Error => continue,
        }

        queue.push_back(cur_item_id);
    }

    if had_error {
        Err(eyre!("Error during static analysis"))
    } else {
        Ok(())
    }
}
