use std::ops::Not;

use ariadne::{Color, Label};
use color_eyre::{eyre::eyre, Result};
use hashbrown::HashSet;
use tracing::{debug_span, trace};

use crate::{
    diagnostics,
    interners::Interners,
    opcode::{If, Op, OpCode, While},
    program::{static_analysis::ConstVal, ItemHeader, ItemId, ItemKind, Program},
    simulate::SimulatorValue,
    source_file::SourceStorage,
};

impl Program {
    pub fn resolve_idents_in_block(
        &self,
        item: ItemHeader,
        mut body: Vec<Op>,
        had_error: &mut bool,
        interner: &Interners,
        source_store: &SourceStorage,
    ) -> Vec<Op> {
        for op in &mut body {
            match &mut op.code {
                OpCode::While(while_op) => {
                    let temp_body = std::mem::take(&mut while_op.condition);
                    while_op.condition = self.resolve_idents_in_block(
                        item,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                    );
                    let temp_body = std::mem::take(&mut while_op.body_block);
                    while_op.body_block = self.resolve_idents_in_block(
                        item,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                    );
                }
                OpCode::If(if_op) => {
                    // Mmmm.. repetition...
                    let temp_body = std::mem::take(&mut if_op.condition);
                    if_op.condition = self.resolve_idents_in_block(
                        item,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                    );
                    let temp_body = std::mem::take(&mut if_op.then_block);
                    if_op.then_block = self.resolve_idents_in_block(
                        item,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                    );
                    let temp_body = std::mem::take(&mut if_op.else_block);
                    if_op.else_block = self.resolve_idents_in_block(
                        item,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                    );
                }
                // Symbol in own module.
                OpCode::UnresolvedIdent {
                    item: item_token,
                    module: None,
                } => {
                    // Obviously a symbol is visible to itself.
                    let visible_id = if item_token.lexeme == item.name.lexeme {
                        Some(item.id())
                    } else {
                        self.get_visible_symbol(item, item_token.lexeme)
                    };
                    if let Some(id) = visible_id {
                        op.code = OpCode::ResolvedIdent { item_id: id };
                    } else {
                        let module = &self.modules[&item.module];
                        let token_lexeme = interner.resolve_lexeme(item_token.lexeme);
                        let module_lexeme = interner.resolve_lexeme(module.name);
                        *had_error = true;
                        diagnostics::emit_error(
                            item_token.location,
                            format!(
                                "symbol `{token_lexeme}` not found in module `{module_lexeme}`"
                            ),
                            Some(
                                Label::new(item_token.location)
                                    .with_color(Color::Red)
                                    .with_message("not found"),
                            ),
                            None,
                            source_store,
                        );
                    }
                }
                // Symbol in other module.
                OpCode::UnresolvedIdent {
                    item: item_token,
                    module: Some(module_token),
                } => {
                    let module_id = match self.module_ident_map.get(&module_token.lexeme) {
                        Some(id) => *id,
                        None => {
                            let module_name = interner.resolve_lexeme(module_token.lexeme);
                            diagnostics::emit_error(
                                item_token.location,
                                format!("module `{module_name}` not found"),
                                Some(
                                    Label::new(item_token.location)
                                        .with_color(Color::Red)
                                        .with_message("not found"),
                                ),
                                None,
                                source_store,
                            );
                            *had_error = true;
                            continue;
                        }
                    };

                    let module = &self.modules[&module_id];
                    match module.top_level_symbols.get(&item_token.lexeme) {
                        Some(item_id) => {
                            op.code = OpCode::ResolvedIdent { item_id: *item_id };
                        }
                        None => {
                            let item_name = interner.resolve_lexeme(item_token.lexeme);
                            let module_name = interner.resolve_lexeme(module_token.lexeme);
                            diagnostics::emit_error(
                                item_token.location,
                                format!("symbol `{item_name}` not found in module `{module_name}`"),
                                Some(
                                    Label::new(item_token.location)
                                        .with_color(Color::Red)
                                        .with_message("not found"),
                                ),
                                None,
                                source_store,
                            );
                            *had_error = true;
                            continue;
                        }
                    }
                }

                _ => {}
            }
        }

        body
    }

    pub fn resolve_idents(
        &mut self,
        interner: &mut Interners,
        source_store: &SourceStorage,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::resolve_idents)).entered();
        let mut had_error = false;
        let items: Vec<_> = self
            .item_headers
            .iter()
            .filter(|(_, item)| item.kind() != ItemKind::Memory)
            .map(|(id, item)| (*id, *item))
            .collect();

        for (item_id, item) in items {
            trace!(name = interner.get_symbol_name(self, item_id));

            if item.kind() == ItemKind::StructDef {
                //
            } else {
                let body = self.item_bodies.remove(&item_id).unwrap();

                self.item_bodies.insert(
                    item_id,
                    self.resolve_idents_in_block(
                        item,
                        body,
                        &mut had_error,
                        interner,
                        source_store,
                    ),
                );
            }
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("error during ident resolation"))
    }

    pub fn check_invalid_cyclic_refs_in_block(
        &self,
        root_item: ItemHeader,
        block: &[Op],
        cur_item: ItemHeader,
        kind: &str,
        already_checked: &mut HashSet<ItemId>,
        check_queue: &mut Vec<ItemHeader>,
        had_error: &mut bool,
        source_store: &SourceStorage,
    ) {
        for op in block {
            match op.code {
                OpCode::While(ref while_op) => {
                    self.check_invalid_cyclic_refs_in_block(
                        root_item,
                        &while_op.condition,
                        cur_item,
                        kind,
                        already_checked,
                        check_queue,
                        had_error,
                        source_store,
                    );
                    self.check_invalid_cyclic_refs_in_block(
                        root_item,
                        &while_op.body_block,
                        cur_item,
                        kind,
                        already_checked,
                        check_queue,
                        had_error,
                        source_store,
                    );
                }
                OpCode::If(ref if_op) => {
                    self.check_invalid_cyclic_refs_in_block(
                        root_item,
                        &if_op.condition,
                        cur_item,
                        kind,
                        already_checked,
                        check_queue,
                        had_error,
                        source_store,
                    );
                    self.check_invalid_cyclic_refs_in_block(
                        root_item,
                        &if_op.then_block,
                        cur_item,
                        kind,
                        already_checked,
                        check_queue,
                        had_error,
                        source_store,
                    );
                    self.check_invalid_cyclic_refs_in_block(
                        root_item,
                        &if_op.else_block,
                        cur_item,
                        kind,
                        already_checked,
                        check_queue,
                        had_error,
                        source_store,
                    );
                }
                OpCode::ResolvedIdent { item_id, .. } => {
                    // False means that there was already a value in the set with this item_id
                    #[allow(clippy::bool_comparison)]
                    if already_checked.insert(item_id) == false {
                        continue;
                    }

                    if item_id == root_item.id() {
                        *had_error = true;
                        diagnostics::emit_error(
                            cur_item.name.location,
                            format!("cyclic {kind} detected"),
                            [
                                Label::new(root_item.name.location)
                                    .with_color(Color::Red)
                                    .with_message(format!("in this {kind}")),
                                Label::new(op.token.location)
                                    .with_color(Color::Cyan)
                                    .with_message("cyclic reference"),
                            ],
                            None,
                            source_store,
                        );
                    } else {
                        check_queue.push(self.get_item_header(item_id));
                    }
                }
                _ => (),
            }
        }
    }

    pub fn check_invalid_cyclic_refs(
        &self,
        interner: &mut Interners,
        source_store: &SourceStorage,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::check_invalid_cyclic_refs)).entered();
        let mut had_error = false;

        let mut check_queue = Vec::new();
        let mut already_checked = HashSet::new();
        for root_item in self.item_headers.values().copied() {
            trace!(name = interner.get_symbol_name(self, root_item.id()));

            let kind = match root_item.kind() {
                ItemKind::Const => "const",
                ItemKind::Macro => "macro",
                ItemKind::Assert => "assert",
                ItemKind::Memory | ItemKind::Function | ItemKind::StructDef => continue,
            };

            check_queue.clear();
            check_queue.push(root_item);
            already_checked.clear();

            while let Some(item) = check_queue.pop() {
                self.check_invalid_cyclic_refs_in_block(
                    root_item,
                    &self.item_bodies[&item.id],
                    item,
                    kind,
                    &mut already_checked,
                    &mut check_queue,
                    &mut had_error,
                    source_store,
                );
            }
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("failed const self-check"))
    }

    pub fn process_idents_in_block(
        &mut self,
        own_item_id: ItemId,
        block: Vec<Op>,
        had_error: &mut bool,
        interner: &Interners,
        source_store: &SourceStorage,
    ) -> Vec<Op> {
        let mut new_ops: Vec<Op> = Vec::with_capacity(block.len());
        for op in block {
            match op.code {
                OpCode::While(while_op) => {
                    new_ops.push(Op {
                        code: OpCode::While(Box::new(While {
                            condition: self.process_idents_in_block(
                                own_item_id,
                                while_op.condition,
                                had_error,
                                interner,
                                source_store,
                            ),
                            body_block: self.process_idents_in_block(
                                own_item_id,
                                while_op.body_block,
                                had_error,
                                interner,
                                source_store,
                            ),
                            ..*while_op
                        })),
                        id: op.id,
                        token: op.token,
                        expansions: op.expansions,
                    });
                }
                OpCode::If(if_op) => {
                    let new_condition = self.process_idents_in_block(
                        own_item_id,
                        if_op.condition,
                        had_error,
                        interner,
                        source_store,
                    );
                    let new_then_block = self.process_idents_in_block(
                        own_item_id,
                        if_op.then_block,
                        had_error,
                        interner,
                        source_store,
                    );
                    let new_else_block = self.process_idents_in_block(
                        own_item_id,
                        if_op.else_block,
                        had_error,
                        interner,
                        source_store,
                    );

                    new_ops.push(Op {
                        code: OpCode::If(Box::new(If {
                            condition: new_condition,
                            then_block: new_then_block,
                            else_block: new_else_block,
                            ..*if_op
                        })),
                        id: op.id,
                        token: op.token,
                        expansions: op.expansions,
                    });
                }

                OpCode::ResolvedIdent { item_id } => {
                    let found_item = self.item_headers[&item_id];

                    match found_item.kind() {
                        ItemKind::Const => {
                            let Some(vals) = self.const_vals.get( &found_item.id ) else {
                                let own_item = self.item_headers[&own_item_id];
                                let name = interner.resolve_lexeme(own_item.name.lexeme);
                                panic!("ICE: Encountered un-evaluated const during ident processing {name}");
                            };
                            for (_, val) in vals {
                                let (code, const_val) = match val {
                                    SimulatorValue::Int { kind, width } => (
                                        OpCode::PushInt {
                                            width: *width,
                                            value: *kind,
                                        },
                                        ConstVal::Int(*kind),
                                    ),
                                    SimulatorValue::Bool(val) => {
                                        (OpCode::PushBool(*val), ConstVal::Bool(*val))
                                    }
                                };
                                new_ops.push(Op {
                                    code,
                                    id: op.id,
                                    token: op.token,
                                    expansions: op.expansions.clone(),
                                });

                                let analyzer = self.analyzers.get_mut(&own_item_id).unwrap();
                                let op_io = analyzer.get_op_io(op.id);
                                let out_id = op_io.outputs()[0];
                                analyzer.set_value_const(out_id, const_val);
                            }
                        }
                        ItemKind::Memory => {
                            new_ops.push(Op {
                                code: OpCode::Memory {
                                    item_id,
                                    global: found_item.parent().is_none(),
                                },
                                id: op.id,
                                token: op.token,
                                expansions: op.expansions,
                            });
                        }
                        ItemKind::Function => {
                            new_ops.push(Op {
                                code: OpCode::CallFunction { item_id },
                                id: op.id,
                                token: op.token,
                                expansions: op.expansions,
                            });
                        }
                        ItemKind::Macro => {
                            let own_item = self.item_headers[&own_item_id];
                            let name = interner.resolve_lexeme(own_item.name.lexeme);
                            panic!(
                                "ICE: Encountered assert, or macro during ident processing {name}"
                            );
                        }

                        ItemKind::Assert | ItemKind::StructDef => {
                            *had_error = true;
                            diagnostics::emit_error(
                                op.token.location,
                                format!("{:?} cannot be used in operations", found_item.kind()),
                                Some(
                                    Label::new(op.token.location)
                                        .with_color(Color::Red)
                                        .with_message("here"),
                                ),
                                None,
                                source_store,
                            );
                            continue;
                        }
                    }
                }
                _ => new_ops.push(op),
            }
        }
        new_ops
    }

    pub fn process_idents(
        &mut self,
        interner: &mut Interners,
        source_store: &SourceStorage,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::process_idents)).entered();
        let mut had_error = false;

        // Macros should already have been expanded.
        let all_item_ids: Vec<_> = self
            .item_headers
            .iter()
            .filter(|(_, i)| {
                i.kind() != ItemKind::Macro
                    && i.kind() != ItemKind::Memory
                    && i.kind() != ItemKind::StructDef
            })
            .map(|(id, _)| *id)
            .collect();

        for own_item_id in all_item_ids {
            trace!("Processing {}", interner.get_symbol_name(self, own_item_id));

            let old_body = self.item_bodies.remove(&own_item_id).unwrap();
            let new_body = self.process_idents_in_block(
                own_item_id,
                old_body,
                &mut had_error,
                interner,
                source_store,
            );
            self.item_bodies.insert(own_item_id, new_body);
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("error processing idents"))
    }
}
