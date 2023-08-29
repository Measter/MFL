use std::ops::Not;

use ariadne::{Color, Label};
use color_eyre::{eyre::eyre, Result};
use hashbrown::HashSet;
use intcast::IntCast;
use lasso::Spur;
use tracing::{debug_span, trace};

use crate::{
    diagnostics,
    opcode::{If, Op, OpCode, UnresolvedIdent, While},
    program::{
        static_analysis::ConstVal, symbol_redef_error, ItemHeader, ItemId, ItemKind, Program,
    },
    simulate::SimulatorValue,
    source_file::{FileId, Spanned, WithSpan},
    type_store::{
        BuiltinTypes, UnresolvedStruct, UnresolvedType, UnresolvedTypeIds, UnresolvedTypeTokens,
    },
    Stores,
};

impl Program {
    fn resolve_single_ident(
        &self,
        stores: &Stores,
        had_error: &mut bool,
        item_header: ItemHeader,
        ident: &UnresolvedIdent,
    ) -> Result<ItemId, ()> {
        let [first_ident, rest @ ..] = ident.path.as_slice() else {
            unreachable!()
        };

        let mut current_item = if ident.is_from_root {
            let Some(tlm) = self.top_level_modules.get(&first_ident.inner) else {
                let item_name = stores.strings.resolve(first_ident.inner);
                diagnostics::emit_error(
                    stores,
                    first_ident.location,
                    format!("symbol `{item_name}` not found"),
                    Some(Label::new(first_ident.location).with_color(Color::Red)),
                    None,
                );
                *had_error = true;
                return Err(());
            };
            *tlm
        } else {
            let Some(start_item) = self.get_visible_symbol(item_header, first_ident.inner) else {
                // TODO: Handle naming builtins here
                let item_name = stores.strings.resolve(first_ident.inner);
                diagnostics::emit_error(
                    stores,
                    first_ident.location,
                    format!("symbol `{item_name}` not found"),
                    Some(Label::new(first_ident.location).with_color(Color::Red)),
                    None,
                );
                *had_error = true;
                return Err(());
            };
            start_item
        };

        let mut last_ident = *first_ident;

        for sub_ident in rest {
            let cur_item = self.get_item_header(current_item);
            if cur_item.kind != ItemKind::Module {
                diagnostics::emit_error(
                    stores,
                    sub_ident.location,
                    "cannot path into non-module items",
                    [
                        Label::new(sub_ident.location).with_color(Color::Red),
                        Label::new(last_ident.location)
                            .with_color(Color::Cyan)
                            .with_message("not a module"),
                    ],
                    None,
                );
                *had_error = true;
                return Err(());
            }

            let scope = self.get_scope(cur_item.id);
            let Some(sub_item) = scope.get_symbol(sub_ident.inner) else {
                diagnostics::emit_error(
                    stores,
                    sub_ident.location,
                    "symbol not found",
                    [Label::new(sub_ident.location).with_color(Color::Red)],
                    None,
                );
                *had_error = true;
                return Err(());
            };

            last_ident = *sub_ident;
            current_item = sub_item;
        }

        Ok(current_item)
    }

    fn resolve_idents_in_type(
        &self,
        stores: &mut Stores,
        had_error: &mut bool,
        item_header: ItemHeader,
        unresolved_type: &UnresolvedTypeTokens,
        generic_params: Option<&Vec<Spanned<Spur>>>,
    ) -> Result<UnresolvedTypeIds, ()> {
        let res = match unresolved_type {
            UnresolvedTypeTokens::Simple(unresolved_ident) => {
                let item_name = unresolved_ident
                    .path
                    .last()
                    .expect("ICE: empty unresolved ident");

                let name = stores.strings.resolve(item_name.inner);
                let builtin_name = BuiltinTypes::from_name(name);

                if (unresolved_ident.path.len() > 1
                    || unresolved_ident.is_from_root
                    || unresolved_ident.generic_params.is_some())
                    && builtin_name.is_some()
                {
                    // Emit error
                    diagnostics::emit_error(
                        stores,
                        unresolved_ident.span,
                        "cannot name builtin with a path",
                        [Label::new(unresolved_ident.span).with_color(Color::Red)],
                        None,
                    );
                    *had_error = true;
                    return Err(());
                } else if let Some(builtin) = builtin_name {
                    UnresolvedTypeIds::SimpleBuiltin(builtin)
                } else if unresolved_ident.path.len() == 1
                    && !unresolved_ident.is_from_root
                    && unresolved_ident.generic_params.is_none()
                    && generic_params
                        .and_then(|t| t.iter().find(|tp| tp.inner == item_name.inner))
                        .is_some()
                {
                    UnresolvedTypeIds::SimpleGenericParam(*item_name)
                } else {
                    let ident = self.resolve_single_ident(
                        stores,
                        had_error,
                        item_header,
                        unresolved_ident,
                    )?;

                    match &unresolved_ident.generic_params {
                        Some(params) => {
                            let params: Vec<_> = params
                                .iter()
                                .map(|p| {
                                    let UnresolvedType::Tokens(p) = p else {
                                        unreachable!()
                                    };
                                    self.resolve_idents_in_type(
                                        stores,
                                        had_error,
                                        item_header,
                                        p,
                                        generic_params,
                                    )
                                })
                                .collect::<Result<_, _>>()?;

                            UnresolvedTypeIds::GenericInstance {
                                id: ident,
                                id_token: item_name.inner.with_span(unresolved_ident.span),
                                params,
                            }
                        }
                        None => UnresolvedTypeIds::SimpleCustom {
                            id: ident,
                            token: item_name.inner.with_span(unresolved_ident.span),
                        },
                    }
                }
            }
            UnresolvedTypeTokens::Array(sub_type, length) => {
                let sub_type = self.resolve_idents_in_type(
                    stores,
                    had_error,
                    item_header,
                    sub_type,
                    generic_params,
                )?;

                UnresolvedTypeIds::Array(Box::new(sub_type), *length)
            }
            UnresolvedTypeTokens::Pointer(sub_type) => {
                let sub_type = self.resolve_idents_in_type(
                    stores,
                    had_error,
                    item_header,
                    sub_type,
                    generic_params,
                )?;

                UnresolvedTypeIds::Pointer(Box::new(sub_type))
            }
        };

        Ok(res)
    }

    pub fn resolve_idents_in_block(
        &self,
        stores: &mut Stores,
        had_error: &mut bool,
        item: ItemHeader,
        mut body: Vec<Op>,
        generic_params: Option<&Vec<Spanned<Spur>>>,
    ) -> Vec<Op> {
        for op in &mut body {
            match &mut op.code {
                OpCode::While(while_op) => {
                    let temp_body = std::mem::take(&mut while_op.condition);
                    while_op.condition = self.resolve_idents_in_block(
                        stores,
                        had_error,
                        item,
                        temp_body,
                        generic_params,
                    );
                    let temp_body = std::mem::take(&mut while_op.body_block);
                    while_op.body_block = self.resolve_idents_in_block(
                        stores,
                        had_error,
                        item,
                        temp_body,
                        generic_params,
                    );
                }
                OpCode::If(if_op) => {
                    // Mmmm.. repetition...
                    let temp_body = std::mem::take(&mut if_op.condition);
                    if_op.condition = self.resolve_idents_in_block(
                        stores,
                        had_error,
                        item,
                        temp_body,
                        generic_params,
                    );
                    let temp_body = std::mem::take(&mut if_op.then_block);
                    if_op.then_block = self.resolve_idents_in_block(
                        stores,
                        had_error,
                        item,
                        temp_body,
                        generic_params,
                    );
                    let temp_body = std::mem::take(&mut if_op.else_block);
                    if_op.else_block = self.resolve_idents_in_block(
                        stores,
                        had_error,
                        item,
                        temp_body,
                        generic_params,
                    );
                }

                OpCode::UnresolvedIdent(ident) => {
                    let Ok(item_id) = self.resolve_single_ident(stores, had_error, item, ident)
                    else {
                        continue;
                    };

                    let resolved_generic_params = ident.generic_params.as_ref().map(|v| {
                        let mut resolved_generic_params = Vec::new();

                        for param in v {
                            let UnresolvedType::Tokens(param) = param else {
                                unreachable!()
                            };
                            let Ok(f) = self.resolve_idents_in_type(
                                stores,
                                had_error,
                                item,
                                param,
                                generic_params,
                            ) else {
                                continue;
                            };
                            resolved_generic_params.push(UnresolvedType::Id(f));
                        }
                        resolved_generic_params
                    });

                    let found_item_header = self.get_item_header(item_id);
                    match found_item_header.kind() {
                        ItemKind::Function
                        | ItemKind::GenericFunction
                        | ItemKind::Const
                        | ItemKind::Memory => {
                            op.code = OpCode::ResolvedIdent {
                                item_id,
                                generic_params: resolved_generic_params,
                            };
                        }
                        ItemKind::StructDef => {
                            let ty = UnresolvedTypeTokens::Simple(ident.clone());
                            let Ok(new_ty) = self.resolve_idents_in_type(
                                stores,
                                had_error,
                                item,
                                &ty,
                                generic_params,
                            ) else {
                                *had_error = true;
                                continue;
                            };

                            op.code = OpCode::UnresolvedPackStruct {
                                unresolved_type: UnresolvedType::Id(new_ty),
                            }
                        }
                        ItemKind::Assert | ItemKind::Module => {
                            *had_error = true;
                            let mut labels =
                                vec![Label::new(op.token.location).with_color(Color::Red)];
                            // This would be the case if the item was a top-level module.
                            let note = if found_item_header.name.location.file_id != FileId::dud() {
                                labels.push(
                                    Label::new(found_item_header.name.location)
                                        .with_color(Color::Cyan)
                                        .with_message(format!(
                                            "item is a {:?}",
                                            found_item_header.kind()
                                        )),
                                );
                                String::new()
                            } else {
                                let name = stores.strings.resolve(found_item_header.name.inner);
                                format!("`{name}` is a top-level module")
                            };

                            diagnostics::emit_error(
                                stores,
                                op.token.location,
                                format!("cannot refer to a {:?} here", found_item_header.kind()),
                                labels,
                                note,
                            );
                            continue;
                        }
                    }
                }
                OpCode::UnresolvedCast { unresolved_type }
                | OpCode::UnresolvedPackStruct { unresolved_type }
                | OpCode::UnresolvedSizeOf { unresolved_type } => {
                    let UnresolvedType::Tokens(ty) = unresolved_type else {
                        panic!("ICE: tried to resolve type on resolved type")
                    };

                    let Ok(new_ty) =
                        self.resolve_idents_in_type(stores, had_error, item, ty, generic_params)
                    else {
                        *had_error = true;
                        continue;
                    };
                    *unresolved_type = UnresolvedType::Id(new_ty);
                }
                _ => {}
            }
        }

        body
    }

    fn resolve_idents_in_struct_def(
        &self,
        stores: &mut Stores,
        had_error: &mut bool,
        item: ItemHeader,
        mut def: UnresolvedStruct,
    ) -> UnresolvedStruct {
        for field in &mut def.fields {
            let UnresolvedType::Tokens(field_kind) = &field.kind else {
                unreachable!()
            };

            let Ok(new_kind) = self.resolve_idents_in_type(
                stores,
                had_error,
                item,
                field_kind,
                def.generic_params.as_ref(),
            ) else {
                *had_error = true;
                continue;
            };

            field.kind = UnresolvedType::Id(new_kind);
        }

        def
    }

    fn resolve_idents_in_module_imports(
        &mut self,
        stores: &Stores,
        had_error: &mut bool,
        item: ItemHeader,
    ) {
        let imports = self.get_scope(item.id).unresolved_imports.clone();

        for import in imports {
            let Ok(resolved_item) = self.resolve_single_ident(stores, had_error, item, &import)
            else {
                continue;
            };
            let item_name = self.get_item_header(resolved_item).name;
            let scope = &mut self.scopes[item.id.0.to_usize()];

            if let Err(prev_loc) =
                scope.add_visible_symbol(item_name.inner.with_span(import.span), resolved_item)
            {
                *had_error = true;
                symbol_redef_error(stores, import.span, prev_loc);
            }
        }
    }

    pub fn resolve_idents(&mut self, stores: &mut Stores) -> Result<()> {
        let _span = debug_span!(stringify!(Program::resolve_idents)).entered();
        let mut had_error = false;
        let items: Vec<_> = self.item_headers.clone();

        for item in items {
            trace!(name = stores.strings.get_symbol_name(self, item.id));

            if item.kind() == ItemKind::StructDef {
                let def = self.structs_unresolved.remove(&item.id).unwrap();
                self.structs_unresolved.insert(
                    item.id,
                    self.resolve_idents_in_struct_def(stores, &mut had_error, item, def),
                );
            } else if item.kind() == ItemKind::Memory {
                let generic_params = match item.parent {
                    Some(parent_id)
                        if self.get_item_header(parent_id).kind == ItemKind::GenericFunction =>
                    {
                        self.generic_template_parameters.get(&parent_id)
                    }
                    _ => None,
                };

                let mut memory_type = self.memory_type_unresolved.remove(&item.id).unwrap();
                let UnresolvedType::Tokens(memory_type_tokens) = &memory_type.inner else {
                    unreachable!()
                };
                let Ok(new_kind) = self.resolve_idents_in_type(
                    stores,
                    &mut had_error,
                    item,
                    memory_type_tokens,
                    generic_params,
                ) else {
                    had_error = true;
                    continue;
                };
                memory_type.inner = UnresolvedType::Id(new_kind);

                self.memory_type_unresolved.insert(item.id, memory_type);
            } else if item.kind() == ItemKind::Module {
                self.resolve_idents_in_module_imports(stores, &mut had_error, item);
            } else {
                let mut sig = self.item_signatures_unresolved.remove(&item.id).unwrap();

                let generic_params = if item.kind() == ItemKind::GenericFunction {
                    self.generic_template_parameters.get(&item.id)
                } else {
                    None
                };

                for kind in sig
                    .entry_stack
                    .inner
                    .iter_mut()
                    .chain(&mut sig.exit_stack.inner)
                {
                    let UnresolvedType::Tokens(kind_tokens) = &kind.inner else {
                        unreachable!()
                    };
                    let Ok(new_kind) = self.resolve_idents_in_type(
                        stores,
                        &mut had_error,
                        item,
                        kind_tokens,
                        generic_params,
                    ) else {
                        had_error = true;
                        continue;
                    };

                    kind.inner = UnresolvedType::Id(new_kind);
                }

                self.item_signatures_unresolved.insert(item.id, sig);
                let body = self.item_bodies.remove(&item.id).unwrap();

                self.item_bodies.insert(
                    item.id,
                    self.resolve_idents_in_block(
                        stores,
                        &mut had_error,
                        item,
                        body,
                        generic_params,
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
        stores: &mut Stores,
        had_error: &mut bool,
        root_item: ItemHeader,
        block: &[Op],
        cur_item: ItemHeader,
        kind: &str,
        already_checked: &mut HashSet<ItemId>,
        check_queue: &mut Vec<ItemHeader>,
    ) {
        for op in block {
            match op.code {
                OpCode::While(ref while_op) => {
                    self.check_invalid_cyclic_refs_in_block(
                        stores,
                        had_error,
                        root_item,
                        &while_op.condition,
                        cur_item,
                        kind,
                        already_checked,
                        check_queue,
                    );
                    self.check_invalid_cyclic_refs_in_block(
                        stores,
                        had_error,
                        root_item,
                        &while_op.body_block,
                        cur_item,
                        kind,
                        already_checked,
                        check_queue,
                    );
                }
                OpCode::If(ref if_op) => {
                    self.check_invalid_cyclic_refs_in_block(
                        stores,
                        had_error,
                        root_item,
                        &if_op.condition,
                        cur_item,
                        kind,
                        already_checked,
                        check_queue,
                    );
                    self.check_invalid_cyclic_refs_in_block(
                        stores,
                        had_error,
                        root_item,
                        &if_op.then_block,
                        cur_item,
                        kind,
                        already_checked,
                        check_queue,
                    );
                    self.check_invalid_cyclic_refs_in_block(
                        stores,
                        had_error,
                        root_item,
                        &if_op.else_block,
                        cur_item,
                        kind,
                        already_checked,
                        check_queue,
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
                            stores,
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
                        );
                    } else {
                        check_queue.push(self.get_item_header(item_id));
                    }
                }
                _ => (),
            }
        }
    }

    pub fn check_invalid_cyclic_refs(&self, stores: &mut Stores) -> Result<()> {
        let _span = debug_span!(stringify!(Program::check_invalid_cyclic_refs)).entered();
        let mut had_error = false;

        let mut check_queue = Vec::new();
        let mut already_checked = HashSet::new();
        for root_item in self.item_headers.iter().copied() {
            trace!(name = stores.strings.get_symbol_name(self, root_item.id()));

            let kind = match root_item.kind() {
                ItemKind::Const => "const",
                ItemKind::Assert => "assert",
                ItemKind::Memory
                | ItemKind::Function
                | ItemKind::StructDef
                | ItemKind::Module
                | ItemKind::GenericFunction => continue,
            };

            check_queue.clear();
            check_queue.push(root_item);
            already_checked.clear();

            while let Some(item) = check_queue.pop() {
                self.check_invalid_cyclic_refs_in_block(
                    stores,
                    &mut had_error,
                    root_item,
                    &self.item_bodies[&item.id],
                    item,
                    kind,
                    &mut already_checked,
                    &mut check_queue,
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
        stores: &mut Stores,
        had_error: &mut bool,
        own_item_id: ItemId,
        block: Vec<Op>,
    ) -> Vec<Op> {
        let mut new_ops: Vec<Op> = Vec::with_capacity(block.len());
        for op in block {
            match op.code {
                OpCode::While(while_op) => {
                    new_ops.push(Op {
                        code: OpCode::While(Box::new(While {
                            condition: self.process_idents_in_block(
                                stores,
                                had_error,
                                own_item_id,
                                while_op.condition,
                            ),
                            body_block: self.process_idents_in_block(
                                stores,
                                had_error,
                                own_item_id,
                                while_op.body_block,
                            ),
                            ..*while_op
                        })),
                        id: op.id,
                        token: op.token,
                    });
                }
                OpCode::If(if_op) => {
                    let new_condition = self.process_idents_in_block(
                        stores,
                        had_error,
                        own_item_id,
                        if_op.condition,
                    );
                    let new_then_block = self.process_idents_in_block(
                        stores,
                        had_error,
                        own_item_id,
                        if_op.then_block,
                    );
                    let new_else_block = self.process_idents_in_block(
                        stores,
                        had_error,
                        own_item_id,
                        if_op.else_block,
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
                    });
                }

                OpCode::ResolvedIdent { item_id, .. } => {
                    let found_item = self.get_item_header(item_id);

                    match found_item.kind() {
                        ItemKind::Const => {
                            let Some(vals) = self.const_vals.get(&found_item.id) else {
                                let own_item = self.get_item_header(own_item_id);
                                let name = stores.strings.resolve(own_item.name.inner);
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
                            });
                        }
                        ItemKind::Function => {
                            new_ops.push(Op {
                                code: OpCode::CallFunction { item_id },
                                id: op.id,
                                token: op.token,
                            });
                        }
                        ItemKind::GenericFunction => {
                            unreachable!()
                        }

                        ItemKind::Assert | ItemKind::StructDef | ItemKind::Module => {
                            *had_error = true;
                            diagnostics::emit_error(
                                stores,
                                op.token.location,
                                format!("{:?} cannot be used in operations", found_item.kind()),
                                Some(
                                    Label::new(op.token.location)
                                        .with_color(Color::Red)
                                        .with_message("here"),
                                ),
                                None,
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

    pub fn process_idents(&mut self, stores: &mut Stores) -> Result<()> {
        let _span = debug_span!(stringify!(Program::process_idents)).entered();
        let mut had_error = false;

        // Macros should already have been expanded.
        let all_item_ids: Vec<_> = self
            .item_headers
            .iter()
            .filter(|i| {
                i.kind() != ItemKind::Memory
                    && i.kind() != ItemKind::StructDef
                    && i.kind() != ItemKind::Module
                    && i.kind() != ItemKind::GenericFunction
            })
            .map(|i| i.id)
            .collect();

        for own_item_id in all_item_ids {
            trace!(
                "Processing {}",
                stores.strings.get_symbol_name(self, own_item_id)
            );

            let old_body = self.item_bodies.remove(&own_item_id).unwrap();
            let new_body =
                self.process_idents_in_block(stores, &mut had_error, own_item_id, old_body);
            self.item_bodies.insert(own_item_id, new_body);
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("error processing idents"))
    }
}
