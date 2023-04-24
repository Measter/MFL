use std::ops::Not;

use ariadne::{Color, Label};
use color_eyre::{eyre::eyre, Result};
use hashbrown::HashSet;
use lasso::Spur;
use tracing::{debug_span, trace};

use crate::{
    diagnostics,
    interners::Interners,
    opcode::{If, Op, OpCode, While},
    program::{
        static_analysis::ConstVal, symbol_redef_error, ItemHeader, ItemId, ItemKind, Program,
    },
    simulate::SimulatorValue,
    source_file::{FileId, SourceLocation, SourceStorage, Spanned, WithSpan},
    type_store::{
        BuiltinTypes, UnresolvedStruct, UnresolvedType, UnresolvedTypeIds, UnresolvedTypeTokens,
    },
};

impl Program {
    fn resolve_single_ident(
        &self,
        item_header: ItemHeader,
        interner: &Interners,
        source_store: &SourceStorage,
        had_error: &mut bool,
        ident: &[Spanned<Spur>],
    ) -> Result<ItemId, ()> {
        match ident {
            [] => panic!("ICE: empty unresolved ident"),
            // Symbol visible from the current item.
            [item_token] => {
                let visible_id = if item_token.inner == item_header.name.inner {
                    // Obviously a symbol is visible to itself.
                    Some(item_header.id())
                } else {
                    self.get_visible_symbol(item_header, item_token.inner)
                };

                if let Some(id) = visible_id {
                    Ok(id)
                } else {
                    let token_lexeme = interner.resolve_lexeme(item_token.inner);
                    *had_error = true;
                    diagnostics::emit_error(
                        item_token.location,
                        format!("symbol `{token_lexeme}` not found"),
                        Some(
                            Label::new(item_token.location)
                                .with_color(Color::Red)
                                .with_message("not found"),
                        ),
                        None,
                        source_store,
                    );

                    Err(())
                }
            }
            // Path from the top level module.
            [top_level_ident, sub_idents @ .., last_ident] => {
                let start = match self.get_visible_symbol(item_header, top_level_ident.inner) {
                    Some(item_id) => item_id,
                    None => {
                        let item_name = interner.resolve_lexeme(top_level_ident.inner);
                        diagnostics::emit_error(
                            top_level_ident.location,
                            format!("symbol `{item_name}` not found"),
                            Some(Label::new(top_level_ident.location).with_color(Color::Red)),
                            None,
                            source_store,
                        );
                        *had_error = true;
                        return Err(());
                    }
                };

                // We know this is a multi-part ident, so the start must be a module.
                let mut cur_module = &self.module_info[&start];
                for sm in sub_idents {
                    let next_module = match cur_module.get_visible_symbol(sm.inner) {
                        Some(nid) => nid,
                        None => {
                            let module_name = interner.resolve_lexeme(sm.inner);
                            diagnostics::emit_error(
                                sm.location,
                                format!("module `{module_name}` not found"),
                                Some(Label::new(sm.location).with_color(Color::Red)),
                                None,
                                source_store,
                            );
                            *had_error = true;
                            return Err(());
                        }
                    };

                    cur_module = &self.module_info[&next_module];
                }

                match cur_module.get_visible_symbol(last_ident.inner) {
                    Some(item_id) => Ok(item_id),
                    None => {
                        let item_name = interner.resolve_lexeme(last_ident.inner);
                        diagnostics::emit_error(
                            last_ident.location,
                            format!("symbol `{item_name}` not found in module"),
                            Some(Label::new(last_ident.location).with_color(Color::Red)),
                            None,
                            source_store,
                        );
                        *had_error = true;
                        Err(())
                    }
                }
            }
        }
    }

    fn resolve_idents_in_type(
        &self,
        item_header: ItemHeader,
        interner: &Interners,
        source_store: &SourceStorage,
        had_error: &mut bool,
        unresolved_type: &UnresolvedTypeTokens,
        generic_params: Option<&Vec<Spanned<Spur>>>,
    ) -> Result<UnresolvedTypeIds, ()> {
        let res = match unresolved_type {
            UnresolvedTypeTokens::Simple(unresolved_ident) => {
                let item_name = unresolved_ident
                    .last()
                    .expect("ICE: empty unresolved ident");

                let path_location = unresolved_ident
                    .iter()
                    .map(|t| t.location)
                    .reduce(SourceLocation::merge)
                    .unwrap();

                let name = interner.resolve_lexeme(item_name.inner);
                let builtin_name = BuiltinTypes::from_name(name);

                if unresolved_ident.len() > 1 && builtin_name.is_some() {
                    // Emit error
                    diagnostics::emit_error(
                        path_location,
                        "cannot name builtin with a module",
                        [Label::new(path_location).with_color(Color::Red)],
                        None,
                        source_store,
                    );
                    *had_error = true;
                    return Err(());
                } else if let Some(builtin) = builtin_name {
                    UnresolvedTypeIds::SimpleBuiltin(builtin)
                } else if unresolved_ident.len() == 1
                    && generic_params
                        .and_then(|t| t.iter().find(|tp| tp.inner == item_name.inner))
                        .is_some()
                {
                    UnresolvedTypeIds::SimpleGenericParam(*item_name)
                } else {
                    let ident = self.resolve_single_ident(
                        item_header,
                        interner,
                        source_store,
                        had_error,
                        unresolved_ident,
                    )?;

                    UnresolvedTypeIds::SimpleCustom {
                        id: ident,
                        token: item_name.inner.with_span(path_location),
                    }
                }
            }
            UnresolvedTypeTokens::Array(sub_type, length) => {
                let sub_type = self.resolve_idents_in_type(
                    item_header,
                    interner,
                    source_store,
                    had_error,
                    sub_type,
                    generic_params,
                )?;

                UnresolvedTypeIds::Array(Box::new(sub_type), *length)
            }
            UnresolvedTypeTokens::Pointer(sub_type) => {
                let sub_type = self.resolve_idents_in_type(
                    item_header,
                    interner,
                    source_store,
                    had_error,
                    sub_type,
                    generic_params,
                )?;

                UnresolvedTypeIds::Pointer(Box::new(sub_type))
            }

            UnresolvedTypeTokens::GenericInstance {
                type_name: unresolved_ident,
                params,
            } => {
                let item_name = unresolved_ident
                    .last()
                    .expect("ICE: empty unresolved ident");

                let path_location = unresolved_ident
                    .iter()
                    .map(|t| t.location)
                    .reduce(SourceLocation::merge)
                    .unwrap();

                let name = interner.resolve_lexeme(item_name.inner);
                let builtin_name = BuiltinTypes::from_name(name);

                if unresolved_ident.len() > 1 && builtin_name.is_some() {
                    // Emit error
                    diagnostics::emit_error(
                        path_location,
                        "cannot name builtin with a module",
                        [Label::new(path_location).with_color(Color::Red)],
                        None,
                        source_store,
                    );
                    *had_error = true;
                    return Err(());
                } else if let Some(builtin) = builtin_name {
                    assert!(generic_params.is_none());
                    UnresolvedTypeIds::SimpleBuiltin(builtin)
                } else {
                    let Ok(ident) = self.resolve_single_ident(
                        item_header,
                        interner,
                        source_store,
                        had_error,
                        unresolved_ident,
                    ) else {
                        return Err(());
                    };

                    let params: Vec<_> = params
                        .iter()
                        .map(|p| {
                            self.resolve_idents_in_type(
                                item_header,
                                interner,
                                source_store,
                                had_error,
                                p,
                                generic_params,
                            )
                        })
                        .collect::<Result<_, _>>()?;

                    UnresolvedTypeIds::GenericInstance {
                        id: ident,
                        id_token: item_name.inner.with_span(path_location),
                        params,
                    }
                }
            }
        };

        Ok(res)
    }

    pub fn resolve_idents_in_block(
        &self,
        item: ItemHeader,
        mut body: Vec<Op>,
        had_error: &mut bool,
        interner: &Interners,
        source_store: &SourceStorage,
        generic_params: Option<&Vec<Spanned<Spur>>>,
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
                        generic_params,
                    );
                    let temp_body = std::mem::take(&mut while_op.body_block);
                    while_op.body_block = self.resolve_idents_in_block(
                        item,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                        generic_params,
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
                        generic_params,
                    );
                    let temp_body = std::mem::take(&mut if_op.then_block);
                    if_op.then_block = self.resolve_idents_in_block(
                        item,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                        generic_params,
                    );
                    let temp_body = std::mem::take(&mut if_op.else_block);
                    if_op.else_block = self.resolve_idents_in_block(
                        item,
                        temp_body,
                        had_error,
                        interner,
                        source_store,
                        generic_params,
                    );
                }

                OpCode::UnresolvedIdent(ident) => {
                    let Ok(item_id) = self.resolve_single_ident(item, interner, source_store, had_error, &ident.path) else {
                        continue;
                    };

                    let mut resolved_generic_params = Vec::new();
                    for param in &ident.generic_params {
                        let UnresolvedType::Tokens(param) = param else { unreachable!() };
                        let Ok(f) = self.resolve_idents_in_type(
                            item,
                            interner,
                            source_store,
                            had_error,
                            param,
                            generic_params,
                        ) else { continue; };
                        resolved_generic_params.push(UnresolvedType::Id(f));
                    }

                    let found_item_header = self.item_headers[&item_id];
                    if !matches!(
                        found_item_header.kind(),
                        ItemKind::Function
                            | ItemKind::GenericFunction
                            | ItemKind::Const
                            | ItemKind::Memory
                    ) {
                        *had_error = true;
                        let mut labels = vec![Label::new(op.token.location).with_color(Color::Red)];
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
                            let name = interner.resolve_lexeme(found_item_header.name.inner);
                            format!("`{name}` is a top-level module")
                        };

                        diagnostics::emit_error(
                            op.token.location,
                            format!("cannot refer to a {:?} here", found_item_header.kind()),
                            labels,
                            note,
                            source_store,
                        );
                        continue;
                    }

                    op.code = OpCode::ResolvedIdent {
                        item_id,
                        generic_params: resolved_generic_params,
                    };
                }
                OpCode::UnresolvedCast { unresolved_type }
                | OpCode::UnresolvedPackStruct { unresolved_type }
                | OpCode::UnresolvedSizeOf { unresolved_type } => {
                    let UnresolvedType::Tokens(ty) = unresolved_type else { panic!("ICE: tried to resolve type on resolved type") };

                    let Ok(new_ty) = self.resolve_idents_in_type(item, interner, source_store, had_error, ty, generic_params) else {
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
        item: ItemHeader,
        mut def: UnresolvedStruct,
        had_error: &mut bool,
        interner: &Interners,
        source_store: &SourceStorage,
    ) -> UnresolvedStruct {
        for field in &mut def.fields {
            let UnresolvedType::Tokens(field_kind) = &field.kind else { unreachable!() };

            let Ok(new_kind) = self.resolve_idents_in_type(
                item,
                interner,
                source_store,
                had_error,
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
        interner: &Interners,
        source_store: &SourceStorage,
        had_error: &mut bool,
        item: ItemHeader,
    ) {
        // Top level modules are visible from every module, so let's make sure those are imported.
        let module_info = self.module_info.get_mut(&item.id()).unwrap();
        for (name, id) in &self.top_level_modules {
            let res = module_info.add_visible_symbol(
                *name,
                SourceLocation::new(FileId::dud(), 0..0),
                *id,
            );

            if let Err(prev_loc) = res {
                diagnostics::emit_error(
                    prev_loc,
                    "item has same name as top-level module",
                    [Label::new(prev_loc).with_color(Color::Red)],
                    None,
                    source_store,
                );
                *had_error = true;
            }
        }

        let module_imports = module_info.unresolved_imports.clone();

        for import in module_imports {
            let Ok(resolved_item) = self.resolve_single_ident(
                        item,
                        interner,
                        source_store,
                        had_error,
                        &import.inner,
                    ) else { continue };
            let item_name = self.get_item_header(resolved_item).name;
            let module_info = self.module_info.get_mut(&item.id()).unwrap();

            let res =
                module_info.add_visible_symbol(item_name.inner, import.location, resolved_item);
            if let Err(prev_loc) = res {
                *had_error = true;
                symbol_redef_error(import.location, prev_loc, source_store);
            }
        }
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
            .map(|(id, item)| (*id, *item))
            .collect();

        for (item_id, item) in items {
            trace!(name = interner.get_symbol_name(self, item_id));

            if item.kind() == ItemKind::StructDef {
                let def = self.structs_unresolved.remove(&item_id).unwrap();
                self.structs_unresolved.insert(
                    item_id,
                    self.resolve_idents_in_struct_def(
                        item,
                        def,
                        &mut had_error,
                        interner,
                        source_store,
                    ),
                );
            } else if item.kind() == ItemKind::Memory {
                let generic_params = match item.parent {
                    Some(parent_id)
                        if self.get_item_header(parent_id).kind == ItemKind::GenericFunction =>
                    {
                        Some(&self.function_data[&parent_id].generic_params)
                    }
                    _ => None,
                };

                let mut sig = self.item_signatures_unresolved.remove(&item_id).unwrap();
                let memory_type = sig.memory_type.as_mut().unwrap();
                let UnresolvedType::Tokens(memory_type_tokens) = &memory_type.inner else {
                    unreachable!()
                };
                let Ok(new_kind) = self.resolve_idents_in_type(
                    item,
                    interner,
                    source_store,
                    &mut had_error,
                    memory_type_tokens,
                    generic_params,
                ) else {
                    had_error = true;
                    continue;
                };
                memory_type.inner = UnresolvedType::Id(new_kind);

                self.item_signatures_unresolved.insert(item_id, sig);
            } else if item.kind() == ItemKind::Module {
                self.resolve_idents_in_module_imports(interner, source_store, &mut had_error, item);
            } else {
                let mut sig = self.item_signatures_unresolved.remove(&item_id).unwrap();

                let generic_params = if item.kind() == ItemKind::GenericFunction {
                    Some(&self.function_data[&item_id].generic_params)
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
                        item,
                        interner,
                        source_store,
                        &mut had_error,
                        kind_tokens,
                        generic_params,
                    ) else {
                        had_error = true;
                        continue;
                    };

                    kind.inner = UnresolvedType::Id(new_kind);
                }

                self.item_signatures_unresolved.insert(item_id, sig);
                let body = self.item_bodies.remove(&item_id).unwrap();

                self.item_bodies.insert(
                    item_id,
                    self.resolve_idents_in_block(
                        item,
                        body,
                        &mut had_error,
                        interner,
                        source_store,
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

                OpCode::ResolvedIdent { item_id, .. } => {
                    let found_item = self.item_headers[&item_id];

                    match found_item.kind() {
                        ItemKind::Const => {
                            let Some(vals) = self.const_vals.get( &found_item.id ) else {
                                let own_item = self.item_headers[&own_item_id];
                                let name = interner.resolve_lexeme(own_item.name.inner);
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
                        ItemKind::GenericFunction => {
                            unreachable!()
                        }

                        ItemKind::Assert | ItemKind::StructDef | ItemKind::Module => {
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
                i.kind() != ItemKind::Memory
                    && i.kind() != ItemKind::StructDef
                    && i.kind() != ItemKind::Module
                    && i.kind() != ItemKind::GenericFunction
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
