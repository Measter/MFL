use std::{fmt::Write, ops::Not};

use ariadne::{Color, Label};
use color_eyre::{eyre::eyre, Result};
use hashbrown::{HashMap, HashSet};
use lasso::Spur;
use tracing::debug_span;

use crate::{
    diagnostics,
    interners::Interner,
    opcode::{Op, OpCode},
    program::{ItemId, ItemKind, Program},
    source_file::{SourceStorage, WithSpan},
    type_store::{BuiltinTypes, UnresolvedType, UnresolvedTypeIds},
};

fn mangle_type_name(interner: &mut Interner, ty: &UnresolvedTypeIds, name: &mut String) {
    match ty {
        UnresolvedTypeIds::SimpleCustom { token, .. } => {
            let t_name = interner.resolve(token.inner);
            name.push_str(t_name);
        }
        UnresolvedTypeIds::SimpleBuiltin(t) => {
            let t_name = match t {
                BuiltinTypes::U8 => "u8",
                BuiltinTypes::U16 => "u16",
                BuiltinTypes::U32 => "u32",
                BuiltinTypes::U64 => "u64",
                BuiltinTypes::S8 => "s8",
                BuiltinTypes::S16 => "s16",
                BuiltinTypes::S32 => "s32",
                BuiltinTypes::S64 => "s64",
                BuiltinTypes::Bool => "bool",
                BuiltinTypes::String => "String",
            };
            name.push_str(t_name);
        }
        UnresolvedTypeIds::SimpleGenericParam(_) => unreachable!(),
        UnresolvedTypeIds::Array(t, len) => {
            mangle_type_name(interner, t, name);
            write!(name, "$AO${len}$AC$").unwrap();
        }
        UnresolvedTypeIds::Pointer(t) => {
            write!(name, "ptr$PO$").unwrap();
            mangle_type_name(interner, t, name);
            write!(name, "$PC$").unwrap();
        }
        UnresolvedTypeIds::GenericInstance {
            id_token, params, ..
        } => {
            let t_name = interner.resolve(id_token.inner);
            write!(name, "{t_name}$GO$").unwrap();
            let [first, rest @ ..] = params.as_slice() else { unreachable!() };
            mangle_type_name(interner, first, name);
            for r in rest {
                name.push('_');
                mangle_type_name(interner, r, name);
            }

            name.push_str("$GC$");
        }
    }
}

fn build_mangled_name(interner: &mut Interner, base: Spur, params: &[UnresolvedType]) -> String {
    let mut name = interner.resolve(base).to_owned();
    name.push_str("$GO$");

    let [UnresolvedType::Id(first), rest @ ..] = params else { unreachable!() };
    mangle_type_name(interner, first, &mut name);

    for tn in rest {
        name.push('_');
        let UnresolvedType::Id(tn) = tn else { unreachable!() };
        mangle_type_name(interner, tn, &mut name);
    }

    name.push_str("$GC$");
    name
}

fn expand_generic_params_in_type(
    base: &UnresolvedTypeIds,
    param_map: &HashMap<Spur, &UnresolvedTypeIds>,
) -> UnresolvedTypeIds {
    match base {
        UnresolvedTypeIds::SimpleCustom { .. } | UnresolvedTypeIds::SimpleBuiltin(_) => {
            base.clone()
        }
        UnresolvedTypeIds::SimpleGenericParam(p) => param_map[&p.inner].clone(),
        UnresolvedTypeIds::Array(inner, len) => {
            let inner = expand_generic_params_in_type(inner, param_map);
            UnresolvedTypeIds::Array(Box::new(inner), *len)
        }
        UnresolvedTypeIds::Pointer(inner) => {
            let inner = expand_generic_params_in_type(inner, param_map);
            UnresolvedTypeIds::Pointer(Box::new(inner))
        }
        UnresolvedTypeIds::GenericInstance {
            id,
            id_token,
            params,
        } => {
            let params = params
                .iter()
                .map(|t| expand_generic_params_in_type(t, param_map))
                .collect();
            UnresolvedTypeIds::GenericInstance {
                id: *id,
                id_token: *id_token,
                params,
            }
        }
    }
}

fn expand_generic_params_in_block(
    block: &mut [Op],
    param_map: &HashMap<Spur, &UnresolvedTypeIds>,
    alloc_map: &HashMap<ItemId, ItemId>,
) {
    for op in block {
        match &mut op.code {
            OpCode::While(while_op) => {
                expand_generic_params_in_block(&mut while_op.condition, param_map, alloc_map);
                expand_generic_params_in_block(&mut while_op.body_block, param_map, alloc_map);
            }
            OpCode::If(if_op) => {
                expand_generic_params_in_block(&mut if_op.condition, param_map, alloc_map);
                expand_generic_params_in_block(&mut if_op.then_block, param_map, alloc_map);
                expand_generic_params_in_block(&mut if_op.else_block, param_map, alloc_map);
            }

            OpCode::ResolvedIdent {
                generic_params,
                item_id,
            } => {
                for p in generic_params {
                    let UnresolvedType::Id(p) = p else { unreachable!() };
                    *p = expand_generic_params_in_type(p, param_map);
                }
                if let Some(new_id) = alloc_map.get(item_id) {
                    *item_id = *new_id;
                }
            }
            OpCode::UnresolvedCast { unresolved_type }
            | OpCode::UnresolvedPackStruct { unresolved_type }
            | OpCode::UnresolvedSizeOf { unresolved_type } => {
                let UnresolvedType::Id(p) = unresolved_type else { unreachable!() };
                *p = expand_generic_params_in_type(p, param_map);
            }

            _ => {}
        }
    }
}

impl Program {
    fn get_generic_function_instance(
        &mut self,
        interner: &mut Interner,
        source_store: &SourceStorage,
        fn_id: ItemId,
        generic_params: &[UnresolvedType],
    ) -> ItemId {
        let base_fd_params = &self.generic_template_parameters[&fn_id];

        let base_header = self.get_item_header(fn_id);
        assert_eq!(generic_params.len(), base_fd_params.len());

        let new_name = build_mangled_name(interner, base_header.name.inner, generic_params);
        if let Some(id) = self.generic_functions_map.get(&(fn_id, new_name.clone())) {
            return *id;
        }

        let param_map: HashMap<_, _> = base_fd_params
            .iter()
            .zip(generic_params)
            .map(|(name, ty)| {
                let UnresolvedType::Id(ty) = ty else {unreachable!()};
                (name.inner, ty)
            })
            .collect();

        // Essentially, we need to do what the parser does when it encounters a non-generic function.
        let mut exit_stack = Vec::new();
        let mut entry_stack = Vec::new();
        let old_sig = &self.item_signatures_unresolved[&fn_id];

        for stack_item in &old_sig.exit_stack.inner {
            let UnresolvedType::Id(stack_type) = &stack_item.inner else { unreachable!() };
            let new_id = expand_generic_params_in_type(stack_type, &param_map);
            let new_type = UnresolvedType::Id(new_id);
            exit_stack.push(new_type.with_span(stack_item.location));
        }

        for stack_item in &old_sig.entry_stack.inner {
            let UnresolvedType::Id(stack_type) = &stack_item.inner else { unreachable!() };
            let new_id = expand_generic_params_in_type(stack_type, &param_map);
            let new_type = UnresolvedType::Id(new_id);
            entry_stack.push(new_type.with_span(stack_item.location));
        }

        let new_name_spur = interner.intern(&new_name);
        let new_proc_id = self.new_function(
            source_store,
            &mut false,
            new_name_spur.with_span(base_header.name.location),
            base_header.parent.unwrap(),
            entry_stack.with_span(old_sig.entry_stack.location),
            exit_stack.with_span(old_sig.exit_stack.location),
        );

        // Ugh...
        let base_scope = self.get_scope(fn_id).clone();

        let mut old_alloc_map = HashMap::new();
        for (&name, &item) in base_scope.get_child_items() {
            let item_header = self.get_item_header(item.inner);
            if item_header.kind != ItemKind::Memory {
                // We just reuse the existing item, so we need to add it manually.
                let new_scope = self.get_scope_mut(new_proc_id);
                new_scope
                    .add_child(name.with_span(item.location), item.inner)
                    .unwrap();
                continue;
            }

            let alloc_type = &self.memory_type_unresolved[&item_header.id];
            let UnresolvedType::Id(alloc_memory_type) = &alloc_type.inner else { unreachable!() };

            let new_memory_sig = expand_generic_params_in_type(alloc_memory_type, &param_map);
            let new_sig = UnresolvedType::Id(new_memory_sig).with_span(alloc_type.location);

            let new_alloc_id = self.new_memory(
                source_store,
                &mut false,
                item_header.name,
                new_proc_id,
                new_sig,
            );

            old_alloc_map.insert(item_header.id, new_alloc_id);
        }

        let mut body = self.item_bodies[&fn_id].clone();
        expand_generic_params_in_block(&mut body, &param_map, &old_alloc_map);
        // TODO: Need to clone allocs and consts, and then update the body with the new IDs.
        self.set_item_body(new_proc_id, body);
        self.generic_functions_map
            .insert((fn_id, new_name), new_proc_id);

        new_proc_id
    }

    fn instantiate_generic_functions_in_block(
        &mut self,
        interner: &mut Interner,
        source_store: &SourceStorage,
        had_error: &mut bool,
        queue: &mut Vec<ItemId>,
        seen_ids: &mut HashSet<ItemId>,
        mut body: Vec<Op>,
    ) -> Vec<Op> {
        for op in &mut body {
            match &mut op.code {
                OpCode::While(while_op) => {
                    let temp_body = std::mem::take(&mut while_op.condition);
                    while_op.condition = self.instantiate_generic_functions_in_block(
                        interner,
                        source_store,
                        had_error,
                        queue,
                        seen_ids,
                        temp_body,
                    );

                    let temp_body = std::mem::take(&mut while_op.body_block);
                    while_op.body_block = self.instantiate_generic_functions_in_block(
                        interner,
                        source_store,
                        had_error,
                        queue,
                        seen_ids,
                        temp_body,
                    );
                }
                OpCode::If(if_op) => {
                    let temp_body = std::mem::take(&mut if_op.condition);
                    if_op.condition = self.instantiate_generic_functions_in_block(
                        interner,
                        source_store,
                        had_error,
                        queue,
                        seen_ids,
                        temp_body,
                    );

                    let temp_body = std::mem::take(&mut if_op.then_block);
                    if_op.then_block = self.instantiate_generic_functions_in_block(
                        interner,
                        source_store,
                        had_error,
                        queue,
                        seen_ids,
                        temp_body,
                    );

                    let temp_body = std::mem::take(&mut if_op.else_block);
                    if_op.else_block = self.instantiate_generic_functions_in_block(
                        interner,
                        source_store,
                        had_error,
                        queue,
                        seen_ids,
                        temp_body,
                    );
                }
                OpCode::ResolvedIdent {
                    item_id,
                    generic_params,
                } if self.get_item_header(*item_id).kind == ItemKind::GenericFunction => {
                    if generic_params.is_empty() {
                        *had_error = true;
                        diagnostics::emit_error(
                            op.token.location,
                            "generic function call missing generic parameters",
                            [Label::new(op.token.location).with_color(Color::Red)],
                            None,
                            source_store,
                        );

                        continue;
                    }

                    let new_id = self.get_generic_function_instance(
                        interner,
                        source_store,
                        *item_id,
                        generic_params,
                    );
                    *item_id = new_id;

                    if seen_ids.insert(new_id) {
                        // Not seen before
                        queue.push(new_id);
                    }
                }
                _ => {}
            }
        }

        body
    }

    pub fn instantiate_generic_functions(
        &mut self,
        interner: &mut Interner,
        source_store: &SourceStorage,
    ) -> Result<()> {
        let _span = debug_span!(stringify!(Program::instantiate_generic_functions)).entered();
        let mut had_error = false;

        let mut queue: Vec<_> = self
            .item_headers
            .iter()
            .filter(|i| i.kind() == ItemKind::Function)
            .map(|i| i.id)
            .collect();
        let mut seen_ids = HashSet::new();

        while let Some(item_id) = queue.pop() {
            seen_ids.insert(item_id);
            let body = self.item_bodies.remove(&item_id).unwrap();
            let new_body = self.instantiate_generic_functions_in_block(
                interner,
                source_store,
                &mut had_error,
                &mut queue,
                &mut seen_ids,
                body,
            );

            self.item_bodies.insert(item_id, new_body);
        }

        had_error
            .not()
            .then_some(())
            .ok_or_else(|| eyre!("failed to instantiate generic functions"))
    }
}
