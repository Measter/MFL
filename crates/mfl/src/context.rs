use std::hash::Hash;

use ariadne::{Color, Label};
use hashbrown::HashMap;
use intcast::IntCast;
use lasso::Spur;
use smallvec::SmallVec;

use crate::{
    diagnostics,
    error_signal::ErrorSignal,
    ir::{
        Basic, Control, If, NameResolvedType, OpCode, StructDef, UnresolvedIdent, UnresolvedType,
        While,
    },
    option::OptionExt,
    pass_manager::PassContext,
    simulate::SimulatorValue,
    stores::{
        block::BlockId,
        source::{SourceLocation, Spanned, WithSpan},
        types::TypeId,
    },
    Stores,
};

use super::ir::NameResolvedOp;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LangItem {
    String,
    Alloc,
    Free,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ItemId(u16);

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ItemKind {
    Assert,
    Const,
    Variable,
    Function,
    GenericFunction,
    StructDef,
    Module,
}

#[derive(Debug, Clone, Copy)]
pub struct ItemHeader {
    pub name: Spanned<Spur>,
    pub id: ItemId,
    pub parent: Option<ItemId>,
    pub kind: ItemKind,
    pub lang_item: Option<LangItem>,
}

#[derive(Debug, Clone)]
pub struct UnresolvedItemSignature {
    pub exit: Spanned<Vec<Spanned<UnresolvedType>>>,
    pub entry: Spanned<Vec<Spanned<UnresolvedType>>>,
}

pub struct UnresolvedIr {
    item_signatures: HashMap<ItemId, UnresolvedItemSignature>,
    variable_type: HashMap<ItemId, Spanned<UnresolvedType>>,
    structs: HashMap<ItemId, StructDef<UnresolvedType>>,
    scopes: Vec<UnresolvedScope>,
}

impl UnresolvedIr {
    #[inline]
    #[track_caller]
    pub fn get_item_signature(&self, id: ItemId) -> &UnresolvedItemSignature {
        &self.item_signatures[&id]
    }

    #[inline]
    #[track_caller]
    pub fn get_variable_type(&self, id: ItemId) -> Spanned<&UnresolvedType> {
        let v = &self.variable_type[&id];
        (&v.inner).with_span(v.location)
    }

    #[inline]
    #[track_caller]
    pub fn get_scope(&self, id: ItemId) -> &UnresolvedScope {
        &self.scopes[id.0.to_usize()]
    }

    #[inline]
    #[track_caller]
    pub fn get_scope_mut(&mut self, id: ItemId) -> &mut UnresolvedScope {
        &mut self.scopes[id.0.to_usize()]
    }

    #[inline]
    #[track_caller]
    pub fn get_struct(&self, id: ItemId) -> &StructDef<UnresolvedType> {
        &self.structs[&id]
    }
}

impl UnresolvedIr {
    fn new() -> Self {
        UnresolvedIr {
            item_signatures: HashMap::new(),
            variable_type: HashMap::new(),
            structs: HashMap::new(),
            scopes: Vec::new(),
        }
    }
}

#[derive(Clone)]
pub struct NameResolvedItemSignature {
    pub exit: Vec<NameResolvedType>,
    pub entry: Vec<NameResolvedType>,
}

pub struct NameResolvedIr {
    item_signatures: HashMap<ItemId, NameResolvedItemSignature>,
    variable_type: HashMap<ItemId, NameResolvedType>,
    // Need to split this UnresolvedStruct business.
    structs: HashMap<ItemId, StructDef<NameResolvedType>>,
    scopes: Vec<NameResolvedScope>,
}

impl NameResolvedIr {
    #[inline]
    #[track_caller]
    pub fn get_item_signature(&self, id: ItemId) -> &NameResolvedItemSignature {
        &self.item_signatures[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_item_signature(&mut self, id: ItemId, sig: NameResolvedItemSignature) {
        self.item_signatures
            .insert(id, sig)
            .expect_none("Redefined item signature");
    }

    #[inline]
    #[track_caller]
    pub fn get_variable_type(&self, id: ItemId) -> &NameResolvedType {
        &self.variable_type[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_variable_type(&mut self, id: ItemId, def: NameResolvedType) {
        self.variable_type
            .insert(id, def)
            .expect_none("Redefined variable type");
    }

    #[inline]
    #[track_caller]
    pub fn get_scope(&self, id: ItemId) -> &NameResolvedScope {
        &self.scopes[id.0.to_usize()]
    }

    #[inline]
    #[track_caller]
    pub fn get_scope_mut(&mut self, id: ItemId) -> &mut NameResolvedScope {
        &mut self.scopes[id.0.to_usize()]
    }

    #[inline]
    #[track_caller]
    pub fn get_struct(&self, id: ItemId) -> &StructDef<NameResolvedType> {
        &self.structs[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_struct(&mut self, id: ItemId, def: StructDef<NameResolvedType>) {
        self.structs.insert(id, def).expect_none("Redefined struct");
    }
}

impl NameResolvedIr {
    fn new() -> Self {
        NameResolvedIr {
            item_signatures: HashMap::new(),
            variable_type: HashMap::new(),
            structs: HashMap::new(),
            scopes: Vec::new(),
        }
    }
}

pub struct TypeResolvedItemSignature {
    pub exit: Vec<TypeId>,
    pub entry: Vec<TypeId>,
}

pub struct TypeResolvedIr {
    item_signatures: HashMap<ItemId, TypeResolvedItemSignature>,
    variable_type: HashMap<ItemId, TypeId>,
}

impl TypeResolvedIr {
    #[inline]
    #[track_caller]
    pub fn get_item_signature(&self, id: ItemId) -> &TypeResolvedItemSignature {
        &self.item_signatures[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_item_signature(&mut self, id: ItemId, sig: TypeResolvedItemSignature) {
        self.item_signatures
            .insert(id, sig)
            .expect_none("Redefined item signature");
    }

    #[inline]
    #[track_caller]
    pub fn get_variable_type(&self, id: ItemId) -> TypeId {
        self.variable_type[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_variable_type(&mut self, id: ItemId, mem_type: TypeId) {
        self.variable_type
            .insert(id, mem_type)
            .expect_none("Redefined variable type");
    }
}

impl TypeResolvedIr {
    fn new() -> Self {
        TypeResolvedIr {
            item_signatures: HashMap::new(),
            variable_type: HashMap::new(),
        }
    }
}

pub struct Context {
    core_module_id: Option<ItemId>,
    top_level_modules: HashMap<Spur, ItemId>,
    lang_items: HashMap<LangItem, ItemId>,

    headers: Vec<ItemHeader>,
    const_vals: HashMap<ItemId, Vec<SimulatorValue>>,
    item_body: HashMap<ItemId, BlockId>,

    // TODO: Separate out the IRs from the rest of the context so that we don't
    // need to clone the bodies.
    urir: UnresolvedIr,
    nrir: NameResolvedIr,
    trir: TypeResolvedIr,

    // Bit of a hacky workaround for how I've done the struct resolution.
    generic_structs: Vec<ItemId>,
    generic_function_cache: HashMap<(ItemId, SmallVec<[TypeId; 4]>), ItemId>,
    generic_template_parameters: HashMap<ItemId, Vec<Spanned<Spur>>>,
}

impl Context {
    #[inline]
    pub fn get_all_items(&self) -> impl Iterator<Item = ItemHeader> + '_ {
        self.headers.iter().copied()
    }

    pub fn get_lang_items(&self) -> &HashMap<LangItem, ItemId> {
        &self.lang_items
    }

    pub fn set_core_module(&mut self, id: ItemId) {
        self.core_module_id = Some(id);
    }

    pub fn update_core_symbols(&mut self) {
        let core_module_id = self.core_module_id.expect("ICE: Core module not set");
        // For now this is just String.
        let core_scope = self.nrir.get_scope_mut(core_module_id);

        let string_item_id = self.lang_items[&LangItem::String];
        let string_header = self.headers[string_item_id.0.to_usize()];
        core_scope
            .add_visible_symbol(string_header.name, string_item_id)
            .expect("ICE: Core already contains String");
    }

    #[inline]
    pub fn urir(&self) -> &UnresolvedIr {
        &self.urir
    }

    #[inline]
    pub fn urir_mut(&mut self) -> &mut UnresolvedIr {
        &mut self.urir
    }

    #[inline]
    pub fn nrir(&self) -> &NameResolvedIr {
        &self.nrir
    }

    #[inline]
    pub fn nrir_mut(&mut self) -> &mut NameResolvedIr {
        &mut self.nrir
    }

    #[inline]
    pub fn trir(&self) -> &TypeResolvedIr {
        &self.trir
    }

    #[inline]
    pub fn trir_mut(&mut self) -> &mut TypeResolvedIr {
        &mut self.trir
    }

    #[inline]
    pub fn get_top_level_module(&self, name: Spur) -> Option<ItemId> {
        self.top_level_modules.get(&name).copied()
    }

    #[inline]
    pub fn get_item_header(&self, id: ItemId) -> ItemHeader {
        self.headers[id.0.to_usize()]
    }

    #[inline]
    #[track_caller]
    pub fn get_item_body(&self, id: ItemId) -> BlockId {
        self.item_body[&id]
    }

    #[inline]
    #[track_caller]
    pub fn set_item_body(&mut self, id: ItemId, block_id: BlockId) {
        self.item_body
            .insert(id, block_id)
            .expect_none("ICE: Set same item body multiple times");
    }

    #[inline]
    #[track_caller]
    pub fn get_consts(&self, id: ItemId) -> Option<&[SimulatorValue]> {
        self.const_vals.get(&id).map(|v| &**v)
    }

    #[inline]
    #[track_caller]
    pub fn set_consts(&mut self, id: ItemId, consts: Vec<SimulatorValue>) {
        self.const_vals
            .insert(id, consts)
            .expect_none("ICE: replaced existing const values");
    }

    pub fn get_generic_structs(&self) -> &[ItemId] {
        &self.generic_structs
    }

    #[inline]
    #[track_caller]
    pub fn get_function_template_paramaters(&self, id: ItemId) -> &[Spanned<Spur>] {
        &self.generic_template_parameters[&id]
    }
}

impl Context {
    pub fn new() -> Self {
        Context {
            core_module_id: None,
            top_level_modules: HashMap::new(),
            lang_items: HashMap::new(),
            headers: Vec::new(),
            item_body: HashMap::new(),
            const_vals: HashMap::new(),
            urir: UnresolvedIr::new(),
            nrir: NameResolvedIr::new(),
            trir: TypeResolvedIr::new(),
            generic_structs: Vec::new(),
            generic_function_cache: HashMap::new(),
            generic_template_parameters: HashMap::new(),
        }
    }

    fn add_to_parent(
        &mut self,
        stores: &Stores,
        had_error: &mut ErrorSignal,
        parent_id: ItemId,
        child_name: Spanned<Spur>,
        child_id: ItemId,
    ) {
        let parent_scope = &mut self.nrir.scopes[parent_id.0.to_usize()];
        if let Err(prev_loc) = parent_scope.add_child(child_name, child_id) {
            had_error.set();
            make_symbol_redef_error(stores, child_name.location, prev_loc);
        }
    }

    fn new_header(
        &mut self,
        name: Spanned<Spur>,
        parent: Option<ItemId>,
        kind: ItemKind,
    ) -> ItemHeader {
        let new_id = self.headers.len();
        let new_id = ItemId(new_id.to_u16().unwrap());

        let item_header = ItemHeader {
            name,
            id: new_id,
            parent,
            kind,
            lang_item: None,
        };

        self.headers.push(item_header);
        self.urir.scopes.push(UnresolvedScope::new());
        self.nrir.scopes.push(NameResolvedScope::new());
        item_header
    }

    pub fn new_module(
        &mut self,
        stores: &Stores,
        had_error: &mut ErrorSignal,
        name: Spanned<Spur>,
        parent: Option<ItemId>,
        is_top_level: bool,
    ) -> ItemId {
        let header = self.new_header(name, parent, ItemKind::Module);

        if let Some(parent_id) = parent {
            self.add_to_parent(stores, had_error, parent_id, name, header.id);
        }

        if is_top_level {
            self.top_level_modules.insert(name.inner, header.id);
        }

        header.id
    }

    pub fn new_function(
        &mut self,
        stores: &Stores,
        had_error: &mut ErrorSignal,
        name: Spanned<Spur>,
        parent: ItemId,
        entry_stack: Spanned<Vec<Spanned<UnresolvedType>>>,
        exit_stack: Spanned<Vec<Spanned<UnresolvedType>>>,
    ) -> ItemId {
        let header = self.new_header(name, Some(parent), ItemKind::Function);
        self.urir.item_signatures.insert(
            header.id,
            UnresolvedItemSignature {
                exit: exit_stack,
                entry: entry_stack,
            },
        );

        self.add_to_parent(stores, had_error, parent, name, header.id);
        header.id
    }

    pub fn new_assert(
        &mut self,
        stores: &Stores,
        had_error: &mut ErrorSignal,
        name: Spanned<Spur>,
        parent: ItemId,
    ) -> ItemId {
        let header = self.new_header(name, Some(parent), ItemKind::Assert);

        // Hardcode a bool output type
        let bool_symbol = stores.strings.get("bool");
        self.urir.item_signatures.insert(
            header.id,
            UnresolvedItemSignature {
                exit: vec![UnresolvedType::Simple(UnresolvedIdent {
                    span: name.location,
                    is_from_root: false,
                    path: vec![bool_symbol.with_span(name.location)],
                    generic_params: None,
                })
                .with_span(name.location)]
                .with_span(name.location),
                entry: Vec::new().with_span(name.location),
            },
        );

        self.add_to_parent(stores, had_error, parent, name, header.id);
        header.id
    }

    pub fn new_const(
        &mut self,
        stores: &Stores,
        had_error: &mut ErrorSignal,
        name: Spanned<Spur>,
        parent: ItemId,
        exit_stack: Spanned<Vec<Spanned<UnresolvedType>>>,
    ) -> ItemId {
        let header = self.new_header(name, Some(parent), ItemKind::Const);

        self.urir.item_signatures.insert(
            header.id,
            UnresolvedItemSignature {
                exit: exit_stack,
                entry: Vec::new().with_span(name.location),
            },
        );

        self.add_to_parent(stores, had_error, parent, name, header.id);
        header.id
    }

    pub fn new_generic_function(
        &mut self,
        stores: &Stores,
        had_error: &mut ErrorSignal,
        name: Spanned<Spur>,
        parent: ItemId,
        entry_stack: Spanned<Vec<Spanned<UnresolvedType>>>,
        exit_stack: Spanned<Vec<Spanned<UnresolvedType>>>,
        params: Vec<Spanned<Spur>>,
    ) -> ItemId {
        let header = self.new_header(name, Some(parent), ItemKind::GenericFunction);

        self.urir.item_signatures.insert(
            header.id,
            UnresolvedItemSignature {
                exit: exit_stack,
                entry: entry_stack,
            },
        );

        self.generic_template_parameters.insert(header.id, params);
        self.add_to_parent(stores, had_error, parent, name, header.id);
        header.id
    }

    pub fn new_struct(
        &mut self,
        stores: &Stores,
        had_error: &mut ErrorSignal,
        module: ItemId,
        def: StructDef<UnresolvedType>,
    ) -> ItemId {
        let name = def.name;
        let header = self.new_header(name, Some(module), ItemKind::StructDef);

        if def.generic_params.is_some() {
            self.generic_structs.push(header.id);
        }

        self.urir.structs.insert(header.id, def);
        self.add_to_parent(stores, had_error, module, name, header.id);
        header.id
    }

    pub fn new_variable(
        &mut self,
        stores: &Stores,
        had_error: &mut ErrorSignal,
        name: Spanned<Spur>,
        parent: ItemId,
        variable_type: Spanned<UnresolvedType>,
    ) -> ItemId {
        let header = self.new_header(name, Some(parent), ItemKind::Variable);
        self.urir.variable_type.insert(header.id, variable_type);
        self.add_to_parent(stores, had_error, parent, name, header.id);
        header.id
    }

    pub fn set_lang_item(
        &mut self,
        stores: &Stores,
        had_error: &mut ErrorSignal,
        lang_item_token: Spanned<Spur>,
        item_id: ItemId,
    ) {
        let token_string = stores.strings.resolve(lang_item_token.inner);
        let kind = match token_string {
            "string" => LangItem::String,
            "alloc" => LangItem::Alloc,
            "free" => LangItem::Free,
            _ => {
                diagnostics::emit_error(
                    stores,
                    lang_item_token.location,
                    format!("Unknown lang item `{token_string}`"),
                    [Label::new(lang_item_token.location).with_color(Color::Red)],
                    None,
                );
                had_error.set();
                return;
            }
        };

        self.lang_items.insert(kind, item_id);
        self.headers[item_id.0 as usize].lang_item = Some(kind);
    }

    // `self` is only used in recursion, but it makes conceptual sense for this to be a method.
    #[allow(clippy::only_used_in_recursion)]
    fn expand_generic_params_in_type(
        &self,
        base: &NameResolvedType,
        param_map: &HashMap<Spur, NameResolvedType>,
    ) -> NameResolvedType {
        match base {
            NameResolvedType::SimpleCustom { .. } | NameResolvedType::SimpleBuiltin(_) => {
                base.clone()
            }
            NameResolvedType::SimpleGenericParam(p) => param_map[&p.inner].clone(),
            NameResolvedType::Array(inner, len) => {
                let inner = self.expand_generic_params_in_type(inner, param_map);
                NameResolvedType::Array(Box::new(inner), *len)
            }
            NameResolvedType::Pointer(inner) => {
                let inner = self.expand_generic_params_in_type(inner, param_map);
                NameResolvedType::Pointer(Box::new(inner))
            }
            NameResolvedType::GenericInstance {
                id,
                id_token,
                params,
            } => {
                let params = params
                    .iter()
                    .map(|t| self.expand_generic_params_in_type(t, param_map))
                    .collect();
                NameResolvedType::GenericInstance {
                    id: *id,
                    id_token: *id_token,
                    params,
                }
            }
        }
    }

    fn expand_generic_params_in_block(
        &mut self,
        stores: &mut Stores,
        pass_ctx: &mut PassContext,
        block_id: BlockId,
        param_map: &HashMap<Spur, NameResolvedType>,
        old_alloc_map: &HashMap<ItemId, ItemId>,
    ) -> BlockId {
        let mut new_body = Vec::new();

        let old_block = stores.blocks.get_block(block_id).clone();
        for op_id in old_block.ops {
            let op_code = stores.ops.get_name_resolved(op_id).clone();
            let new_code = match op_code {
                OpCode::Basic(bo) => match bo {
                    Basic::Control(Control::If(if_op)) => {
                        let resolved_condition = self.expand_generic_params_in_block(
                            stores,
                            pass_ctx,
                            if_op.condition,
                            param_map,
                            old_alloc_map,
                        );
                        let resolved_then = self.expand_generic_params_in_block(
                            stores,
                            pass_ctx,
                            if_op.then_block,
                            param_map,
                            old_alloc_map,
                        );
                        let resolved_else = self.expand_generic_params_in_block(
                            stores,
                            pass_ctx,
                            if_op.else_block,
                            param_map,
                            old_alloc_map,
                        );
                        OpCode::Basic(Basic::Control(Control::If(If {
                            tokens: if_op.tokens,
                            condition: resolved_condition,
                            then_block: resolved_then,
                            else_block: resolved_else,
                        })))
                    }
                    Basic::Control(Control::While(while_op)) => {
                        let resolved_condition = self.expand_generic_params_in_block(
                            stores,
                            pass_ctx,
                            while_op.condition,
                            param_map,
                            old_alloc_map,
                        );
                        let resolved_body = self.expand_generic_params_in_block(
                            stores,
                            pass_ctx,
                            while_op.body_block,
                            param_map,
                            old_alloc_map,
                        );

                        OpCode::Basic(Basic::Control(Control::While(While {
                            tokens: while_op.tokens,
                            condition: resolved_condition,
                            body_block: resolved_body,
                        })))
                    }
                    _ => OpCode::Basic(bo),
                },
                OpCode::Complex(co) => match co {
                    ref op_code @ (NameResolvedOp::Cast { ref id }
                    | NameResolvedOp::PackStruct { ref id }
                    | NameResolvedOp::SizeOf { ref id }) => {
                        if let Some(type_item) = id.item_id() {
                            pass_ctx
                                .ensure_declare_structs(self, stores, type_item)
                                .unwrap();
                        }
                        let new_id = self.expand_generic_params_in_type(id, param_map);
                        match op_code {
                            NameResolvedOp::Cast { .. } => {
                                OpCode::Complex(NameResolvedOp::Cast { id: new_id })
                            }
                            NameResolvedOp::PackStruct { .. } => {
                                OpCode::Complex(NameResolvedOp::PackStruct { id: new_id })
                            }
                            NameResolvedOp::SizeOf { .. } => {
                                OpCode::Complex(NameResolvedOp::SizeOf { id: new_id })
                            }
                            _ => unreachable!(),
                        }
                    }

                    NameResolvedOp::Const { id } => OpCode::Complex(NameResolvedOp::Const { id }),
                    NameResolvedOp::Variable { id, is_global } => {
                        let id = if let Some(new_id) = old_alloc_map.get(&id) {
                            *new_id
                        } else {
                            id
                        };
                        OpCode::Complex(NameResolvedOp::Variable { id, is_global })
                    }

                    NameResolvedOp::CallFunction { id, generic_params } => {
                        let new_params = if let Some(gps) = generic_params.as_ref() {
                            let mut new_params = Vec::new();
                            for gp in gps {
                                new_params.push(self.expand_generic_params_in_type(gp, param_map));
                            }

                            Some(new_params)
                        } else {
                            None
                        };

                        OpCode::Complex(NameResolvedOp::CallFunction {
                            id,
                            generic_params: new_params,
                        })
                    }
                },
            };

            let old_token = stores.ops.get_token(op_id);
            let mut old_unresolved = stores.ops.get_unresolved(op_id).clone();
            // Need to patch up the old unresolved opcode so that the If and While codes point to the new blocks.
            match (&mut old_unresolved, &new_code) {
                (
                    OpCode::Basic(Basic::Control(Control::If(old_if))),
                    OpCode::Basic(Basic::Control(Control::If(new_if))),
                ) => {
                    old_if.condition = new_if.condition;
                    old_if.then_block = new_if.then_block;
                    old_if.else_block = new_if.else_block;
                }
                (
                    OpCode::Basic(Basic::Control(Control::While(old_while))),
                    OpCode::Basic(Basic::Control(Control::While(new_while))),
                ) => {
                    old_while.condition = new_while.condition;
                    old_while.body_block = new_while.body_block
                }
                _ => {}
            }

            let new_op_id = stores.ops.new_op(old_unresolved, old_token);
            stores.ops.set_name_resolved(new_op_id, new_code);

            new_body.push(new_op_id);
        }

        stores.blocks.new_block(new_body)
    }

    pub fn get_generic_function_instance(
        &mut self,
        stores: &mut Stores,
        pass_ctx: &mut PassContext,
        had_error: &mut ErrorSignal,
        base_fn_id: ItemId,
        resolved_generic_params: SmallVec<[TypeId; 4]>,
        unresolved_generic_params: SmallVec<[NameResolvedType; 4]>,
    ) -> Result<ItemId, ()> {
        if let Some(id) = self
            .generic_function_cache
            .get(&(base_fn_id, resolved_generic_params.clone()))
        {
            return Ok(*id);
        }

        // We need to make sure the generic function has been ident-resolved before this step.
        let resolve_res = pass_ctx.ensure_ident_resolved_signature(self, stores, base_fn_id);
        let resolve_res =
            resolve_res.and_then(|_| pass_ctx.ensure_ident_resolved_body(self, stores, base_fn_id));
        if resolve_res.is_err() {
            had_error.set();
            return Err(());
        }

        let base_fd_params = &self.generic_template_parameters[&base_fn_id];
        let base_header = self.get_item_header(base_fn_id);
        assert_eq!(resolved_generic_params.len(), base_fd_params.len());
        assert_eq!(unresolved_generic_params.len(), base_fd_params.len());

        let param_map: HashMap<_, _> = base_fd_params
            .iter()
            .zip(unresolved_generic_params)
            .map(|(name, ty)| (name.inner, ty))
            .collect();

        // Essentially we need to do what the parser does what in encounters a non-generic function.
        let orig_unresolved_sig = self.urir.get_item_signature(base_fn_id).clone();
        let orig_name_resolved_sig = self.nrir.get_item_signature(base_fn_id);
        let mut instantiated_sig = NameResolvedItemSignature {
            exit: Vec::new(),
            entry: Vec::new(),
        };

        for stack_item in &orig_name_resolved_sig.exit {
            let new_id = self.expand_generic_params_in_type(stack_item, &param_map);
            instantiated_sig.exit.push(new_id);
        }

        for stack_item in &orig_name_resolved_sig.entry {
            let new_id = self.expand_generic_params_in_type(stack_item, &param_map);
            instantiated_sig.entry.push(new_id);
        }

        let new_name = stores.build_mangled_name(base_header.name.inner, &resolved_generic_params);

        let new_proc_id = self.new_function(
            stores,
            had_error,
            new_name.with_span(base_header.name.location),
            base_header.parent.unwrap(),
            orig_unresolved_sig.entry,
            orig_unresolved_sig.exit,
        );
        self.nrir.set_item_signature(new_proc_id, instantiated_sig);

        // Clone the variable items.
        let base_scope = self.nrir.get_scope(base_fn_id).clone();
        let mut old_alloc_map = HashMap::new();
        for (&child_name, &child_item) in base_scope.get_child_items() {
            let child_item_header = self.get_item_header(child_item.inner);
            if child_item_header.kind != ItemKind::Variable {
                // We just reuse the existing item, so we need to add it manually.
                let new_scope = self.nrir.get_scope_mut(new_proc_id);
                new_scope
                    .add_child(child_name.with_span(child_item.location), child_item.inner)
                    .unwrap();
                continue;
            }

            if pass_ctx
                .ensure_ident_resolved_signature(self, stores, child_item_header.id)
                .is_err()
            {
                had_error.set();
                continue;
            }

            let alloc_type_unresolved = self.urir.get_variable_type(child_item_header.id);
            let new_alloc_id = self.new_variable(
                stores,
                had_error,
                child_item_header.name,
                new_proc_id,
                alloc_type_unresolved.map(|i| i.clone()),
            );
            let alloc_type = self.nrir.get_variable_type(child_item_header.id);
            let new_variable_sig = self.expand_generic_params_in_type(alloc_type, &param_map);
            self.nrir.set_variable_type(new_alloc_id, new_variable_sig);
            pass_ctx.add_new_item(new_alloc_id, child_item_header.id);

            old_alloc_map.insert(child_item_header.id, new_alloc_id);
        }

        let body = self.get_item_body(base_fn_id);
        let new_body =
            self.expand_generic_params_in_block(stores, pass_ctx, body, &param_map, &old_alloc_map);
        self.set_item_body(new_proc_id, new_body);
        self.generic_function_cache
            .insert((base_fn_id, resolved_generic_params), new_proc_id);
        pass_ctx.add_new_item(new_proc_id, base_fn_id);

        Ok(new_proc_id)
    }

    pub fn get_visible_symbol(&self, from: ItemHeader, symbol: Spur) -> Option<ItemId> {
        // 1. Check ourselves
        if from.name.inner == symbol {
            return Some(from.id);
        }

        // 2. Check our children
        let own_scope = self.nrir.get_scope(from.id);
        if let Some(child) = own_scope.get_symbol(symbol) {
            return Some(child);
        }

        // 3. If we're not a module traverse up the tree checking siblings until we hit a module.
        if from.kind != ItemKind::Module {
            let mut parent = from.parent;
            while let Some(parent_id) = parent {
                let parent_scope = self.nrir.get_scope(parent_id);
                if let Some(child) = parent_scope.get_symbol(symbol) {
                    return Some(child);
                }

                let parent_header = self.get_item_header(parent_id);
                if parent_header.kind == ItemKind::Module {
                    break;
                }
                parent = parent_header.parent;
            }
        }

        // 4. Check top level modules
        self.top_level_modules.get(&symbol).copied()
    }
}

pub struct UnresolvedScope {
    imports: Vec<UnresolvedIdent>,
}

impl UnresolvedScope {
    pub fn add_unresolved_import(&mut self, path: UnresolvedIdent) {
        self.imports.push(path);
    }

    pub fn imports(&self) -> &[UnresolvedIdent] {
        &self.imports
    }

    fn new() -> UnresolvedScope {
        UnresolvedScope {
            imports: Vec::new(),
        }
    }
}

#[derive(Clone)]
pub struct NameResolvedScope {
    child_items: HashMap<Spur, Spanned<ItemId>>,
    visible_symbols: HashMap<Spur, Spanned<ItemId>>,
}

impl NameResolvedScope {
    #[inline]
    pub fn get_symbol(&self, name: Spur) -> Option<ItemId> {
        self.visible_symbols.get(&name).map(|id| id.inner)
    }

    #[inline]
    pub fn get_child_items(&self) -> &HashMap<Spur, Spanned<ItemId>> {
        &self.child_items
    }

    fn add_child(&mut self, name: Spanned<Spur>, id: ItemId) -> Result<(), SourceLocation> {
        use hashbrown::hash_map::Entry;
        match self.child_items.entry(name.inner) {
            Entry::Occupied(a) => return Err(a.get().location),
            Entry::Vacant(a) => a.insert(id.with_span(name.location)),
        };

        // Children are added before imports are resolved, so this should never fail.
        self.visible_symbols
            .insert(name.inner, id.with_span(name.location))
            .expect_none("ICE: Name collision when adding child");
        Ok(())
    }

    pub fn add_visible_symbol(
        &mut self,
        symbol: Spanned<Spur>,
        id: ItemId,
    ) -> Result<(), SourceLocation> {
        use hashbrown::hash_map::Entry;
        match self.visible_symbols.entry(symbol.inner) {
            Entry::Occupied(a) => return Err(a.get().location),
            Entry::Vacant(a) => a.insert(id.with_span(symbol.location)),
        };
        Ok(())
    }

    fn new() -> NameResolvedScope {
        NameResolvedScope {
            child_items: HashMap::new(),
            visible_symbols: HashMap::new(),
        }
    }
}

pub fn make_symbol_redef_error(stores: &Stores, new_def: SourceLocation, prev_def: SourceLocation) {
    diagnostics::emit_error(
        stores,
        new_def,
        "item of that name already exists",
        [
            Label::new(new_def).with_color(Color::Red),
            Label::new(prev_def)
                .with_color(Color::Cyan)
                .with_message("previously defined here"),
        ],
        None,
    );
}
