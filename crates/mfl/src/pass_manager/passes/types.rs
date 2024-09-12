use stores::items::ItemId;

use crate::{
    error_signal::ErrorSignal,
    ir::NameResolvedType,
    pass_manager::{static_analysis::ensure_structs_declared_in_type, PassManager},
    stores::{diagnostics::Diagnostic, types::TypeKind},
    Stores,
};

pub fn declare_struct(stores: &mut Stores, had_error: &mut ErrorSignal, cur_id: ItemId) {
    let def = stores.sigs.nrir.get_struct(cur_id).clone();
    // We check if the name already exists by trying to resolve it.
    if let Ok(existing_info) = stores.types.resolve_type(
        stores.strings,
        &NameResolvedType::SimpleCustom {
            id: cur_id,
            token: def.name,
        },
    ) {
        if let Some(loc) = existing_info.location {
            // The user defined the type.
            Diagnostic::error(def.name.location, "type with this name already exists")
                .with_help_label(loc, "already defined here")
                .attached(stores.diags, cur_id);
        } else {
            // It's a builtin type
            Diagnostic::error(
                def.name.location,
                "cannot define struct with name of a primitive",
            )
            .attached(stores.diags, cur_id);
        }

        had_error.set();
    }

    let has_generics = !def.generic_params.is_empty();
    let def_name = def.name;

    let friendly_name = stores.strings.try_get_friendly_name(cur_id).unwrap();
    let mangled_name = stores.strings.try_get_mangled_name(cur_id).unwrap();

    if has_generics {
        stores.types.add_type(
            friendly_name,
            mangled_name,
            def_name.location,
            TypeKind::GenericStructBase(cur_id),
        );
    } else {
        stores.types.add_type(
            friendly_name,
            mangled_name,
            def_name.location,
            TypeKind::Struct(cur_id),
        );
    }
}

pub fn define_struct(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
    let def = stores.sigs.nrir.get_struct(cur_id).clone();
    for field in &def.fields {
        // Failure here can be handled by the type resolver.
        ensure_structs_declared_in_type(stores, pass_manager, had_error, &field.kind.inner);
    }

    if !def.generic_params.is_empty() {
        stores
            .types
            .partially_resolve_generic_struct(stores.strings, cur_id, &def);
    } else if let Err(missing_token) =
        stores
            .types
            .define_fixed_struct(stores.strings, cur_id, &def)
    {
        // The type that failed to resolve is us.
        Diagnostic::error(missing_token.location, "undefined field type")
            .with_help_label(def.name.location, "in this struct")
            .attached(stores.diags, cur_id);
        had_error.set();
        return;
    }
}
