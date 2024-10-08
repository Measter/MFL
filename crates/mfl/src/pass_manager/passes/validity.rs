use hashbrown::HashMap;
use stores::items::ItemId;

use crate::{
    error_signal::ErrorSignal,
    pass_manager::PassManager,
    simulate::SimulatorValue,
    stores::{
        diagnostics::Diagnostic,
        item::{ItemAttribute, ItemKind, LangItem},
        Stores,
    },
};

mod cycles;

pub(crate) fn validity_check(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
    let cur_item_header = stores.items.get_item_header(cur_id);

    match cur_item_header.kind {
        ItemKind::Assert | ItemKind::Const => {
            if pass_manager
                .ensure_ident_resolved_body(stores, cur_id)
                .is_ok()
            {
                cycles::check_invalid_cycles(stores, pass_manager, had_error, cur_id);
            }
            validate_attributes(stores, had_error, cur_id);
        }
        ItemKind::Variable | ItemKind::Function | ItemKind::FunctionDecl | ItemKind::Module => {
            validate_attributes(stores, had_error, cur_id);
        }
        ItemKind::GenericFunction => {
            validate_attributes(stores, had_error, cur_id);
            validate_unique_generic_params(stores, had_error, cur_id);
        }
        ItemKind::StructDef => {
            if pass_manager
                .ensure_ident_resolved_signature(stores, cur_id)
                .is_ok()
            {
                cycles::check_invalid_cycles(stores, pass_manager, had_error, cur_id);
            }

            validate_attributes(stores, had_error, cur_id);
            validate_unique_generic_params(stores, had_error, cur_id);
        }
        ItemKind::Enum => {
            validate_enum_variants(stores, pass_manager, had_error, cur_id);
            validate_attributes(stores, had_error, cur_id);
        }
        ItemKind::Primitive(_) => {
            // No checks to be done here.
        }
    }
}

fn validate_attributes(stores: &mut Stores, had_error: &mut ErrorSignal, cur_item: ItemId) {
    let item_header = stores.items.get_item_header(cur_item);

    match item_header.kind {
        ItemKind::Assert | ItemKind::Const | ItemKind::Variable => {
            if item_header.attributes.contains(ItemAttribute::Extern) {
                Diagnostic::bad_extern(stores.diags, item_header);
                had_error.set();
            }
            if let Some(lang_item) = item_header.lang_item {
                Diagnostic::bad_lang_item(stores.diags, item_header, lang_item);
                had_error.set();
            }
        }

        ItemKind::GenericFunction => {
            if item_header.attributes.contains(ItemAttribute::Extern) {
                Diagnostic::bad_extern(stores.diags, item_header);
                had_error.set();
            }

            if let Some(lang_item @ LangItem::String) = item_header.lang_item {
                Diagnostic::bad_lang_item(stores.diags, item_header, lang_item);
                had_error.set();
            }
        }

        ItemKind::Function | ItemKind::FunctionDecl => {
            if let Some(lang_item @ LangItem::String) = item_header.lang_item {
                Diagnostic::bad_lang_item(stores.diags, item_header, lang_item);
                had_error.set();
            }

            if item_header.attributes.contains(ItemAttribute::Extern)
                && item_header.attributes.contains(ItemAttribute::TrackCaller)
            {
                Diagnostic::error(
                    item_header.name.location,
                    "extern functions cannot be track_caller",
                )
                .attached(stores.diags, item_header.id);
            }
        }

        ItemKind::StructDef => {
            if item_header.attributes.contains(ItemAttribute::Extern) {
                Diagnostic::bad_extern(stores.diags, item_header);
                had_error.set();
            }

            if let Some(lang_item @ (LangItem::Alloc | LangItem::Free)) = item_header.lang_item {
                Diagnostic::bad_lang_item(stores.diags, item_header, lang_item);
                had_error.set();
            }
        }

        ItemKind::Enum => {
            if item_header.attributes.contains(ItemAttribute::Extern) {
                Diagnostic::bad_extern(stores.diags, item_header);
                had_error.set();
            }

            if let Some(lang_item @ (LangItem::Alloc | LangItem::Free)) = item_header.lang_item {
                Diagnostic::bad_lang_item(stores.diags, item_header, lang_item);
                had_error.set();
            }
        }

        ItemKind::Module | ItemKind::Primitive(_) => {}
    }
}

fn validate_enum_variants(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
    let def = stores.sigs.urir.get_enum(cur_id).clone();

    let mut seen_discriminants = HashMap::new();

    for &(name, const_item_id) in &def.variants {
        if pass_manager
            .ensure_evaluated_consts_asserts(stores, const_item_id)
            .is_err()
        {
            had_error.set();
            continue;
        }

        let [SimulatorValue::EnumValue { discrim, .. }] =
            stores.items.get_consts(const_item_id).unwrap()
        else {
            unreachable!()
        };

        if let Some(&prev_loc) = seen_discriminants.get(discrim) {
            let mut diag = Diagnostic::error(name.location, "descriminant collision");
            diag.add_primary_label_message(format!("variant's discriminant is {discrim}",));
            diag.with_secondary_label(prev_loc, "this variant has the same discriminant")
                .attached(stores.diags, cur_id);
            had_error.set();
        } else {
            seen_discriminants.insert(*discrim, name.location);
        }
    }
}

fn validate_unique_generic_params(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
    let item_header = stores.items.get_item_header(cur_id);
    let generic_params = match item_header.kind {
        ItemKind::GenericFunction => stores.items.get_function_template_paramaters(cur_id),
        ItemKind::StructDef => {
            let struct_def = stores.sigs.nrir.get_struct(cur_id);
            &struct_def.generic_params
        }
        _ => unreachable!(),
    };

    let mut param_bundles: HashMap<_, Vec<_>> = HashMap::new();
    generic_params.iter().for_each(|p| {
        param_bundles.entry(p.inner).or_default().push(p.location);
    });

    for (name, locations) in param_bundles {
        if locations.len() == 1 {
            continue;
        }

        let param_name = stores.strings.resolve(name);
        let mut diag = Diagnostic::error(
            locations[0],
            format!("generic parameter `{param_name}` is not unique"),
        )
        .primary_label_message("this parameter");

        for loc in &locations[1..] {
            diag.add_secondary_label(*loc, "has the same name");
        }

        diag.attached(stores.diags, cur_id);
        had_error.set();
    }
}
