use ariadne::{Color, Label};

use crate::{
    item_store::{ItemStore, ItemAttribute, ItemHeader, ItemId, ItemKind, LangItem},
    diagnostics,
    error_signal::ErrorSignal,
    stores::Stores,
};

pub(crate) fn validate_attributes(
    item_store: &mut ItemStore,
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    cur_item: ItemId,
) {
    let item_header = item_store.get_item_header(cur_item);

    match item_header.kind {
        ItemKind::Assert | ItemKind::Const | ItemKind::Variable => {
            if item_header.attributes.contains(ItemAttribute::Extern) {
                bad_extern_diagnostic(stores, item_header, had_error);
            }
            if let Some(lang_item) = item_header.lang_item {
                bad_lang_item_diagnostic(stores, item_header, lang_item, had_error);
            }
        }

        ItemKind::GenericFunction | ItemKind::FunctionDecl => {
            if item_header.attributes.contains(ItemAttribute::Extern) {
                bad_extern_diagnostic(stores, item_header, had_error);
            }
        }

        ItemKind::Function => {
            if let Some(lang_item @ LangItem::String) = item_header.lang_item {
                bad_lang_item_diagnostic(stores, item_header, lang_item, had_error);
            }
        }
        ItemKind::StructDef => {
            if item_header.attributes.contains(ItemAttribute::Extern) {
                bad_extern_diagnostic(stores, item_header, had_error);
            }

            if let Some(lang_item @ (LangItem::Alloc | LangItem::Free)) = item_header.lang_item {
                bad_lang_item_diagnostic(stores, item_header, lang_item, had_error);
            }
        }

        ItemKind::Module => {}
    }
}

fn bad_lang_item_diagnostic(
    stores: &mut Stores,
    item_header: ItemHeader,
    lang_item: LangItem,
    had_error: &mut ErrorSignal,
) {
    diagnostics::emit_error(
        stores,
        item_header.name.location,
        format!(
            "{} is invalid for lang item {}",
            item_header.kind.kind_str(),
            lang_item.kind_str()
        ),
        [Label::new(item_header.name.location).with_color(Color::Red)],
        None,
    );
    had_error.set();
}

fn bad_extern_diagnostic(
    stores: &mut Stores,
    item_header: ItemHeader,
    had_error: &mut ErrorSignal,
) {
    diagnostics::emit_error(
        stores,
        item_header.name.location,
        format!("{} cannot be extern", item_header.kind.kind_str()),
        [Label::new(item_header.name.location).with_color(Color::Red)],
        None,
    );
    had_error.set();
}
