use stores::items::ItemId;

use crate::{
    error_signal::ErrorSignal,
    stores::{
        diagnostics::Diagnostic,
        item::{ItemAttribute, ItemKind, LangItem},
        Stores,
    },
};

pub(crate) fn validate_attributes(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    cur_item: ItemId,
) {
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

        ItemKind::Module => {}
    }
}
