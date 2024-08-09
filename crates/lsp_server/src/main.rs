use std::{collections::HashMap, path::Path};

use ariadne::Span;
use lexer::{Token, TokenKind};
use stores::{
    source::{SourceLocation, SourceStore, Spanned},
    strings::StringStore,
};
use tokio::sync::Mutex;
use tower_lsp::{
    jsonrpc::Result,
    lsp_types::{
        DidChangeTextDocumentParams, DidOpenTextDocumentParams, DocumentFilter, InitializeParams,
        InitializeResult, MessageType, PositionEncodingKind, SemanticToken, SemanticTokenType,
        SemanticTokens, SemanticTokensFullOptions, SemanticTokensLegend, SemanticTokensOptions,
        SemanticTokensParams, SemanticTokensRegistrationOptions, SemanticTokensResult,
        SemanticTokensServerCapabilities, ServerCapabilities, ServerInfo,
        StaticRegistrationOptions, TextDocumentRegistrationOptions, TextDocumentSyncCapability,
        TextDocumentSyncKind, Url, WorkDoneProgressOptions,
    },
    Client, LanguageServer, LspService, Server,
};

pub const LEGEND_TYPE: &[SemanticTokenType] = &[
    SemanticTokenType::COMMENT,
    SemanticTokenType::STRING,
    SemanticTokenType::KEYWORD,
    SemanticTokenType::NUMBER,
    SemanticTokenType::OPERATOR,
    SemanticTokenType::TYPE,
    SemanticTokenType::FUNCTION,
];

#[derive(Clone, Copy)]
pub enum Legend {
    Comment,
    String,
    Keyword,
    Number,
    Operator,
    Type,
    Function,
}

struct IncompleteSemanticToken {
    loc: SourceLocation,
    legend: Legend,
}

struct Stores {
    semantic_token_map: HashMap<String, Vec<IncompleteSemanticToken>>,
    source_store: SourceStore,
    string_store: StringStore,
}

fn is_primitive(string_store: &StringStore, token: Spanned<Token>) -> bool {
    matches!(
        string_store.resolve(token.inner.lexeme),
        "u8" | "s8" | "u16" | "s16" | "u32" | "s32" | "u64" | "s64" | "f32" | "f64" | "bool"
    )
}

struct Backend {
    client: Client,
    stores: Mutex<Stores>,
}

impl Backend {
    fn new(client: Client) -> Self {
        Self {
            client,
            stores: Mutex::new(Stores {
                semantic_token_map: HashMap::new(),
                source_store: SourceStore::new(),
                string_store: StringStore::new(),
            }),
        }
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        let res = InitializeResult {
            server_info: Some(ServerInfo {
                name: "MFL LSP".to_owned(),
                version: None,
            }),
            capabilities: ServerCapabilities {
                position_encoding: Some(PositionEncodingKind::UTF16),
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                semantic_tokens_provider: Some(
                    SemanticTokensServerCapabilities::SemanticTokensRegistrationOptions(
                        SemanticTokensRegistrationOptions {
                            text_document_registration_options: TextDocumentRegistrationOptions {
                                document_selector: Some(vec![DocumentFilter {
                                    language: Some("mfl".to_owned()),
                                    scheme: Some("file".to_owned()),
                                    pattern: None,
                                }]),
                            },
                            semantic_tokens_options: SemanticTokensOptions {
                                work_done_progress_options: WorkDoneProgressOptions::default(),
                                legend: SemanticTokensLegend {
                                    token_types: LEGEND_TYPE.into(),
                                    token_modifiers: Vec::new(),
                                },
                                range: None,
                                full: Some(SemanticTokensFullOptions::Bool(true)),
                            },
                            static_registration_options: StaticRegistrationOptions::default(),
                        },
                    ),
                ),
                ..Default::default()
            },
        };

        Ok(res)
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.on_update(params.text_document.uri, params.text_document.text)
            .await;
    }

    async fn did_change(&self, mut params: DidChangeTextDocumentParams) {
        self.on_update(
            params.text_document.uri,
            std::mem::take(&mut params.content_changes[0].text),
        )
        .await;
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        let uri = params.text_document.uri.to_string();
        self.client
            .log_message(MessageType::LOG, "semantic_token_full")
            .await;

        let stores = self.stores.lock().await;

        let Some(tokens) = stores.semantic_token_map.get(&uri) else {
            return Ok(None);
        };
        if tokens.is_empty() {
            return Ok(None);
        }

        let source = stores.source_store.source(tokens[0].loc.file_id);
        let mut semantic_tokens = Vec::new();
        let mut pre_line = 0;
        let mut pre_start = 0;

        for token in tokens {
            let Some((_, line, start)) = source.get_offset_line(token.loc.start()) else {
                continue;
            };

            let delta_line = line - pre_line;
            let delta_start = if delta_line == 0 {
                start - pre_start
            } else {
                start
            };

            semantic_tokens.push(SemanticToken {
                delta_line: delta_line as u32,
                delta_start: delta_start as u32,
                length: token.loc.len() as u32,
                token_type: token.legend as u32,
                token_modifiers_bitset: 0,
            });
            pre_line = line;
            pre_start = start;
        }

        Ok(Some(SemanticTokensResult::Tokens(SemanticTokens {
            result_id: None,
            data: semantic_tokens,
        })))
    }
}

impl Backend {
    async fn on_update(&self, uri: Url, text: String) {
        let mut stores = self.stores.lock().await;
        let Stores {
            semantic_token_map,
            source_store,
            string_store,
        } = &mut *stores;

        let file_id = source_store.add(Path::new(&uri.to_string()), &text);

        let tokens = lexer::lex(source_store, string_store, &text, file_id);
        let mut sem_toks = Vec::new();
        for token in tokens {
            match token {
                Err(_) => {
                    // Do nothing for now, add diagnostics later.
                }
                Ok(token) => {
                    let legend = match token.inner.kind {
                        // Comment
                        TokenKind::Comment => Legend::Comment,

                        // String
                        TokenKind::Char(_) | TokenKind::String(_) | TokenKind::Here(_) => {
                            Legend::String
                        }

                        // Keyword
                        TokenKind::Assert
                        | TokenKind::Cast
                        | TokenKind::Const
                        | TokenKind::Elif
                        | TokenKind::Else
                        | TokenKind::EmitStack
                        | TokenKind::Exit
                        | TokenKind::Extern
                        | TokenKind::GoesTo
                        | TokenKind::If
                        | TokenKind::AssumeInit
                        | TokenKind::Import
                        | TokenKind::LangItem
                        | TokenKind::Module
                        | TokenKind::Proc
                        | TokenKind::Return
                        | TokenKind::Struct
                        | TokenKind::Union
                        | TokenKind::Variable
                        | TokenKind::While => Legend::Keyword,

                        // Number
                        TokenKind::Boolean(_) | TokenKind::Float | TokenKind::Integer(_) => {
                            Legend::Number
                        }

                        // Operator
                        TokenKind::BitAnd
                        | TokenKind::BitNot
                        | TokenKind::BitOr
                        | TokenKind::BitXor
                        | TokenKind::Div
                        | TokenKind::Equal
                        | TokenKind::Greater
                        | TokenKind::GreaterEqual
                        | TokenKind::IsNull
                        | TokenKind::Less
                        | TokenKind::LessEqual
                        | TokenKind::Minus
                        | TokenKind::NotEqual
                        | TokenKind::Plus
                        | TokenKind::Rem
                        | TokenKind::ShiftLeft
                        | TokenKind::ShiftRight
                        | TokenKind::Star => Legend::Operator,

                        // Type
                        TokenKind::Ident if is_primitive(string_store, token) => Legend::Type,

                        // Function
                        TokenKind::Drop
                        | TokenKind::Dup
                        | TokenKind::Extract(_)
                        | TokenKind::Insert(_)
                        | TokenKind::Load
                        | TokenKind::Over
                        | TokenKind::Pack
                        | TokenKind::Reverse
                        | TokenKind::Rot
                        | TokenKind::SizeOf
                        | TokenKind::Store
                        | TokenKind::Swap
                        | TokenKind::SysCall
                        | TokenKind::Unpack => Legend::Function,

                        // Nothing
                        TokenKind::Ampersand
                        | TokenKind::BracketClose(_)
                        | TokenKind::BracketOpen(_)
                        | TokenKind::ColonColon
                        | TokenKind::Comma
                        | TokenKind::Dot
                        | TokenKind::Ident
                        | TokenKind::Whitespace => continue,
                    };

                    sem_toks.push(IncompleteSemanticToken {
                        loc: token.location,
                        legend,
                    })
                }
            }
        }

        semantic_token_map.insert(uri.to_string(), sem_toks);
    }
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::build(Backend::new).finish();

    Server::new(stdin, stdout, socket).serve(service).await;
}
