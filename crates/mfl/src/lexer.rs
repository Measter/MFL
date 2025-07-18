use lexer::{BracketKind, LexerError, Token};
use stores::source::{FileId, SourceLocation, Spanned};
use tracing::debug_span;

use crate::{error_signal::ErrorSignal, stores::diagnostics::Diagnostic, Stores};

#[derive(Debug, Clone)]
pub struct TreeGroup {
    pub bracket_kind: BracketKind,
    pub open: Spanned<Token>,
    pub close: Option<Spanned<Token>>,
    pub tokens: Vec<TokenTree>,
}

impl TreeGroup {
    pub fn span(&self) -> SourceLocation {
        let last = self
            .close
            .map(|t| t.location)
            .or(self.tokens.last().map(TokenTree::span))
            .unwrap_or(self.open.location);

        self.open.location.merge(last)
    }

    pub fn last_token(&self) -> Spanned<Token> {
        self.close
            .or(self.tokens.last().map(TokenTree::last_token))
            .unwrap_or(self.open)
    }

    pub fn first_token(&self) -> Spanned<Token> {
        self.open
    }
}

#[derive(Debug, Clone)]
pub enum TokenTree {
    Single(Spanned<Token>),
    Group(TreeGroup),
}

impl TokenTree {
    pub fn span(&self) -> SourceLocation {
        match self {
            TokenTree::Single(tk) => tk.location,
            TokenTree::Group(tg) => tg.span(),
        }
    }

    pub fn last_token(&self) -> Spanned<Token> {
        match self {
            TokenTree::Single(tk) => *tk,
            TokenTree::Group(tg) => tg.last_token(),
        }
    }

    pub fn first_token(&self) -> Spanned<Token> {
        match self {
            TokenTree::Single(tk) => *tk,
            TokenTree::Group(tg) => tg.first_token(),
        }
    }

    #[inline]
    #[track_caller]
    pub fn unwrap_single(&self) -> Spanned<Token> {
        match self {
            TokenTree::Single(tk) => *tk,
            TokenTree::Group(_) => panic!("ICE: Tried to unwrap_single a Group"),
        }
    }

    pub fn expects_brace_group(&self) -> bool {
        matches!(self, TokenTree::Single(tk) if tk.inner.expects_brace_group())
    }

    pub fn is_brace_group(&self) -> bool {
        matches!(self, TokenTree::Group(tg) if tg.bracket_kind == BracketKind::Brace)
    }

    pub fn kind_str(&self) -> &'static str {
        match self {
            TokenTree::Single(tk) => tk.inner.kind_str(),
            TokenTree::Group(_) => "bracket group",
        }
    }
}

pub(crate) fn lex_file(
    stores: &mut Stores,
    contents: &str,
    file_id: FileId,
) -> Result<Vec<TokenTree>, ()> {
    let _span = debug_span!(stringify!(lexer::lex_file)).entered();

    let mut had_error = ErrorSignal::new();
    let mut token_tree_group_stack = Vec::<TreeGroup>::new();
    let mut token_tree_stream = Vec::<TokenTree>::new();

    let tokens = lexer::lex(stores.strings, contents, file_id).into_iter();

    for tk in tokens {
        let token = match tk {
            Ok(tk) => tk,
            Err(LexerError::UnexpectedChar(location)) => {
                let span_text = stores.source.get_str(location);
                Diagnostic::error(
                    location,
                    format!("unexpected character in input: `{span_text:?}`"),
                )
                .detached(stores.diags);
                had_error.set();
                continue;
            }
            Err(LexerError::UnclosedString(location)) => {
                Diagnostic::error(location, "unterminated string literal").detached(stores.diags);
                had_error.set();
                continue;
            }
            Err(LexerError::UnclosedChar(location)) => {
                Diagnostic::error(location, "unterminated char literal").detached(stores.diags);
                had_error.set();
                continue;
            }
        };

        match token.inner {
            Token::BracketOpen(bk) => token_tree_group_stack.push(TreeGroup {
                bracket_kind: bk,
                open: token,
                close: None,
                tokens: Vec::new(),
            }),
            Token::BracketClose(tk) if !token_tree_group_stack.is_empty() => {
                let last = token_tree_group_stack.last().unwrap();
                let tt_val = if last.bracket_kind == tk {
                    let mut cur_group = token_tree_group_stack.pop().unwrap();
                    cur_group.close = Some(token);
                    TokenTree::Group(cur_group)
                } else {
                    Diagnostic::error(token.location, "unmatched bracket").detached(stores.diags);
                    had_error.set();

                    TokenTree::Single(token)
                };

                let stream = token_tree_group_stack
                    .last_mut()
                    .map(|tg| &mut tg.tokens)
                    .unwrap_or(&mut token_tree_stream);
                stream.push(tt_val);
            }
            Token::Comment => continue,
            _ => {
                let stream = token_tree_group_stack
                    .last_mut()
                    .map(|tg| &mut tg.tokens)
                    .unwrap_or(&mut token_tree_stream);
                stream.push(TokenTree::Single(token));
            }
        }
    }

    while let Some(cur_group) = token_tree_group_stack.pop() {
        Diagnostic::error(cur_group.open.location, "unclosed bracket").detached(stores.diags);
        had_error.set();

        let stream = token_tree_group_stack
            .last_mut()
            .map(|tg| &mut tg.tokens)
            .unwrap_or(&mut token_tree_stream);
        stream.push(TokenTree::Group(cur_group));
    }

    if had_error.into_err() {
        Err(())
    } else {
        Ok(token_tree_stream)
    }
}

#[allow(unused)]
fn pretty_print_tree(tree: &Vec<TokenTree>, depth: usize) {
    for tt in tree {
        match tt {
            TokenTree::Single(tk) => {
                eprintln!("{:width$}{:?}", " ", tk.inner, width = depth * 4);
            }
            TokenTree::Group(tg) => {
                eprintln!(
                    "{:width$}{:?}",
                    " ",
                    Token::BracketOpen(tg.bracket_kind),
                    width = depth * 4
                );
                pretty_print_tree(&tg.tokens, depth + 1);
                if let Some(ctk) = tg.close {
                    eprintln!(
                        "{:width$}{:?}",
                        " ",
                        Token::BracketClose(tg.bracket_kind),
                        width = depth * 4
                    );
                }
            }
        }
    }
}
