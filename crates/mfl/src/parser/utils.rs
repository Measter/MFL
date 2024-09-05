use std::{fmt::Display, slice::Iter, str::FromStr};

use lasso::Spur;
use lexer::{BracketKind, IntegerBase, Token, TokenKind};
use num_traits::{Float, PrimInt, Unsigned};
use stores::{
    items::ItemId,
    source::{SourceLocation, Spanned, WithSpan},
};

use crate::{
    error_signal::ErrorSignal,
    ir::{IdentPathRoot, OpCode, UnresolvedIdent, UnresolvedOp, UnresolvedType},
    lexer::{TokenTree, TreeGroup},
    parser::matcher::{integer_tokens, Matcher},
    stores::{diagnostics::Diagnostic, signatures::StackDefItemUnresolved},
    Stores,
};

use super::matcher::{stack_def_tokens, valid_type_token, ExpectedTokenMatcher, IsMatch};

pub type ParseOpResult = Result<(OpCode<UnresolvedOp>, SourceLocation), ()>;

pub(super) struct TokenIter<'a> {
    it: Iter<'a, TokenTree>,
}

impl<'a> TokenIter<'a> {
    pub(super) fn new(it: Iter<'a, TokenTree>) -> Self {
        Self { it }
    }

    pub(super) fn next(&mut self) -> Option<&'a TokenTree> {
        self.it.next()
    }

    pub(super) fn expect_single(
        &mut self,
        stores: &mut Stores,
        item_id: ItemId,
        filter: impl ExpectedTokenMatcher<Spanned<TokenKind>>,
        prev: SourceLocation,
    ) -> Result<Spanned<Token>, ()> {
        match self.peek() {
            Some(TokenTree::Single(tk)) => match filter.is_match(tk.map(|t| t.kind)) {
                IsMatch::Yes => Ok(self.next().unwrap_single()),
                IsMatch::No(kind_str, location) => {
                    Diagnostic::error(
                        location,
                        format!("expected `{}`, found `{kind_str}`", filter.kind_str()),
                    )
                    .attached(stores.diags, item_id);

                    Err(())
                }
            },
            Some(TokenTree::Group(tg)) => {
                Diagnostic::error(
                    tg.span(),
                    format!("expected `{}`, found bracket group", filter.kind_str()),
                )
                .attached(stores.diags, item_id);
                Err(())
            }
            None => {
                Diagnostic::error(prev, "unexpected end of tokens").attached(stores.diags, item_id);
                Err(())
            }
        }
    }

    pub(super) fn expect_group(
        &mut self,
        stores: &mut Stores,
        item_id: ItemId,
        expected: BracketKind,
        prev: Spanned<Token>,
    ) -> Result<&'a TreeGroup, ()> {
        match self.peek() {
            Some(TokenTree::Group(tg)) if tg.bracket_kind == expected => {
                Ok(self.next().unwrap_group())
            }
            Some(TokenTree::Group(tk)) => {
                Diagnostic::error(
                    tk.open.location,
                    format!("expected `{}`, found `{}`", expected, tk.bracket_kind,),
                )
                .attached(stores.diags, item_id);
                Err(())
            }
            Some(TokenTree::Single(tk)) => {
                Diagnostic::error(
                    tk.location,
                    format!(
                        "expected `{}`, found `{}`",
                        expected,
                        tk.inner.kind.kind_str()
                    ),
                )
                .attached(stores.diags, item_id);
                Err(())
            }
            None => {
                Diagnostic::error(prev.location, "unexpected end of tokens")
                    .attached(stores.diags, item_id);
                Err(())
            }
        }
    }

    pub(super) fn peek(&self) -> Option<&'a TokenTree> {
        self.it.as_slice().first()
    }

    pub(super) fn next_is_group(&self, kind: BracketKind) -> bool {
        matches!(self.peek(), Some(TokenTree::Group(tg)) if tg.bracket_kind == kind)
    }

    pub(super) fn next_is_single(
        &self,
        filter: impl ExpectedTokenMatcher<Spanned<TokenKind>>,
    ) -> bool {
        let Some(TokenTree::Single(next)) = self.peek() else {
            return false;
        };

        filter.is_match(next.map(|t| t.kind)).yes()
    }

    pub(super) fn next_is_single_and(
        &self,
        filter: impl ExpectedTokenMatcher<Spanned<TokenKind>>,
        and: impl Fn(Spanned<Token>) -> bool,
    ) -> bool {
        // matches!(self.peek(), Some(TokenTree::Single(tk)) if filter.is_match(tk.inner.kind) && and(*tk))
        let Some(TokenTree::Single(next)) = self.peek() else {
            return false;
        };

        if filter.is_match(next.map(|t| t.kind)).no() {
            return false;
        }

        and(*next)
    }

    pub(super) fn next_is<'tt>(&self, filter: impl ExpectedTokenMatcher<&'tt TokenTree>) -> bool
    where
        'a: 'tt,
    {
        let Some(next) = self.peek() else {
            return false;
        };

        filter.is_match(next).yes()
    }
}

pub trait Recover<T, E> {
    fn recover(self, had_error: &mut ErrorSignal, fallback: T) -> T;
}

impl<T, E> Recover<T, E> for Result<T, E> {
    fn recover(self, had_error: &mut ErrorSignal, fallback: T) -> T {
        match self {
            Ok(kk) => kk,
            Err(_) => {
                had_error.set();
                fallback
            }
        }
    }
}

pub(super) trait LengthRequirement: Display {
    fn is_met(&self, len: usize) -> bool;
}

impl LengthRequirement for usize {
    fn is_met(&self, len: usize) -> bool {
        *self == len
    }
}

pub struct Min(pub usize);
impl Display for Min {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(">=")?;
        self.0.fmt(f)
    }
}
impl LengthRequirement for Min {
    fn is_met(&self, len: usize) -> bool {
        len >= self.0
    }
}

pub(super) trait TreeGroupResultExt {
    fn with_kinds<'a>(
        self,
        stores: &mut Stores,
        item_id: ItemId,
        filter: impl ExpectedTokenMatcher<&'a TokenTree>,
    ) -> Self
    where
        Self: 'a;
    fn with_length(
        self,
        stores: &mut Stores,
        item_id: ItemId,
        length: impl LengthRequirement,
    ) -> Self;
}
impl TreeGroupResultExt for Result<&TreeGroup, ()> {
    fn with_kinds<'a>(
        self,
        stores: &mut Stores,
        item_id: ItemId,
        filter: impl ExpectedTokenMatcher<&'a TokenTree>,
    ) -> Self
    where
        Self: 'a,
    {
        let group = self?;

        let mut had_error = ErrorSignal::new();
        for tt in &group.tokens {
            if let IsMatch::No(kind_str, loc) = filter.is_match(tt) {
                Diagnostic::error(
                    loc,
                    format!("expected `{}`, found `{kind_str}`", filter.kind_str(),),
                )
                .attached(stores.diags, item_id);
                had_error.set();
            }
        }

        if had_error.into_err() {
            Err(())
        } else {
            Ok(group)
        }
    }

    fn with_length(
        self,
        stores: &mut Stores,
        item_id: ItemId,
        length: impl LengthRequirement,
    ) -> Self {
        let group = self?;
        if !length.is_met(group.tokens.len()) {
            Diagnostic::error(
                group.span(),
                format!("expected {length} tokens, found {}", group.tokens.len()),
            )
            .attached(stores.diags, item_id);
            Err(())
        } else {
            Ok(group)
        }
    }
}

pub(super) trait TokenTreeOptionExt<'a> {
    fn unwrap_single(self) -> Spanned<Token>;
    fn unwrap_group(self) -> &'a TreeGroup;
}

impl<'a> TokenTreeOptionExt<'a> for Option<&'a TokenTree> {
    #[inline]
    #[track_caller]
    fn unwrap_single(self) -> Spanned<Token> {
        match self.unwrap() {
            TokenTree::Single(tk) => *tk,
            TokenTree::Group(_) => panic!("ICE: Tried to unwrap_single a Group"),
        }
    }

    #[inline]
    #[track_caller]
    fn unwrap_group(self) -> &'a TreeGroup {
        match self.unwrap() {
            TokenTree::Single(_) => panic!("ICE: Tried to unwrap_group a Single"),
            TokenTree::Group(tg) => tg,
        }
    }
}

impl TreeGroup {
    pub(super) fn fallback(kind: BracketKind, token: Spanned<Token>) -> Self {
        Self {
            bracket_kind: kind,
            open: token,
            close: Some(token),
            tokens: Vec::new(),
        }
    }
}

pub struct Terminated {
    pub close: Spanned<Token>,
    pub list: Vec<TokenTree>,
}

pub fn get_terminated_tokens<'a>(
    stores: &mut Stores,
    token_iter: &mut TokenIter<'a>,
    item_id: ItemId,
    open_token: Spanned<Token>,
    expected_len: Option<usize>,
    inner_matcher: impl ExpectedTokenMatcher<&'a TokenTree>,
    close_matcher: impl ExpectedTokenMatcher<&'a TokenTree>,
    consume_close: bool,
) -> Result<Terminated, ()> {
    let mut had_error = ErrorSignal::new();
    let mut tokens = Vec::<TokenTree>::new();
    let mut prev = open_token;

    // When parsing If, Elif, and While conditions, the terminating token is a brack group with braces, however the
    // condition block itself can contain an If or While expression with its own bracket group. We need to keep track
    // of whether we're expecting an additional bracket group.
    let mut additional_brace_groups = 0;
    let terminator_is_brace_group = close_matcher.is_brace_group();

    loop {
        let Some(next_token) = token_iter.peek() else {
            Diagnostic::error(prev.location, "unexpected end of tokens")
                .attached(stores.diags, item_id);
            return Err(());
        };

        if terminator_is_brace_group && next_token.expects_brace_group() {
            additional_brace_groups += 1;
        }

        if additional_brace_groups == 0 && close_matcher.is_match(next_token).yes() {
            break; // The end of the list, so break the loop.
        }

        if terminator_is_brace_group && additional_brace_groups > 0 && next_token.is_brace_group() {
            additional_brace_groups -= 1;
        }

        let item_token = if inner_matcher.is_match(next_token).yes() {
            token_iter.next().unwrap()
        } else {
            had_error.set();

            // If it's not the close token, we should consume it so we can continue.
            if close_matcher.is_match(next_token).no() {
                token_iter.next();
            }

            continue;
        };

        // TODO: Try to get rid of this
        tokens.push(item_token.clone());
        prev = item_token.last_token();
    }

    let close_token = if consume_close {
        token_iter.next().unwrap().first_token()
    } else {
        token_iter.peek().unwrap().first_token()
    };

    if let Some(len) = expected_len {
        if len != tokens.len() {
            let range = open_token.location.merge(close_token.location);
            Diagnostic::error(
                range,
                format!("expected {len} tokens, found {}", tokens.len()),
            )
            .attached(stores.diags, item_id);
            had_error.set();
        }
    }

    if had_error.into_err() {
        Err(())
    } else {
        Ok(Terminated {
            close: close_token,
            list: tokens,
        })
    }
}

pub fn parse_multiple_unresolved_types(
    stores: &mut Stores,
    item_id: ItemId,
    prev: SourceLocation,
    tokens: &[TokenTree],
) -> Result<Vec<Spanned<UnresolvedType>>, ()> {
    let mut had_error = ErrorSignal::new();
    let mut types: Vec<Spanned<UnresolvedType>> = Vec::new();
    let mut token_iter = TokenIter::new(tokens.iter());

    while token_iter.peek().is_some() {
        let Ok((unresolved_type, _)) =
            parse_unresolved_type(&mut token_iter, stores, item_id, prev, &mut had_error)
        else {
            continue;
        };
        types.push(unresolved_type);

        if TrailingCommaResult::Break
            == validate_trailing_comma(
                &mut token_iter,
                stores,
                &mut had_error,
                item_id,
                "paramaters",
            )
        {
            break;
        }
    }

    if had_error.into_err() {
        Err(())
    } else {
        Ok(types)
    }
}

pub fn parse_unresolved_type(
    token_iter: &mut TokenIter,
    stores: &mut Stores,
    item_id: ItemId,
    prev: SourceLocation,
    had_error: &mut ErrorSignal,
) -> Result<(Spanned<UnresolvedType>, Spanned<Token>), Option<SourceLocation>> {
    let Ok(ident) = token_iter.expect_single(
        stores,
        item_id,
        Matcher("ident", |t: Spanned<TokenKind>| {
            if matches!(t.inner, TokenKind::Ident | TokenKind::ColonColon) {
                IsMatch::Yes
            } else {
                IsMatch::No(t.inner.kind_str(), t.location)
            }
        }),
        prev,
    ) else {
        had_error.set();
        let bad_token = token_iter.next().map(|t| t.span()).unwrap_or(prev); // Consume the token so we can progress.
        return Err(Some(bad_token));
    };

    let Ok((ident, mut last_token)) = parse_ident(stores, had_error, item_id, token_iter, ident)
    else {
        had_error.set();
        return Err(None);
    };

    let mut type_span = ident.span;
    let mut parsed_type = UnresolvedType::Simple(ident);
    fn pointer_or_array(tt: &TokenTree) -> IsMatch {
        match tt {
            TokenTree::Single(tk)
                if matches!(tk.inner.kind, TokenKind::Ampersand | TokenKind::Star) =>
            {
                IsMatch::Yes
            }
            TokenTree::Group(tg) if tg.bracket_kind == BracketKind::Square => IsMatch::Yes,
            _ => IsMatch::No(tt.kind_str(), tt.span()),
        }
    }
    while token_iter.next_is(Matcher("[`, `*` or `&", pointer_or_array)) {
        let Some(next_token) = token_iter.peek() else {
            unreachable!()
        };

        match next_token {
            TokenTree::Group(_) => {
                let Ok(delim) = token_iter
                    .expect_group(stores, item_id, BracketKind::Square, last_token)
                    .with_kinds(stores, item_id, Matcher("integer", integer_tokens))
                    .with_length(stores, item_id, 1)
                else {
                    had_error.set();
                    continue;
                };

                let TokenTree::Single(len_token) = delim.tokens[0] else {
                    unreachable!()
                };
                let length = parse_integer_lexeme(stores, item_id, len_token).map_err(|_| None)?;

                type_span = type_span.merge(delim.span());
                parsed_type = UnresolvedType::Array(Box::new(parsed_type), length);
            }
            TokenTree::Single(_) => {
                // Parsing a pointer!
                let next = token_iter.next().unwrap_single();

                type_span = type_span.merge(next.location);
                parsed_type = match next.inner.kind {
                    TokenKind::Ampersand => UnresolvedType::SinglePointer(Box::new(parsed_type)),
                    TokenKind::Star => UnresolvedType::MultiPointer(Box::new(parsed_type)),
                    _ => unreachable!(),
                }
            }
        }

        last_token = next_token.last_token();
    }
    Ok((parsed_type.with_span(type_span), last_token))
}

pub fn parse_ident(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    token_iter: &mut TokenIter,
    mut token: Spanned<Token>,
) -> Result<(UnresolvedIdent, Spanned<Token>), ()> {
    let mut import_span = token.location;
    let mut last_token = token;

    let (path_root, mut path) = match token.inner.kind {
        TokenKind::ColonColon => {
            let ident = if token_iter.next_is_single_and(TokenKind::Ident, |t| {
                t.location.neighbour_of(token.location)
            }) {
                token_iter.next().unwrap_single()
            } else {
                Diagnostic::error(token.location, "unexpected end of ident")
                    .attached(stores.diags, item_id);
                had_error.set();
                return Err(());
            };

            last_token = ident;
            import_span = import_span.merge(ident.location);

            (IdentPathRoot::Root, vec![ident.map(|t| t.lexeme)])
        }
        TokenKind::Ident => (IdentPathRoot::CurrentScope, vec![token.map(|t| t.lexeme)]),
        TokenKind::SelfKw => (IdentPathRoot::CurrentModule, Vec::new()),
        _ => unreachable!(),
    };

    while token_iter.next_is_single_and(TokenKind::ColonColon, |t| {
        t.location.neighbour_of(last_token.location)
    }) {
        let colons = token_iter.next().unwrap_single(); // Consume the ColonColon.
        let item_id = if token_iter.next_is_single_and(TokenKind::Ident, |t| {
            t.location.neighbour_of(colons.location)
        }) {
            token_iter.next().unwrap_single()
        } else {
            Diagnostic::error(colons.location, "unexpected end of ident")
                .attached(stores.diags, item_id);
            had_error.set();
            return Err(());
        };

        last_token = item_id;
        import_span = import_span.merge(item_id.location);

        path.push(item_id.map(|t| t.lexeme));
    }

    let generic_params = if token_iter.next_is_group(BracketKind::Paren) {
        let Ok(delim) = token_iter
            .expect_group(stores, item_id, BracketKind::Paren, token)
            .with_kinds(stores, item_id, Matcher("type", valid_type_token))
        else {
            had_error.set();
            return Err(());
        };

        token.location = token.location.merge(delim.span());

        let Ok(unresolved_types) =
            parse_multiple_unresolved_types(stores, item_id, delim.open.location, &delim.tokens)
        else {
            had_error.set();
            return Err(());
        };

        import_span = import_span.merge(delim.span());
        last_token = delim.last_token();

        unresolved_types.into_iter().map(|ut| ut.inner).collect()
    } else {
        Vec::new()
    };

    Ok((
        UnresolvedIdent {
            span: import_span,
            path_root,
            path,
            generic_params,
        },
        last_token,
    ))
}

pub fn parse_integer_lexeme<T>(
    stores: &mut Stores,
    item_id: ItemId,
    int_token: Spanned<Token>,
) -> Result<T, ()>
where
    T: PrimInt + Unsigned + FromStr + Display,
{
    let TokenKind::Integer(literal_base) = int_token.inner.kind else {
        panic!("ICE: called parse_integer_lexeme with a non-integer token")
    };
    let string = stores.strings.resolve(int_token.inner.lexeme);
    // Need to skip the non-decimal prefix
    let string = if literal_base != IntegerBase::Decimal {
        &string[2..]
    } else {
        string
    };

    let string: String = string.chars().filter(|&c| c != '_').collect();

    let res = T::from_str_radix(&string, literal_base as _);
    let Ok(int) = res else {
        Diagnostic::error(int_token.location, "integer out of bounds")
            .primary_label_message(format!(
                "integer must be in range {}..={}",
                T::min_value(),
                T::max_value()
            ))
            .attached(stores.diags, item_id);
        return Err(());
    };

    Ok(int)
}

pub fn parse_float_lexeme<T>(
    stores: &mut Stores,
    item_id: ItemId,
    float_token: Spanned<Token>,
) -> Result<T, ()>
where
    T: Float + FromStr + Display,
{
    let TokenKind::Float = float_token.inner.kind else {
        panic!("ICE: called parse_float_lexeme with a non-float token")
    };
    let string = stores.strings.resolve(float_token.inner.lexeme);
    let string: String = string.chars().filter(|&c| c != '_').collect();

    let res = T::from_str(&string);
    let Ok(int) = res else {
        Diagnostic::error(float_token.location, "float out of bounds")
            .primary_label_message(format!(
                "float must be in range {}..={}",
                T::min_value(),
                T::max_value()
            ))
            .attached(stores.diags, item_id);
        return Err(());
    };

    Ok(int)
}

pub fn parse_integer_param(
    stores: &mut Stores,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    token: Spanned<Token>,
) -> Result<(Spanned<u8>, SourceLocation), ()> {
    let delim = token_iter
        .expect_group(stores, item_id, BracketKind::Paren, token)
        .with_kinds(stores, item_id, Matcher("integer", integer_tokens))
        .with_length(stores, item_id, 1)?;

    let count_token = delim.tokens[0].unwrap_single();
    let count: u8 = parse_integer_lexeme(stores, item_id, count_token)?;
    Ok((count.with_span(count_token.location), delim.span()))
}

pub fn parse_proc_entry_stack_def(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    prev_token: Spanned<Token>,
) -> Spanned<Vec<StackDefItemUnresolved>> {
    let fallback = TreeGroup::fallback(BracketKind::Square, prev_token);
    let stack = token_iter
        .expect_group(stores, item_id, BracketKind::Square, prev_token)
        .with_kinds(stores, item_id, Matcher("ident", stack_def_tokens))
        .recover(had_error, &fallback);

    let mut token_iter = TokenIter::new(stack.tokens.iter());
    let mut entries = Vec::new();
    let mut prev_token = stack.first_token();

    if !stack.tokens.is_empty() {
        while token_iter.peek().is_some() {
            let (name, prev) = if token_iter.next_is_single(TokenKind::Variable) {
                token_iter.next(); // Consume the var token.

                let name_token = token_iter
                    .expect_single(stores, item_id, TokenKind::Ident, prev_token.location)
                    .recover(had_error, prev_token);

                (Some(name_token.map(|t| t.lexeme)), name_token)
            } else {
                (None, prev_token)
            };

            let Ok((unresolved_type, last_token)) =
                parse_unresolved_type(&mut token_iter, stores, item_id, prev.location, had_error)
            else {
                continue;
            };

            if let Some(name) = name {
                entries.push(StackDefItemUnresolved::Var {
                    name,
                    kind: unresolved_type,
                });
            } else {
                entries.push(StackDefItemUnresolved::Stack(unresolved_type));
            };
            prev_token = last_token;

            if TrailingCommaResult::Break
                == validate_trailing_comma(
                    &mut token_iter,
                    stores,
                    had_error,
                    item_id,
                    "paramaters",
                )
            {
                break;
            }
        }
    }

    entries.with_span(stack.span())
}

pub fn parse_stack_def(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    prev_token: Spanned<Token>,
) -> Spanned<Vec<Spanned<UnresolvedType>>> {
    let fallback = TreeGroup::fallback(BracketKind::Square, prev_token);
    let stack = token_iter
        .expect_group(stores, item_id, BracketKind::Square, prev_token)
        .with_kinds(stores, item_id, Matcher("ident", valid_type_token))
        .recover(had_error, &fallback);

    let stack_location = stack.span();
    let unresolved_types =
        parse_multiple_unresolved_types(stores, item_id, stack.open.location, &stack.tokens)
            .recover(had_error, Vec::new());

    unresolved_types.with_span(stack_location)
}

pub fn try_parse_generic_pramas(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    token_iter: &mut TokenIter,
    item_id: ItemId,
    prev_token: Spanned<Token>,
) -> Result<(Vec<Spanned<Spur>>, Spanned<Token>), ()> {
    if token_iter.next_is_group(BracketKind::Paren) {
        let group = token_iter
            .expect_group(stores, item_id, BracketKind::Paren, prev_token)
            .with_kinds(
                stores,
                item_id,
                Matcher("generic params", |tk: Spanned<TokenKind>| {
                    if let TokenKind::Ident | TokenKind::Comma = tk.inner {
                        IsMatch::Yes
                    } else {
                        IsMatch::No(tk.inner.kind_str(), tk.location)
                    }
                }),
            )?;

        let mut params = Vec::new();
        let mut token_iter = TokenIter::new(group.tokens.iter());
        let mut prev_token = prev_token;

        while token_iter.peek().is_some() {
            let next = token_iter
                .expect_single(stores, item_id, TokenKind::Ident, prev_token.location)
                .recover(had_error, prev_token);

            params.push(next.map(|t| t.lexeme));
            prev_token = next;

            if TrailingCommaResult::Break
                == validate_trailing_comma(
                    &mut token_iter,
                    stores,
                    had_error,
                    item_id,
                    "paramaters",
                )
            {
                break;
            }
        }

        Ok((params, group.last_token()))
    } else {
        Ok((Vec::new(), prev_token))
    }
}

#[derive(PartialEq, Eq)]
pub enum TrailingCommaResult {
    Break,
    Continue,
}

pub fn validate_trailing_comma(
    token_iter: &mut TokenIter,
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: ItemId,
    kind_str: &str,
) -> TrailingCommaResult {
    let requires_end = if token_iter.next_is_single(TokenKind::Comma) {
        token_iter.next();
        false
    } else {
        true
    };

    let next = token_iter.peek();

    if requires_end && token_iter.peek().is_some() {
        let next = next.unwrap();
        Diagnostic::error(
            next.span(),
            format!("expected end of {kind_str}, found `{}`", next.kind_str()),
        )
        .with_note("You may be missing a comma")
        .attached(stores.diags, item_id);

        had_error.set();
    }

    if next.is_none() {
        TrailingCommaResult::Break
    } else {
        TrailingCommaResult::Continue
    }
}
