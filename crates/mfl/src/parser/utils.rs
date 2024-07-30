use std::{fmt::Display, slice::Iter, str::FromStr};

use ariadne::{Color, Label};
use num_traits::{PrimInt, Unsigned};

use crate::{
    diagnostics,
    error_signal::ErrorSignal,
    ir::{OpCode, UnresolvedIdent, UnresolvedOp, UnresolvedType},
    lexer::{BracketKind, IntegerBase, Token, TokenKind, TokenTree, TreeGroup},
    stores::source::{SourceLocation, Spanned, WithSpan},
    Stores,
};

pub type ParseOpResult = Result<(OpCode<UnresolvedOp>, SourceLocation), ()>;

pub(super) trait ExpectedTokenMatcher<T> {
    fn kind_str(&self) -> &'static str;
    fn is_match(&self, tk: T) -> bool;
    fn is_brace_group(&self) -> bool {
        false
    }
}

impl ExpectedTokenMatcher<TokenKind> for TokenKind {
    fn kind_str(&self) -> &'static str {
        TokenKind::kind_str(*self)
    }

    fn is_match(&self, tk: TokenKind) -> bool {
        tk == *self
    }
}

impl ExpectedTokenMatcher<&TokenTree> for TokenKind {
    fn kind_str(&self) -> &'static str {
        TokenKind::kind_str(*self)
    }

    fn is_match(&self, tk: &TokenTree) -> bool {
        match tk {
            TokenTree::Single(tk) => tk.inner.kind == *self,
            TokenTree::Group(_) => false,
        }
    }
}

// Wrapper because Rust's inference is dumb.
pub(super) struct Matcher<T>(pub &'static str, pub fn(T) -> bool);

impl ExpectedTokenMatcher<TokenKind> for Matcher<TokenKind> {
    fn kind_str(&self) -> &'static str {
        self.0
    }

    fn is_match(&self, tk: TokenKind) -> bool {
        self.1(tk)
    }
}

impl ExpectedTokenMatcher<&TokenTree> for Matcher<TokenKind> {
    fn kind_str(&self) -> &'static str {
        self.0
    }

    fn is_match(&self, tk: &TokenTree) -> bool {
        match tk {
            TokenTree::Single(tk) => self.1(tk.inner.kind),
            TokenTree::Group(_) => false,
        }
    }
}

impl<'a> ExpectedTokenMatcher<&'a TokenTree> for Matcher<&'a TokenTree> {
    fn kind_str(&self) -> &'static str {
        self.0
    }

    fn is_match(&self, tk: &'a TokenTree) -> bool {
        self.1(tk)
    }
}

pub(super) struct ConditionMatch;
impl ExpectedTokenMatcher<&TokenTree> for ConditionMatch {
    fn kind_str(&self) -> &'static str {
        "{"
    }

    fn is_match(&self, tk: &TokenTree) -> bool {
        matches!(tk, TokenTree::Group(tg) if tg.bracket_kind == BracketKind::Brace)
    }

    fn is_brace_group(&self) -> bool {
        true
    }
}

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
        stores: &Stores,
        filter: impl ExpectedTokenMatcher<TokenKind>,
        prev: SourceLocation,
    ) -> Result<Spanned<Token>, ()> {
        match self.peek() {
            Some(TokenTree::Single(tk)) if filter.is_match(tk.inner.kind) => {
                Ok(self.next().unwrap_single())
            }
            Some(TokenTree::Single(tk)) => {
                diagnostics::emit_error(
                    stores,
                    tk.location,
                    format!(
                        "expected `{}`, found `{}`",
                        filter.kind_str(),
                        tk.inner.kind.kind_str()
                    ),
                    Some(Label::new(tk.location).with_color(Color::Red)),
                    None,
                );
                Err(())
            }
            Some(TokenTree::Group(tg)) => {
                diagnostics::emit_error(
                    stores,
                    tg.span(),
                    format!("expected `{}`, found bracket group", filter.kind_str()),
                    Some(Label::new(tg.span()).with_color(Color::Red)),
                    None,
                );
                Err(())
            }
            None => {
                diagnostics::emit_error(
                    stores,
                    prev,
                    "unexpected end of tokens",
                    Some(Label::new(prev).with_color(Color::Red)),
                    None,
                );
                Err(())
            }
        }
    }

    pub(super) fn expect_group(
        &mut self,
        stores: &Stores,
        expected: BracketKind,
        prev: Spanned<Token>,
    ) -> Result<&'a TreeGroup, ()> {
        match self.peek() {
            Some(TokenTree::Group(tg)) if tg.bracket_kind == expected => {
                Ok(self.next().unwrap_group())
            }
            Some(TokenTree::Group(tk)) => {
                diagnostics::emit_error(
                    stores,
                    tk.open.location,
                    format!("expected `{}`, found `{}`", expected, tk.bracket_kind,),
                    Some(Label::new(tk.open.location).with_color(Color::Red)),
                    None,
                );
                Err(())
            }
            Some(TokenTree::Single(tk)) => {
                diagnostics::emit_error(
                    stores,
                    tk.location,
                    format!(
                        "expected `{}`, found `{}`",
                        expected,
                        tk.inner.kind.kind_str()
                    ),
                    Some(Label::new(tk.location).with_color(Color::Red)),
                    None,
                );
                Err(())
            }
            None => {
                diagnostics::emit_error(
                    stores,
                    prev.location,
                    "unexpected end of tokens",
                    Some(Label::new(prev.location).with_color(Color::Red)),
                    None,
                );
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

    pub(super) fn next_is_single(&self, filter: impl ExpectedTokenMatcher<TokenKind>) -> bool {
        matches!(self.peek(), Some(TokenTree::Single(tk)) if filter.is_match(tk.inner.kind))
    }

    pub(super) fn next_is_single_and(
        &self,
        filter: impl ExpectedTokenMatcher<TokenKind>,
        and: impl Fn(Spanned<Token>) -> bool,
    ) -> bool {
        matches!(self.peek(), Some(TokenTree::Single(tk)) if filter.is_match(tk.inner.kind) && and(*tk))
    }

    pub(super) fn next_is<'tt>(&self, filter: impl ExpectedTokenMatcher<&'tt TokenTree>) -> bool
    where
        'a: 'tt,
    {
        matches!(self.peek(), Some(tt) if filter.is_match(tt))
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
        stores: &Stores,
        filter: impl ExpectedTokenMatcher<&'a TokenTree>,
    ) -> Self
    where
        Self: 'a;
    fn with_length(self, stores: &Stores, length: impl LengthRequirement) -> Self;
}
impl TreeGroupResultExt for Result<&TreeGroup, ()> {
    fn with_kinds<'a>(
        self,
        stores: &Stores,
        filter: impl ExpectedTokenMatcher<&'a TokenTree>,
    ) -> Self
    where
        Self: 'a,
    {
        let group = self?;

        let mut had_error = ErrorSignal::new();
        for tt in &group.tokens {
            if !filter.is_match(tt) {
                diagnostics::emit_error(
                    stores,
                    tt.span(),
                    format!(
                        "expected `{}`, found `{}`",
                        filter.kind_str(),
                        tt.kind_str(),
                    ),
                    Some(Label::new(tt.span()).with_color(Color::Red)),
                    None,
                );
                had_error.set();
            }
        }

        if had_error.into_bool() {
            Err(())
        } else {
            Ok(group)
        }
    }

    fn with_length(self, stores: &Stores, length: impl LengthRequirement) -> Self {
        let group = self?;
        if !length.is_met(group.tokens.len()) {
            diagnostics::emit_error(
                stores,
                group.span(),
                format!("expected {length} tokens, found {}", group.tokens.len()),
                [Label::new(group.span()).with_color(Color::Red)],
                None,
            );
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

pub fn valid_type_token(tt: &TokenTree) -> bool {
    match tt {
        TokenTree::Single(tk) => matches!(
            tk.inner.kind,
            TokenKind::Ident
                | TokenKind::Integer { .. }
                | TokenKind::ColonColon
                | TokenKind::Ampersand
                | TokenKind::Star
        ),
        TokenTree::Group(tg) => {
            (tg.bracket_kind == BracketKind::Paren || tg.bracket_kind == BracketKind::Square)
                && tg.tokens.iter().all(valid_type_token)
        }
    }
}

pub struct Terminated {
    pub close: Spanned<Token>,
    pub list: Vec<TokenTree>,
}

pub fn get_terminated_tokens<'a>(
    stores: &Stores,
    token_iter: &mut TokenIter<'a>,
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
            diagnostics::emit_error(
                stores,
                prev.location,
                "unexpected end of tokens",
                Some(Label::new(prev.location).with_color(Color::Red)),
                None,
            );
            return Err(());
        };

        if terminator_is_brace_group && next_token.expects_brace_group() {
            additional_brace_groups += 1;
        }

        if additional_brace_groups == 0 && close_matcher.is_match(next_token) {
            break; // The end of the list, so break the loop.
        }

        if terminator_is_brace_group && additional_brace_groups > 0 && next_token.is_brace_group() {
            additional_brace_groups -= 1;
        }

        let item_token = if inner_matcher.is_match(next_token) {
            token_iter.next().unwrap()
        } else {
            had_error.set();

            // If it's not the close token, we should consume it so we can continue.
            if !close_matcher.is_match(next_token) {
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
            diagnostics::emit_error(
                stores,
                range,
                format!("expected {len} tokens, found {}", tokens.len()),
                [Label::new(range).with_color(Color::Red)],
                None,
            );
            had_error.set();
        }
    }

    if had_error.into_bool() {
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
    prev: SourceLocation,
    tokens: &[TokenTree],
) -> Result<Vec<Spanned<UnresolvedType>>, ()> {
    let mut had_error = ErrorSignal::new();
    let mut types: Vec<Spanned<UnresolvedType>> = Vec::new();
    let mut token_iter = TokenIter::new(tokens.iter());

    while token_iter.peek().is_some() {
        let Ok(unresolved_type) =
            parse_unresolved_type(&mut token_iter, stores, prev, &mut had_error)
        else {
            continue;
        };
        types.push(unresolved_type);
    }

    if had_error.into_bool() {
        Err(())
    } else {
        Ok(types)
    }
}

pub fn parse_unresolved_type(
    token_iter: &mut TokenIter,
    stores: &mut Stores,
    prev: SourceLocation,
    had_error: &mut ErrorSignal,
) -> Result<Spanned<UnresolvedType>, Option<SourceLocation>> {
    let Ok(ident) = token_iter.expect_single(
        stores,
        Matcher("ident", |t| {
            t == TokenKind::Ident || t == TokenKind::ColonColon
        }),
        prev,
    ) else {
        had_error.set();
        let bad_token = token_iter.next().map(|t| t.span()).unwrap_or(prev); // Consume the token so we can progress.
        return Err(Some(bad_token));
    };

    let Ok((ident, last_token)) = parse_ident(stores, had_error, token_iter, ident) else {
        had_error.set();
        return Err(None);
    };

    let mut type_span = ident.span;
    let mut parsed_type = UnresolvedType::Simple(ident);
    fn pointer_or_array(tt: &TokenTree) -> bool {
        match tt {
            TokenTree::Single(tk) => {
                matches!(tk.inner.kind, TokenKind::Ampersand | TokenKind::Star)
            }
            TokenTree::Group(tg) => tg.bracket_kind == BracketKind::Square,
        }
    }
    while token_iter.next_is(Matcher("[`, `*` or `&", pointer_or_array)) {
        let Some(next_token) = token_iter.peek() else {
            unreachable!()
        };

        match next_token {
            TokenTree::Group(_) => {
                let Ok(delim) = token_iter
                    .expect_group(stores, BracketKind::Square, last_token)
                    .with_kinds(
                        stores,
                        Matcher("integer", |t| matches!(t, TokenKind::Integer { .. })),
                    )
                    .with_length(stores, 1)
                else {
                    had_error.set();
                    continue;
                };

                let TokenTree::Single(len_token) = delim.tokens[0] else {
                    unreachable!()
                };
                let length = parse_integer_lexeme(stores, len_token).map_err(|_| None)?;

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
    }
    Ok(parsed_type.with_span(type_span))
}

pub fn parse_ident(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    token_iter: &mut TokenIter,
    mut token: Spanned<Token>,
) -> Result<(UnresolvedIdent, Spanned<Token>), ()> {
    let mut import_span = token.location;
    let mut last_token = token;

    let (is_from_root, mut path) = if token.inner.kind == TokenKind::ColonColon {
        let ident = if token_iter.next_is_single_and(TokenKind::Ident, |t| {
            t.location.neighbour_of(token.location)
        }) {
            token_iter.next().unwrap_single()
        } else {
            diagnostics::emit_error(
                stores,
                token.location,
                "unexpected end of ident",
                Some(Label::new(token.location).with_color(Color::Red)),
                None,
            );
            had_error.set();
            return Err(());
        };

        last_token = ident;
        import_span = import_span.merge(ident.location);

        (true, vec![ident.map(|t| t.lexeme)])
    } else {
        (false, vec![token.map(|t| t.lexeme)])
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
            diagnostics::emit_error(
                stores,
                colons.location,
                "unexpected end of ident",
                Some(Label::new(colons.location).with_color(Color::Red)),
                None,
            );
            had_error.set();
            return Err(());
        };

        last_token = item_id;
        import_span = import_span.merge(item_id.location);

        path.push(item_id.map(|t| t.lexeme));
    }

    let generic_params = if token_iter.next_is_group(BracketKind::Paren) {
        let Ok(delim) = token_iter
            .expect_group(stores, BracketKind::Paren, token)
            .with_kinds(stores, Matcher("ident", valid_type_token))
        else {
            had_error.set();
            return Err(());
        };

        token.location = token.location.merge(delim.span());

        let span = delim.span();
        let Ok(unresolved_types) =
            parse_multiple_unresolved_types(stores, delim.open.location, &delim.tokens)
        else {
            had_error.set();
            return Err(());
        };

        if unresolved_types.is_empty() {
            diagnostics::emit_error(
                stores,
                span,
                "expected at least type, found 0",
                [Label::new(span).with_color(Color::Red)],
                None,
            );
            had_error.set();
            return Err(());
        }

        import_span = import_span.merge(delim.span());
        last_token = delim.last_token();

        unresolved_types.into_iter().map(|ut| ut.inner).collect()
    } else {
        Vec::new()
    };

    Ok((
        UnresolvedIdent {
            span: import_span,
            is_from_root,
            path,
            generic_params,
        },
        last_token,
    ))
}

pub fn parse_integer_lexeme<T>(stores: &Stores, int_token: Spanned<Token>) -> Result<T, ()>
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
        diagnostics::emit_error(
            stores,
            int_token.location,
            "integer out bounds",
            [Label::new(int_token.location)
                .with_color(Color::Red)
                .with_message(format!(
                    "integer must be in range {}..={}",
                    T::min_value(),
                    T::max_value()
                ))],
            None,
        );
        return Err(());
    };

    Ok(int)
}

pub fn parse_integer_param(
    stores: &Stores,
    token_iter: &mut TokenIter,
    token: Spanned<Token>,
) -> Result<(Spanned<u8>, SourceLocation), ()> {
    let delim = token_iter
        .expect_group(stores, BracketKind::Paren, token)
        .with_kinds(
            stores,
            Matcher("integer", |t| matches!(t, TokenKind::Integer(_))),
        )
        .with_length(stores, 1)?;

    let count_token = delim.tokens[0].unwrap_single();
    let count: u8 = parse_integer_lexeme(stores, count_token)?;
    Ok((count.with_span(count_token.location), delim.span()))
}

pub fn parse_stack_def(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    token_iter: &mut TokenIter,
    prev_token: Spanned<Token>,
) -> Spanned<Vec<Spanned<UnresolvedType>>> {
    let fallback = TreeGroup::fallback(BracketKind::Square, prev_token);
    let stack = token_iter
        .expect_group(stores, BracketKind::Square, prev_token)
        .with_kinds(stores, Matcher("ident", valid_type_token))
        .recover(had_error, &fallback);

    let stack_location = stack.span();
    let unresolved_types =
        parse_multiple_unresolved_types(stores, stack.open.location, &stack.tokens)
            .recover(had_error, Vec::new());

    unresolved_types.with_span(stack_location)
}
