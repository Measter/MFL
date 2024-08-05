use crate::{
    lexer::{BracketKind, TokenKind, TokenTree},
    stores::source::{SourceLocation, Spanned},
};

#[derive(Debug, Clone, Copy)]
pub(super) enum IsMatch {
    Yes,
    No(SourceLocation),
}

impl IsMatch {
    pub(super) fn yes(self) -> bool {
        match self {
            IsMatch::Yes => true,
            IsMatch::No(_) => false,
        }
    }

    pub(super) fn no(self) -> bool {
        match self {
            IsMatch::Yes => false,
            IsMatch::No(_) => true,
        }
    }
}

pub(super) trait ExpectedTokenMatcher<T> {
    fn kind_str(&self) -> &'static str;
    fn is_match(&self, tk: T) -> IsMatch;
    fn is_brace_group(&self) -> bool {
        false
    }
}

impl ExpectedTokenMatcher<Spanned<TokenKind>> for TokenKind {
    fn kind_str(&self) -> &'static str {
        TokenKind::kind_str(*self)
    }

    fn is_match(&self, tk: Spanned<TokenKind>) -> IsMatch {
        if tk.inner == *self {
            IsMatch::Yes
        } else {
            IsMatch::No(tk.location)
        }
    }
}

impl ExpectedTokenMatcher<&TokenTree> for TokenKind {
    fn kind_str(&self) -> &'static str {
        TokenKind::kind_str(*self)
    }

    fn is_match(&self, tk: &TokenTree) -> IsMatch {
        match tk {
            TokenTree::Single(tk) if tk.inner.kind == *self => IsMatch::Yes,
            _ => IsMatch::No(tk.span()),
        }
    }
}

// Wrapper because Rust's inference is dumb.
pub(super) struct Matcher<T>(pub &'static str, pub fn(T) -> IsMatch);

impl ExpectedTokenMatcher<Spanned<TokenKind>> for Matcher<Spanned<TokenKind>> {
    fn kind_str(&self) -> &'static str {
        self.0
    }

    fn is_match(&self, tk: Spanned<TokenKind>) -> IsMatch {
        self.1(tk)
    }
}

impl ExpectedTokenMatcher<&TokenTree> for Matcher<Spanned<TokenKind>> {
    fn kind_str(&self) -> &'static str {
        self.0
    }

    fn is_match(&self, tk: &TokenTree) -> IsMatch {
        match tk {
            TokenTree::Single(tk) => self.1(tk.map(|t| t.kind)),
            TokenTree::Group(_) => IsMatch::No(tk.span()),
        }
    }
}

impl<'a> ExpectedTokenMatcher<&'a TokenTree> for Matcher<&'a TokenTree> {
    fn kind_str(&self) -> &'static str {
        self.0
    }

    fn is_match(&self, tk: &'a TokenTree) -> IsMatch {
        self.1(tk)
    }
}

pub(super) struct ConditionMatch;
impl ExpectedTokenMatcher<&TokenTree> for ConditionMatch {
    fn kind_str(&self) -> &'static str {
        "{"
    }

    fn is_match(&self, tk: &TokenTree) -> IsMatch {
        if matches!(tk, TokenTree::Group(tg) if tg.bracket_kind == BracketKind::Brace) {
            IsMatch::Yes
        } else {
            IsMatch::No(tk.span())
        }
    }

    fn is_brace_group(&self) -> bool {
        true
    }
}

pub(super) fn integer_tokens(t: Spanned<TokenKind>) -> IsMatch {
    if let TokenKind::Integer(_) = t.inner {
        IsMatch::Yes
    } else {
        IsMatch::No(t.location)
    }
}

pub(super) fn valid_type_token(tt: &TokenTree) -> IsMatch {
    match tt {
        TokenTree::Single(tk)
            if matches!(
                tk.inner.kind,
                TokenKind::Ident
                    | TokenKind::Integer { .. }
                    | TokenKind::ColonColon
                    | TokenKind::Ampersand
                    | TokenKind::Star
            ) =>
        {
            IsMatch::Yes
        }

        TokenTree::Group(tg)
            if tg.bracket_kind == BracketKind::Paren || tg.bracket_kind == BracketKind::Square =>
        {
            let Some(invalid) = tg.tokens.iter().map(valid_type_token).find(|im| im.no()) else {
                return IsMatch::Yes;
            };
            invalid
        }

        _ => IsMatch::No(tt.span()),
    }
}

pub(super) fn attribute_tokens(tt: &TokenTree) -> IsMatch {
    match tt {
        TokenTree::Single(tk)
            if matches!(
                tk.inner.kind,
                TokenKind::Extern | TokenKind::Ident | TokenKind::LangItem
            ) =>
        {
            IsMatch::Yes
        }
        TokenTree::Group(g) if g.bracket_kind == BracketKind::Paren => IsMatch::Yes,
        _ => IsMatch::No(tt.span()),
    }
}
