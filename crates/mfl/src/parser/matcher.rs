use lexer::{BracketKind, Token};
use stores::source::{SourceLocation, Spanned};

use crate::lexer::TokenTree;

#[derive(Debug, Clone, Copy)]
pub(super) enum IsMatch {
    Yes,
    No(&'static str, SourceLocation),
}

impl IsMatch {
    pub(super) fn yes(self) -> bool {
        match self {
            IsMatch::Yes => true,
            IsMatch::No(..) => false,
        }
    }

    pub(super) fn no(self) -> bool {
        match self {
            IsMatch::Yes => false,
            IsMatch::No(..) => true,
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

impl ExpectedTokenMatcher<Spanned<Token>> for Token {
    fn kind_str(&self) -> &'static str {
        Token::kind_str(*self)
    }

    fn is_match(&self, tk: Spanned<Token>) -> IsMatch {
        if tk.inner == *self {
            IsMatch::Yes
        } else {
            IsMatch::No(tk.inner.kind_str(), tk.location)
        }
    }
}

impl ExpectedTokenMatcher<&TokenTree> for Token {
    fn kind_str(&self) -> &'static str {
        Token::kind_str(*self)
    }

    fn is_match(&self, tk: &TokenTree) -> IsMatch {
        match tk {
            TokenTree::Single(tk) if tk.inner == *self => IsMatch::Yes,
            _ => IsMatch::No(tk.kind_str(), tk.span()),
        }
    }
}

// Wrapper because Rust's inference is dumb.
pub(super) struct Matcher<T>(pub &'static str, pub fn(T) -> IsMatch);

impl ExpectedTokenMatcher<Spanned<Token>> for Matcher<Spanned<Token>> {
    fn kind_str(&self) -> &'static str {
        self.0
    }

    fn is_match(&self, tk: Spanned<Token>) -> IsMatch {
        self.1(tk)
    }
}

impl ExpectedTokenMatcher<&TokenTree> for Matcher<Spanned<Token>> {
    fn kind_str(&self) -> &'static str {
        self.0
    }

    fn is_match(&self, tk: &TokenTree) -> IsMatch {
        match tk {
            TokenTree::Single(tk) => self.1(*tk),
            TokenTree::Group(_) => IsMatch::No(tk.kind_str(), tk.span()),
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
            IsMatch::No(tk.kind_str(), tk.span())
        }
    }

    fn is_brace_group(&self) -> bool {
        true
    }
}

pub(super) struct IdentPathMatch;
impl ExpectedTokenMatcher<Spanned<Token>> for IdentPathMatch {
    fn kind_str(&self) -> &'static str {
        "ident"
    }

    fn is_match(&self, tk: Spanned<Token>) -> IsMatch {
        match tk.inner {
            Token::ColonColon | Token::Lib | Token::SelfKw | Token::Super | Token::Ident => {
                IsMatch::Yes
            }
            _ => IsMatch::No(tk.inner.kind_str(), tk.location),
        }
    }
}

pub(super) fn integer_tokens(t: Spanned<Token>) -> IsMatch {
    if let Token::Integer(_) = t.inner {
        IsMatch::Yes
    } else {
        IsMatch::No(t.inner.kind_str(), t.location)
    }
}

pub(super) fn valid_type_token(tt: &TokenTree) -> IsMatch {
    match tt {
        TokenTree::Single(tk)
            if matches!(
                tk.inner,
                Token::Ident
                    | Token::Integer { .. }
                    | Token::ColonColon
                    | Token::Ampersand
                    | Token::Star
                    | Token::Comma
                    | Token::Proc
                    | Token::GoesTo
                    | Token::Lib
                    | Token::SelfKw
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

        _ => IsMatch::No(tt.kind_str(), tt.span()),
    }
}

pub(super) fn attribute_tokens(tt: &TokenTree) -> IsMatch {
    match tt {
        TokenTree::Single(tk)
            if matches!(tk.inner, Token::Extern | Token::Ident | Token::LangItem) =>
        {
            IsMatch::Yes
        }
        TokenTree::Group(g) if g.bracket_kind == BracketKind::Paren => IsMatch::Yes,
        _ => IsMatch::No(tt.kind_str(), tt.span()),
    }
}

pub(super) fn stack_def_tokens(tt: &TokenTree) -> IsMatch {
    match tt {
        TokenTree::Single(tk)
            if matches!(
                tk.inner,
                Token::Ident
                    | Token::Integer { .. }
                    | Token::ColonColon
                    | Token::Colon
                    | Token::Ampersand
                    | Token::Star
                    | Token::Comma
                    | Token::Variable
                    | Token::Proc
                    | Token::GoesTo
                    | Token::Lib
                    | Token::SelfKw
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

        _ => IsMatch::No(tt.kind_str(), tt.span()),
    }
}
