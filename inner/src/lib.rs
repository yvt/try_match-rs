#![warn(rust_2018_idioms)]
#![forbid(unsafe_code)]

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input,
    spanned::Spanned,
    Expr, Ident, LitStr, Pat, PatIdent, Result, Token,
};

macro_rules! abort {
    ($span:expr, $($format:tt)+) => {{
        return Err(syn::Error::new($span, format!($($format)+)));
    }};
}

macro_rules! bail_if_err {
    ($expr:expr) => {
        match $expr {
            Ok(x) => x,
            Err(e) => return e.into_compile_error().into(),
        }
    };
}

struct MacroInput {
    in_value: Expr,
    pat: Pat,
    guard: Option<(Token![if], Box<Expr>)>,
}

impl Parse for MacroInput {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let in_value = input.parse()?;
        input.parse::<Token![,]>()?;
        let pat = Pat::parse_multi_with_leading_vert(&input)?;
        let guard = if input.peek(Token![if]) {
            let if_token: Token![if] = input.parse()?;
            let guard: Expr = input.parse()?;
            Some((if_token, Box::new(guard)))
        } else {
            None
        };

        Ok(Self {
            pat,
            in_value,
            guard,
        })
    }
}

#[proc_macro]
pub fn implicit_try_match_inner(input: TokenStream) -> TokenStream {
    let MacroInput {
        mut pat,
        in_value,
        guard,
    } = parse_macro_input!(input);

    // Make sure all `Pat::Ident` that are variable bindings have subpatterns,
    // and the rest don't
    let mut introduced_subpat = false;
    bail_if_err!(for_each_pat_ident_mut(&mut pat, &mut |pat| {
        if pat.subpat.is_some() {
            // Definitely a variable binding and already has a subpattern
            Ok(())
        } else {
            match is_likely_variable_binding(&pat.ident) {
                // Probably a variable binding; add a wildcard subpattern
                Some(true) => {
                    pat.subpat = Some((
                        syn::token::At {
                            spans: [Span::call_site()],
                        },
                        Box::new(Pat::Wild(syn::PatWild {
                            attrs: Vec::new(),
                            underscore_token: syn::token::Underscore {
                                spans: [Span::call_site()],
                            },
                        })),
                    ));
                    introduced_subpat = true;
                    Ok(())
                }
                // Probably a constant pattern
                Some(false) => Ok(()),
                // Unsure; abort compilation to be safe
                None => abort!(pat.span(), "ambiguous identifier pattern"),
            }
        }
    }));

    let mut idents = Vec::new();
    bail_if_err!(for_each_pat_ident(&pat, &mut |ident| {
        if ident.subpat.is_some() {
            idents.push(ident);
        }
        Ok(())
    }));

    idents.sort_unstable_by_key(|i| &i.ident);
    idents.dedup_by_key(|i| &i.ident);

    let success_output =
        // Check if bound variables are all like `_0`, `_1`, in which case
        // collect them in a tuple
        if let Some(tokens) = bail_if_err!(check_tuple_captures(&idents)) {
            tokens
        } else {
            // Decide what to do based on the number of bound variables
            match &idents[..] {
                [] => {
                    quote! {()}
                }
                [single] => {
                    let ident = &single.ident;
                    quote! {#ident}
                }
                multi => {
                    // `var1`, `var2`, ...
                    let idents: Vec<_> = multi.iter().map(|p| p.ident.clone()).collect();

                    // `_M_0`, `_M_1`, ...
                    let ty_params: Vec<_> = (0..idents.len())
                        .map(|i| Ident::new(&format!("_M_{}", i), Span::call_site()))
                        .collect();

                    // `"var1"`, `"var2"`, ...
                    let ident_strs: Vec<_> = idents
                        .iter()
                        .map(|i| LitStr::new(&format!("{}", i), i.span()))
                        .collect();

                    let ty_name = Ident::new("__Match", Span::call_site());

                    let debug_impl = {
                        let fmt = quote! { ::core::fmt };
                        quote! {
                            impl<#(#ty_params),*> #fmt::Debug for #ty_name<#(#ty_params),*>
                            where
                                #(#ty_params: #fmt::Debug),*
                            {
                                fn fmt(&self, f: &mut #fmt::Formatter<'_>) -> #fmt::Result {
                                    f.debug_struct("<anonymous>")
                                        #(.field(#ident_strs, &self.#idents))*
                                        .finish()
                                }
                            }
                        }
                    };

                    quote! {{
                        #[derive(Clone, Copy)]
                        struct #ty_name<#(#ty_params),*> {
                            #(
                                #idents: #ty_params
                            ),*
                        }

                        #debug_impl

                        #ty_name { #(#idents),* }
                    }}
                }
            }
        };

    let guard = guard.map(|(t0, t1)| quote! { #t0 #t1 });

    let allow_redundant_pattern = if introduced_subpat {
        // Clippy may warn about wildcard subpatterns on variable bindings.
        // They could indeed be redundant if they don't shadow constants, but we
        // have no way of telling that.
        quote! { #[allow(clippy::redundant_pattern)] }
    } else {
        quote! {}
    };

    let output = quote! {
        match #in_value {
            #allow_redundant_pattern
            #pat #guard => ::core::result::Result::Ok(#success_output),
            in_value => ::core::result::Result::Err(in_value),
        }
    };

    TokenStream::from(output)
}

/// Check if `idents` contains a tuple binding (e.g., `_4`). If it does, returns
/// a `TokenStream` that collects the bound variables (e.g., `(_0, _1)`).
#[allow(clippy::manual_strip)] // `strip_prefix` is only available in Rust ≥ 1.45
fn check_tuple_captures(idents: &[&PatIdent]) -> Result<Option<proc_macro2::TokenStream>> {
    let mut some_tuple_cap = None;
    let mut some_non_tuple_cap = None;

    let mut indices: Vec<(u128, &Ident)> = idents
        .iter()
        .map(|i| {
            let index = {
                let text = i.ident.to_string();
                if text.starts_with('_') {
                    // assuming the index fits in `u128`...
                    text[1..].parse().ok()
                } else {
                    None
                }
            };

            if let Some(index) = index {
                some_tuple_cap = Some(*i);
                (index, &i.ident)
            } else {
                some_non_tuple_cap = Some(*i);
                (0 /* dummy */, &i.ident)
            }
        })
        .collect();

    if let (Some(i1), Some(i2)) = (some_tuple_cap, some_non_tuple_cap) {
        abort!(
            i1.span(),
            "can't have both of a tuple binding `{}` and a non-tuple binding \
             `{}` at the same time",
            i1.ident,
            i2.ident
        );
    }

    if some_tuple_cap.is_some() {
        // Create a reverse map from tuple fields to bound variables
        indices.sort_unstable_by_key(|e| e.0);

        for (&(ind, ref ident), i) in indices.iter().zip(0u128..) {
            use std::cmp::Ordering::*;
            match ind.cmp(&i) {
                Equal => {}
                // If `ind` and `i` increase in a different pace, that means
                // some index is missed or specified twice
                Less => {
                    // FIXME: Duplicate bindings may be valid in "or" patterns
                    assert_eq!(ind, i - 1);
                    abort!(
                        ident.span(),
                        "duplicate tuple binding: `_{}` is defined for multiple times",
                        ind
                    );
                }
                Greater if ind - 1 == i => {
                    abort!(
                        ident.span(),
                        "non-contiguous tuple binding: `_{}` is missing",
                        ind - 1
                    );
                }
                Greater => {
                    abort!(
                        ident.span(),
                        "non-contiguous tuple binding: `_{}` .. `_{}` are missing",
                        i,
                        ind - 1
                    );
                }
            }
        }

        // `var1`, `var2`, ...
        let idents: Vec<_> = indices.into_iter().map(|p| p.1).collect();

        Ok(Some(quote! { ( #(#idents),* ) }))
    } else {
        Ok(None)
    }
}

macro_rules! define_for_each_pat_ident {
    (
        #[mut($($mut:tt)*)]
        #[iter($iter:ident)]
        #[out_lifetime($($out_lifetime:tt)*)]
        fn $ident:ident(..);
    ) => {
        #[allow(clippy::needless_lifetimes)]
        fn $ident<'a>(
            pat: &'a $($mut)* Pat,
            out: &mut impl FnMut(&$($out_lifetime)* $($mut)* PatIdent) -> Result<()>,
        ) -> Result<()> {
            match pat {
                Pat::Const(_) => {}
                Pat::Ident(pat) => {
                    out(pat)?;
                    if let Some((_, subpat)) = & $($mut)* pat.subpat {
                        $ident(subpat, out)?;
                    }
                }
                Pat::Lit(_) => {}
                Pat::Macro(_) => {}
                Pat::Or(pat) => {
                    for case in pat.cases.$iter() {
                        $ident(case, out)?;
                    }
                }
                Pat::Paren(pat) => $ident(& $($mut)* pat.pat, out)?,
                Pat::Path(_) => {}
                Pat::Range(_) => {}
                Pat::Reference(pat) => $ident(& $($mut)* pat.pat, out)?,
                Pat::Rest(_) => {}
                Pat::Slice(pat) => {
                    for elem in pat.elems.$iter() {
                        $ident(elem, out)?;
                    }
                }
                Pat::Struct(pat) => {
                    for field in pat.fields.$iter() {
                        $ident(& $($mut)* field.pat, out)?;
                    }
                }
                Pat::Tuple(pat) => {
                    for elem in pat.elems.$iter() {
                        $ident(elem, out)?;
                    }
                }
                Pat::TupleStruct(pat) => {
                    for elem in pat.elems.$iter() {
                        $ident(elem, out)?;
                    }
                }
                Pat::Type(pat) => $ident(& $($mut)* pat.pat, out)?,
                Pat::Wild(_) => {}
                // `Pat` can't be covered exhaustively.
                // `Verbatim` is intentionally unhandled so that future additions to
                // `Pat` won't break existing code.
                _ => abort!(pat.span(), "unsupported pattern"),
            }
            Ok(())
        }
    }
}

define_for_each_pat_ident! {
    #[mut()]
    #[iter(iter)]
    #[out_lifetime('a)]
    fn for_each_pat_ident(..);
}

define_for_each_pat_ident! {
    #[mut(mut)]
    #[iter(iter_mut)]
    #[out_lifetime()]
    fn for_each_pat_ident_mut(..);
}

/// Use heuristics to determine if an [`Ident`] represents a variable binding.
fn is_likely_variable_binding(ident: &Ident) -> Option<bool> {
    struct Scanner {
        raw_ident: RawIdent,
        ident: Ident,
    }

    enum RawIdent {
        ExpectingR,
        ExpectingHash,
        Done,
    }

    enum Ident {
        ExpectingAlphanumOrUnderscore,
        ExpectingAlphanum,
        Done(Option<bool>),
    }

    use std::fmt::Write;
    impl Write for Scanner {
        fn write_str(&mut self, s: &str) -> std::fmt::Result {
            for b in s.bytes() {
                // Skip `r#` prefix
                match (&self.raw_ident, b) {
                    (RawIdent::ExpectingR, b'r') => {
                        self.raw_ident = RawIdent::ExpectingHash;
                    }
                    (RawIdent::ExpectingHash, b'#') => {
                        self.raw_ident = RawIdent::Done;

                        // It starts with `r#`; reset `self.ident`
                        self.ident = Ident::ExpectingAlphanumOrUnderscore;
                        continue;
                    }
                    _ => {
                        // It doesn't have a `r#` prefix
                        self.raw_ident = RawIdent::Done;
                    }
                }

                // Match against pattern `^_?([0-9a-zA-Z])`
                //
                // It's intentionally limited to ASCII characters so that the
                // result is consistent between Unicode versions. The Unicode
                // stability policy can be found here:
                // <http://www.unicode.org/policies/stability_policy.html>
                match (&self.ident, b) {
                    (Ident::Done(_), _) => {}
                    (Ident::ExpectingAlphanumOrUnderscore | Ident::ExpectingAlphanum, b)
                        if b.is_ascii_alphanumeric() =>
                    {
                        // Output `true` if the alphanumeric byte matches `[0-9a-z]`
                        self.ident = Ident::Done(Some(!b.is_ascii_uppercase()));
                    }
                    (Ident::ExpectingAlphanumOrUnderscore, b'_') => {
                        self.ident = Ident::ExpectingAlphanum;
                    }
                    _ => {
                        self.ident = Ident::Done(None);
                    }
                }
            }
            Ok(())
        }
    }

    let mut scanner = Scanner {
        raw_ident: RawIdent::ExpectingR,
        ident: Ident::ExpectingAlphanumOrUnderscore,
    };
    write!(scanner, "{}", ident).unwrap();

    match scanner.ident {
        Ident::ExpectingAlphanumOrUnderscore => None, // Empty or `r#`, should be impossible
        Ident::ExpectingAlphanum => None,             // `_`, should be handled by `Pat::Wild`
        Ident::Done(output) => output,
    }
}
