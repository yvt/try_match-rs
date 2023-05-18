#![warn(rust_2018_idioms)]
#![forbid(unsafe_code)]

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use std::mem::replace;
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input,
    spanned::Spanned,
    Expr, Ident, LitStr, Pat, PatIdent, Result, Token,
};

macro_rules! abort {
    ($span:expr, $($format:tt)+) => {{
        return Err(syn::Error::new($span, format!($($format)+)).into());
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
    wrap_output_fn: proc_macro2::TokenStream,
    fallback_arm: proc_macro2::TokenStream,
}

impl Parse for MacroInput {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let in_value = input.parse()?;

        input.parse::<Token![,]>()?;

        let pat = Pat::parse_multi_with_leading_vert(input)?;
        let guard = if input.peek(Token![if]) {
            let if_token: Token![if] = input.parse()?;
            let guard: Expr = input.parse()?;
            Some((if_token, Box::new(guard)))
        } else {
            None
        };

        input.parse::<Token![,]>()?;

        let wrap_output_fn = input.parse::<proc_macro2::Group>()?.stream();
        let fallback_arm = input.parse::<proc_macro2::Group>()?.stream();

        Ok(Self {
            pat,
            in_value,
            guard,
            wrap_output_fn,
            fallback_arm,
        })
    }
}

#[proc_macro]
pub fn implicit_try_match_inner(input: TokenStream) -> TokenStream {
    let MacroInput {
        mut pat,
        in_value,
        guard,
        wrap_output_fn,
        fallback_arm,
    } = parse_macro_input!(input);

    // Make sure all `Pat::Ident` that are variable bindings have subpatterns,
    // and the rest don't
    let mut visitor = ForceVariableBindings {
        introduced_subpat: false,
    };
    bail_if_err!(pat_visit_mut::Visit::visit_pat(&mut visitor, &mut pat));
    let ForceVariableBindings { introduced_subpat } = visitor;

    // Collect identifiers
    let mut visitor = CollectVariableBindings {
        bindings: Vec::new(),
    };
    pat_visit::Visit::visit_pat(&mut visitor, &pat)
        .expect("errors should have already been reported");
    let CollectVariableBindings {
        bindings: mut idents,
    } = visitor;

    idents.sort_unstable_by_key(|i| &i.ident);
    idents.dedup_by_key(|i| &i.ident);

    let success_output =
        // Check if bound variables are all like `_0`, `_1`, in which case
        // collect them in a tuple
        if let Some(tokens) = bail_if_err!(check_tuple_captures(&idents)) {
            // XXX: Suppress `clippy::just_underscores_and_digits` by
            // introducing a macro-generated span into the patterns
            // <https://github.com/yvt/try_match-rs/issues/2>
            //
            // Clippy suppresses ignore lint if `pat.span.from_expansion()`:
            // <https://github.com/rust-lang/rust-clippy/blob/f9c1d155b4c9cad224fe96aad486993dc123c9b6/clippy_lints/src/non_expressive_names.rs#L140>
            //
            // `pat.span` is created by `first_token_span.to(last_token_span)`:
            // <https://github.com/rust-lang/rust/blob/eac35583d2ffb5ed9e564dee0822c9a244058ee0/compiler/rustc_parse/src/parser/pat.rs#L463>
            //
            // `Span::to` returns a macro-generated one if the given `Span`s
            // have different contexts:
            // <https://github.com/rust-lang/rust/blob/eac35583d2ffb5ed9e564dee0822c9a244058ee0/compiler/rustc_span/src/lib.rs#L831-L842>
            pat_visit_mut::Visit::visit_pat(&mut SuppressClippyIdentWarnings, &mut pat)
                .expect("errors should have already been reported");

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
            #pat #guard => #wrap_output_fn(#success_output),
            #fallback_arm
        }
    };

    TokenStream::from(output)
}

/// An implementation of [`pat_visit_mut::Visit`] to add subpatterns to all
/// likely variable bindings.
struct ForceVariableBindings {
    introduced_subpat: bool,
}

impl pat_visit_mut::Visit for ForceVariableBindings {
    type Error = syn::Error;

    fn visit_pat_ident(&mut self, pat: &mut PatIdent) -> Result<()> {
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
                    self.introduced_subpat = true;
                    Ok(())
                }
                // Probably a constant pattern
                Some(false) => Ok(()),
                // Unsure; abort compilation to be safe
                None => abort!(pat.span(), "ambiguous identifier pattern"),
            }
        }
    }

    fn visit_field_pat(&mut self, field: &mut syn::FieldPat) -> Result<()> {
        pat_visit_mut::visit_field_pat(self, field)?;

        if field.colon_token.is_none() {
            // Field shorthand in a struct pattern - by processing it with
            // `self.visit_pat_ident`, we have just turned it into an invalid
            // pattern (e.g., `St { a }` -> `St { a @ _ }`). Expand the
            // shorthand to make it valid.
            field.colon_token = Some(syn::token::Colon {
                spans: [Span::call_site()],
            });
        }

        Ok(())
    }
}

/// An implementation of [`pat_visit::Visit`] to collect variable bindings,
/// assuming they have been processed by [`ForceVariableBindings`].
struct CollectVariableBindings<'a> {
    bindings: Vec<&'a PatIdent>,
}

impl<'a> pat_visit::Visit<'a> for CollectVariableBindings<'a> {
    type Error = syn::Error;

    fn visit_pat_ident(&mut self, pat: &'a PatIdent) -> Result<()> {
        // `pat.subpat.is_some()` iff it's a variable binding
        if pat.subpat.is_some() {
            self.bindings.push(pat);
        }

        pat_visit::visit_pat_ident(self, pat)
    }
}

/// An implementation of [`pat_visit_mut::Visit`] to suppress Clippy warnings
/// for tuple field patterns. See the use site for the reasons behind.
struct SuppressClippyIdentWarnings;

impl pat_visit_mut::Visit for SuppressClippyIdentWarnings {
    type Error = syn::Error;

    fn visit_pat_ident(&mut self, pat: &mut PatIdent) -> Result<()> {
        // `pat.subpat.is_some()` iff it's a variable binding
        if let Some((_, subpat)) = &mut pat.subpat {
            // Wrap `subpat` with a `PatParen` so that the last token of
            // the pattern becomes macro-generated
            let old_subpat = replace(
                &mut **subpat,
                Pat::Verbatim(proc_macro2::TokenStream::default()),
            );
            **subpat = Pat::Paren(syn::PatParen {
                attrs: Vec::new(),
                paren_token: syn::token::Paren::default(),
                pat: Box::new(old_subpat),
            });
        }
        Ok(())
    }
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

macro_rules! define_visit_pat_trait {
    (
        #[mut($($mut:tt)*)]
        #[iter($iter:ident)]
        #[out_lifetime($($out_lifetime:tt)*)]
        fn visit_pat(..);
        ..
    ) => {
        use syn::{FieldPat, Pat, PatIdent, spanned::Spanned};

        pub trait Visit<$($out_lifetime)*> {
            type Error: From<syn::Error>;

            fn visit_pat(
                &mut self,
                pat: & $($out_lifetime)* $($mut)* Pat,
            ) -> Result<(), Self::Error> {
                visit_pat(self, pat)
            }

            fn visit_pat_ident(
                &mut self,
                pat: & $($out_lifetime)* $($mut)* PatIdent,
            ) -> Result<(), Self::Error> {
                visit_pat_ident(self, pat)
            }

            fn visit_field_pat(
                &mut self,
                field: & $($out_lifetime)* $($mut)* FieldPat,
            ) -> Result<(), Self::Error> {
                visit_field_pat(self, field)
            }
        }

        pub fn visit_pat<'a, V: ?Sized + Visit< $($out_lifetime)* >>(
            visit: &mut V,
            pat: &'a $($mut)* Pat,
        ) -> Result<(), V::Error> {
            match pat {
                Pat::Const(_) => Ok(()),
                Pat::Ident(pat) => visit.visit_pat_ident(pat),
                Pat::Lit(_) => Ok(()),
                Pat::Macro(_) => Ok(()),
                Pat::Or(pat) => {
                    for case in pat.cases.$iter() {
                        visit.visit_pat(case)?;
                    }
                    Ok(())
                }
                Pat::Paren(pat) => visit.visit_pat(& $($mut)* pat.pat),
                Pat::Path(_) => Ok(()),
                Pat::Range(_) => Ok(()),
                Pat::Reference(pat) => visit.visit_pat(& $($mut)* pat.pat),
                Pat::Rest(_) => Ok(()),
                Pat::Slice(pat) => {
                    for elem in pat.elems.$iter() {
                        visit.visit_pat(elem)?;
                    }
                    Ok(())
                }
                Pat::Struct(pat) => {
                    for field in pat.fields.$iter() {
                        visit.visit_field_pat(field)?;
                    }
                    Ok(())
                }
                Pat::Tuple(pat) => {
                    for elem in pat.elems.$iter() {
                        visit.visit_pat(elem)?;
                    }
                    Ok(())
                }
                Pat::TupleStruct(pat) => {
                    for elem in pat.elems.$iter() {
                        visit.visit_pat(elem)?;
                    }
                    Ok(())
                }
                Pat::Type(pat) => visit.visit_pat(& $($mut)* pat.pat),
                Pat::Wild(_) => Ok(()),
                // `Pat` can't be covered exhaustively.
                // `Verbatim` is intentionally unhandled so that future additions to
                // `Pat` won't break existing code.
                _ => abort!(pat.span(), "unsupported pattern"),
            }
        }

        pub fn visit_pat_ident<'a, V: ?Sized + Visit< $($out_lifetime)* >>(
            visit: &mut V,
            pat: &'a $($mut)* PatIdent,
        ) -> Result<(), V::Error> {
            if let Some((_, subpat)) = & $($mut)* pat.subpat {
                visit.visit_pat(subpat)?;
            }
            Ok(())
        }

        pub fn visit_field_pat<'a, V: ?Sized + Visit< $($out_lifetime)* >>(
            visit: &mut V,
            field: &'a $($mut)* FieldPat,
        ) -> Result<(), V::Error> {
            visit.visit_pat(& $($mut)* field.pat)
        }
    }
}

mod pat_visit {
    define_visit_pat_trait! {
        #[mut()]
        #[iter(iter)]
        #[out_lifetime('a)]
        fn visit_pat(..);
        ..
    }
}

#[allow(clippy::needless_lifetimes)]
mod pat_visit_mut {
    define_visit_pat_trait! {
        #[mut(mut)]
        #[iter(iter_mut)]
        #[out_lifetime()]
        fn visit_pat(..);
        ..
    }
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
