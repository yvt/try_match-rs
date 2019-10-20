extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::Span;
use proc_macro_error::abort;
use quote::quote;
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input,
    spanned::Spanned,
    Error, Ident, LitStr, Pat, PatIdent, Result,
};

struct MacroInput {
    use_std: bool,
    pat: Pat,
}

impl Parse for MacroInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let std_mode: Ident = input.parse()?;
        let pat = input.parse()?;

        Ok(Self {
            use_std: if std_mode == "std" {
                true
            } else if std_mode == "no_std" {
                false
            } else {
                return Err(Error::new_spanned(std_mode, ""));
            },
            pat,
        })
    }
}

#[proc_macro_hack::proc_macro_hack]
#[proc_macro_error::proc_macro_error]
pub fn collect_captures(input: TokenStream) -> TokenStream {
    let MacroInput { use_std, pat } = parse_macro_input!(input);

    let mut idents = Vec::new();
    collect_pat_ident(&pat, &mut idents);

    let output = match &idents[..] {
        [] => {
            quote! {()}
        }
        [single] => {
            quote! {#single}
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

            let debug_impl = if use_std {
                let fmt = quote! { ::std::fmt };
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
            } else {
                quote! {}
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
    };

    TokenStream::from(output)
}

fn collect_pat_ident<'a>(pat: &'a Pat, out: &mut Vec<&'a PatIdent>) {
    match pat {
        Pat::Box(pat) => collect_pat_ident(&pat.pat, out),
        Pat::Ident(pat) => {
            out.push(pat);
            if let Some((_, subpat)) = &pat.subpat {
                collect_pat_ident(&subpat, out);
            }
        }
        Pat::Lit(_) => {}
        Pat::Macro(_) => {}
        Pat::Or(pat) => {
            for case in pat.cases.iter() {
                collect_pat_ident(&case, out);
            }
        }
        Pat::Path(_) => {}
        Pat::Range(_) => {}
        Pat::Reference(pat) => collect_pat_ident(&pat.pat, out),
        Pat::Rest(_) => {}
        Pat::Slice(pat) => {
            for elem in pat.elems.iter() {
                collect_pat_ident(&elem, out);
            }
        }
        Pat::Struct(pat) => {
            for field in pat.fields.iter() {
                collect_pat_ident(&field.pat, out);
            }
        }
        Pat::Tuple(pat) => {
            for elem in pat.elems.iter() {
                collect_pat_ident(&elem, out);
            }
        }
        Pat::TupleStruct(pat) => {
            for elem in pat.pat.elems.iter() {
                collect_pat_ident(&elem, out);
            }
        }
        Pat::Type(pat) => collect_pat_ident(&pat.pat, out),
        Pat::Wild(_) => {}
        // `Pat` can't be covered exhaustively
        Pat::Verbatim(_) | _ => abort!(pat.span(), "unsupported pattern"),
    }
}
