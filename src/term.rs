//! Terms of the dependently typed language and helpers for building them.
//!
//! Operations that need to know about bound variables (free variables,
//! substitution, alpha-equivalence) live in [`crate::substitution`].

/// A term of the language.
///
/// | Rust            | Notation          |
/// |-----------------|-------------------|
/// | `Sort(u)`       | `Sort u`          |
/// | `Var(x)`        | `x` (local)       |
/// | `Const(c)`      | `c` (global)      |
/// | `Pi(x, A, B)`   | `Pi (x : A). B`   |
/// | `Lam(x, A, b)`  | `fun (x : A). b`  |
/// | `App(f, a)`     | `f a`             |
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Sort(u64),
    Var(String),
    Const(String),
    Pi(String, Box<Term>, Box<Term>),
    Lam(String, Box<Term>, Box<Term>),
    App(Box<Term>, Box<Term>),
}

/// `x`, a local variable.
pub fn var(x: &str) -> Term {
    Term::Var(x.into())
}

/// `c`, a global constant from the signature.
pub fn const_term(c: &str) -> Term {
    Term::Const(c.into())
}

/// `f a`
pub fn app(f: Term, a: Term) -> Term {
    Term::App(Box::new(f), Box::new(a))
}

/// `f a_1 ... a_n`
pub fn apps(f: Term, args: impl IntoIterator<Item = Term>) -> Term {
    args.into_iter().fold(f, app)
}

/// `Pi (x : A). B`
pub fn pi(x: &str, a: Term, b: Term) -> Term {
    Term::Pi(x.into(), Box::new(a), Box::new(b))
}

/// `fun (x : A). b`
pub fn lam(x: &str, a: Term, b: Term) -> Term {
    Term::Lam(x.into(), Box::new(a), Box::new(b))
}

/// `A -> B`, a non-dependent `Pi`.
pub fn arrow(a: Term, b: Term) -> Term {
    pi("_", a, b)
}

/// Builds `Pi (x_1 : A_1) ... Pi (x_k : A_k). tail` from the telescope
/// `(x_1 : A_1) ... (x_k : A_k)`, written `Pi (xs : As). tail` in the text.
///
/// A *telescope* is a sequence of bindings in which each type `A_i` may
/// mention the earlier names `x_1, ..., x_{i-1}`.
pub fn telescope(binders: &[(String, Term)], tail: Term) -> Term {
    binders
        .iter()
        .rev()
        .fold(tail, |body, (name, ty)| pi(name, ty.clone(), body))
}

/// Decomposes a term into its *spine* `h a_1 ... a_n`: a head `h` that is not an
/// application, and the arguments it is applied to.
///
/// For example, `f a b` becomes `(f, [a, b])`, and a term that is not an
/// application becomes `(t, [])`.
pub fn spine(t: &Term) -> (Term, Vec<Term>) {
    match t {
        Term::App(f, a) => {
            let (head, mut args) = spine(f);
            args.push((**a).clone());
            (head, args)
        }
        _ => (t.clone(), vec![]),
    }
}

/// Does the global constant `name` occur anywhere in `t`?
pub fn occurs_const(t: &Term, name: &str) -> bool {
    match t {
        Term::Const(c) => c == name,
        Term::App(f, a) => occurs_const(f, name) || occurs_const(a, name),
        Term::Pi(_, a, b) | Term::Lam(_, a, b) => occurs_const(a, name) || occurs_const(b, name),
        Term::Sort(_) | Term::Var(_) => false,
    }
}
