use std::collections::{HashMap, HashSet};

// Terms for the dependently-typed language
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Sort(u64),
    Var(String),
    Const(String),
    Pi(String, Box<Term>, Box<Term>),
    Lam(String, Box<Term>, Box<Term>),
    App(Box<Term>, Box<Term>),
}

// Convenience constructors for terms
pub fn var(x: &str) -> Term {
    Term::Var(x.into())
}
pub fn konst(x: &str) -> Term {
    Term::Const(x.into())
}
pub fn app(f: Term, a: Term) -> Term {
    Term::App(Box::new(f), Box::new(a))
}
pub fn apps(f: Term, args: impl IntoIterator<Item = Term>) -> Term {
    args.into_iter().fold(f, app)
}
pub fn pi(x: &str, a: Term, b: Term) -> Term {
    Term::Pi(x.into(), Box::new(a), Box::new(b))
}
pub fn lam(x: &str, a: Term, b: Term) -> Term {
    Term::Lam(x.into(), Box::new(a), Box::new(b))
}
pub fn arrow(a: Term, b: Term) -> Term {
    pi("_", a, b)
}

// Gather free variables
pub fn fv(t: &Term) -> HashSet<String> {
    match t {
        Term::Sort(_) | Term::Const(_) => HashSet::new(),
        Term::Var(x) => HashSet::from([x.clone()]),
        Term::App(f, a) => {
            let mut s = fv(f);
            s.extend(fv(a));
            s
        }
        Term::Pi(x, a, b) | Term::Lam(x, a, b) => {
            let mut s = fv(a);
            let mut body = fv(b);
            body.remove(x);
            s.extend(body);
            s
        }
    }
}

// Gather all names (bound and free)
pub fn all_names(t: &Term) -> HashSet<String> {
    match t {
        Term::Sort(_) | Term::Const(_) => HashSet::new(),
        Term::Var(x) => HashSet::from([x.clone()]),
        Term::App(f, a) => {
            let mut s = all_names(f);
            s.extend(all_names(a));
            s
        }
        Term::Pi(x, a, b) | Term::Lam(x, a, b) => {
            let mut s = all_names(a);
            s.extend(all_names(b));
            s.insert(x.clone());
            s
        }
    }
}

// Generate a fresh variable name based on a hint, avoiding names in the given set
pub fn fresh(hint: &str, avoid: &HashSet<String>) -> String {
    let mut s = hint.to_string();
    while avoid.contains(&s) {
        s.push('\'');
    }
    s
}

// Substitute a term for a variable in another term, avoiding capture
pub fn subst(t: &Term, x: &str, replacement: &Term) -> Term {
    match t {
        Term::Sort(_) | Term::Const(_) => t.clone(),
        Term::Var(y) => {
            if y == x {
                replacement.clone()
            } else {
                t.clone()
            }
        }
        Term::App(f, a) => app(subst(f, x, replacement), subst(a, x, replacement)),
        Term::Pi(y, a, b) | Term::Lam(y, a, b) => {
            let na = subst(a, x, replacement);
            let (ny, nb) = if y == x || !fv(b).contains(x) {
                (y.clone(), (**b).clone())
            } else if !fv(replacement).contains(y) {
                (y.clone(), subst(b, x, replacement))
            } else {
                let mut avoid = all_names(b);
                avoid.extend(all_names(a));
                avoid.extend(all_names(replacement));
                avoid.insert(x.to_string());
                let z = fresh(y, &avoid);
                let renamed = subst(b, y, &var(&z));
                (z, subst(&renamed, x, replacement))
            };
            if matches!(t, Term::Pi(..)) {
                Term::Pi(ny, Box::new(na), Box::new(nb))
            } else {
                Term::Lam(ny, Box::new(na), Box::new(nb))
            }
        }
    }
}

pub fn subst_many(t: &Term, replacements: &HashMap<String, Term>) -> Term {
    // Simultaneous capture-avoiding substitution. Do not let a replacement's
    // free variables be substituted by later replacements.
    let mut used = all_names(t);
    let mut keys: Vec<&String> = replacements.keys().collect();
    keys.sort();
    for (name, value) in replacements {
        used.insert(name.clone());
        used.extend(all_names(value));
    }
    let mut staged = t.clone();
    let mut placeholders = vec![];
    for key in keys {
        let temp = fresh("__subst", &used);
        used.insert(temp.clone());
        staged = subst(&staged, key, &var(&temp));
        placeholders.push((temp, replacements[key].clone()));
    }
    for (temp, value) in placeholders {
        staged = subst(&staged, &temp, &value);
    }
    staged
}

// Check if two terms are alpha-equivalent (equal up to renaming of bound variables)
pub fn alpha(a: &Term, b: &Term) -> bool {
    fn pos(stack: &[String], x: &str) -> Option<usize> {
        stack.iter().rev().position(|s| s == x)
    }
    fn go(a: &Term, b: &Term, ea: &mut Vec<String>, eb: &mut Vec<String>) -> bool {
        match (a, b) {
            (Term::Sort(x), Term::Sort(y)) => x == y,
            (Term::Const(x), Term::Const(y)) => x == y,
            (Term::Var(x), Term::Var(y)) => match (pos(ea, x), pos(eb, y)) {
                (Some(i), Some(j)) => i == j,
                (None, None) => x == y,
                _ => false,
            },
            (Term::App(f, a), Term::App(g, b)) => go(f, g, ea, eb) && go(a, b, ea, eb),
            (Term::Pi(x, a, b), Term::Pi(y, c, d)) | (Term::Lam(x, a, b), Term::Lam(y, c, d)) => {
                if !go(a, c, ea, eb) {
                    return false;
                }
                ea.push(x.clone());
                eb.push(y.clone());
                let ok = go(b, d, ea, eb);
                ea.pop();
                eb.pop();
                ok
            }
            _ => false,
        }
    }
    go(a, b, &mut vec![], &mut vec![])
}

// Decompose a term into its head and spine (list of arguments)
// For example, the term `f a b` would be decomposed into `(f, [a, b])`.
pub fn spine(t: &Term) -> (Term, Vec<Term>) {
    match t {
        Term::App(f, a) => {
            let (h, mut xs) = spine(f);
            xs.push((**a).clone());
            (h, xs)
        }
        _ => (t.clone(), vec![]),
    }
}

pub fn occurs_const(t: &Term, name: &str) -> bool {
    match t {
        Term::Const(n) => n == name,
        Term::App(f, a) => occurs_const(f, name) || occurs_const(a, name),
        Term::Pi(_, a, b) | Term::Lam(_, a, b) => occurs_const(a, name) || occurs_const(b, name),
        _ => false,
    }
}
