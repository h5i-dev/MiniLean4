/*
(x : A) ∈ Γ（most recently added one）
───────────────────────────────────── Var
Γ ⊢ x : A

───────────────────────── Sort
Γ ⊢ Sort u : Sort (u+1)

Γ ⊢ A : Sort u     Γ, x:A ⊢ B : Sort v
────────────────────────────────────── Pi
Γ ⊢ Π(x:A). B : Sort (max u v)

Γ ⊢ A : Sort u     Γ, x:A ⊢ t : B
────────────────────────────────── Lam
Γ ⊢ λ(x:A). t : Π(x:A). B
*/

#[derive(Clone, Debug, PartialEq, Eq)]
enum Term {
    Sort(u64),
    Var(String),
    Pi(String, Box<Term>, Box<Term>),
    Lam(String, Box<Term>, Box<Term>),
}

type Context = Vec<(String, Term)>;

pub fn infer(gamma: &Context, t: &Term) -> Result<Term, ()> {
    match t {
        Term::Sort(u) => Ok(Term::Sort(u + 1)),
        Term::Var(x) => {
            for (y, a) in gamma.iter().rev() {
                if y == x {
                    return Ok(a.clone());
                }
            }
            Err(())
        },
        Term::Pi(x, a, b) => {
            if let Ok(u) = ensure_sort(gamma, a) {
                let mut new_gamma = gamma.clone();
                new_gamma.push((x.clone(), *a.clone()));
                if let Ok(v) = ensure_sort(gamma, b) {
                    return Ok(Term::Sort(std::cmp::max(u, v)));
                }
            }
            Err(())
        },
        Term::Lam(x, a, b) => {
            if let Ok(_) = ensure_sort(gamma, a) {
                let mut new_gamma = gamma.clone();
                new_gamma.push((x.clone(), *a.clone()));
                return Ok(Term::Pi(x.clone(), a.clone(), b.clone()));
            }
            Err(())
        },
    }
}

pub fn ensure_sort(gamma: &Context, t: &Term) -> Result<u64, ()> {
    match infer(gamma, t) {
        Ok(s) => match s {
            Term::Sort(u) => Ok(u),
            _ => Err(())
        },
        Err(_) => Err(()),
    }
}

pub fn get_pos_in_context(gamma: &Context, var_name: &String) -> Option<usize> {
    for (i, (s, _, )) in gamma.into_iter().rev().enumerate() {
        if s == var_name {
            return Some(i);
        }
    }
    
    None
} 

pub fn alpha(a: &Term, b: &Term, gamma_a: &Context, gamma_b: &Context) -> bool {
    match (a, b) {
        (Term::Sort(u), Term::Sort(v)) => u == v,
        (Term::Var(x), Term::Var(y)) => {
            let i = get_pos_in_context(gamma_a, x);
            let j = get_pos_in_context(gamma_b, y);
            match (i, j) {
                (Some(i), Some(j)) => i == j,
                (None, None) => x == y,
                _ => false
            }
        },
        (Term::Pi(x, a_1, b_1), Term::Pi(y, a_2, b_2)) => {
            if !alpha(a_1, a_2, gamma_a, gamma_b) {
                return false;
            }
            return alpha(b_1, b_2, gamma_a, gamma_b);
        },
        (Term::Lam(x, a_1, a_2), Term::Lam(y, b_1, b_2)) => {
            if !alpha(a_1, a_2, gamma_a, gamma_b) {
                return false;
            }
            return alpha(b_1, b_2, gamma_a, gamma_b);
        },
        _ => false
    }
}