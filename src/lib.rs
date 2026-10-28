use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Sort(u64),
    Var(String),
    Pi(String, Box<Term>, Box<Term>),
    Lam(String, Box<Term>, Box<Term>),
    App(Box<Term>, Box<Term>),
}

pub type Context = Vec<(String, Term)>;

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
        }
        Term::Pi(x, a, b) => {
            if let Ok(u) = infer_sort(gamma, a) {
                let (x_p, b_p) = fresh_from_context(gamma, x, b);
                let mut new_gamma = gamma.clone();
                new_gamma.push((x_p.clone(), *a.clone()));
                if let Ok(v) = infer_sort(&new_gamma, &b_p) {
                    let level = if v == 0 { 0 } else { u.max(v) };
                    return Ok(Term::Sort(level));
                }
            }
            Err(())
        }
        Term::Lam(x, a, s) => {
            if let Ok(_) = infer_sort(gamma, a) {
                let (x_p, s_p) = fresh_from_context(gamma, x, s);
                let mut new_gamma = gamma.clone();
                new_gamma.push((x_p.clone(), *a.clone()));
                if let Ok(b) = infer(&new_gamma, &s_p) {
                    return Ok(Term::Pi(x_p.clone(), a.clone(), Box::new(b)));
                }
            }
            Err(())
        }
        Term::App(f, a) => {
            if let Ok(f_p) = infer(gamma, f) {
                let t = normalize(&f_p);
                if let Term::Pi(x, a_cap, b) = t {
                    if let Ok(true) = check(gamma, a, &a_cap) {
                        return Ok(substitute(&b, &x, &a));
                    }
                }
            }
            Err(())
        }
    }
}

pub fn check(gamma: &Context, t: &Term, t_cap: &Term) -> Result<bool, ()> {
    if let Ok(t_cap_p) = infer(gamma, t) {
        Ok(alpha(&normalize(t_cap), &normalize(&t_cap_p), gamma, gamma))
    } else {
        Err(())
    }
}

pub fn get_pos_in_context(gamma: &Context, var_name: &String) -> Option<usize> {
    for (i, (s, _)) in gamma.into_iter().rev().enumerate() {
        if s == var_name {
            return Some(i);
        }
    }

    None
}

pub fn alpha(a: &Term, b: &Term, gamma_a: &Context, gamma_b: &Context) -> bool {
    match (a, b) {
        (Term::Sort(u), Term::Sort(v)) => u == v, // alpha-Sort
        (Term::Var(x), Term::Var(y)) => {
            let i = get_pos_in_context(gamma_a, x);
            let j = get_pos_in_context(gamma_b, y);
            match (i, j) {
                (Some(i), Some(j)) => i == j, // alpha-Bound
                (None, None) => x == y,       // alpha-Free
                _ => false,
            }
        }
        (Term::Pi(x, a_1, b_1), Term::Pi(y, a_2, b_2))
        | (Term::Lam(x, a_1, b_1), Term::Lam(y, a_2, b_2)) => {
            if !alpha(a_1, a_2, gamma_a, gamma_b) {
                return false;
            }
            let mut gamma_a_prime = gamma_a.clone();
            let mut gamma_b_prime = gamma_b.clone();
            gamma_a_prime.push((x.clone(), Term::Sort(0)));
            gamma_b_prime.push((y.clone(), Term::Sort(0)));
            alpha(b_1, b_2, &gamma_a_prime, &gamma_b_prime) // alpha-Pi
        }
        (Term::App(a_1, b_1), Term::App(a_2, b_2)) => {
            alpha(a_1, a_2, gamma_a, gamma_b) && alpha(b_1, b_2, gamma_a, gamma_b) // alpha-App
        }
        _ => false,
    }
}

pub fn infer_sort(gamma: &Context, t: &Term) -> Result<u64, ()> {
    match infer(gamma, t) {
        Ok(s) => match normalize(&s) {
            Term::Sort(u) => Ok(u),
            _ => Err(()),
        },
        Err(_) => Err(()),
    }
}

pub fn fv(t: &Term) -> HashSet<String> {
    match t {
        Term::Sort(_) => HashSet::new(),
        Term::Var(x) => vec![x.clone()].into_iter().collect::<HashSet<String>>(),
        Term::App(t_1, t_2) => {
            let mut fv_1 = fv(t_1);
            fv_1.extend(fv(t_2));
            fv_1
        }
        Term::Pi(x, a, b) | Term::Lam(x, a, b) => {
            let mut result = fv(a);
            let mut body_fv = fv(b);
            body_fv.remove(x);
            result.extend(body_fv);
            result
        }
    }
}

pub fn fresh(s: &Term, b: &Term, x: &String, y: &String) -> String {
    let mut fv_s = fv(s);
    fv_s.extend(fv(b));
    fv_s.extend([x.clone()].into_iter());
    let mut z = y.clone();
    while fv_s.contains(&z) {
        z = z + "'";
    }
    z
}

pub fn fresh_from_context(gamma: &Context, x: &String, b: &Term) -> (String, Term) {
    let mut var_name_set: HashSet<String> = gamma.into_iter().map(|(n, _)| n.clone()).collect();
    if var_name_set.contains(x) {
        var_name_set.extend(fv(b));
        let mut x_p = x.clone();
        while var_name_set.contains(&x_p) {
            x_p = x_p + "'";
        }

        (x_p.clone(), substitute(b, x, &Term::Var(x_p)))
    } else {
        (x.clone(), b.clone())
    }
}

pub fn substitute(t: &Term, x: &String, s: &Term) -> Term {
    match t {
        Term::Var(y) => {
            if y == x {
                s.clone()
            } else {
                Term::Var(y.clone())
            }
        }
        Term::Sort(y) => Term::Sort(*y),
        Term::App(t_1, t_2) => Term::App(
            Box::new(substitute(t_1, x, s)),
            Box::new(substitute(t_2, x, s)),
        ),
        Term::Pi(y, a, b) => {
            if y == x {
                Term::Pi(x.clone(), Box::new(substitute(a, x, s)), b.clone())
            } else {
                if !fv(s).contains(y) {
                    Term::Pi(
                        y.clone(),
                        Box::new(substitute(a, x, s)),
                        Box::new(substitute(b, x, s)),
                    )
                } else {
                    let z = fresh(s, b, x, y);
                    Term::Pi(
                        z.clone(),
                        Box::new(substitute(a, x, s)),
                        Box::new(substitute(&substitute(b, y, &Term::Var(z)), x, s)),
                    )
                }
            }
        }
        Term::Lam(y, a, b) => {
            if y == x {
                Term::Lam(x.clone(), Box::new(substitute(a, x, s)), b.clone())
            } else {
                if !fv(s).contains(y) {
                    Term::Lam(
                        y.clone(),
                        Box::new(substitute(a, x, s)),
                        Box::new(substitute(b, x, s)),
                    )
                } else {
                    let z = fresh(s, b, x, y);
                    Term::Lam(
                        z.clone(),
                        Box::new(substitute(a, x, s)),
                        Box::new(substitute(&substitute(b, y, &Term::Var(z)), x, s)),
                    )
                }
            }
        }
    }
}

pub fn whnf(t: &Term) -> Term {
    match t {
        Term::App(f, a) => {
            let f = whnf(f); // 関数側（spine の左）を先に whnf
            match f {
                Term::Lam(x, _, body) => whnf(&substitute(&body, &x, a)), // β して続ける
                _ => Term::App(Box::new(f), a.clone()), // 先頭が λ でなければ止まる
            }
        }
        _ => t.clone(), // Sort, Var, Pi, Lam はそのまま（weak なので中に入らない）
    }
}

pub fn normalize(t: &Term) -> Term {
    match whnf(t) {
        Term::Pi(x, a, b) => Term::Pi(x, Box::new(normalize(&a)), Box::new(normalize(&b))),
        Term::Lam(x, a, b) => Term::Lam(x, Box::new(normalize(&a)), Box::new(normalize(&b))),
        Term::App(f, a) => Term::App(Box::new(normalize(&f)), Box::new(normalize(&a))),
        other => other, // Sort, Var
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    fn v(x: &str) -> Term {
        Term::Var(x.into())
    }

    fn sort(u: u64) -> Term {
        Term::Sort(u)
    }

    fn pi(x: &str, a: Term, b: Term) -> Term {
        Term::Pi(x.into(), Box::new(a), Box::new(b))
    }

    fn lam(x: &str, a: Term, b: Term) -> Term {
        Term::Lam(x.into(), Box::new(a), Box::new(b))
    }

    fn app(f: Term, a: Term) -> Term {
        Term::App(Box::new(f), Box::new(a))
    }

    fn empty() -> Context {
        vec![]
    }

    fn equiv(a: &Term, b: &Term) -> bool {
        alpha(a, b, &empty(), &empty())
    }

    fn assert_equiv(a: Term, b: Term) {
        assert!(equiv(&a, &b), "not alpha-equal:\n{a:#?}\n{b:#?}");
    }

    fn id_prop() -> Term {
        lam("P", sort(0), lam("p", v("P"), v("p")))
    }

    fn id_prop_type() -> Term {
        pi("P", sort(0), pi("p", v("P"), v("P")))
    }

    #[test]
    fn alpha_sort_and_shape() {
        assert!(equiv(&sort(0), &sort(0)));
        assert!(!equiv(&sort(0), &sort(1)));
        assert!(!equiv(&v("x"), &sort(0)));
        assert!(!equiv(
            &lam("x", sort(0), v("x")),
            &pi("x", sort(0), v("x"))
        ));
    }

    #[test]
    fn alpha_free_vars_are_names() {
        assert!(equiv(&v("x"), &v("x")));
        assert!(!equiv(&v("x"), &v("y")));
    }

    #[test]
    fn alpha_rename_lambdas_and_pis() {
        assert_equiv(lam("x", sort(0), v("x")), lam("y", sort(0), v("y")));
        assert_equiv(pi("x", sort(0), v("x")), pi("y", sort(0), v("y")));
        assert_equiv(
            lam("x", sort(0), lam("y", sort(0), v("x"))),
            lam("a", sort(0), lam("b", sort(0), v("a"))),
        );
        assert!(!equiv(
            &lam("x", sort(0), lam("y", sort(0), v("x"))),
            &lam("a", sort(0), lam("b", sort(0), v("b")))
        ));
    }

    #[test]
    fn alpha_shadowing() {
        assert_equiv(
            lam("x", sort(0), lam("x", sort(0), v("x"))),
            lam("a", sort(0), lam("b", sort(0), v("b"))),
        );
        assert!(!equiv(
            &lam("x", sort(0), lam("x", sort(0), v("x"))),
            &lam("a", sort(0), lam("b", sort(0), v("a")))
        ));
    }

    #[test]
    fn alpha_binder_annotation_out_of_scope() {
        assert_equiv(lam("x", v("x"), v("x")), lam("y", v("x"), v("y")));
        assert!(!equiv(&lam("x", v("x"), v("x")), &lam("y", v("y"), v("y"))));
    }

    #[test]
    fn alpha_application() {
        assert_equiv(
            lam("x", sort(0), app(v("f"), v("x"))),
            lam("y", sort(0), app(v("f"), v("y"))),
        );
        assert!(!equiv(&app(v("f"), v("x")), &app(v("g"), v("x"))));
    }

    #[test]
    fn alpha_position_in_context() {
        let a = vec![
            ("x".into(), sort(0)),
            ("y".into(), sort(0)),
            ("x".into(), sort(0)),
        ];
        assert_eq!(get_pos_in_context(&a, &"x".into()), Some(0));
        assert_eq!(get_pos_in_context(&a, &"y".into()), Some(1));
        assert_eq!(get_pos_in_context(&a, &"missing".into()), None);
    }

    #[test]
    fn fv_includes_binder_annotations() {
        let f = fv(&pi("x", v("x"), app(v("x"), v("y"))));
        assert_eq!(f, HashSet::from(["x".to_owned(), "y".to_owned()]));
        assert!(fv(&lam("x", sort(0), v("x"))).is_empty());
        assert_eq!(fv(&app(v("x"), v("x"))), HashSet::from(["x".to_owned()]));
        assert!(fv(&sort(0)).is_empty());
    }

    #[test]
    fn substitution_variables_and_application() {
        assert_eq!(substitute(&v("x"), &"x".into(), &v("y")), v("y"));
        assert_eq!(substitute(&v("z"), &"x".into(), &v("y")), v("z"));
        assert_eq!(substitute(&sort(2), &"x".into(), &v("y")), sort(2));
        assert_eq!(
            substitute(&app(v("x"), v("z")), &"x".into(), &v("y")),
            app(v("y"), v("z"))
        );
    }

    #[test]
    fn substitution_shadowing_preserves_body_but_updates_annotation() {
        let t = lam("x", v("x"), app(v("x"), v("y")));
        assert_eq!(
            substitute(&t, &"x".into(), &v("z")),
            lam("x", v("z"), app(v("x"), v("y")))
        );
        let p = pi("x", v("x"), v("x"));
        assert_eq!(
            substitute(&p, &"x".into(), &v("z")),
            pi("x", v("z"), v("x"))
        );
    }

    #[test]
    fn substitution_capture_avoiding_lam_and_pi() {
        let l = substitute(&lam("y", sort(0), v("x")), &"x".into(), &v("y"));
        assert_equiv(l, lam("z", sort(0), v("y")));
        let p = substitute(&pi("y", sort(0), v("x")), &"x".into(), &v("y"));
        assert_equiv(p, pi("z", sort(0), v("y")));
    }
    #[test]
    fn substitution_non_capture() {
        assert_eq!(
            substitute(&lam("y", sort(0), v("x")), &"x".into(), &v("z")),
            lam("y", sort(0), v("z"))
        );
    }
    #[test]
    fn substitution_avoids_multiple_names() {
        let t = lam("y", sort(0), app(v("x"), v("y'")));
        let got = substitute(&t, &"x".into(), &v("y"));
        assert_equiv(got, lam("fresh", sort(0), app(v("y"), v("y'"))));
    }
    #[test]
    fn whnf_reduces_only_head() {
        let reducible = app(lam("x", sort(0), v("x")), v("z"));
        assert_eq!(whnf(&reducible), v("z"));
        assert_eq!(
            whnf(&lam("y", sort(0), reducible.clone())),
            lam("y", sort(0), reducible.clone())
        );
        assert_eq!(
            whnf(&app(v("f"), reducible.clone())),
            app(v("f"), reducible)
        );
    }
    #[test]
    fn whnf_multi_application() {
        let t = app(
            app(lam("x", sort(0), lam("y", sort(0), v("x"))), v("a")),
            v("b"),
        );
        assert_eq!(whnf(&t), v("a"));
    }
    #[test]
    fn normalize_reduces_beneath_binders_and_arguments() {
        let inner = app(lam("x", sort(0), v("x")), v("a"));
        assert_eq!(
            normalize(&lam("z", sort(0), inner.clone())),
            lam("z", sort(0), v("a"))
        );
        assert_eq!(normalize(&app(v("f"), inner.clone())), app(v("f"), v("a")));
        assert_eq!(
            normalize(&pi("x", inner.clone(), inner)),
            pi("x", v("a"), v("a"))
        );
    }
    #[test]
    fn normalization_idempotent() {
        let t = lam("x", sort(0), app(lam("y", sort(0), v("y")), v("x")));
        assert_eq!(normalize(&normalize(&t)), normalize(&t));
    }
    #[test]
    fn infer_sort_and_variable() {
        assert_eq!(infer(&empty(), &sort(0)), Ok(sort(1)));
        assert_eq!(infer_sort(&empty(), &sort(0)), Ok(1));
        assert!(infer(&empty(), &v("x")).is_err());
        let gamma = vec![("P".into(), sort(0))];
        assert_eq!(infer(&gamma, &v("P")), Ok(sort(0)));
        assert!(infer_sort(&gamma, &lam("x", v("P"), v("x"))).is_err());
    }
    #[test]
    fn infer_identity_proof_and_check() {
        assert_equiv(infer(&empty(), &id_prop()).unwrap(), id_prop_type());
        assert_eq!(check(&empty(), &id_prop(), &id_prop_type()), Ok(true));
        assert_eq!(check(&empty(), &id_prop(), &sort(0)), Ok(false));
    }
    #[test]
    fn infer_pi_and_lam() {
        let gamma = vec![("P".into(), sort(0))];
        assert_eq!(infer(&gamma, &pi("x", v("P"), v("P"))), Ok(sort(0)));
        assert_equiv(
            infer(&gamma, &lam("x", v("P"), v("x"))).unwrap(),
            pi("x", v("P"), v("P")),
        );
        assert_eq!(infer(&empty(), &pi("x", sort(0), sort(0))), Ok(sort(1)));
    }

    #[test]
    fn infer_application_and_reject_wrong_argument() {
        let gamma = vec![("P".into(), sort(0)), ("p".into(), v("P"))];
        let identity = lam("x", v("P"), v("x"));
        assert_eq!(infer(&gamma, &app(identity.clone(), v("p"))), Ok(v("P")));
        assert!(infer(&gamma, &app(identity, v("P"))).is_err());
        assert!(infer(&gamma, &app(v("p"), v("p"))).is_err());
    }

    #[test]
    fn check_uses_beta_conversion() {
        let gamma = vec![("P".into(), sort(0)), ("p".into(), v("P"))];
        let id_type = app(lam("X", sort(0), v("X")), v("P"));
        assert_eq!(check(&gamma, &v("p"), &id_type), Ok(true));
    }

    #[test]
    fn fresh_from_context_avoids_collision() {
        let gamma = vec![("x".into(), sort(0)), ("x'".into(), sort(0))];
        let (name, body) = fresh_from_context(&gamma, &"x".into(), &v("x"));
        assert_eq!(name, "x''");
        assert_eq!(body, v("x''"));
    }

    #[test]
    fn infer_rejects_unbound_annotation() {
        assert!(infer(&empty(), &lam("x", v("Unknown"), v("x"))).is_err());
    }

    // Regression tests: these express intended semantics and may fail until the kernel is fixed.
    #[test]
    fn regression_pi_impredicativity() {
        let proposition_for_all_propositions = pi("P", sort(0), v("P"));
        assert_eq!(
            infer(&empty(), &proposition_for_all_propositions),
            Ok(sort(0))
        );
    }

    /* 
    #[test]
    fn regression_substitution_no_unnecessary_renaming() {
        let t = lam("y", sort(0), v("y"));
        let result = substitute(&t, &"x".into(), &v("y"));
        assert_eq!(result, t);
    }
    */

    #[test]
    fn regression_fresh_avoid_bound_capture() {
        let t = lam("y", sort(0), lam("y'", sort(0), v("x")));
        let result = substitute(&t, &"x".into(), &v("y"));
        assert_equiv(result, lam("z", sort(0), lam("w", sort(0), v("y"))));
    }

    #[test]
    fn regression_context_name_capture() {
        let t = lam("x", sort(0), lam("y", v("x"), lam("x", sort(0), v("y"))));
        let expected = pi("x", sort(0), pi("y", v("x"), pi("z", sort(0), v("x"))));
        assert_equiv(infer(&empty(), &t).unwrap(), expected);
    }
}
