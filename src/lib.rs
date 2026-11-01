use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Sort(u64),
    Var(String),
    Pi(String, Box<Term>, Box<Term>),
    Lam(String, Box<Term>, Box<Term>),
    App(Box<Term>, Box<Term>),
    Const(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decl { pub ty: Term, pub kind: DeclKind }

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeclKind {
    Axiom,
    Def { body: Term },
    Inductive { nparams: usize, nindices: usize, ctors: Vec<String> },
    Ctor { nparams: usize, nfield: usize, induct: String },
    Rec { induct: String, major_idx: usize, rules: Vec<RecRule> }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecRule { pub ctor: String, pub nfield: usize, pub rhs: Term }

pub type Context = Vec<(String, Term)>;
pub type Env = HashMap<String, Decl>;

pub fn infer(env: &Env, gamma: &Context, t: &Term) -> Result<Term, ()> {
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
            if let Ok(u) = infer_sort(env, gamma, a) {
                let (x_p, b_p) = fresh_from_context(gamma, x, b);
                let mut new_gamma = gamma.clone();
                new_gamma.push((x_p.clone(), *a.clone()));
                if let Ok(v) = infer_sort(env, &new_gamma, &b_p) {
                    let level = if v == 0 { 0 } else { u.max(v) };
                    return Ok(Term::Sort(level));
                }
            }
            Err(())
        }
        Term::Lam(x, a, s) => {
            if let Ok(_) = infer_sort(env, gamma, a) {
                let (x_p, s_p) = fresh_from_context(gamma, x, s);
                let mut new_gamma = gamma.clone();
                new_gamma.push((x_p.clone(), *a.clone()));
                if let Ok(b) = infer(env, &new_gamma, &s_p) {
                    return Ok(Term::Pi(x_p.clone(), a.clone(), Box::new(b)));
                }
            }
            Err(())
        }
        Term::App(f, a) => {
            if let Ok(f_p) = infer(env, gamma, f) {
                let t = normalize(env, &f_p);
                if let Term::Pi(x, a_cap, b) = t {
                    if let Ok(true) = check(env, gamma, a, &a_cap) {
                        return Ok(substitute(&b, &x, &a));
                    }
                }
            }
            Err(())
        }
        Term::Const(_) => todo!(),
    }
}

pub fn check(env: &Env, gamma: &Context, t: &Term, t_cap: &Term) -> Result<bool, ()> {
    if let Ok(t_cap_p) = infer(env, gamma, t) {
        Ok(alpha(&normalize(env, t_cap), &normalize(env, &t_cap_p)))
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

pub fn alpha(a: &Term, b: &Term) -> bool {
    alpha_with_binders(a, b, &vec![], &vec![])
}

pub fn alpha_with_binders(a: &Term, b: &Term, e_a: &Context, e_b: &Context) -> bool {
    match (a, b) {
        (Term::Sort(u), Term::Sort(v)) => u == v, // alpha-Sort
        (Term::Var(x), Term::Var(y)) => {
            let i = get_pos_in_context(e_a, x);
            let j = get_pos_in_context(e_b, y);
            match (i, j) {
                (Some(i), Some(j)) => i == j, // alpha-Bound
                (None, None) => x == y,       // alpha-Free
                _ => false,
            }
        }
        (Term::Pi(x, a_1, b_1), Term::Pi(y, a_2, b_2))
        | (Term::Lam(x, a_1, b_1), Term::Lam(y, a_2, b_2)) => {
            if !alpha_with_binders(a_1, a_2, e_a, e_b) {
                return false;
            }
            let mut e_a_prime = e_a.clone();
            let mut e_b_prime = e_b.clone();
            e_a_prime.push((x.clone(), Term::Sort(0)));
            e_b_prime.push((y.clone(), Term::Sort(0)));
            alpha_with_binders(b_1, b_2, &e_a_prime, &e_b_prime) // alpha-Pi
        }
        (Term::App(a_1, b_1), Term::App(a_2, b_2)) => {
            alpha_with_binders(a_1, a_2, e_a, e_b) && alpha_with_binders(b_1, b_2, e_a, e_b) // alpha-App
        }
        (Term::Const(s_1), Term::Const(s_2)) => s_1 == s_2,
        _ => false,
    }
}

pub fn infer_sort(env: &Env, gamma: &Context, t: &Term) -> Result<u64, ()> {
    match infer(env, gamma, t) {
        Ok(s) => match normalize(env, &s) {
            Term::Sort(u) => Ok(u),
            _ => Err(()),
        },
        Err(_) => Err(()),
    }
}

/// Free varuables
pub fn fv(t: &Term) -> HashSet<String> {
    match t {
        Term::Sort(_) | Term::Const(_) => HashSet::new(),
        Term::Var(x) => HashSet::from([x.clone()]),
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

/// Free variables and bound variable names.
pub fn all_names(t: &Term) -> HashSet<String> {
    match t {
        Term::Sort(_) | Term::Const(_) => HashSet::new(),
        Term::Var(x) => HashSet::from([x.clone()]),
        Term::App(f, a) => {
            let mut names = all_names(f);
            names.extend(all_names(a));
            names
        }
        Term::Pi(x, a, b) | Term::Lam(x, a, b) => {
            let mut names = all_names(a);
            names.extend(all_names(b));
            names.insert(x.clone());
            names
        }
    }
}

/// Choose a fresh name, avoiding both free and bound names.
fn fresh_name(
    preferred: &str,
    avoid: &HashSet<String>,
) -> String {
    let mut name = preferred.to_string();
    while avoid.contains(&name) {
        name.push('\'');
    }
    name
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

/// Capture-avoiding substitution: t[x := s].
pub fn substitute(t: &Term, x: &String, s: &Term) -> Term {
    match t {
        Term::Sort(_) | Term::Const(_) => t.clone(),

        Term::Var(y) => {
            if y == x { s.clone() } else { t.clone() }
        }

        Term::App(f, a) => Term::App(
            Box::new(substitute(f, x, s)),
            Box::new(substitute(a, x, s)),
        ),

        Term::Pi(y, a, b) | Term::Lam(y, a, b) => {
            // The binder does not scope over its annotation.
            let new_a = substitute(a, x, s);

            let (new_y, new_b) = if y == x {
                // x is shadowed in the body.
                (y.clone(), (**b).clone())
            } else if !fv(b).contains(x) {
                // No occurrence to substitute in the body.
                (y.clone(), (**b).clone())
            } else if !fv(s).contains(y) {
                // Substitution cannot capture any variable.
                (y.clone(), substitute(b, x, s))
            } else {
                // Rename y before substituting x.
                let mut avoid = all_names(b);
                avoid.extend(all_names(a));
                avoid.extend(all_names(s));
                avoid.insert(x.clone());

                let z = fresh_name(y, &avoid);

                // Rename occurrences bound by this binder.
                let renamed = substitute(
                    b,
                    y,
                    &Term::Var(z.clone()),
                );

                (z, substitute(&renamed, x, s))
            };

            match t {
                Term::Pi(..) => Term::Pi(
                    new_y,
                    Box::new(new_a),
                    Box::new(new_b),
                ),
                Term::Lam(..) => Term::Lam(
                    new_y,
                    Box::new(new_a),
                    Box::new(new_b),
                ),
                _ => unreachable!(),
            }
        }
    }
}

// convert `t = h a1 ... an` to `(h, [a1, ..., an])` 
fn unfold_app(t: &Term) -> (Term, Vec<Term>) {
    match t {
        Term::App(f, a) => {
            let (h, mut args) = unfold_app(f);
            args.push(*a.clone());
            (h, args)
        }
        _ => (t.clone(), vec![])
    }
}

fn mk_app(h: &Term, args: &[Term]) -> Term {
    let mut t = h.clone();
    for a in args {
        t = Term::App(Box::new(t), Box::new(a.clone()));
    }
    t
}

pub fn whnf(env: &Env, t: &Term) -> Term {
    let mut t = t.clone();
    loop {
        let (h, args) = unfold_app(&t);
        match &h {
            // β: 先頭が λ で、引数が1つ以上ある
            Term::Lam(x, _, body) if !args.is_empty() => {
                t = mk_app(&substitute(body, x, &args[0]), &args[1..]);
            }
            Term::Const(c) => match env.get(c).map(|d| &d.kind) {
                // δ: 本体を持つ定数は、本体に展開する（引数はそのまま後ろに付ける）
                Some(DeclKind::Def { body }) => {
                    t = mk_app(&body, &args);
                }
                // ι: 再帰子で、主引数まで引数がそろっている
                Some(DeclKind::Rec { major_idx, rules, .. }) if args.len() > *major_idx => {
                    let (k, kargs) = unfold_app(&whnf(env, &args[*major_idx]));
                    // k がコンストラクタで、それに対応する rule があれば
                    //   fields = kargs[nparams..]（先頭のパラメータを飛ばす）
                    //   t = rhs に args[..major_idx] と fields を順に適用し、
                    //       残りの引数 args[major_idx+1..] も続けて適用したもの
                    // なければ return t（主引数が変数などで止まっている）
                    todo!()
                }
                _ => return t, // Axiom, Inductive, Ctor, 引数が足りない Rec
            },
            _ => return t, // Var, Sort, Pi, 引数のない Lam
        }
    }
}

/* 
// weak head norm form
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
}*/

pub fn normalize(env: &Env, t: &Term) -> Term {
    match whnf(env, t) {
        Term::Pi(x, a, b) => Term::Pi(x, Box::new(normalize(env, &a)), Box::new(normalize(env, &b))),
        Term::Lam(x, a, b) => Term::Lam(x, Box::new(normalize(env, &a)), Box::new(normalize(env, &b))),
        Term::App(f, a) => Term::App(Box::new(normalize(env, &f)), Box::new(normalize(env, &a))),
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
        alpha_with_binders(a, b, &empty(), &empty())
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
        assert_eq!(whnf(&HashMap::new(), &reducible), v("z"));
        assert_eq!(
            whnf(&HashMap::new(), &lam("y", sort(0), reducible.clone())),
            lam("y", sort(0), reducible.clone())
        );
        assert_eq!(
            whnf(&HashMap::new(), &app(v("f"), reducible.clone())),
            app(v("f"), reducible)
        );
    }
    #[test]
    fn whnf_multi_application() {
        let t = app(
            app(lam("x", sort(0), lam("y", sort(0), v("x"))), v("a")),
            v("b"),
        );
        assert_eq!(whnf(&HashMap::new(), &t), v("a"));
    }
    #[test]
    fn normalize_reduces_beneath_binders_and_arguments() {
        let inner = app(lam("x", sort(0), v("x")), v("a"));
        assert_eq!(
            normalize(&HashMap::new(), &lam("z", sort(0), inner.clone())),
            lam("z", sort(0), v("a"))
        );
        assert_eq!(normalize(&HashMap::new(), &app(v("f"), inner.clone())), app(v("f"), v("a")));
        assert_eq!(
            normalize(&HashMap::new(), &pi("x", inner.clone(), inner)),
            pi("x", v("a"), v("a"))
        );
    }
    #[test]
    fn normalization_idempotent() {
        let t = lam("x", sort(0), app(lam("y", sort(0), v("y")), v("x")));
        assert_eq!(normalize(&HashMap::new(), &normalize(&HashMap::new(), &t)), normalize(&HashMap::new(), &t));
    }
    #[test]
    fn infer_sort_and_variable() {
        assert_eq!(infer(&HashMap::new(), &empty(), &sort(0)), Ok(sort(1)));
        assert_eq!(infer_sort(&HashMap::new(), &empty(), &sort(0)), Ok(1));
        assert!(infer(&HashMap::new(), &empty(), &v("x")).is_err());
        let gamma = vec![("P".into(), sort(0))];
        assert_eq!(infer(&HashMap::new(), &gamma, &v("P")), Ok(sort(0)));
        assert!(infer_sort(&HashMap::new(), &gamma, &lam("x", v("P"), v("x"))).is_err());
    }
    #[test]
    fn infer_identity_proof_and_check() {
        assert_equiv(infer(&HashMap::new(), &empty(), &id_prop()).unwrap(), id_prop_type());
        assert_eq!(check(&HashMap::new(), &empty(), &id_prop(), &id_prop_type()), Ok(true));
        assert_eq!(check(&HashMap::new(), &empty(), &id_prop(), &sort(0)), Ok(false));
    }
    #[test]
    fn infer_pi_and_lam() {
        let gamma = vec![("P".into(), sort(0))];
        assert_eq!(infer(&HashMap::new(), &gamma, &pi("x", v("P"), v("P"))), Ok(sort(0)));
        assert_equiv(
            infer(&HashMap::new(), &gamma, &lam("x", v("P"), v("x"))).unwrap(),
            pi("x", v("P"), v("P")),
        );
        assert_eq!(infer(&HashMap::new(), &empty(), &pi("x", sort(0), sort(0))), Ok(sort(1)));
    }

    #[test]
    fn infer_application_and_reject_wrong_argument() {
        let gamma = vec![("P".into(), sort(0)), ("p".into(), v("P"))];
        let identity = lam("x", v("P"), v("x"));
        assert_eq!(infer(&HashMap::new(), &gamma, &app(identity.clone(), v("p"))), Ok(v("P")));
        assert!(infer(&HashMap::new(), &gamma, &app(identity, v("P"))).is_err());
        assert!(infer(&HashMap::new(), &gamma, &app(v("p"), v("p"))).is_err());
    }

    #[test]
    fn check_uses_beta_conversion() {
        let gamma = vec![("P".into(), sort(0)), ("p".into(), v("P"))];
        let id_type = app(lam("X", sort(0), v("X")), v("P"));
        assert_eq!(check(&HashMap::new(), &gamma, &v("p"), &id_type), Ok(true));
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
        assert!(infer(&HashMap::new(), &empty(), &lam("x", v("Unknown"), v("x"))).is_err());
    }

    // Regression tests: these express intended semantics and may fail until the kernel is fixed.
    #[test]
    fn regression_pi_impredicativity() {
        let proposition_for_all_propositions = pi("P", sort(0), v("P"));
        assert_eq!(
            infer(&HashMap::new(), &empty(), &proposition_for_all_propositions),
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
        assert_equiv(infer(&HashMap::new(), &empty(), &t).unwrap(), expected);
    }

    #[test]
    fn substitution_no_unnecessary_renaming() {
        let t = lam("y", sort(0), v("y"));
        let result = substitute(&t, &"x".into(), &v("y"));

        assert_eq!(result, t);
    }

    #[test]
    fn substitution_avoids_inner_binder_capture() {
        // [x := y] (λy. λy'. x)
        let t = lam(
            "y",
            sort(0),
            lam("y'", sort(0), v("x")),
        );

        let result = substitute(&t, &"x".into(), &v("y"));

        assert_equiv(
            result,
            lam("z", sort(0),
                lam("w", sort(0), v("y"))),
        );
    }

    #[test]
    fn substitution_preserves_shadowing() {
        // [x := z] (λx : x. x)
        let t = lam("x", v("x"), v("x"));
        let result = substitute(&t, &"x".into(), &v("z"));

        assert_eq!(result, lam("x", v("z"), v("x")));
    }

    #[test]
    fn substitution_renames_only_when_needed() {
        // [x := y] (λy. x)
        let t = lam("y", sort(0), v("x"));
        let result = substitute(&t, &"x".into(), &v("y"));

        assert_equiv(result, lam("z", sort(0), v("y")));
    }

}
