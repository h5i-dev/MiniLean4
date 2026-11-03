//! Tests for inductive declarations: acceptance, strict positivity,
//! universe checks, generated recursor types, and iota-reduction.

use crate::{
    declaration::{ConstructorSpec, InductiveSpec},
    kernel::Kernel,
    term::{app, apps, arrow, const_term, lam, pi, var, Term, Term::Sort},
};

fn nat() -> Term {
    const_term("Nat")
}
fn zero() -> Term {
    const_term("Nat.zero")
}
fn succ(n: Term) -> Term {
    app(const_term("Nat.succ"), n)
}
fn numeral(n: usize) -> Term {
    (0..n).fold(zero(), |t, _| succ(t))
}

fn add_tree(k: &mut Kernel) {
    // inductive Tree where
    // | leaf : Tree
    // | node : Tree -> Tree
    // | branch : Tree -> Tree -> Tree
    k.add_inductive(InductiveSpec {
        name: "Tree".into(),
        params: vec![],
        indices: vec![],
        universe_level: 1,
        constructors: vec![
            ConstructorSpec {
                name: "Tree.leaf".into(),
                fields: vec![],
                result_indices: vec![],
            },
            ConstructorSpec {
                name: "Tree.node".into(),
                fields: vec![("child".into(), const_term("Tree"))],
                result_indices: vec![],
            },
            ConstructorSpec {
                name: "Tree.branch".into(),
                fields: vec![
                    ("left".into(), const_term("Tree")),
                    ("right".into(), const_term("Tree")),
                ],
                result_indices: vec![],
            },
        ],
    })
    .unwrap();
}

fn leaf() -> Term {
    const_term("Tree.leaf")
}
fn node(child: Term) -> Term {
    app(const_term("Tree.node"), child)
}
fn branch(left: Term, right: Term) -> Term {
    apps(const_term("Tree.branch"), [left, right])
}

fn add_list(k: &mut Kernel) {
    // inductive List (A : Type) where
    // | nil : List A
    // | cons : A -> List A -> List A
    k.add_inductive(InductiveSpec {
        name: "List".into(),
        params: vec![("A".into(), Term::Sort(1))],
        indices: vec![],
        universe_level: 1,
        constructors: vec![
            ConstructorSpec {
                name: "List.nil".into(),
                fields: vec![],
                result_indices: vec![],
            },
            ConstructorSpec {
                name: "List.cons".into(),
                fields: vec![
                    ("head".into(), var("A")),
                    ("tail".into(), app(const_term("List"), var("A"))),
                ],
                result_indices: vec![],
            },
        ],
    })
    .unwrap();
}

fn list_nat() -> Term {
    app(const_term("List"), nat())
}
fn nil() -> Term {
    app(const_term("List.nil"), nat())
}
fn cons(head: Term, tail: Term) -> Term {
    apps(const_term("List.cons"), [nat(), head, tail])
}

// Nat addition, defined only using the existing Nat.rec1:
// add(x, y) = Nat.rec1 (fun _ => Nat) y (fun _ ih => succ ih) x
fn add(x: Term, y: Term) -> Term {
    apps(
        const_term("Nat.rec1"),
        [
            lam("_n", nat(), nat()),
            y,
            lam("_n", nat(), lam("ih", nat(), succ(var("ih")))),
            x,
        ],
    )
}

// count(Tree): leaf=1, node(child)=1+count(child),
// branch(l,r)=1+count(l)+count(r).
fn tree_size(t: Term) -> Term {
    let tree = const_term("Tree");
    let motive = lam("t", tree.clone(), nat());
    let on_leaf = numeral(1);
    let on_node = lam("child", tree.clone(), lam("ih", nat(), succ(var("ih"))));
    let on_branch = lam(
        "left",
        tree.clone(),
        lam(
            "right",
            tree,
            lam(
                "ih_left",
                nat(),
                lam(
                    "ih_right",
                    nat(),
                    succ(add(var("ih_left"), var("ih_right"))),
                ),
            ),
        ),
    );
    apps(const_term("Tree.rec1"), [motive, on_leaf, on_node, on_branch, t])
}

// length(List Nat): nil=0, cons(head, tail)=1+length(tail).
fn list_length(xs: Term) -> Term {
    let list = list_nat();
    let motive = lam("xs", list.clone(), nat());
    let on_nil = zero();
    let on_cons = lam(
        "head",
        nat(),
        lam("tail", list, lam("ih", nat(), succ(var("ih")))),
    );
    apps(const_term("List.rec1"), [nat(), motive, on_nil, on_cons, xs])
}

#[test]
fn tree_constructors_have_expected_types() {
    let mut k = Kernel::standard();
    add_tree(&mut k);
    let tree = const_term("Tree");
    assert!(k
        .is_def_eq(k.type_of_const("Tree.leaf").unwrap(), &tree)
        .unwrap());
}

#[test]
fn generic_list_recursor_reduces() {
    let mut k = Kernel::standard();
    k.add_inductive(InductiveSpec {
        name: "List".into(),
        params: vec![("A".into(), Sort(1))],
        indices: vec![],
        universe_level: 1,
        constructors: vec![
            ConstructorSpec {
                name: "List.nil".into(),
                fields: vec![],
                result_indices: vec![],
            },
            ConstructorSpec {
                name: "List.cons".into(),
                fields: vec![
                    ("head".into(), var("A")),
                    ("tail".into(), app(const_term("List"), var("A"))),
                ],
                result_indices: vec![],
            },
        ],
    })
    .unwrap();
    let nat = const_term("Nat");
    let list_nat = app(const_term("List"), nat.clone());
    let nil = app(const_term("List.nil"), nat.clone());
    let singleton = apps(
        const_term("List.cons"),
        [nat.clone(), const_term("Nat.zero"), nil.clone()],
    );
    k.check(&vec![], &singleton, &list_nat).unwrap();
    let motive = lam("xs", list_nat.clone(), nat.clone());
    let succ = lam(
        "head",
        nat.clone(),
        lam(
            "tail",
            list_nat.clone(),
            lam("ih", nat.clone(), app(const_term("Nat.succ"), var("ih"))),
        ),
    );
    let count = apps(
        const_term("List.rec1"),
        [nat, motive, const_term("Nat.zero"), succ, singleton],
    );
    assert!(k
        .is_def_eq(&count, &app(const_term("Nat.succ"), const_term("Nat.zero")))
        .unwrap());
}

#[test]
fn arbitrary_recursor_levels() {
    let mut k = Kernel::standard();
    k.register_recursor("Nat", 4).unwrap();
    k.register_recursor("Eq", 5).unwrap();
    assert!(k.type_of_const("Nat.rec4").is_some());
    assert!(k.type_of_const("Eq.rec5").is_some());
}

#[test]
fn reject_constructor_universe_overflow() {
    let mut k = Kernel::standard();
    let bad = InductiveSpec {
        name: "TooLarge".into(),
        params: vec![],
        indices: vec![],
        universe_level: 1,
        constructors: vec![ConstructorSpec {
            name: "TooLarge.mk".into(),
            fields: vec![("x".into(), Sort(1))],
            result_indices: vec![],
        }],
    };
    assert!(k.add_inductive(bad).is_err());
}

#[test]
fn proposition_elimination_policy() {
    let mut k = Kernel::standard();
    k.add_inductive(InductiveSpec {
        name: "Either".into(),
        params: vec![("P".into(), Sort(0)), ("Q".into(), Sort(0))],
        indices: vec![],
        universe_level: 0,
        constructors: vec![
            ConstructorSpec {
                name: "Either.left".into(),
                fields: vec![("p".into(), var("P"))],
                result_indices: vec![],
            },
            ConstructorSpec {
                name: "Either.right".into(),
                fields: vec![("q".into(), var("Q"))],
                result_indices: vec![],
            },
        ],
    })
    .unwrap();
    assert!(k.register_recursor("Either", 3).is_err());
    k.add_inductive(InductiveSpec {
        name: "Both".into(),
        params: vec![("P".into(), Sort(0)), ("Q".into(), Sort(0))],
        indices: vec![],
        universe_level: 0,
        constructors: vec![ConstructorSpec {
            name: "Both.mk".into(),
            fields: vec![("p".into(), var("P")), ("q".into(), var("Q"))],
            result_indices: vec![],
        }],
    })
    .unwrap();
    k.register_recursor("Both", 3).unwrap();
}

fn simple_spec(name: &str, fields: Vec<(&str, Term)>) -> InductiveSpec {
    InductiveSpec {
        name: name.into(),
        params: vec![],
        indices: vec![],
        universe_level: 1,
        constructors: vec![ConstructorSpec {
            name: format!("{name}.mk"),
            fields: fields.into_iter().map(|(n, t)| (n.into(), t)).collect(),
            result_indices: vec![],
        }],
    }
}

#[test]
fn tree_recursor_computes_size() {
    let mut k = Kernel::standard();
    add_tree(&mut k);
    // branch(node(leaf), leaf) has 4 nodes.
    let t = branch(node(leaf()), leaf());
    k.check(&vec![], &tree_size(t.clone()), &nat()).unwrap();
    assert!(k.is_def_eq(&tree_size(t), &numeral(4)).unwrap());
}

#[test]
fn list_recursor_computes_length() {
    let mut k = Kernel::standard();
    add_list(&mut k);
    let xs = cons(zero(), cons(numeral(1), nil()));
    k.check(&vec![], &xs, &list_nat()).unwrap();
    assert!(k.is_def_eq(&list_length(xs), &numeral(2)).unwrap());
}

#[test]
fn list_recursor_type_matches_text() {
    // List.rec_v : Pi (A : Sort 1). Pi (M : List A -> Sort v).
    //   M (nil A) -> (Pi (a : A). Pi (as : List A). M as -> M (cons A a as)) ->
    //   Pi (x : List A). M x
    let mut k = Kernel::standard();
    add_list(&mut k);
    let list_a = app(const_term("List"), var("A"));
    let expected = pi(
        "A",
        Sort(1),
        pi(
            "M",
            arrow(list_a.clone(), Sort(1)),
            arrow(
                app(var("M"), app(const_term("List.nil"), var("A"))),
                arrow(
                    pi(
                        "a",
                        var("A"),
                        pi(
                            "as",
                            list_a.clone(),
                            arrow(
                                app(var("M"), var("as")),
                                app(
                                    var("M"),
                                    apps(const_term("List.cons"), [var("A"), var("a"), var("as")]),
                                ),
                            ),
                        ),
                    ),
                    pi("x", list_a, app(var("M"), var("x"))),
                ),
            ),
        ),
    );
    assert!(k
        .is_def_eq(k.type_of_const("List.rec1").unwrap(), &expected)
        .unwrap());
}

#[test]
fn function_valued_recursive_field_reduces() {
    // inductive Ord where | zero : Ord | lim : (Nat -> Ord) -> Ord
    let mut k = Kernel::standard();
    k.add_inductive(InductiveSpec {
        name: "Ord".into(),
        params: vec![],
        indices: vec![],
        universe_level: 1,
        constructors: vec![
            ConstructorSpec {
                name: "Ord.zero".into(),
                fields: vec![],
                result_indices: vec![],
            },
            ConstructorSpec {
                name: "Ord.lim".into(),
                fields: vec![("f".into(), arrow(nat(), const_term("Ord")))],
                result_indices: vec![],
            },
        ],
    })
    .unwrap();
    let info = k.inductive("Ord").unwrap();
    let lim = &info.constructors[1];
    assert_eq!(lim.recursive_fields.len(), 1);
    assert_eq!(lim.recursive_fields[0].argument_binders.len(), 1);
    // rec (lim (fun n. zero)) with the lim case returning succ (ih 0).
    let t = apps(
        const_term("Ord.rec1"),
        [
            lam("o", const_term("Ord"), nat()),
            zero(),
            lam(
                "f",
                arrow(nat(), const_term("Ord")),
                lam("ih", arrow(nat(), nat()), succ(app(var("ih"), zero()))),
            ),
            app(const_term("Ord.lim"), lam("n", nat(), const_term("Ord.zero"))),
        ],
    );
    k.check(&vec![], &t, &nat()).unwrap();
    assert!(k.is_def_eq(&t, &numeral(1)).unwrap());
}

#[test]
fn rejects_non_positive_fields_and_rolls_back() {
    let mut k = Kernel::standard();
    let bad = |name: &str, field: Term| simple_spec(name, vec![("x", field)]);
    // Negative occurrence: (Bad -> Nat).
    let negative = bad("Bad", arrow(const_term("Bad"), nat()));
    // Nested negative occurrence: ((Bad2 -> Nat) -> Bad2).
    let nested = bad(
        "Bad2",
        arrow(arrow(const_term("Bad2"), nat()), const_term("Bad2")),
    );
    for spec in [negative, nested] {
        let name = spec.name.clone();
        assert!(k.add_inductive(spec).is_err());
        assert!(k.type_of_const(&name).is_none());
        assert!(k.inductive(&name).is_none());
    }
}

#[test]
fn rejects_non_uniform_parameter_and_index_occurrence() {
    let mut k = Kernel::standard();
    // Parameter must appear unchanged: Box A has a field Box Nat.
    let non_uniform = InductiveSpec {
        name: "Box".into(),
        params: vec![("A".into(), Sort(1))],
        indices: vec![],
        universe_level: 1,
        constructors: vec![ConstructorSpec {
            name: "Box.mk".into(),
            fields: vec![("x".into(), app(const_term("Box"), nat()))],
            result_indices: vec![],
        }],
    };
    assert!(k.add_inductive(non_uniform).is_err());
    // I must not occur in a result index.
    let in_index = InductiveSpec {
        name: "Idx".into(),
        params: vec![],
        indices: vec![("i".into(), nat())],
        universe_level: 1,
        constructors: vec![ConstructorSpec {
            name: "Idx.mk".into(),
            fields: vec![],
            result_indices: vec![app(const_term("Idx"), zero())],
        }],
    };
    assert!(k.add_inductive(in_index).is_err());
}

#[test]
fn eq_recursor_eliminates_into_every_universe() {
    let mut k = Kernel::standard();
    assert!(k.inductive("Eq").unwrap().large_elimination);
    k.register_recursor("Eq", 3).unwrap();
    assert!(k.type_of_const("Eq.rec3").is_some());
}
