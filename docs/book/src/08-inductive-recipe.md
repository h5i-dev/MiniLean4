<div class="lead" markdown="1">

Chapter 7 built the recursor for the natural numbers by hand. In Lean, a user never does that: they write an `inductive` declaration, and the kernel checks it and generates the type former, the constructors, the recursor, and its computation rules. This chapter develops that procedure in three steps, from more constructors to parameters to indices, and then states it in general. The kernel's own code for it is about five hundred lines.

</div>

## More constructors: trees

$\Nat$ has two constructors, and only one of them has a recursive argument. Consider a type with three:

```lean
inductive Tree where
  | leaf   : Tree
  | node   : Tree -> Tree
  | branch : Tree -> Tree -> Tree
```

For example, $\mathsf{branch}\;(\mathsf{node}\;\mathsf{leaf})\;\mathsf{leaf}$ is a tree built from four constructors. To build $M\;t$ for every tree $t$, where $M : \mathsf{Tree} \to \Sort{v}$, the recipe of Chapter 7 asks for one case per constructor, and each argument of type $\mathsf{Tree}$ contributes one induction hypothesis:

$$
\begin{array}{lcl}
m_{\mathsf{leaf}} &:& M\;\mathsf{leaf} \\[2pt]
m_{\mathsf{node}} &:& \tPi{t}{\mathsf{Tree}}{M\;t \to M\;(\mathsf{node}\;t)} \\[2pt]
m_{\mathsf{branch}} &:& \tPi{l}{\mathsf{Tree}}{\tPi{r}{\mathsf{Tree}}{M\;l \to M\;r \to M\;(\mathsf{branch}\;l\;r)}}
\end{array}
$$

The recursor takes the motive, the three cases, and a tree:

$$
\mathsf{Tree.rec}_v : \tPi{M}{\mathsf{Tree} \to \Sort{v}}{\;
  M\;\mathsf{leaf} \to (\cdots_{\mathsf{node}}) \to (\cdots_{\mathsf{branch}}) \to \tPi{t}{\mathsf{Tree}}{M\;t}},
$$

where the dots stand for the types of $m_{\mathsf{node}}$ and $m_{\mathsf{branch}}$. Compared with $\NatRec{v}$, only the number of cases and the number of hypotheses per case have changed. Writing $R$ for the partial application $\mathsf{Tree.rec}_v\;M\;m_{\mathsf{leaf}}\;m_{\mathsf{node}}\;m_{\mathsf{branch}}$, the iota-rules are

$$
\begin{array}{rcl}
R\;\mathsf{leaf} &\iotared& m_{\mathsf{leaf}} \\[2pt]
R\;(\mathsf{node}\;t) &\iotared& m_{\mathsf{node}}\;t\;(R\;t) \\[2pt]
R\;(\mathsf{branch}\;l\;r) &\iotared& m_{\mathsf{branch}}\;l\;r\;(R\;l)\;(R\;r).
\end{array}
$$

Each rule selects the case for the constructor at the head of the major premise, and fills each hypothesis with a recursive call on the corresponding subtree. For example, with $M = \tLam{\_}{\mathsf{Tree}}{\Nat}$ and the cases

$$
m_{\mathsf{leaf}} = 1, \qquad
m_{\mathsf{node}} = \tLam{t}{\mathsf{Tree}}{\tLam{i}{\Nat}{1 + i}}, \qquad
m_{\mathsf{branch}} = \tLam{l}{\mathsf{Tree}}{\tLam{r}{\mathsf{Tree}}{\tLam{i}{\Nat}{\tLam{j}{\Nat}{1 + i + j}}}},
$$

$R$ counts the constructors of a tree:

$$
R\;(\mathsf{branch}\;(\mathsf{node}\;\mathsf{leaf})\;\mathsf{leaf})
\to 1 + R\;(\mathsf{node}\;\mathsf{leaf}) + R\;\mathsf{leaf}
\to 1 + (1 + R\;\mathsf{leaf}) + 1
\to 1 + (1 + 1) + 1 = 4.
$$

With $M$ a predicate ($v = 0$), the same recursor is structural induction on trees. In general, a type with $n$ constructors gets a recursor with $n$ minor premises $m_1, \ldots, m_n$, and the kernel needs no code specific to the type: it only needs to know, for each constructor, which case to pick and which arguments to recurse on.

Here is that tree as the kernel sees it. Each box is a constructor application; the recursive fields hang below it, and the line at the bottom of each box is the recursor case that handles it, with $(R\;l)$ and $(R\;r)$ the induction hypotheses computed by recursive calls. Type another tree to see its cases.

<div class="explorer" data-kind="ctree" data-term="Tree.branch (Tree.node Tree.leaf) Tree.leaf"><pre class="prelude">inductive Tree : Sort 1 where
  | leaf
  | node (t : Tree)
  | branch (l : Tree) (r : Tree)</pre></div>

<div class="playground" data-file="tree-count"><pre>inductive Tree : Sort 1 where
  | leaf
  | node (t : Tree)
  | branch (l : Tree) (r : Tree)

def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n
def one : Nat := Nat.succ Nat.zero
def four : Nat := Nat.succ (Nat.succ (Nat.succ one))

# The minor premise for branch takes l, r, then the two induction hypotheses.
def count : Tree -> Nat := fun (t : Tree) => Tree.rec1 (fun (_t : Tree) => Nat) one (fun (t : Tree) => fun (i : Nat) => Nat.succ i) (fun (l : Tree) => fun (r : Tree) => fun (i : Nat) => fun (j : Nat) => Nat.succ (add i j)) t

goal Eq Nat (count (Tree.branch (Tree.node Tree.leaf) Tree.leaf)) four
rfl
qed</pre></div>

## Parameters: lists

A list of numbers is either empty or a number in front of a list of numbers, so we could declare a type $\mathsf{ListNat}$ with constructors $\mathsf{nil}$ and $\mathsf{cons} : \Nat \to \mathsf{ListNat} \to \mathsf{ListNat}$. But then lists of trees would need another declaration, $\mathsf{ListTree}$, with the same constructors and a separate recursor, and so on for every element type. It is better to make the element type an argument of the type itself:

```lean
inductive List (A : Sort 1) where
  | nil  : List A
  | cons : A -> List A -> List A
```

Now $\mathsf{List}\;\Nat$ and $\mathsf{List}\;\mathsf{Tree}$ are two instances of one declaration. The declaration adds

$$
\mathsf{List} : \Sort{1} \to \Sort{1}, \qquad
\mathsf{nil} : \tPi{A}{\Sort{1}}{\mathsf{List}\;A}, \qquad
\mathsf{cons} : \tPi{A}{\Sort{1}}{A \to \mathsf{List}\;A \to \mathsf{List}\;A}.
$$

The constructors take $A$ as an explicit first argument. For example, the one-element list $[5]$ is $\mathsf{cons}\;\Nat\;5\;(\mathsf{nil}\;\Nat)$. Within one list, $A$ never changes: the tail of $\mathsf{cons}\;A\;a\;\mathit{as}$ is again a $\mathsf{List}\;A$. An argument of the type that stays the same in every constructor and every recursive argument is called a **parameter**. Because it never changes, the recursor can take it once, before the motive, and treat it as fixed:

$$
\begin{array}{l}
\mathsf{List.rec}_v : \tPi{A}{\Sort{1}}{\tPi{M}{\mathsf{List}\;A \to \Sort{v}}{\;M\;(\mathsf{nil}\;A) \to {}}} \\[2pt]
\qquad (\tPi{a}{A}{\tPi{\mathit{as}}{\mathsf{List}\;A}{M\;\mathit{as} \to M\;(\mathsf{cons}\;A\;a\;\mathit{as})}}) \to \tPi{x}{\mathsf{List}\;A}{M\;x} \\[8pt]
\mathsf{List.rec}_v\;A\;M\;m_1\;m_2\;(\mathsf{nil}\;A') \;\iotared\; m_1 \\[2pt]
\mathsf{List.rec}_v\;A\;M\;m_1\;m_2\;(\mathsf{cons}\;A'\;a\;\mathit{as}) \;\iotared\; m_2\;a\;\mathit{as}\;(\mathsf{List.rec}_v\;A\;M\;m_1\;m_2\;\mathit{as})
\end{array}
$$

Apart from the leading $A$, this is the recipe of Chapter 7 once more: $\mathsf{cons}$ has two arguments, of which only $\mathit{as}$ is recursive, so its case gets one induction hypothesis. The rules ignore the parameter $A'$ stored in the constructor; in a well-typed term it is convertible to $A$. For example, the length of a list is

$$
\mathit{length} \mathrel{:=} \tLam{A}{\Sort{1}}{\tLam{x}{\mathsf{List}\;A}{
\mathsf{List.rec}_1\;A\;(\tLam{\_}{\mathsf{List}\;A}{\Nat})\;\zero\;(\tLam{a}{A}{\tLam{\mathit{as}}{\mathsf{List}\;A}{\tLam{r}{\Nat}{\suc\;r}}})\;x}}.
$$

A list value carries the parameter $A$ in every constructor, which the tree below shows next to each box: the parameter is repeated, the fields differ.

<div class="explorer" data-kind="ctree" data-term="List.cons Nat (Nat.succ Nat.zero) (List.cons Nat Nat.zero (List.nil Nat))"><pre class="prelude">inductive List (A : Sort 1) : Sort 1 where
  | nil
  | cons (head : A) (tail : List A)</pre></div>

<div class="playground" data-file="examples/generic-list.leanmini"><pre>inductive List (A : Sort 1) : Sort 1 where
  | nil
  | cons (head : A) (tail : List A)

def length : forall (A : Sort 1), List A -> Nat := fun (A : Sort 1) => fun (xs : List A) => List.rec1 A (fun (_xs : List A) => Nat) Nat.zero (fun (head : A) => fun (tail : List A) => fun (r : Nat) => Nat.succ r) xs

# length [0, 0] = 2
goal Eq Nat (length Nat (List.cons Nat Nat.zero (List.cons Nat Nat.zero (List.nil Nat)))) (Nat.succ (Nat.succ Nat.zero))
rfl
qed</pre></div>

## Indices: vectors

A $\mathsf{List}\;\Nat$ may have any length. What if we want the length to be part of the type, so that $\mathsf{Vec}\;\Nat\;0$ and $\mathsf{Vec}\;\Nat\;2$ are different types?

```lean
inductive Vec (A : Sort 1) : Nat -> Sort 1 where
  | vnil  : Vec A 0
  | vcons : (n : Nat) -> A -> Vec A n -> Vec A (succ n)
```

The element type $A$ is still a parameter. The length is not: $\mathsf{vnil}$ has length $0$, and $\mathsf{vcons}$ takes a vector of length $n$ and returns one of length $\suc\;n$. An argument of the type that may differ between constructors, and between a constructor and its recursive arguments, is called an **index**. The constructors are

$$
\mathsf{vnil} : \tPi{A}{\Sort{1}}{\mathsf{Vec}\;A\;\zero}, \qquad
\mathsf{vcons} : \tPi{A}{\Sort{1}}{\tPi{n}{\Nat}{A \to \mathsf{Vec}\;A\;n \to \mathsf{Vec}\;A\;(\suc\;n)}}.
$$

Because an index varies, the recursor cannot fix it in advance. Instead, the motive takes it as an argument, $M : \tPi{n}{\Nat}{\mathsf{Vec}\;A\;n \to \Sort{v}}$, and the case for $\mathsf{vcons}$ is

$$
\tPi{n}{\Nat}{\tPi{a}{A}{\tPi{\mathit{xs}}{\mathsf{Vec}\;A\;n}{M\;n\;\mathit{xs} \to M\;(\suc\;n)\;(\mathsf{vcons}\;A\;n\;a\;\mathit{xs})}}}.
$$

The induction hypothesis is about a vector of length $n$, read off the type $\mathsf{Vec}\;A\;n$ of the recursive argument, and the conclusion is about one of length $\suc\;n$, read off the result type of the constructor. The script `examples/generic-vec.leanmini` ([Appendix E](e-leanmini-reference.md)) declares this type and checks a small term that uses it.

## The general recipe

This section states the procedure for a single inductive type with parameters and indices. Mutual and nested inductive types, which Lean also supports, are out of scope.

The procedure also answers a question that T-Const leaves open. A constant without a body is an assumption: T-Const would accept $c : \tPi{P}{\Sort{0}}{P}$ just as readily as $\zero : \Nat$, and with it the system would be inconsistent. The constants generated below are not arbitrary assumptions. They are instances of a fixed schema, the inductive types of the Calculus of Inductive Constructions, whose consistency is known [Werner 1994].

**Telescopes.** We write $(\vec{x} : \vec{A})$ for a sequence of bindings $(x_1 : A_1) \cdots (x_k : A_k)$ in which each $A_i$ may mention $x_1, \ldots, x_{i-1}$; $\tPi{\vec{x}}{\vec{A}}{B}$ for $\tPi{x_1}{A_1}{\cdots\,\tPi{x_k}{A_k}{B}}$; and $f\;\vec{x}$ for $f\;x_1 \cdots x_k$. The length of $\vec{x}$ is $|\vec{x}|$. In the code, a telescope is a `Context`, and `telescope(binders, tail)` in `src/term.rs` builds the nested $\Pi$.

**Declarations.** A declaration introduces a type former $I$ and constructors $c_1, \ldots, c_n$:

$$
\begin{array}{rcll}
I &:& \tPi{\vec{p}}{\vec{P}}{\tPi{\vec{\imath}}{\vec{J}}{\Sort{u}}} & \\[2pt]
c_j &:& \tPi{\vec{p}}{\vec{P}}{\tPi{\vec{a}}{\vec{A}_j}{I\;\vec{p}\;\vec{t}_j}} & (j = 1, \ldots, n)
\end{array}
$$

The **parameters** $\vec{p}$ are shared by all constructors and appear unchanged in every result type. The **indices** $\vec{\imath}$ may differ between constructors: the index terms $\vec{t}_j$ may mention $\vec{p}$ and the constructor's own arguments $\vec{a}$, which are called its **fields**. For the examples so far, with the leading $\Pi$ over the parameters omitted from the constructor types:

| Type former | Parameters | Indices | Constructors |
|---|---|---|---|
| $\Nat : \Sort{1}$ | none | none | $\zero : \Nat$, $\;\suc : \Nat \to \Nat$ |
| $\mathsf{Tree} : \Sort{1}$ | none | none | $\mathsf{leaf}$, $\mathsf{node}$, $\mathsf{branch}$ |
| $\mathsf{List} : \Sort{1} \to \Sort{1}$ | $(A : \Sort{1})$ | none | $\mathsf{nil} : \mathsf{List}\;A$, $\;\mathsf{cons} : A \to \mathsf{List}\;A \to \mathsf{List}\;A$ |
| $\mathsf{Vec} : \Sort{1} \to \Nat \to \Sort{1}$ | $(A : \Sort{1})$ | $(n : \Nat)$ | $\mathsf{vnil} : \mathsf{Vec}\;A\;\zero$, $\;\mathsf{vcons} : \tPi{n}{\Nat}{A \to \mathsf{Vec}\;A\;n \to \mathsf{Vec}\;A\;(\suc\;n)}$ |

**Acceptance.** The kernel accepts a declaration only if the following four conditions hold.

1. The type of $I$ is a type in the current signature.
2. With $I$ added to the signature, each constructor type is a type, and it ends in $I\;\vec{p}\;\vec{t}_j$, where $\vec{p}$ are exactly the parameters in order and $I$ does not occur in $\vec{t}_j$.
3. **Strict positivity.** Each field type either does not mention $I$, or has the form $\tPi{\vec{y}}{\vec{B}}{I\;\vec{p}\;\vec{s}}$ where $I$ occurs neither in $\vec{B}$ nor in $\vec{s}$. A field of the second form is **recursive**.
4. **Universes.** If $u \ge 1$, each field type lies in some $\Sort{w}$ with $w \le u$. If $u = 0$, there is no condition.

Condition 2 lets the recursor treat the parameters uniformly. Condition 3 rules out declarations such as

```lean
inductive Bad where
  | mk : (Bad -> False) -> Bad
```

whose field mentions `Bad` to the left of an arrow. Case analysis on `Bad` would let one define $f : \mathsf{Bad} \to \mathsf{False}$ by $f\;(\mathsf{mk}\;g) = g\;(\mathsf{mk}\;g)$. Then $f\;(\mathsf{mk}\;f)$ is a closed term of type $\mathsf{False}$, and it reduces to itself, so it has no normal form. For a type $\mathsf{Tree}$ under declaration, some field types and their status are:

| Field type | Status | Reason |
|---|---|---|
| $\Nat$ | accepted, not recursive | does not mention $\mathsf{Tree}$ |
| $\mathsf{Tree}$ | accepted, recursive | induction hypothesis $M\;a_k$ |
| $\Nat \to \mathsf{Tree}$ | accepted, recursive | produces trees; hypothesis $\tPi{n}{\Nat}{M\;(a_k\;n)}$ |
| $\mathsf{Tree} \to \Nat$ | rejected | $\mathsf{Tree}$ to the left of an arrow |
| $\mathsf{List}\;\mathsf{Tree}$ | rejected here | nested occurrence; Lean accepts it, but it is out of scope |

A field of type $\Nat \to \mathsf{Tree}$ is a tree with infinitely many children, one for each number; the recursor can still recurse into each child $a_k\;n$. A field of type $\mathsf{Tree} \to \Nat$ *consumes* trees instead of containing them, and it is the shape that makes `Bad` paradoxical.

Condition 4 prevents a type from containing a larger universe. Without it, a declaration $T : \Sort{1}$ with a constructor $\mathsf{mk} : \Sort{1} \to T$ would place a copy of all of $\Sort{1}$ inside $\Sort{1}$, which is the self-containment that [Chapter 13](13-universes.md) shows to be inconsistent. For $u = 0$ no condition is needed, because $\Sort{0}$ is impredicative.

**The recursor.** For an accepted declaration, the kernel generates a recursor $I.\mathsf{rec}_v$ for each admissible level $v$ (see below):

$$
I.\mathsf{rec}_v :
\tPi{\vec{p}}{\vec{P}}{\;
\tPi{M}{(\tPi{\vec{\imath}}{\vec{J}}{I\;\vec{p}\;\vec{\imath} \to \Sort{v}})}{\;
\tPi{m_1}{C_1}{\cdots\,\tPi{m_n}{C_n}{\;
\tPi{\vec{\imath}}{\vec{J}}{\tPi{x}{I\;\vec{p}\;\vec{\imath}}{M\;\vec{\imath}\;x}}}}}}.
$$

The parameters come first and stay fixed, as for lists; the motive takes the indices and the element, as for vectors. The minor premise $C_j$ asks for the case of constructor $c_j$: given its fields and an induction hypothesis for each recursive field, build $M$ for $c_j$ applied to those fields:

$$
\begin{array}{l}
C_j = \tPi{\vec{a}}{\vec{A}_j}{\;\tPi{\vec{h}}{\vec{H}_j}{\;M\;\vec{t}_j\;(c_j\;\vec{p}\;\vec{a})}}, \\[4pt]
H_{j,k} = \tPi{\vec{y}}{\vec{B}}{M\;\vec{s}\;(a_k\;\vec{y})}
\quad\text{for each recursive field } a_k : \tPi{\vec{y}}{\vec{B}}{I\;\vec{p}\;\vec{s}}.
\end{array}
$$

The final arguments are the indices and the element $x$ itself, the major premise.

**The rules.** For each constructor, the kernel generates one iota-rule, which applies the minor premise to the fields and to the induction hypotheses, computed by recursive calls:

$$
I.\mathsf{rec}_v\;\vec{p}\;M\;\vec{m}\;\vec{\imath}\;(c_j\;\vec{p}\,'\;\vec{a}) \;\iotared\; m_j\;\vec{a}\;\vec{h},
\qquad
h_k = \tLam{\vec{y}}{\vec{B}}{I.\mathsf{rec}_v\;\vec{p}\;M\;\vec{m}\;\vec{s}\;(a_k\;\vec{y})}.
$$

The major premise is at position $|\vec{p}| + 1 + n + |\vec{\imath}|$ (counting from zero), the constructor has $|\vec{p}|$ parameters and $|\vec{a}|$ fields, and in a well-typed redex $\vec{p}\,'$ is convertible to $\vec{p}$, so the rule ignores it, as the rules for lists ignore $A'$. For $\Nat$, $\mathsf{Tree}$, $\mathsf{List}$, and $\mathsf{Vec}$ the procedure produces exactly the recursors and rules of this chapter and the last, and the recursor types agree with the ones Lean 4 generates, up to the names of bound variables and implicit arguments.

**Eliminating from propositions.** If $u \ge 1$, the recursor is generated for every level $v$. If $u = 0$, so that $I$ is a proposition, the recursor is generated only for $v = 0$, unless $I$ is a **subsingleton**: it has at most one constructor, and each field either is a proof (its type lies in $\Sort{0}$) or occurs among the index terms $\vec{t}_j$. The restriction keeps data from depending on *which* proof of a proposition was given. For example, $P \vee Q$ has two constructors, so a function from proofs of $P \vee Q$ into $\Nat$ could return $0$ for one and $1$ for the other, and a proof would carry computational information. Lean's `Or.rec` and `Exists.rec` therefore eliminate only into `Prop`, while `And.rec` and `Eq.rec` eliminate into every universe: `And` has one constructor whose fields are proofs, and `Eq` ([Chapter 9](09-equality.md)) has one constructor with no fields.

So the kernel's rules stay fixed while the signature grows: one generic procedure turns each declaration into signature entries, and a single reduction function runs their rules ([Chapter 12](12-reduction-conversion.md#computation-rules-as-data)).

## In the code

<aside class="code" markdown="1">

The procedure lives in `src/inductive/`. The input is an `InductiveSpec` (`src/declaration.rs`): the name, the parameter and index telescopes, the universe level $u$, and one `ConstructorSpec` per constructor giving its fields and its index terms $\vec{t}_j$. The script parser builds this from an `inductive` block.

- `Kernel::add_inductive` in `src/inductive/mod.rs` runs the four acceptance conditions in order (`check_inductive_type` is condition 1, `check_constructor_fields` checks that fields are types and enforces condition 4, `check_constructor_result` is condition 2) and, if all pass, registers the type former and constructors and records an `InductiveInfo`. On failure the signature is left unchanged.
- `src/inductive/positivity.rs` is condition 3. `check_recursive_field` peels the leading $\Pi$s of a field type, rejecting any whose domain mentions $I$, and requires the target to be $I$ applied to exactly the parameter variables followed by index terms that do not mention $I$. It returns a `RecursiveFieldInfo` recording $\vec{y} : \vec{B}$ and $\vec{s}$, which is all the recursor generator needs.
- `src/inductive/recursor.rs` builds the recursor type from the formula above. `recursor_type` assembles the telescope $\vec{p}$, the motive, the minor premises, the indices, and the major premise; `minor_premise_type` builds each $C_j$; `induction_hypothesis_type` builds each $H_{j,k}$. The generated binder names (`__motive`, `__minor_j`, `__ih_j_k`, `__major`) start with two underscores, which user declarations may not use, so they can never clash with fields.
- `allows_large_elimination` in `mod.rs` implements the subsingleton test. `add_inductive` registers `I.rec0` always and `I.rec1` when large elimination is allowed; `register_recursor` generates higher levels on demand.

The iota-rules are not generated as terms. `whnf` applies them directly from the stored `InductiveInfo`, which [Chapter 12](12-reduction-conversion.md) explains.

</aside>

The heart of the generator is short enough to read in full. Compare it with the formula for $C_j$.

```rust
/// C_j = Pi (as : As_j). Pi (hs : Hs_j). M ts_j (c_j ps as)
fn minor_premise_type(info: &InductiveInfo, j: usize, constructor: &ConstructorInfo) -> Term {
    // c_j ps as
    let constructor_application = apps(
        const_term(&constructor.name),
        info.params.iter().chain(constructor.fields.iter()).map(|(name, _)| var(name)),
    );
    // (as : As_j) followed by (hs : Hs_j)
    let mut minor_premise_binders = constructor.fields.clone();
    for (k, recursive_field) in constructor.recursive_fields.iter().enumerate() {
        minor_premise_binders.push((
            format!("{INDUCTION_HYPOTHESIS_PREFIX}{j}_{k}"),
            induction_hypothesis_type(constructor, recursive_field),
        ));
    }
    telescope(&minor_premise_binders, apply_motive(&constructor.result_indices, constructor_application))
}
```

The kernel never special-cases $\Nat$. `Kernel::standard` in `src/kernel.rs` declares $\Nat$ and $\mathsf{Eq}$ by calling `add_inductive` with the same `InductiveSpec` a user script would produce, so Figure 7.1 is *generated*, not hard-coded, and the tests in `src/inductive/tests.rs` check that the generated types agree with the hand-written ones.

<aside class="warning" markdown="1">

The positivity check is a soundness requirement, not a convenience. Lean, Coq, and Agda have each had bugs over the years in this part of the kernel, because the general case (nested and mutual inductives, universe constraints, indices mentioning other inductives) is complicated. Our restricted schema keeps the check to eighty lines. When extending it, the question to ask of every new feature is: can a value of the type be built from a function that consumes the type?

</aside>

## Exercises

<div class="exercise" markdown="1">

Write the recursor type $\mathsf{Bool.rec}_v$ for `inductive Bool where | true | false`, and define negation with it.

<details markdown="1">
<summary>Solution</summary>

$\mathsf{Bool.rec}_v : \tPi{M}{\mathsf{Bool} \to \Sort{v}}{M\;\mathsf{true} \to M\;\mathsf{false} \to \tPi{b}{\mathsf{Bool}}{M\;b}}$, with no induction hypotheses since neither constructor has fields. Negation is $\tLam{b}{\mathsf{Bool}}{\mathsf{Bool.rec}_1\;(\tLam{\_}{\mathsf{Bool}}{\mathsf{Bool}})\;\mathsf{false}\;\mathsf{true}\;b}$. The recursor of a type without recursive fields is just case analysis.

</details>

</div>

<div class="exercise" markdown="1">

Which of the four acceptance conditions rejects each of the following, if any? (a) `inductive T : Sort 1 where | mk (f : Sort 1)`. (b) `inductive T : Sort 1 where | mk (f : T -> T)`. (c) `inductive T : Sort 0 where | mk (f : Sort 1)`.

<details markdown="1">
<summary>Solution</summary>

(a) Condition 4: the field $\Sort{1}$ has type $\Sort{2}$, which exceeds $u = 1$. (b) Condition 3: $T$ occurs to the left of an arrow in a field type. (c) Accepted: for $u = 0$ condition 4 imposes nothing, and the type is a proposition that packs up a type; this is the impredicativity of $\Sort{0}$ at work, and it is harmless because $T$ eliminates only into $\Sort{0}$ (it is not a subsingleton, since its field is neither a proof nor an index).

</details>

</div>

<div class="summary-box" markdown="1">

What to remember

- A declaration gives a type former with parameters and indices, and constructors with fields. Parameters are fixed throughout; indices vary and become arguments of the motive.
- The recursor has one minor premise per constructor, with one induction hypothesis per recursive field, and one iota-rule per constructor.
- Acceptance requires well-formedness, uniform parameters, strict positivity, and a universe bound. Positivity is what keeps recursion terminating and the logic consistent.
- Propositions eliminate only into $\Sort{0}$ unless they are subsingletons.
- The kernel generates all of this from data; it contains no code specific to $\Nat$.

</div>
