<div class="lead" markdown="1">

After handling variable names, we can implement computation. We define three kinds of reduction, then use them for weak head normalization, full normalization, and definitional equality. Inductive computation rules live in the signature, allowing one reduction function to handle every declared inductive type.

</div>

## Reduction

Applying a $\lambda$-abstraction to an argument is computed by substituting the argument for the bound variable:

$$
(\tLam{x}{A}{t})\;s \;\betared\; \subst{t}{x}{s}.
$$

This step is **beta-reduction**, and a subterm of the form $(\tLam{x}{A}{t})\;s$ is a **beta-redex**. Part II added two more kinds of step: **delta-reduction**, which unfolds a definition ([Chapter 7](07-inductive-nat.md)), and **iota-reduction**, which runs a recursor on a constructor (Figures 7.1 and 9.1, and the general rule of [Chapter 8](08-inductive-recipe.md)). We allow each step anywhere inside a term, and write $\to$ for a single step of any kind. A term in which no step applies is in **normal form**. For example, with $\mathit{Id} = \tLam{X}{\Sort{0}}{X}$,

$$
\tLam{h}{\mathit{Id}\;P}{(\tLam{y}{P}{y})\;h} \;\betared\; \tLam{h}{P}{(\tLam{y}{P}{y})\;h} \;\betared\; \tLam{h}{P}{h},
$$

and the last term is in normal form. Reducing the inner redex first leads to the same result.

## Conversion

**Definitional equality**, also called **conversion**, identifies terms that compute to the same result, up to the names of bound variables.

<div class="definition" markdown="1">

**Definition 12.1 (Conversion).** $s \conv t$ is the smallest equivalence relation that contains $\alphaeq$ and $\to$ and is closed under all term constructors.

</div>

To decide $s \conv t$, the kernel normalizes both terms and compares the results with $\alphaeq$. This procedure relies on two facts.

- Reduction is **confluent**: different reduction orders cannot lead to different normal forms. So $s \conv t$ holds exactly when the normal forms of $s$ and $t$ are alpha-equivalent; there is no need to search for a clever sequence of steps.
- Every well-typed term **has** a normal form, so normalization terminates. This holds for our system, but it is a deep theorem (strong normalization, [Chapter 14](14-properties.md)) [Barendregt 1992].

A practical kernel also caps the number of reduction steps, so that a bug cannot make it loop forever; our implementation stops after 20,000 steps with the error "reduction fuel exhausted".

<aside class="intuition" markdown="1">

Why decide equality by normalizing rather than by searching for a chain of steps? Because confluence turns an existence question ("is there some way to make these equal?") into a canonical-form question ("do they have the same normal form?"), which has a direct algorithm. The price is that normalization can be expensive: a definition that unfolds into a large term is fully expanded even if the two sides differ in their first symbol. Production kernels avoid this with lazy comparison, discussed at the end of the chapter.

</aside>

## Computation rules as data

Figures 7.1 and 9.1 write each iota-rule as a separate equation, which suggests that every new inductive type needs new reduction code in the kernel. It does not. A kernel stores the iota-rules as data in the signature, next to the recursor, and a single piece of code applies them for every inductive type.

Each recursor entry records the position of its **major premise**, the argument whose constructor decides which rule applies, and the constructors of its inductive type. For each constructor the kernel knows how many leading arguments are **parameters** (which the rule ignores) and how many are **fields** (which the rule passes on), and which fields are recursive. For three of our recursors, the data and the resulting right-hand sides are as follows; type annotations on $\lambda$ are omitted.

$$
\begin{array}{llcll}
\textbf{Recursor} & \textbf{Major} & \textbf{Constructor} & \textbf{Params, fields} & \textbf{Right-hand side} \\[2pt]
\NatRec{u} & \text{4th} & \zero & 0,\;0 & \lambda M\,z\,s.\; z \\[2pt]
& & \suc & 0,\;1 & \lambda M\,z\,s\,n.\; s\;n\;(\NatRec{u}\;M\;z\;s\;n) \\[2pt]
\EqRecDep{u,v} & \text{6th} & \refl{u} & 2,\;0 & \lambda A\,a\,M\,m\,b.\; m \\[2pt]
\mathsf{Tree.rec}_v & \text{5th} & \mathsf{leaf} & 0,\;0 & \lambda M\,m_1\,m_2\,m_3.\; m_1 \\[2pt]
& & \mathsf{node} & 0,\;1 & \lambda M\,m_1\,m_2\,m_3\,t.\; m_2\;t\;(\mathsf{Tree.rec}_v\;M\,m_1\,m_2\,m_3\;t) \\[2pt]
& & \mathsf{branch} & 0,\;2 & \lambda M\,m_1\,m_2\,m_3\,l\,r.\; m_3\;l\;r\;(\mathsf{Tree.rec}_v\;M\,m_1\,m_2\,m_3\;l)\;(\cdots\;r)
\end{array}
$$

The right-hand side takes the arguments before the major premise, then the fields of the constructor. For example, $\NatRec{u}\;M\;z\;s\;(\suc\;n)$ selects the second rule and becomes

$$
(\lambda M\,z\,s\,n.\; s\;n\;(\NatRec{u}\;M\;z\;s\;n))\;M\;z\;s\;n,
$$

which beta-reduces to the right-hand side of the second equation in Figure 7.1. Likewise, the only rule of $\EqRecDep{u,v}$ fires on $\EqRecDep{u,v}\;A\;a\;M\;m\;b\;(\refl{u}\;A'\;c)$. The constructor $\refl{u}$ has two parameters, $A'$ and $c$, and no fields, so the right-hand side receives just $A\;a\;M\;m\;b$ and returns $m$.

## Weak head normal form and normalization

Algorithm 12.1 defines the three functions that Algorithm 5.1 left open. Both $\Whnf$ and $\Normalize$ view a term as a **spine** $h\;a_1 \cdots a_n$: a head $h$ that is not an application, applied to $n \ge 0$ arguments ([Chapter 2](02-syntax.md)). Every term has exactly one such decomposition.

<div class="rulebox" markdown="1">

<p class="caption">Algorithm 12.1. Weak head normalization with beta, delta, and iota; full normalization; and definitional equality.</p>

```text
Whnf(t):
  loop:
    write t as a spine h a_1 ... a_n
    if h = λ(x : A). b and n ≥ 1:                               -- beta
        t ← (b[x ↦ a_1]) a_2 ... a_n
    else if h = c and (c : C := d) ∈ Σ:                         -- delta
        t ← d a_1 ... a_n
    else if h = c is a recursor with major position p ≤ n:      -- iota
        k b_1 ... b_j ← Whnf(a_p)
        if k is a constructor of c's inductive type with q parameters:
            t ← rhs_k a_1 ... a_{p-1} b_{q+1} ... b_j a_{p+1} ... a_n
        else return t                                           -- stuck, e.g. on a variable
    else return t

Normalize(t):
  t ← Whnf(t)
  if t = Π(x : A). B:  return Π(x : Normalize(A)). Normalize(B)
  if t = λ(x : A). b:  return λ(x : Normalize(A)). Normalize(b)
  else write t as a spine h a_1 ... a_n and return h Normalize(a_1) ... Normalize(a_n)

IsDefEq(s, t):
  return  · ; · ⊢ Normalize(s) =α Normalize(t)                  -- Figure 11.1
```

</div>

$\Whnf$ reduces only at the head of a term, until no rule applies there; the result is the **weak head normal form**. It never looks inside a $\lambda$, a $\Pi$, or the arguments of a stuck head. This is enough when a caller only needs the outermost shape of a type, such as a $\Pi$ in the application case of $\Infer$, and it is cheaper than full normalization. $\Normalize$ first computes the weak head normal form and then normalizes every immediate subterm. For example, with $t = \tLam{h}{\mathit{Id}\;P}{h}$ and $\mathit{Id}$ as above,

$$
\Whnf(t) = t, \qquad \Normalize(t) = \tLam{h}{P}{h},
$$

because the head of $t$ is a $\lambda$ with no arguments, while $\Normalize$ continues into the annotation $\mathit{Id}\;P$. Likewise, $\Whnf(\mathit{Id}\;(\mathit{Id}\;P \to P)) = \mathit{Id}\;P \to P$, which already shows a $\Pi$ although its domain is not yet normal. Both are visible below: no head step applies, yet the normal form differs.

<div class="explorer" data-kind="reduce" data-term="fun (h : (fun (X : Sort 0) => X) P) => h" data-ctx="P : Sort 0"></div>

The three cases of $\Whnf$ have the following properties.

- The iota case contains no reference to $\Nat$, $\Eq{}$, or $\mathsf{Tree}$. It reads the major position and the constructor data from the signature. It is written once; after that, each new inductive type adds rows of data, not code.
- The major premise is put in weak head normal form *before* the rules are consulted, because it may become a constructor only after computation. For $2 + 1$ in Chapter 7, the major premise is the numeral $1 = \suc\;\zero$, already a constructor; for $\mathit{double}\;(1 + 1)$, it is $1 + 1$, which $\Whnf$ turns into $\suc\;(1 + 0)$ first.
- If the major premise does not become a constructor, for instance because it is a variable, the term is **stuck** and stays as it is; this is why $0 + n$ does not reduce ([Chapter 9](09-equality.md)).

Here is $\Whnf$ at work on $\mathit{double}\;(1 + 1)$, with $\mathit{double}$ as in Chapter 7, computed live. Only the head is ever reduced, but reducing the major premise forces an inner computation.

<div class="explorer" data-kind="reduce" data-term="double (add (Nat.succ Nat.zero) (Nat.succ Nat.zero))"><pre class="prelude">def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n
def double : Nat -> Nat := fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) Nat.zero (fun (k : Nat) => fun (r : Nat) => Nat.succ (Nat.succ r)) n</pre></div>

The step marked *whnf* is the inner computation: the recursor needs its major premise to be a constructor, so $1 + 1$ is reduced at its head first. The final weak head normal form still contains a stuck inner recursor; the normal form below it is what $\Normalize$ produces by continuing inside.

For simplicity, $\IsDefEq$ fully normalizes both terms, as our implementation does. Practical kernels instead compare lazily: they reduce both sides to weak head normal form, compare the heads, and inspect arguments only when needed. This avoids fully normalizing large terms whose heads already differ. Strong normalization guarantees that all three functions terminate on well-typed terms.

## In the code

<aside class="code" markdown="1">

Algorithm 12.1 is `src/reduction.rs`. `whnf`, `normalize`, and `is_def_eq` are thin wrappers that allocate the fuel budget (`REDUCTION_FUEL = 20000`) and call `whnf_with_fuel`, `normalize_with_fuel`, and `is_def_eq_with_fuel`. The loop in `whnf_with_fuel` is a direct transcription:

```rust
let (head, args) = spine(&t);
let reduced = match head {
    // beta: (fun x. b) a_1 a_2 ... a_n  ~>  b[x := a_1] a_2 ... a_n
    Term::Lam(x, _, body) if !args.is_empty() => Some(apps(
        subst(&body, &x, &args[0]),
        args[1..].iter().cloned(),
    )),
    Term::Const(c) => match self.decls.get(&c) {
        // delta: c as  ~>  d as   where (c := d) in Sigma
        Some(Decl { kind: DeclKind::Definition(body), .. }) => Some(apps(body.clone(), args)),
        // iota: I.rec ps M ms is (c_j ps' as)  ~>  m_j as hs
        Some(Decl { kind: DeclKind::Recursor(recursor), .. }) => {
            self.iota_reduce(&c, recursor, &args, fuel)?
        }
        _ => None,
    },
    _ => None,
};
match reduced {
    Some(next) => t = next,
    None => return Ok(t),
}
```

`iota_reduce` finds the major premise at `recursor.major_argument_index`, puts it in weak head normal form, checks that its head is a constructor of the right inductive type applied to all of its parameters and fields, checks that the constructor's parameters are convertible to the recursor's (a well-typed redex guarantees this, but the kernel verifies rather than assumes), and then builds $m_j\;\vec{a}\;\vec{h}$ followed by any extra arguments. The induction hypotheses $\vec{h}$ are built by `induction_hypothesis`, which instantiates the stored $\vec{y} : \vec{B}$ and $\vec{s}$ of each recursive field with the actual parameters and field values and wraps a recursive call in the corresponding $\lambda$s.

The implementation computes each rule's right-hand side from `InductiveInfo` when needed. The table above specifies the same result; computing it avoids storing a second copy of the constructor data.

</aside>

One subtlety in `normalize_with_fuel` deserves mention. After normalizing the function and argument of an application, it calls `whnf` on the rebuilt term once more. Normalizing an argument can expose a new redex at the head: for a stuck recursor application whose major premise *becomes* a constructor only after its own arguments are normalized, the head must be reduced again. Without this re-check, `is_def_eq` would miss some equalities, and the test `conversion_renormalizes_exposed_redex` in `src/proof.rs` guards it.

## Exercises

<div class="exercise" markdown="1">

Give the weak head normal form and the normal form of $(\tLam{f}{\Nat \to \Nat}{f})\;(\tLam{x}{\Nat}{x})\;\zero$.

<details markdown="1">
<summary>Solution</summary>

The spine has head $\tLam{f}{\Nat \to \Nat}{f}$ with two arguments. Beta on the first argument gives $(\tLam{x}{\Nat}{x})\;\zero$, which is again a beta-redex at the head and reduces to $\zero$. So both the weak head normal form and the normal form are $\zero$. (This is the term in the test `conversion_renormalizes_exposed_redex`.)

</details>

</div>

<div class="exercise" markdown="1">

Why does $\Whnf$ not reduce under a $\lambda$? What would go wrong in $\Infer$ if $\Whnf$ returned $\tLam{x}{A}{b}$ with $b$ normalized?

<details markdown="1">
<summary>Solution</summary>

Nothing would be *wrong*: the result would still be convertible to the input. But it would be wasted work. $\Infer$ calls $\Whnf$ only to learn the outermost shape, which is already visible once the head is a $\lambda$. Reducing inside could be arbitrarily expensive, for instance in an annotation that is never compared with anything. Keeping $\Whnf$ shallow keeps type inference cheap on large terms.

</details>

</div>

<div class="summary-box" markdown="1">

What to remember

- Three reduction steps: beta (apply a $\lambda$), delta (unfold a definition), iota (run a recursor on a constructor). Conversion is the equivalence they generate together with alpha-equivalence.
- Conversion is decided by normalizing both sides and comparing up to alpha, which is correct by confluence and terminates by strong normalization.
- Iota-rules are data: the major premise position plus constructor metadata. One `whnf` serves every inductive type.
- Whnf reduces only at the head and is what Infer needs; Normalize goes everywhere and is what IsDefEq uses. A step budget guards against bugs.

</div>
