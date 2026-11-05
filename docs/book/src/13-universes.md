<div class="lead" markdown="1">

Chapter 4 showed that the typing rules implement a logic, and that the system is acceptable only if it is consistent. This chapter asks a question that has been deferred since Chapter 2: what is the type of $\Sort{0}$? The simplest answer, a single universe that contains itself, makes the system inconsistent. Lean's answer, a hierarchy $\Sort{0} : \Sort{1} : \Sort{2} : \cdots$ with an impredicative bottom universe, does not. Along the way the chapter explains the one odd-looking piece of T-Pi, the function $\imax$.

</div>

## What is the type of Sort 0?

A proposition variable appears in the type theory as an assumption $P : \Sort{0}$. It can occur in two places: in a context, as in the left judgment below, or bound by $\lambda$ or $\Pi$, as in the right one:

$$
P : \Sort{0} \vdash \tLam{h}{P}{h} : P \to P
\qquad\text{versus}\qquad
\vdash \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}} : \tPi{P}{\Sort{0}}{P \to P}.
$$

The left judgment proves $P \to P$ for one fixed $P$ supplied from outside. The right one is a single closed term that proves it for *every* $P$, and it can be applied later to any particular proposition; this is what the $\forall$ rows of Figure 4.1 need.

Both forms require $\Sort{0}$ to be a type. C-Ext, which adds $P : \Sort{0}$ to a context, and T-Lam and T-Pi, which bind $P : \Sort{0}$, all have the premise $\Gamma \vdash A : \Sort{u}$ for the type $A$ of the new variable. With $A = \Sort{0}$, this premise reads $\Gamma \vdash \Sort{0} : \Sort{u}$ for some $u$: the universe of propositions must itself have a type. The question is which.

## Type is not a type

Suppose we replace all universes by a single universe $\mathsf{Type}$ that contains itself:

$$
\dfrac{\ctxok{\Gamma}}{\Gamma \vdash \mathsf{Type} : \mathsf{Type}}
\qquad
\dfrac{\Gamma \vdash A : \mathsf{Type} \qquad \Gamma, x : A \vdash B : \mathsf{Type}}{\Gamma \vdash \tPi{x}{A}{B} : \mathsf{Type}}
$$

Translate $\forall P.\,\varphi$ as $\tPi{P}{\mathsf{Type}}{\varphi^\ast}$. Then $P$ ranges over a collection that contains $\mathsf{Type}$ itself and every type built from it. Such a collection is the type-theoretic analogue of the set of all sets, and naive set theory shows that such collections lead to contradictions. The best-known example is **Russell's paradox**: for $R = \{\, x \mid x \notin x \,\}$, both $R \in R$ and $R \notin R$ lead to a contradiction.

Type theory has no membership test like $x \notin x$, so Russell's argument does not carry over word for word. Girard instead adapted a related paradox about the collection of all well-orderings, due to Burali-Forti [Girard 1972], and Hurkens simplified the resulting term [Hurkens 1995]. The result is a closed term $t_{\mathrm{H}}$ with

$$
\vdash t_{\mathrm{H}} : \tPi{P}{\mathsf{Type}}{P},
$$

so the system is inconsistent: $\bot$ has no proof, yet $\bot^\ast$ has a term, and a kernel built on these rules accepts a proof of every statement. The essential ingredient is a type $U$ that quantifies over all of $\mathsf{Type}$ while being a member of $\mathsf{Type}$, which lets $U$ contain a copy of its own double power set, something no set can do. [Appendix C](c-hurkens.md) gives $t_{\mathrm{H}}$ in full, explains how it works, and shows how to reproduce the result by changing one line of the kernel.

The damage reaches the algorithm as well. Subject reduction still holds, so if $t_{\mathrm{H}}$ had a normal form, it would be a normal closed term of type $\tPi{p}{\mathsf{Type}}{p}$. The part of the consistency proof in [Appendix D](d-proof-consistency.md) that analyses normal terms does not use strong normalization and carries over to $\mathsf{Type} : \mathsf{Type}$; it shows that no such normal term exists. Hence $t_{\mathrm{H}}$ has no normal form, strong normalization fails, and $\Normalize$ runs forever on it. A kernel with $\mathsf{Type} : \mathsf{Type}$ is not only unsound but also, on some inputs, non-terminating.

<aside class="history" markdown="1">

Martin-Löf's first type theory of 1971 had this rule, and Girard's paradox was discovered against it the following year. Every dependent type theory since then has had either a hierarchy of universes or some other device to break the self-reference. The paradox is not a curiosity: the self-containing universe is the *obvious* design, and the obvious design is wrong.

</aside>

## A hierarchy with an impredicative bottom

The second answer is that $\Sort{0}$ lives in a larger universe, which lives in a larger one still:

$$
\dfrac{\ctxok{\Gamma}}{\Gamma \vdash \Sort{u} : \Sort{(u+1)}}\rulename{T-Sort}
\qquad\text{so}\qquad
\Sort{0} : \Sort{1} : \Sort{2} : \cdots.
$$

No universe contains itself. A $\Pi$-type takes an argument from one universe and returns a type in another, so T-Pi must also say which universe the $\Pi$-type itself belongs to. Lean's answer uses the function $\imax$:

$$
\dfrac{\Gamma \vdash A : \Sort{u} \qquad \Gamma, x : A \vdash B : \Sort{v}}{\Gamma \vdash \tPi{x}{A}{B} : \Sort{\imax(u, v)}}\rulename{T-Pi}
\qquad
\imax(u, v) =
\begin{cases}
0 & \text{if } v = 0, \\
\max(u, v) & \text{otherwise.}
\end{cases}
$$

The case split in $\imax$ makes a $\Pi$-type *impredicative* when its body is a proposition, and *predicative* otherwise. Pick the universes of $A$ and $B$ below and watch where the $\Pi$-type lands.

<div class="explorer" data-kind="universes"></div>

**Propositions are impredicative.** If the body $B$ is a proposition ($v = 0$), the whole $\Pi$ is a proposition, whatever it quantifies over. In particular $(\forall P.\,\varphi)^\ast = \tPi{P}{\Sort{0}}{\varphi^\ast}$ is in $\Sort{0}$, although it quantifies over all of $\Sort{0}$. A universe that contains types quantifying over itself is called **impredicative**. Because every translated formula lies in $\Sort{0}$, the premise $\psi^\ast : \Sort{0}$ of $\forall$-elim always holds, so a universal statement can be instantiated with any proposition, even with itself. For example, with $\mathit{id} = \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}}$,

$$
\mathit{id} : \tPi{P}{\Sort{0}}{P \to P}
\qquad\text{and}\qquad
\tPi{P}{\Sort{0}}{P \to P} : \Sort{0},
$$

so $\mathit{id}\;(\tPi{P}{\Sort{0}}{P \to P})\;\mathit{id}$ is well typed, with type $\tPi{P}{\Sort{0}}{P \to P}$. The same case makes $\forall n : \Nat,\, n + 0 = n$ a proposition, even though $\Nat$ lives in $\Sort{1}$; [Chapter 7](07-inductive-nat.md) relied on this for induction.

<div class="playground" data-file="impredicative"><pre># "Every proposition implies itself" is itself a proposition,
# so it can be instantiated with itself.
def id : forall (P : Sort 0), P -> P := fun (P : Sort 0) => fun (h : P) => h
def self : forall (P : Sort 0), P -> P := id (forall (P : Sort 0), P -> P) id

# The analogous statement one level up is NOT its own instance:
# forall (A : Sort 1), A -> A lives in Sort 2, not Sort 1.
def idT : forall (A : Sort 1), A -> A := fun (A : Sort 1) => fun (a : A) => a
def selfT : forall (A : Sort 1), A -> A := idT (forall (A : Sort 1), A -> A) idT</pre></div>

**Types are predicative.** If the body is not a proposition ($v \ge 1$), the $\Pi$ lives in the larger of the two universes. A type that quantifies over $\Sort{u}$ then lives in $\Sort{(\max(u+1, v))}$, which is never $\Sort{u}$:

$$
\dfrac{
  \dfrac{}{\Gamma \vdash \Sort{u} : \Sort{(u+1)}}\rulename{T-Sort}
  \qquad
  \Gamma, x : \Sort{u} \vdash B : \Sort{v}
}{\Gamma \vdash \tPi{x}{\Sort{u}}{B} : \Sort{(\max(u+1, v))}}\rulename{T-Pi}
$$

This property is called **predicativity**. For example, the identity on types $\tLam{A}{\Sort{1}}{\tLam{a}{A}{a}}$ has type $\tPi{A}{\Sort{1}}{A \to A}$, which lives in $\Sort{2}$, so it cannot be applied to its own type; a copy at $\Sort{2}$ can. Each level holds the level beneath it, and in practice a few levels suffice; higher levels appear when one quantifies over large collections, such as the category of all small categories.

**Why this is safe.** Impredicativity looks like the self-reference that the previous section warned against, but it is confined: $\Sort{0}$ contains types that quantify over $\Sort{0}$, yet $\Sort{0}$ is not a member of itself. Coquand showed that one impredicative universe at the bottom is consistent [Coquand 1988], whereas Girard's paradox can already be derived once *two* levels are impredicative [Hurkens 1995]. With these rules the system is consistent and strongly normalizing ([Chapter 14](14-properties.md)).

<aside class="intuition" markdown="1">

Why may propositions be impredicative when types may not? Because a proof of a proposition carries no data that a program could extract (this is what the elimination restriction of Chapter 8 enforces). Quantifying over all propositions to define a proposition is like defining a set by a property that mentions all sets: dangerous when the result is itself an object that the quantifier ranges over and can be inspected, harmless when all one can do with it is use it as a hypothesis. The paradox needs to *inspect* the thing it builds; propositions cannot be inspected.

</aside>

## Comparison with Lean

In Lean [de Moura and Ullrich 2021], $\Sort{0}$ is `Prop`, $\Sort{(u+1)}$ is `Type u`, and $\Pi$-types are assigned universes with $\imax$ as above. Two differences remain.

First, `Prop` in Lean has **definitional proof irrelevance**: any two proofs of the same proposition are definitionally equal. Our conversion does not identify proofs; adding this would make conversion depend on types, so the simple "normalize and compare" check of [Chapter 12](12-reduction-conversion.md) would no longer suffice.

Second, Lean has **universe polymorphism**, so definitions can be stated once for all levels $u$, and $\imax$ then matters for level *variables* as well, with constraints such as $\imax(u, v) \le w$ solved symbolically. In our system every level is a concrete number.

The table summarizes the design space.

| Design | Quantifies over | Drawback |
|---|---|---|
| No universes | values only | cannot say "for every proposition" |
| $\mathsf{Type} : \mathsf{Type}$ | everything | inconsistent |
| Two sorts $\ast : \square$ | $\ast$ only | $\square$ itself has no type |
| $\Sort{u} : \Sort{(u+1)}$ with $\max$ | any level | $\forall$ over propositions is not a proposition |
| $\Sort{u} : \Sort{(u+1)}$ with $\imax$ (Lean) | any level | normalization is harder to prove |

<aside class="code" markdown="1">

The whole of this chapter is two lines of `infer` in `src/typecheck.rs`: the `Sort(u)` case returns `Sort(u + 1)`, and the `Pi` case returns `Sort(0)` when the body's level is `0` and the maximum otherwise. [Appendix C](c-hurkens.md) shows that changing the first line to return `Sort(u)` makes the kernel accept Hurkens' term.

</aside>

## Exercises

<div class="exercise" markdown="1">

Compute the universe of $\tPi{A}{\Sort{1}}{\tPi{P}{A \to \Sort{0}}{\tPi{a}{A}{P\;a}}}$, the statement "every predicate on every type holds everywhere" (which is false but well formed).

<details markdown="1">
<summary>Solution</summary>

Innermost: $P\;a : \Sort{0}$, so $\tPi{a}{A}{P\;a} : \Sort{\imax(1, 0)} = \Sort{0}$. Next, $A \to \Sort{0}$ has universe $\imax(1, 1) = 1$ (its body $\Sort{0}$ has type $\Sort{1}$), so the middle $\Pi$ has universe $\imax(1, 0) = 0$. Finally $\Sort{1} : \Sort{2}$ and the body is in $\Sort{0}$, giving $\imax(2, 0) = 0$. The whole statement is a proposition. With $\max$ instead of $\imax$ it would land in $\Sort{2}$.

</details>

</div>

<div class="exercise" markdown="1">

Explain why the `selfT` definition in the playground is rejected, by naming the rule and the two universes involved.

<details markdown="1">
<summary>Solution</summary>

`idT` expects an argument $A : \Sort{1}$. The argument supplied is $\tPi{A}{\Sort{1}}{A \to A}$, whose universe by T-Pi is $\max(2, 1) = 2$, so $\Check$ compares $\Sort{2}$ with $\Sort{1}$ and fails: the kernel reports a type mismatch at the application. This is predicativity: a type that quantifies over $\Sort{1}$ is not in $\Sort{1}$.

</details>

</div>

<div class="summary-box" markdown="1">

What to remember

- $\Sort{0}$ needs a type, because proposition variables are bound by $\lambda$ and $\Pi$.
- A universe containing itself is inconsistent (Girard, Hurkens) and breaks normalization.
- The hierarchy $\Sort{u} : \Sort{(u+1)}$ avoids self-containment; $\imax$ makes propositions impredicative and everything else predicative.
- One impredicative universe at the bottom is safe; two are not. Lean adds proof irrelevance and universe polymorphism on top of the same design.

</div>
