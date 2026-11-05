<div class="lead" markdown="1">

The kernel's job is to decide the judgment "term $t$ has type $A$". This chapter defines that judgment by a small set of inference rules, one for each kind of term and one extra rule that lets computation happen inside types. Reading each rule bottom-up turns it into a recipe for checking a term, and that recipe becomes the algorithm of Chapter 5.

</div>

## Contexts and judgments

A term such as $f\;p$ cannot be checked in isolation: its type depends on what $f$ and $p$ are. A **context** $\Gamma$ records that information. It is an ordered list of assumptions

$$
\Gamma \;=\; x_1 : A_1,\; x_2 : A_2,\; \ldots,\; x_n : A_n,
$$

giving the type of each variable in scope, and $\dom(\Gamma)$ denotes the set of names $\{x_1, \ldots, x_n\}$. The empty context is written $\cdot$.

Order matters. A later type may mention an earlier variable, as in $P : \Sort{0},\; h : P$: the assumption $h : P$ only makes sense once $P$ is known to be a proposition. Names in a context will be required to be distinct, so a context can be used like a dictionary from names to types; but it is a dictionary whose entries depend on each other in sequence.

Two judgments are defined together.

- $\ctxok{\Gamma}$ means that the context $\Gamma$ is *well formed*: each assumed type is a genuine type in the context before it.
- $\Gamma \vdash t : A$ means that under the assumptions in $\Gamma$, the term $t$ has type $A$.

Through the Curry-Howard lens, $\Gamma \vdash t : A$ says that $t$ is a proof of $A$ from the hypotheses $\Gamma$.

## The rules

Figure 3.1 lists all the rules. Each rule has premises above the line and a conclusion below it; the conclusion holds whenever every premise does. The rule names on the right are used throughout the book.

<div class="rulebox" markdown="1">

<p class="caption">Figure 3.1. Well-formed contexts (top row) and typing rules.</p>

$$
\dfrac{\phantom{\ctxok{\Gamma}}}{\ctxok{\cdot}}\rulename{C-Empty}
\qquad
\dfrac{\ctxok{\Gamma} \qquad \Gamma \vdash A : \Sort{u} \qquad x \notin \dom(\Gamma)}{\ctxok{\Gamma, x : A}}\rulename{C-Ext}
$$

$$
\dfrac{\ctxok{\Gamma}}{\Gamma \vdash \Sort{u} : \Sort{(u+1)}}\rulename{T-Sort}
\qquad
\dfrac{\ctxok{\Gamma} \qquad (x : A) \in \Gamma}{\Gamma \vdash x : A}\rulename{T-Var}
$$

$$
\dfrac{\Gamma \vdash A : \Sort{u} \qquad \Gamma, x : A \vdash B : \Sort{v}}{\Gamma \vdash \tPi{x}{A}{B} : \Sort{\imax(u, v)}}\rulename{T-Pi}
$$

$$
\dfrac{\Gamma \vdash A : \Sort{u} \qquad \Gamma, x : A \vdash t : B}{\Gamma \vdash \tLam{x}{A}{t} : \tPi{x}{A}{B}}\rulename{T-Lam}
$$

$$
\dfrac{\Gamma \vdash f : \tPi{x}{A}{B} \qquad \Gamma \vdash a : A}{\Gamma \vdash f\;a : \subst{B}{x}{a}}\rulename{T-App}
$$

$$
\dfrac{\Gamma \vdash t : A \qquad \Gamma \vdash B : \Sort{u} \qquad A \conv B}{\Gamma \vdash t : B}\rulename{T-Conv}
$$

</div>

Two of the rules use operations on terms that the next chapters treat as black boxes.

**Substitution.** T-App writes $\subst{B}{x}{a}$ for the result of replacing every free occurrence of $x$ in $B$ by $a$. For example, $\subst{(P \to P)}{P}{Q} = Q \to Q$. Replacing names inside binders needs care, which [Chapter 11](11-substitution-alpha.md) explains; until then the intuitive meaning is enough.

**Definitional equality.** T-Conv writes $A \conv B$ when $A$ and $B$ are "the same type" in a sense the kernel can decide mechanically. Two kinds of difference are ignored.

- The names of bound variables. $\tPi{P}{\Sort{0}}{P \to P}$ and $\tPi{Q}{\Sort{0}}{Q \to Q}$ state the same proposition. Terms that differ only in this way are *alpha-equivalent*, written $A \alphaeq B$.
- Computation. If $\mathit{Id} = \tLam{X}{\Sort{0}}{X}$, then $\mathit{Id}\;P$ computes to $P$ by plugging $P$ in for $X$, so a proof of $\mathit{Id}\;P$ should count as a proof of $P$. The computation step $(\tLam{x}{A}{t})\;s \betared \subst{t}{x}{s}$ is called *beta-reduction*.

The kernel decides $A \conv B$ by computing both sides as far as possible and then checking whether the results are alpha-equivalent. [Chapter 12](12-reduction-conversion.md) defines this precisely.

## Reading the rules

The rules are best read from the bottom up, as a recipe: to establish the conclusion, establish the premises.

**C-Empty and C-Ext.** A context is built one assumption at a time, and each new assumption must have a type as its type. The side condition $x \notin \dom(\Gamma)$ forbids two assumptions with the same name. Since the names of bound variables do not matter, this restricts nothing: a binder that would clash can always be renamed first. [Chapter 11](11-substitution-alpha.md#variable-capture-in-contexts) shows what goes wrong in a kernel that skips this condition.

**T-Sort.** Every universe lives in the next one: $\Sort{0} : \Sort{1}$, $\Sort{1} : \Sort{2}$, and so on. [Chapter 13](13-universes.md) explains why a universe cannot be its own type.

**T-Var.** A variable has the type the context assigns to it. Logically: use a hypothesis.

**T-Pi.** $\tPi{x}{A}{B}$ is a type if $A$ is a type and $B$ is a type once $x : A$ is assumed. The resulting universe is $\imax(u, v)$, which is $0$ if $v = 0$ and $\max(u, v)$ otherwise. In words: a $\Pi$-type is a proposition whenever its body is a proposition, no matter what it quantifies over; otherwise it lives in the larger of the two universes. Logically, this rule says when $A \to B$ and $\forall x{:}A.\,B$ are well-formed statements.

**T-Lam.** To build a function from $A$ to $B$, assume $x : A$ and build a term $t$ of type $B$. The body's type $B$ may mention $x$, and it is kept as is in the resulting $\Pi$-type, which is where dependency enters. Logically, this is the introduction rule for implication and for the universal quantifier: to prove $A \to B$, assume $A$ and prove $B$.

**T-App.** If $f$ maps each $x : A$ to an element of $B$, and $a : A$, then $f\;a$ has type $B$ with $x$ replaced by $a$. When $B$ does not mention $x$ this is modus ponens: from $A \to B$ and $A$, conclude $B$. When it does, it is instantiation of a universal statement. For example, if $f : \tPi{n}{\Nat}{n + 0 = n}$, then $f\;3 : 3 + 0 = 3$ (natural numbers arrive in [Chapter 7](07-inductive-nat.md)).

**T-Conv.** Types that are equal up to computation are interchangeable: from $h : \mathit{Id}\;P$ we may conclude $h : P$. The premise $\Gamma \vdash B : \Sort{u}$ ensures that the new type is itself a type. This is the only rule whose use is not determined by the shape of $t$, a fact that matters for the algorithm in [Chapter 5](05-algorithm.md).

<aside class="intuition" markdown="1">

Each rule is a small piece of common sense about functions. T-Lam says how to make a function; T-App says how to use one; T-Pi says when a function type makes sense; T-Var and T-Sort say what the basic things are; and T-Conv says that computing inside a type does not change what it means. There is nothing specifically "logical" in the rules. The logic is a consequence of reading them through Curry-Howard, which [Chapter 4](04-logic.md) makes precise.

</aside>

## Why application matters

It is tempting to think that the interesting rules are the ones that build things (T-Lam, T-Pi) and that T-App is bookkeeping. The opposite is closer to the truth. Without T-App a hypothesis can be returned but never *used*. Roughly, the provable propositions would then be only those whose conclusion is literally one of the hypotheses, such as $P \to Q \to P$. Composition,

$$
(P \to Q) \to (Q \to R) \to P \to R,
$$

has the proof $\tLam{f}{P \to Q}{\tLam{g}{Q \to R}{\tLam{p}{P}{g\,(f\,p)}}}$, which applies $f$ and then $g$. Every proof that does more than restate an assumption goes through T-App, and in a dependent type theory T-App is also where substitution, and therefore most of the subtlety, lives.

## A first derivation

A derivation is a tree of rule instances whose root is the judgment being established. Here is the derivation that $\tLam{P}{\Sort{0}}{\tLam{h}{P}{h}}$ proves $\tPi{P}{\Sort{0}}{P \to P}$. Write $\Gamma_1 = P : \Sort{0}$ and $\Gamma_2 = \Gamma_1, h : P$, and omit the well-formedness premises $\ctxok{\Gamma}$, which are routine.

$$
\dfrac{
  \dfrac{}{\cdot \vdash \Sort{0} : \Sort{1}}\rulename{T-Sort}
  \qquad
  \dfrac{
    \dfrac{}{\Gamma_1 \vdash P : \Sort{0}}\rulename{T-Var}
    \qquad
    \dfrac{}{\Gamma_2 \vdash h : P}\rulename{T-Var}
  }{\Gamma_1 \vdash \tLam{h}{P}{h} : \tPi{h}{P}{P}}\rulename{T-Lam}
}{\cdot \vdash \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}} : \tPi{P}{\Sort{0}}{\tPi{h}{P}{P}}}\rulename{T-Lam}
$$

The kernel builds exactly this tree. Below, each node is one application of a rule, with the judgment it establishes; switch to the call view to read it top-down as the recursion that produces it. Replace the term with your own to see which rules fire.

<div class="explorer" data-kind="derive" data-view="tree" data-term="fun (P : Sort 0) => fun (h : P) => h"></div>

Two observations. First, the shape of the tree follows the shape of the term: a $\lambda$ at the root, a $\lambda$ below it, variables at the leaves. Second, the type at the root is $\tPi{P}{\Sort{0}}{\tPi{h}{P}{P}}$, whereas the stated proposition was $\tPi{P}{\Sort{0}}{P \to P}$. These differ only in the name of a bound variable ($h$ versus the anonymous `_` of the arrow), so they are alpha-equivalent, and T-Conv bridges the gap. [Chapter 6](06-worked-examples.md) revisits this example with the algorithm.

<aside class="code" markdown="1">

The rules of this chapter are implemented by `Kernel::infer` and `Kernel::check` in `src/typecheck.rs`, which [Chapter 5](05-algorithm.md) reads line by line. Contexts are the Rust type `Context = Vec<(String, Term)>` in `src/declaration.rs`: a vector of name-type pairs, searched from the end so that the most recent assumption for a name wins.

</aside>

## Exercises

<div class="exercise" markdown="1">

Which rule, applied bottom-up, handles each of the following judgments, and what premises does it produce? (a) $\Gamma \vdash \tLam{x}{A}{x} : A \to A$. (b) $\Gamma \vdash \Sort{2} : \Sort{3}$. (c) $\Gamma \vdash f\;a : B$ where $f : A \to B$.

<details markdown="1">
<summary>Solution</summary>

(a) T-Lam, with premises $\Gamma \vdash A : \Sort{u}$ for some $u$ and $\Gamma, x : A \vdash x : A$; the latter is T-Var. The resulting type is $\tPi{x}{A}{A}$, which is $A \to A$ up to the binder name.
(b) T-Sort, with the single premise $\ctxok{\Gamma}$.
(c) T-App, with premises $\Gamma \vdash f : \tPi{\_}{A}{B}$ and $\Gamma \vdash a : A$. The conclusion is $\subst{B}{\_}{a} = B$, since `_` does not occur in $B$.

</details>

</div>

<div class="exercise" markdown="1">

Using T-Pi, compute the universe of $\tPi{P}{\Sort{0}}{P \to P}$ and of $\tPi{A}{\Sort{1}}{A \to A}$.

<details markdown="1">
<summary>Solution</summary>

For the first, $\Sort{0} : \Sort{1}$ so $u = 1$, and $P \to P : \Sort{0}$ (by T-Pi again with $u = v = 0$) so $v = 0$. Hence the universe is $\Sort{\imax(1, 0)} = \Sort{0}$: a statement quantifying over all propositions is itself a proposition.
For the second, $u = 2$ and $A \to A : \Sort{1}$ so $v = 1$, giving $\Sort{\imax(2,1)} = \Sort{2}$. [Chapter 13](13-universes.md) explains the asymmetry.

</details>

</div>

<div class="summary-box" markdown="1">

What to remember

- A context is an ordered list of distinct assumptions $x : A$; the judgment $\Gamma \vdash t : A$ says that $t$ has type $A$ under those assumptions.
- There is one rule per kind of term, plus T-Conv, which identifies types up to computation and bound-variable renaming.
- T-App is where hypotheses are used and where substitution happens; T-Conv is the only rule not triggered by the shape of the term.
- Substitution and definitional equality are treated as black boxes until Part III.

</div>
