<div class="lead" markdown="1">

This chapter runs Algorithm 5.1 by hand on a handful of small terms and relates each run to the typing rules. The examples are chosen to show the algorithm doing each of its jobs: building a derivation, catching a wrong proof, using a hypothesis, instantiating a universal statement, and computing inside a type. Every trace below can be reproduced in the kernel with the playgrounds.

</div>

To verify a proof $t$ of a theorem $T$, the kernel calls $\Check(\cdot, t, T)$, which calls $\Infer(\cdot, t)$ and compares the result with $T$. The traces show the recursive calls that $\Infer$ makes, with the typing rule each call corresponds to. Expand or collapse the nodes to follow the recursion.

## The identity proof

Let $\Gamma_1 = P : \Sort{0}$ and $\Gamma_2 = \Gamma_1, h : P$. The derivation of the opening example of [Chapter 1](01-propositions-as-types.md), with the well-formedness premises omitted, is

$$
\dfrac{
  \dfrac{}{\cdot \vdash \Sort{0} : \Sort{1}}\rulename{T-Sort}
  \qquad
  \dfrac{
    \dfrac{}{\Gamma_1 \vdash P : \Sort{0}}\rulename{T-Var}
    \qquad
    \dfrac{}{\Gamma_2 \vdash h : P}\rulename{T-Var}
  }{\Gamma_1 \vdash \tLam{h}{P}{h} : P \to P}\rulename{T-Lam}
}{\cdot \vdash \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}} : \tPi{P}{\Sort{0}}{P \to P}}\rulename{T-Lam}
$$

The algorithm builds the same derivation from the bottom up. The call $\Infer(\cdot, \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}})$ proceeds as follows.

<ul class="trace">
<li>$\Infer(\cdot,\; \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}})$ <span class="rule">T-Lam</span>
  <ul>
  <li>$\InferSort(\cdot,\; \Sort{0})$: $\Infer$ returns $\Sort{1}$, so the annotation is a type <span class="rule">T-Sort</span></li>
  <li>$\Freshen$ leaves $P$ unchanged, since the context is empty</li>
  <li>$\Infer(\Gamma_1,\; \tLam{h}{P}{h})$ <span class="rule">T-Lam</span>
    <ul>
    <li>$\InferSort(\Gamma_1,\; P)$: $\Infer$ looks up $P$ and returns $\Sort{0}$ <span class="rule">T-Var</span></li>
    <li>$\Freshen$ leaves $h$ unchanged</li>
    <li>$\Infer(\Gamma_2,\; h)$ looks up $h$ and returns $P$ <span class="rule">T-Var</span></li>
    <li class="result">returns $\tPi{h}{P}{P}$</li>
    </ul>
  </li>
  <li class="result">returns $\tPi{P}{\Sort{0}}{\tPi{h}{P}{P}}$</li>
  </ul>
</li>
</ul>

Each call that returns a type corresponds to one node of the derivation tree, and no call uses computation. Finally, $\Check$ compares the result with the stated type $\tPi{P}{\Sort{0}}{P \to P}$. The two differ only in the name of one bound variable, because $P \to P$ abbreviates $\tPi{\_}{P}{P}$ and neither $h$ nor $\_$ occurs in the body. So $\IsDefEq$ succeeds and the proof is accepted.

The same run, recorded by the kernel itself. The call view matches the list above; the proof-tree view matches the derivation.

<div class="explorer" data-kind="derive" data-term="fun (P : Sort 0) => fun (h : P) => h"></div>

<div class="playground" data-file="examples/identity.leanmini"><pre># The same proof, given as a complete term. The kernel infers its type
# and compares it with the goal.
goal forall (P : Sort 0), P -> P
exact fun (P : Sort 0) => fun (h : P) => h
qed</pre></div>

## A wrong proof

Suppose a user claims that $t = \tLam{P}{\Sort{0}}{\tLam{h}{P}{P}}$ proves $\tPi{P}{\Sort{0}}{P \to P}$. The body returns the proposition $P$ instead of the proof $h$. The kernel calls $\Check(\cdot, t, \tPi{P}{\Sort{0}}{P \to P})$, which first calls $\Infer$. The calls are the same as above, except that the last one, $\Infer(\Gamma_2, P)$, returns $\Sort{0}$. So $\Infer$ *succeeds*, with

$$
\Infer(\cdot, t) \;=\; \tPi{P}{\Sort{0}}{\tPi{h}{P}{\Sort{0}}}.
$$

The term $t$ is perfectly well typed; it is just not a proof of the claimed proposition. $\Check$ then compares the two types. Neither can compute any further, and no renaming of bound variables makes them equal: the innermost body is $\Sort{0}$ on one side and $P$ on the other. So $\IsDefEq$ fails and $\Check$ reports a type mismatch. ([Chapter 11](11-substitution-alpha.md#alpha-equivalence) replays this comparison step by step with the algorithm that $\IsDefEq$ uses.)

The error is found only because the user *stated* the proposition to be proved. A kernel that only ran $\Infer$ would accept $t$ and silently assign it a different type. This is why `goal` comes first in every script, and why `qed` checks against it.

<div class="explorer" data-kind="derive" data-term="fun (P : Sort 0) => fun (h : P) => P"></div>

<div class="playground" data-file="wrong-proof"><pre>goal forall (P : Sort 0), P -> P
exact fun (P : Sort 0) => fun (h : P) => P
qed</pre></div>

<aside class="warning" markdown="1">

"Well typed" and "proves the theorem" are different properties. Every closed term that passes $\Infer$ proves *something*, namely its inferred type. The kernel's job is to confirm that the something is what was claimed. Tactics ([Chapter 10](10-tactics.md)) are designed so that the claim is fixed before any term is built.

</aside>

## Using a hypothesis: modus ponens

The examples so far never apply a function. Consider checking

$$
t = \tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{f}{P \to Q}{\tLam{p}{P}{f\;p}}}}
\quad\text{against}\quad
\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{(P \to Q) \to P \to Q}},
$$

which says "if $P$ implies $Q$ and $P$ holds, then $Q$ holds". The four $\lambda$s extend the context to $\Gamma = P : \Sort{0},\; Q : \Sort{0},\; f : P \to Q,\; p : P$ as before. The body $f\;p$ reaches the application case of $\Infer$:

<ul class="trace">
<li>$\Infer(\Gamma,\; f\;p)$ <span class="rule">T-App</span>
  <ul>
  <li>$\Infer(\Gamma,\; f)$ returns $P \to Q$, that is, $\tPi{\_}{P}{Q}$. $\Whnf$ leaves it unchanged, and it is a $\Pi$ <span class="rule">T-Var</span></li>
  <li>$\Check(\Gamma,\; p,\; P)$ succeeds, since $p : P$ is in $\Gamma$ <span class="rule">T-Var, T-Conv</span></li>
  <li class="result">returns $\subst{Q}{\_}{p} = Q$. The name $\_$ does not occur in $Q$, so the substitution does nothing</li>
  </ul>
</li>
</ul>

If the user had written $f\;f$ instead, the second step would call $\Check(\Gamma, f, P)$, which fails because $P \to Q$ is not $P$: a function cannot be fed to itself here. Try it: change `f p` to `f f` below.

<div class="explorer" data-kind="derive" data-term="fun (P : Sort 0) => fun (Q : Sort 0) => fun (f : P -> Q) => fun (p : P) => f p"></div>

<div class="playground" data-file="modus-ponens"><pre>goal forall (P : Sort 0), forall (Q : Sort 0), (P -> Q) -> P -> Q
exact fun (P : Sort 0) => fun (Q : Sort 0) => fun (f : P -> Q) => fun (p : P) => f p
qed</pre></div>

## Instantiating a universal statement

In a *dependent* application the substitution in T-App does real work. Let $\mathit{id} = \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}}$ be the proof from the first example, and let $\Gamma = Q : \Sort{0}$. Then $\Infer(\Gamma, \mathit{id}\;Q)$:

<ul class="trace">
<li>$\Infer(\Gamma,\; \mathit{id}\;Q)$ <span class="rule">T-App</span>
  <ul>
  <li>$\Infer(\Gamma,\; \mathit{id})$ returns $\tPi{P}{\Sort{0}}{\tPi{h}{P}{P}}$, already a $\Pi$ <span class="rule">T-Lam</span></li>
  <li>$\Check(\Gamma,\; Q,\; \Sort{0})$ succeeds <span class="rule">T-Var</span></li>
  <li class="result">returns $\subst{(\tPi{h}{P}{P})}{P}{Q} = \tPi{h}{Q}{Q}$, that is, $Q \to Q$</li>
  </ul>
</li>
</ul>

Logically, this is $\forall$-elimination: from "every proposition implies itself" we obtain "$Q$ implies $Q$". The type of the result depends on the *value* of the argument $Q$, which is what the dependent $\Pi$-type expresses and why T-App substitutes. In the explorer, $\mathit{id}$ is a defined constant and $Q$ comes from the context; the note on the T-App node records the substitution.

<div class="explorer" data-kind="derive" data-term="id Q" data-ctx="Q : Sort 0"><pre class="prelude">def id : forall (P : Sort 0), P -> P := fun (P : Sort 0) => fun (h : P) => h</pre></div>

## Conversion

Recall $\mathit{Id} = \tLam{X}{\Sort{0}}{X}$ from [Chapter 3](03-typing-rules.md). The core system has no definitions, so $\mathit{Id}\;P$ is shorthand for the term $(\tLam{X}{\Sort{0}}{X})\;P$. Consider checking

$$
t = \tLam{P}{\Sort{0}}{\tLam{h}{\mathit{Id}\;P}{h}}
\quad\text{against}\quad
\tPi{P}{\Sort{0}}{P \to P}.
$$

$\Infer$ first checks that the annotation $\mathit{Id}\;P$ is a type. $\InferSort(\Gamma_1, \mathit{Id}\;P)$ reaches the application case of $\Infer$: the function $\tLam{X}{\Sort{0}}{X}$ has type $\tPi{X}{\Sort{0}}{\Sort{0}}$, the argument $P$ passes $\Check(\Gamma_1, P, \Sort{0})$, and the result is $\subst{\Sort{0}}{X}{P} = \Sort{0}$. So $\mathit{Id}\;P$ is a type, and a proposition. The body $h$ then has type $\mathit{Id}\;P$, so

$$
\Infer(\cdot, t) \;=\; \tPi{P}{\Sort{0}}{\tPi{h}{\mathit{Id}\;P}{\mathit{Id}\;P}}.
$$

Renaming bound variables alone does not turn this into $\tPi{P}{\Sort{0}}{P \to P}$. But $\IsDefEq$ computes both sides before comparing them, and $\mathit{Id}\;P \betared P$, so the inferred type becomes $\tPi{P}{\Sort{0}}{\tPi{h}{P}{P}}$ and the comparison succeeds as in the first example. In the typing rules, this step is a single use of T-Conv at the root of the derivation:

$$
\dfrac{
  \cdot \vdash t : \tPi{P}{\Sort{0}}{\mathit{Id}\;P \to \mathit{Id}\;P}
  \qquad
  \cdot \vdash \tPi{P}{\Sort{0}}{P \to P} : \Sort{0}
  \qquad
  \tPi{P}{\Sort{0}}{\mathit{Id}\;P \to \mathit{Id}\;P} \conv \tPi{P}{\Sort{0}}{P \to P}
}{\cdot \vdash t : \tPi{P}{\Sort{0}}{P \to P}}\rulename{T-Conv}
$$

The algorithm never decides *where* to apply T-Conv. As described in [Chapter 5](05-algorithm.md), conversion is hidden in the call to $\IsDefEq$, which runs only where two types are compared.

The live derivation shows where the computation happens: the annotation $\mathit{Id}\;P$ is checked by T-App, and the inferred type still contains $\mathit{Id}\;P$ until $\Check$ compares it with the goal.

<div class="explorer" data-kind="derive" data-term="fun (P : Sort 0) => fun (h : (fun (X : Sort 0) => X) P) => h"></div>

<div class="playground" data-file="conversion"><pre># The annotation of h is (fun (X : Sort 0) => X) P, which computes to P.
goal forall (P : Sort 0), P -> P
exact fun (P : Sort 0) => fun (h : (fun (X : Sort 0) => X) P) => h
qed</pre></div>

## Exercises

Running $\Infer$ on these by hand, as in the examples above, is a good check of one's understanding of the algorithm. Each can also be tried in a playground.

<div class="exercise" markdown="1">

Prove $\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{P \to Q \to P}}$.

<details markdown="1">
<summary>Solution</summary>

One answer is $\tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{p}{P}{\tLam{q}{Q}{p}}}}$. The proof never uses $q$: the system allows hypotheses to go unused.

</details>

</div>

<div class="exercise" markdown="1">

Prove that implication is transitive:
$\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{\tPi{R}{\Sort{0}}{(P \to Q) \to (Q \to R) \to P \to R}}}$.

<details markdown="1">
<summary>Solution</summary>

One answer ends in $\tLam{f}{P \to Q}{\tLam{g}{Q \to R}{\tLam{p}{P}{g\;(f\;p)}}}$; it uses the application case twice, first for $f\;p : Q$ and then for $g\;(f\;p) : R$.

```leanmini
goal forall (P : Sort 0), forall (Q : Sort 0), forall (R : Sort 0), (P -> Q) -> (Q -> R) -> P -> R
exact fun (P : Sort 0) => fun (Q : Sort 0) => fun (R : Sort 0) => fun (f : P -> Q) => fun (g : Q -> R) => fun (p : P) => g (f p)
qed
```

</details>

</div>

<div class="exercise" markdown="1">

Explain why $\tLam{P}{\Sort{0}}{\tLam{h}{P}{h\;h}}$ is rejected, and at which line of Algorithm 5.1.

<details markdown="1">
<summary>Solution</summary>

In the context $P : \Sort{0}, h : P$, the body $h\;h$ reaches the application case. $\Infer$ returns $P$ for the function $h$, and $\Whnf(P) = P$ is a variable, not a $\Pi$. The algorithm fails at the line `else fail "not a function"`: a proof of $P$ is not something that can be applied. In Rust the message is `application of non-function`.

</details>

</div>

<div class="summary-box" markdown="1">

What to remember

- A run of $\Infer$ mirrors a derivation tree; each returning call is one node.
- $\Infer$ can succeed on a term that does not prove the stated theorem. $\Check$ against the stated type is what catches it.
- T-App is where hypotheses are used (modus ponens) and where universal statements are instantiated (substitution into the body of a $\Pi$).
- Computation inside types is handled entirely by $\IsDefEq$; the algorithm never chooses where to apply T-Conv.

</div>
