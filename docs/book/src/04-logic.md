<div class="lead" markdown="1">

Chapter 3 presented eight typing rules and promised that they are rules of logic. This chapter keeps that promise. It picks a concrete logic, translates its formulas into types, and shows that every proof in the logic becomes a term that the kernel accepts. It then identifies the property, consistency, that a kernel must have before it can be trusted at all.

</div>

## A logic to compare against

The logic has formulas built from proposition variables $P, Q, \ldots$ by implication and by quantification over propositions:

$$
\varphi, \psi \;::=\; P \;\mid\; \varphi \to \psi \;\mid\; \forall P.\,\varphi
$$

This is **second-order propositional logic**: "second-order" because $\forall$ ranges over propositions rather than over individuals. It is small, but far from trivial. Conjunction, disjunction, negation, and falsity can all be defined inside it, for example $\bot = \forall P.\,P$ and $\varphi \wedge \psi = \forall R.\,(\varphi \to \psi \to R) \to R$.

Proofs in this logic are natural-deduction derivations of judgments $\Delta \vdash \varphi$, where $\Delta$ is a list of hypotheses. The rules are the ones in the left column of Figure 4.1 below: use a hypothesis, introduce and eliminate implication, introduce and eliminate the quantifier.

## Translating formulas into types

Each formula translates to a type, written $\varphi^\ast$:

$$
P^\ast = P,
\qquad
(\varphi \to \psi)^\ast = \varphi^\ast \to \psi^\ast,
\qquad
(\forall P.\,\varphi)^\ast = \tPi{P}{\Sort{0}}{\varphi^\ast}.
$$

A proposition variable becomes a type variable, implication becomes the function type, and quantification over propositions becomes a $\Pi$-type over $\Sort{0}$.

A list of hypotheses translates to a context. Besides one assumption $h_i : \varphi_i^\ast$ per hypothesis, the context must declare the proposition variables that occur anywhere in the judgment:

$$
(\varphi_1, \ldots, \varphi_n)^\ast
\;=\;
P_1 : \Sort{0}, \ldots, P_k : \Sort{0},\;
h_1 : \varphi_1^\ast, \ldots, h_n : \varphi_n^\ast,
$$

where $P_1, \ldots, P_k$ are the proposition variables free in $\Delta$ or in the conclusion $\varphi$ of the judgment $\Delta \vdash \varphi$ being translated, and $h_1, \ldots, h_n$ are fresh names. The conclusion must be included because a variable may occur only there, as $P$ does in $\cdot \vdash P \to P$.

Figure 4.1 places each logical rule next to the typing rule that implements it. The premises that merely check that a type is well formed are omitted.

<div class="rulebox" markdown="1">

<p class="caption">Figure 4.1. Natural deduction (middle column) and the typing rules that implement it (right column). In each row, $\Delta^\ast$ is the context for the conclusion.</p>

$$
\begin{array}{lcc}
\text{Hypothesis} &
\dfrac{\varphi_i \in \Delta}{\Delta \vdash \varphi_i} &
\dfrac{(h_i : \varphi_i^\ast) \in \Delta^\ast}{\Delta^\ast \vdash h_i : \varphi_i^\ast}\rulename{T-Var}
\\[18pt]
\to\text{-intro} &
\dfrac{\Delta, \varphi \vdash \psi}{\Delta \vdash \varphi \to \psi} &
\dfrac{\Delta^\ast, h : \varphi^\ast \vdash t : \psi^\ast}{\Delta^\ast \vdash \tLam{h}{\varphi^\ast}{t} : \varphi^\ast \to \psi^\ast}\rulename{T-Lam}
\\[18pt]
\to\text{-elim} &
\dfrac{\Delta \vdash \varphi \to \psi \qquad \Delta \vdash \varphi}{\Delta \vdash \psi} &
\dfrac{\Delta^\ast \vdash f : \varphi^\ast \to \psi^\ast \qquad \Delta^\ast \vdash a : \varphi^\ast}{\Delta^\ast \vdash f\;a : \psi^\ast}\rulename{T-App}
\\[18pt]
\forall\text{-intro} &
\dfrac{\Delta \vdash \varphi \qquad P \notin \FV(\Delta)}{\Delta \vdash \forall P.\,\varphi} &
\dfrac{\Delta^\ast, P : \Sort{0} \vdash t : \varphi^\ast}{\Delta^\ast \vdash \tLam{P}{\Sort{0}}{t} : \tPi{P}{\Sort{0}}{\varphi^\ast}}\rulename{T-Lam}
\\[18pt]
\forall\text{-elim} &
\dfrac{\Delta \vdash \forall P.\,\varphi}{\Delta \vdash \subst{\varphi}{P}{\psi}} &
\dfrac{\Delta^\ast \vdash f : \tPi{P}{\Sort{0}}{\varphi^\ast} \qquad \Delta^\ast \vdash \psi^\ast : \Sort{0}}{\Delta^\ast \vdash f\;\psi^\ast : \subst{\varphi^\ast}{P}{\psi^\ast}}\rulename{T-App}
\end{array}
$$

</div>

Erasing the terms from the right column gives the middle column exactly. Two details deserve comment.

In the $\forall$-intro row, the logic's side condition $P \notin \FV(\Delta)$ guarantees that no hypothesis mentions $P$, so the typing rule may add $P : \Sort{0}$ *after* the hypotheses without breaking the dependency order of the context.

In the $\forall$-elim row, the premise $\psi^\ast : \Sort{0}$ holds for *every* formula $\psi$, even one that contains $\forall$, because T-Pi places every translated formula in $\Sort{0}$. (The $\imax$ in T-Pi is responsible: $\tPi{P}{\Sort{0}}{\varphi^\ast}$ lands in $\Sort{\imax(1, 0)} = \Sort{0}$.) So a universal statement can be instantiated with any formula, as it can in the logic. [Chapter 13](13-universes.md) returns to this point, which is called impredicativity.

## Proofs are terms

<div class="theorem" markdown="1">

**Theorem 4.1 (Proofs are terms).** If $\Delta \vdash \varphi$ is provable in the logic, then $\Delta^\ast \vdash t : \varphi^\ast$ for some term $t$.

</div>

Figure 4.1 turns each step of a logical proof into a step of a typing derivation, so every proof becomes a term by induction on the proof. [Appendix A](a-proof-pat.md) states the theorem with the scoping of proposition variables made explicit and gives the full proof.

The theorem says that the type checker can check every proof of the logic. For the kernel to be *trustworthy*, we also need the opposite guarantee: it must not accept a term for a proposition that the logic refutes.

## Consistency

Define $\bot = \forall P.\,P$, "everything holds". No proof of $\bot$ exists in the logic: if each proposition variable is read as true or false, every rule preserves truth under every reading, but $\forall P.\,P$ is false under the reading that makes some $P$ false.

The type theory should agree. That is, no closed term should have the type

$$
\bot^\ast \;=\; \tPi{P}{\Sort{0}}{P}.
$$

A closed term $t$ of this type would be a disaster: for every proposition $C : \Sort{0}$, the application $t\;C$ would have type $C$, so every proposition would be provable and the kernel would be worthless.

<div class="definition" markdown="1">

**Definition 4.2 (Consistency).** A type system is *consistent* if no closed term has type $\tPi{P}{\Sort{0}}{P}$.

</div>

Consistency is the property that every design decision in this book must preserve. In particular, a design for universes is acceptable only if the system remains consistent; [Chapter 13](13-universes.md) shows a natural-looking design that fails this test, and [Chapter 14](14-properties.md) states consistency for our system as Theorem 14.5.

<aside class="note" markdown="1">

One might hope for the full converse of Theorem 4.1: every term of type $\varphi^\ast$ comes from a proof of $\varphi$. That stronger property is called *conservativity*, and it is harder to establish here, because $\Sort{0}$ also contains types that are not translations of formulas, such as $\tPi{F}{\Sort{0} \to \Sort{0}}{F\;P \to F\;P}$, and a term may pass through them on its way to $\varphi^\ast$. We do not need conservativity. Consistency is what makes the kernel's "yes" worth something, and it is enough.

</aside>

<aside class="intuition" markdown="1">

Why single out $\tPi{P}{\Sort{0}}{P}$ rather than, say, $0 = 1$? Because it is the universal counterfeit: any proof of it can be converted into a proof of anything else by a single application. If some other absurd statement had a proof, that proof could be used to build a proof of $\tPi{P}{\Sort{0}}{P}$ as well, so ruling out this one type rules out all of them.

</aside>

## Exercises

<div class="exercise" markdown="1">

Translate the formula $\forall P.\,\forall Q.\,(P \to Q) \to P \to Q$ to a type, and write the proof term that Figure 4.1 produces for the natural-deduction proof "assume $P \to Q$ and $P$; apply the first to the second".

<details markdown="1">
<summary>Solution</summary>

The type is $\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{(P \to Q) \to P \to Q}}$. Two $\forall$-intros give two outer $\lambda$s over $\Sort{0}$, two $\to$-intros give $\lambda(f : P \to Q)$ and $\lambda(p : P)$, and $\to$-elim gives the body $f\;p$:
$\tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{f}{P \to Q}{\tLam{p}{P}{f\;p}}}}$.

</details>

</div>

<div class="exercise" markdown="1">

Show that from $t : \tPi{P}{\Sort{0}}{P}$ one can build a term of type $\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{P \to Q}}$, "every proposition implies every other".

<details markdown="1">
<summary>Solution</summary>

$\tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{p}{P}{t\;Q}}}$. The hypothesis $p$ is ignored and $t\;Q : Q$ by T-App. This is the sense in which a proof of $\bot^\ast$ proves everything.

</details>

</div>

<div class="summary-box" markdown="1">

What to remember

- Second-order propositional logic translates into the type theory: $\to$ becomes the function type, $\forall P$ becomes $\Pi(P : \Sort{0})$, hypotheses become context entries.
- Theorem 4.1: every proof in the logic becomes a well-typed term. The translation is rule by rule (Figure 4.1).
- The kernel is trustworthy only if it is consistent: no closed term of type $\tPi{P}{\Sort{0}}{P}$.
- Impredicativity, via $\imax$, is what lets a universal statement be instantiated by any formula, including itself.

</div>
