<div class="lead" markdown="1">

So far we have claimed that the kernel's algorithm terminates and that it never accepts a proof of False. Both claims rely on theorems about the type system, whose proofs are much harder than the kernel's own computations. This chapter states those theorems, explains why each matters, and sketches how they establish consistency; Appendix D gives the full proof.

</div>

## The core system

The theorems below concern the *core* system: the rules of Figure 3.1, with the universes of [Chapter 13](13-universes.md) and without the constants of Part II. This is a **Pure Type System** in the sense of Barendregt: the Calculus of Constructions [Coquand 1988] with a hierarchy of predicative universes above its impredicative $\Sort{0}$, close to Luo's Extended Calculus of Constructions [Luo 1990]. The first three properties hold for every functional Pure Type System [Barendregt 1992]. Strong normalization is much harder in the presence of impredicativity and needs Girard's method of reducibility candidates [Girard 1972; Coquand 1988; Luo 1990]. The end of the chapter says what changes with inductive types.

## Four properties

<div class="theorem" markdown="1">

**Theorem 14.1 (Uniqueness of types).** If $\Gamma \vdash t : A$ and $\Gamma \vdash t : B$, then $A \conv B$.

</div>

A term has, up to conversion, one type. $\Infer$ depends on this: there is a single answer for it to compute, and $\Check$ can compare against it without worrying that some other derivation would have produced a different, non-convertible type.

<div class="theorem" markdown="1">

**Theorem 14.2 (Type correctness).** If $\Gamma \vdash t : A$, then either $A = \Sort{u}$ for some $u$, or $\Gamma \vdash A : \Sort{u}$ for some $u$.

</div>

The type of a well-typed term is itself a type (or is a universe, which has a type by T-Sort but need not be written as one). So the result of $\Infer$ can always be fed back into $\InferSort$, and contexts built by the algorithm stay well formed.

<div class="theorem" markdown="1">

**Theorem 14.3 (Subject reduction).** If $\Gamma \vdash t : A$ and $t \betared t'$, then $\Gamma \vdash t' : A$.

</div>

Computation preserves types. This is what justifies T-Conv and the whole strategy of deciding equality by normalization: reducing a term never takes it out of its type, so comparing normal forms compares the right things.

<div class="theorem" markdown="1">

**Theorem 14.4 (Strong normalization).** If $\Gamma \vdash t : A$, then every sequence of beta-reductions starting from $t$ is finite.

</div>

Every well-typed term reaches a normal form, whatever order reductions are performed in. This is the deep one. $\Whnf$, $\Normalize$, and therefore $\IsDefEq$ and $\Infer$ terminate on well-typed input because of it, and the next section shows that consistency rests on it too.

The four properties support the two guarantees in a definite pattern, drawn below: the arrows read "is needed for".

<div class="rulebox" markdown="1">

<p class="caption">Figure 14.1. How the metatheory fits together.</p>

<svg class="dep-diagram" viewBox="0 0 760 300" role="img" aria-label="Dependency diagram: uniqueness of types and type correctness support the algorithm; subject reduction and strong normalization support both decidability and consistency; the normal-form analysis joins strong normalization for consistency.">
<defs><marker id="arr" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0 0L10 5L0 10z" fill="currentColor"/></marker></defs>
<g class="dep-box"><rect x="20" y="20" width="160" height="54" rx="8"/><text x="100" y="42" text-anchor="middle">uniqueness</text><text x="100" y="60" text-anchor="middle">of types (14.1)</text></g>
<g class="dep-box"><rect x="200" y="20" width="160" height="54" rx="8"/><text x="280" y="42" text-anchor="middle">type</text><text x="280" y="60" text-anchor="middle">correctness (14.2)</text></g>
<g class="dep-box"><rect x="400" y="20" width="160" height="54" rx="8"/><text x="480" y="42" text-anchor="middle">subject</text><text x="480" y="60" text-anchor="middle">reduction (14.3)</text></g>
<g class="dep-box hot"><rect x="580" y="20" width="160" height="54" rx="8"/><text x="660" y="42" text-anchor="middle">strong</text><text x="660" y="60" text-anchor="middle">normalization (14.4)</text></g>
<g class="dep-box"><rect x="110" y="140" width="180" height="54" rx="8"/><text x="200" y="162" text-anchor="middle">Infer and Check are</text><text x="200" y="180" text-anchor="middle">well defined (Ch. 5)</text></g>
<g class="dep-box"><rect x="470" y="140" width="180" height="54" rx="8"/><text x="560" y="162" text-anchor="middle">analysis of</text><text x="560" y="180" text-anchor="middle">normal forms (App. D)</text></g>
<g class="dep-box goal"><rect x="110" y="236" width="180" height="48" rx="8"/><text x="200" y="265" text-anchor="middle">decidability</text></g>
<g class="dep-box goal"><rect x="470" y="236" width="180" height="48" rx="8"/><text x="560" y="265" text-anchor="middle">consistency (14.5)</text></g>
<g class="dep-arrows">
<path d="M100 74 L170 140"/><path d="M280 74 L230 140"/>
<path d="M480 74 L300 150"/><path d="M660 74 L300 160"/>
<path d="M480 74 L540 140"/><path d="M660 74 L580 140"/>
<path d="M200 194 L200 236"/><path d="M560 194 L560 236"/>
<path d="M660 74 L620 236"/>
</g>
</svg>

</div>

Together these give the two guarantees we want from a kernel.

- **Decidability.** Algorithm 5.1 terminates on every input, so whether a proof is correct can always be determined.
- **Consistency.** No closed term proves False.

<aside class="note" markdown="1">

Strong normalization is stated for well-typed terms only. The kernel can receive ill-typed terms, and $\Whnf$ is called during inference before typing is established. That is why the implementation has a step budget: it is the engineering substitute for the theorem on inputs the theorem does not cover.

</aside>

## Consistency

<div class="theorem" markdown="1">

**Theorem 14.5 (Consistency).** There is no closed term $t$ with $\cdot \vdash t : \tPi{P}{\Sort{0}}{P}$.

</div>

The argument has two halves, and their shape is visible without the details.

**Reduce to normal forms.** By strong normalization, such a term $t$ would have a normal form $n$, and by subject reduction, $n$ would have the same type. So it suffices to show that no *normal* closed term has type $\tPi{P}{\Sort{0}}{P}$. This step is where all the difficulty lies, because it uses Theorem 14.4.

**Analyse normal forms.** A normal term is a universe, a $\Pi$, a $\lambda$, or a variable applied to some arguments (a *neutral* term). A closed normal term whose type is a $\Pi$ must be a $\lambda$: it cannot be neutral, since no variable is in scope, and universes and $\Pi$-types have a universe as their type, not a $\Pi$. So $n = \tLam{P}{\Sort{0}}{s}$ with $P : \Sort{0} \vdash s : P$ and $s$ normal. Now ask what $s$ can be. A universe, a $\Pi$, or a $\lambda$ would have a universe or a $\Pi$ as its type, not the variable $P$. A neutral term would have to start with a variable in scope, and the only one is $P$ itself, whose type is $\Sort{0}$: it is not $P$, so $s$ cannot be $P$; and it is not a function type, so $P$ cannot be applied to anything. Every case is impossible.

[Appendix D](d-proof-consistency.md) carries this out carefully, including the standard facts about typing and conversion (generation, confluence, substitution) that the case analysis silently uses.

<aside class="intuition" markdown="1">

In words: to prove $\tPi{P}{\Sort{0}}{P}$ you would have to produce a proof of an *arbitrary* proposition $P$ with nothing to work from but the name $P$. Normal forms make "nothing to work from" literal: a normal proof cannot hide a computation that would conjure something up, so it must be built directly from what is in scope, and nothing in scope has type $P$. Strong normalization is what guarantees that every proof *can* be put in this honest form.

</aside>

## With inductive types

The iota-rules of Part II do not overlap with each other or with beta, so reduction remains confluent. Subject reduction, strong normalization, and consistency are known for the Calculus of Inductive Constructions [Werner 1994], of which our system with inductive types is a small fragment. The short consistency argument above no longer suffices by itself, because normal forms now include stuck recursor applications such as $\NatRec{0}\;M\;z\;s\;n$ with $n$ a variable; consistency follows from strong normalization by a more careful analysis of normal forms, in which a neutral term may also be headed by a constant.

Each of the acceptance conditions of [Chapter 8](08-inductive-recipe.md) corresponds to a way this analysis could fail: without positivity, iota-reduction can loop and strong normalization is lost; without the universe condition, a type could contain its own universe and the paradox of Chapter 13 returns; without the elimination restriction on propositions, proof irrelevance (which Lean assumes) would be refuted.

Lean's full theory, with definitional proof irrelevance, universe polymorphism, quotient types, and general nested and mutual inductive types, has subtler metatheory; Carneiro's thesis [Carneiro 2019] is the reference. The central structure, strong normalization plus an analysis of normal forms, is the same.

<aside class="lean" markdown="1">

Lean's kernel, like ours, does not *prove* any of this; it assumes it. The theorems are about the type system, not about the code, and they are established once, on paper, for the system as designed. What the code must do is implement that system faithfully. The compact kernel of this book, and the even more compact description of it in Figure 3.1, Chapter 8, and Algorithm 12.1, is what lets a human reader check "faithfully".

</aside>

## Exercises

<div class="exercise" markdown="1">

Which of the four properties does a kernel with $\mathsf{Type} : \mathsf{Type}$ lose, according to Chapter 13?

<details markdown="1">
<summary>Solution</summary>

Strong normalization (Hurkens' term has no normal form) and consistency (it has type $\tPi{P}{\mathsf{Type}}{P}$). Uniqueness of types and subject reduction still hold; they are properties of the rule shapes, not of the universe structure.

</details>

</div>

<div class="exercise" markdown="1">

The consistency argument says a closed normal term of $\Pi$-type must be a $\lambda$. Why does this fail once constants are added, and what replaces it?

<details markdown="1">
<summary>Solution</summary>

A constant such as $\suc$ or $\NatRec{0}$ is closed and can head a normal term, so a closed normal term of $\Pi$-type may be, for instance, $\suc$ itself or a stuck recursor application. The analysis must then also consider neutral terms headed by constants and show, using the specific types the schema assigns to constructors and recursors, that none of them can inhabit $\tPi{P}{\Sort{0}}{P}$. Werner's thesis does this for the Calculus of Inductive Constructions.

</details>

</div>

<div class="summary-box" markdown="1">

What to remember

- Uniqueness of types and type correctness make $\Infer$ well defined; subject reduction justifies deciding equality by normalization; strong normalization makes everything terminate.
- Consistency follows from strong normalization plus a case analysis of normal forms: nothing in scope can prove an arbitrary $P$.
- Inductive types preserve all four properties provided the acceptance conditions hold; each condition blocks a specific failure.
- The kernel assumes these theorems rather than proving them. Its job is to implement the system they are about, faithfully and legibly.

</div>
