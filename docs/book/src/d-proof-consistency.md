<div class="lead" markdown="1">

[Chapter 14](14-properties.md) states that the core system is consistent: no closed term has type $\tPi{P}{\Sort{0}}{P}$ (Theorem 14.5). This appendix gives the full proof, including the standard facts about typing and conversion that the argument uses. It concerns the core system: the rules of Figure 3.1 with the universes of [Chapter 13](13-universes.md), without the constants of Part II.

</div>

## The idea

The proof combines a deep theorem with an elementary argument. The deep theorem is strong normalization: every well-typed term reduces to a normal form. Together with subject reduction, it means that if any closed term had type $\tPi{P}{\Sort{0}}{P}$, a *normal* closed term would too. The elementary argument is a case analysis showing that no normal closed term can have that type.

The case analysis runs in two rounds. First, the normal form must be a $\lambda$, because nothing else closed and normal can have a $\Pi$ type. Second, its body must be a term of type $P$ in the context $P : \Sort{0}$, and no normal term can be, because the only variable in scope has type $\Sort{0}$, which is neither $P$ nor a function type.

To make the case analysis rigorous, we need to know what the type of a term of each shape looks like (the *generation* lemma), and that terms of different shapes are never convertible (a consequence of *confluence*). Those facts are collected first.

## Facts about the type system

Besides subject reduction and strong normalization from Chapter 14, the proof uses the following standard properties of Pure Type Systems [Barendregt 1992]. Subject reduction extends from one step to any number of steps by induction on the number of steps.

<div class="lemma" markdown="1">

**Lemma D.1 (Standard properties).**

(a) *Generation.* If $\Gamma \vdash t : T$, then, depending on the shape of $t$:

- if $t = x$, then $(x : A) \in \Gamma$ and $T \conv A$ for some $A$;
- if $t = \Sort{u}$, then $T \conv \Sort{(u+1)}$;
- if $t = \tPi{x}{A}{B}$, then $T \conv \Sort{w}$ for some $w$;
- if $t = \tLam{x}{A}{s}$, then $\Gamma, x : A \vdash s : B$ and $T \conv \tPi{x}{A}{B}$ for some $B$;
- if $t = f\;a$, then $\Gamma \vdash f : \tPi{x}{A}{B}$ and $\Gamma \vdash a : A$ for some $x$, $A$, and $B$.

(b) *Confluence.* If $s \conv t$, then $s$ and $t$ reduce to a common term. Consequently: $\tPi{x}{A}{B} \conv \tPi{y}{A'}{B'}$ implies $A \conv A'$ and $\subst{B}{x}{z} \conv \subst{B'}{y}{z}$ for a fresh $z$; and no two of a variable, a universe, and a $\Pi$ are convertible.

(c) *Substitution.* If $s \conv t$, then $\subst{s}{z}{a} \conv \subst{t}{z}{a}$.

</div>

Generation is the typing rules read backwards: it says that the only way to type a term of a given shape is the rule for that shape, possibly followed by uses of T-Conv. That is why each case says "$T \conv \ldots$" rather than "$T = \ldots$".

The consequences in (b) hold because a variable and a universe do not reduce at all, a $\Pi$ reduces only to a $\Pi$ (reduction happens inside its annotation or body, never at its root), and two terms with a common reduct must therefore have the same outermost shape.

## Shapes of normal terms

Recall from [Chapter 12](12-reduction-conversion.md) that every term is a spine $h\;a_1 \cdots a_n$ whose head $h$ is not an application. The next lemma classifies normal terms by their head. Its role is to leave only four possibilities for the normal form in the main proof, each of which can then be ruled out.

<div class="lemma" markdown="1">

**Lemma D.2 (Normal forms).** Let $n$ be a normal term with $\Gamma \vdash n : T$. Then $n$ is a universe, a $\Pi$, a $\lambda$, or a *neutral* term $x\;a_1 \cdots a_k$ with $k \ge 0$ whose head $x$ is a variable in $\dom(\Gamma)$. And if $k \ge 1$, then $\Gamma \vdash x : C$ for some $C$ that is convertible to a $\Pi$.

</div>

<div class="proof" markdown="1">

Write $n = h\;a_1 \cdots a_k$ with $h$ not an application.

If $k = 0$, then $n = h$ is a universe, a $\Pi$, a $\lambda$, or a variable, since those are the only shapes other than application. A variable is in $\dom(\Gamma)$ by generation.

Let $k \ge 1$. Applying the generation lemma for application $k$ times, from the outside in, shows that every prefix $h\;a_1 \cdots a_i$ is typable, and in particular, from the innermost application $h\;a_1$, that $\Gamma \vdash h : \tPi{y}{A}{B}$ for some $y$, $A$, and $B$. Now consider the shape of $h$. It is not a $\lambda$, since $h\;a_1$ would then be a $\beta$-redex inside the normal term $n$. It is not a universe or a $\Pi$ either: by generation, its type would be convertible to a universe, and by confluence a universe is not convertible to $\tPi{y}{A}{B}$. So $h$ is a variable $x$, which is in $\dom(\Gamma)$ by generation, and $\Gamma \vdash x : \tPi{y}{A}{B}$, which is the required $C$.

</div>

## Proof of Theorem 14.5

<div class="theorem" markdown="1">

**Theorem 14.5 (Consistency).** There is no closed term $t$ with $\cdot \vdash t : \tPi{P}{\Sort{0}}{P}$.

</div>

<div class="proof" markdown="1">

Suppose that $\cdot \vdash t : \tPi{P}{\Sort{0}}{P}$. By strong normalization, $t$ reduces to a normal term $n$, and by subject reduction, $\cdot \vdash n : \tPi{P}{\Sort{0}}{P}$. We show that no such $n$ exists, using Lemma D.2 twice.

*The normal form is a $\lambda$.* By Lemma D.2, $n$ is a universe, a $\Pi$, a $\lambda$, or a neutral term.

- It is not neutral, because its head would be a variable in the empty context, and there is none.
- It is not a universe or a $\Pi$, because generation would make $\tPi{P}{\Sort{0}}{P}$ convertible to a universe, which confluence rules out.

So $n = \tLam{x}{A}{s}$. By generation, $x : A \vdash s : B$ and $\tPi{P}{\Sort{0}}{P} \conv \tPi{x}{A}{B}$ for some $B$. By confluence, $A \conv \Sort{0}$ and $\subst{P}{P}{z} \conv \subst{B}{x}{z}$ for a fresh $z$, that is, $z \conv \subst{B}{x}{z}$. Substituting $x$ for $z$ on both sides, which preserves convertibility by part (c) of Lemma D.1, gives $x \conv B$. The body $s$ is normal, because it is a subterm of the normal term $n$. In short: $x : A \vdash s : B$ with $A \conv \Sort{0}$ and $B \conv x$.

*The body cannot exist.* Let $\Gamma = x : A$. By Lemma D.2, $s$ is a universe, a $\Pi$, a $\lambda$, or a neutral term.

- If $s$ is a universe or a $\Pi$, generation makes $B$ convertible to a universe; if $s$ is a $\lambda$, it makes $B$ convertible to a $\Pi$. But $B \conv x$, and by confluence a variable is convertible to neither.
- If $s$ is neutral, its head is a variable in $\dom(\Gamma) = \{x\}$, so $s = x\;a_1 \cdots a_k$. If $k = 0$, then $s = x$, and generation gives $B \conv A$. Then $x \conv B \conv A \conv \Sort{0}$, but a variable is not convertible to a universe. If $k \ge 1$, Lemma D.2 gives $\Gamma \vdash x : C$ with $C$ convertible to a $\Pi$, and generation for the variable $x$ gives $C \conv A \conv \Sort{0}$. Then a $\Pi$ is convertible to a universe, which confluence rules out.

Every case leads to a contradiction, so no closed term has type $\tPi{P}{\Sort{0}}{P}$.

</div>

In words: the only variable available inside the $\lambda$ is $x$, whose type is $\Sort{0}$. It can neither be returned, since $\Sort{0}$ is not $x$, nor be applied to anything, since $\Sort{0}$ is not a function type. Every other normal term has a universe or a $\Pi$ as its type, and $x$ is neither. The argument relies on strong normalization to reduce the question to normal terms; that step is where all the difficulty lies.

<aside class="note" markdown="1">

The second half of the proof, the analysis of normal terms, does not use strong normalization and does not depend on the universe structure. It carries over unchanged to a system with $\mathsf{Type} : \mathsf{Type}$. That is how Chapter 13 concludes that Hurkens' term ([Appendix C](c-hurkens.md)), which has type $\tPi{P}{\mathsf{Type}}{P}$ in that system, cannot have a normal form: if it did, the analysis would rule it out. So in the inconsistent system it is strong normalization that fails, not generation or confluence.

</aside>

<aside class="history" markdown="1">

With the inductive types of Part II, normal forms also include stuck recursor applications, such as $\NatRec{u}\;M\;z\;s\;n$ with $n$ a variable, and the short case analysis above no longer suffices on its own. Consistency of the Calculus of Inductive Constructions, of which the extended system is a fragment, follows from strong normalization by a more careful analysis of normal forms [Werner 1994].

</aside>

<div class="summary-box" markdown="1">

What to remember

- Consistency is proved by combining strong normalization and subject reduction (to pass to a normal form) with a case analysis on the shape of normal terms.
- The case analysis uses two standard facts: generation (the typing rules read backwards) and confluence (terms of different outermost shapes are never convertible).
- A normal closed term of type $\tPi{P}{\Sort{0}}{P}$ would have to be a $\lambda$ whose body has type $x$ in the context $x : \Sort{0}$, and no normal term does.
- The hard part is strong normalization; the shape analysis alone also applies to $\mathsf{Type} : \mathsf{Type}$, and shows that Hurkens' term has no normal form.

</div>
