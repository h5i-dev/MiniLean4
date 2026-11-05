<div class="lead" markdown="1">

[Chapter 11](11-substitution-alpha.md) gave two definitions of alpha-equivalence: a mathematical one (the smallest congruence that allows renaming a bound variable) and an algorithmic one (the rules of Figure 11.1, which walk two terms in lockstep and compare bound variables by position). Theorem 11.1 says that they agree. This appendix proves it.

</div>

## The idea

Both definitions turn out to say the same thing: *the two terms have the same de Bruijn representation*, that is, the same shape once every bound variable is replaced by the distance to its binder. So the proof goes through a third, nameless representation of terms.

- Lemma B.1 shows that the algorithm compares nameless forms. This is almost immediate, because the rules of Figure 11.1 compare positions exactly as de Bruijn indices do.
- Lemmas B.2 and B.3 establish two facts about how nameless forms behave under renaming. The key one is that renaming a bound variable does not change the nameless form.
- Lemma B.4 shows that the mathematical definition also compares nameless forms, using those two facts.
- Theorem 11.1 then follows by chaining the two lemmas through the nameless form.

The proofs are inductions on terms, with one subtlety: substitution may rename a binder, so some inductions must be on the *size* of a term rather than on its structure.

## Nameless terms

A *nameless term* is built like a term, except that binders carry no names and a bound variable is written as a number $\#i$:

$$
d ::= \Sort{u} \mid \#i \mid x \mid \Pi\,d.\,d \mid \lambda\,d.\,d \mid d\;d
$$

Free variables keep their names. The number $\#i$ means "the variable bound by the $i$-th enclosing binder, counting from the innermost at $0$". Recall from Chapter 11 that for a list of names $E$, $\mathrm{idx}(E, x)$ is the position of the last occurrence of $x$ in $E$, counted from the right starting at $0$, and is undefined if $x \notin E$.

For a list of names $E$, the nameless form $\db{t}{E}$ of a term $t$ that occurs under the binders $E$ is defined by

$$
\begin{array}{rlrl}
\db{\Sort{u}}{E} &= \Sort{u} &
\qquad \db{x}{E} &= \begin{cases} \#\mathrm{idx}(E, x) & \text{if } x \in E, \\ x & \text{otherwise,} \end{cases} \\[12pt]
\db{\tPi{x}{A}{B}}{E} &= \Pi\,\db{A}{E}.\,\db{B}{E, x} &
\qquad \db{\tLam{x}{A}{t}}{E} &= \lambda\,\db{A}{E}.\,\db{t}{E, x} \\[4pt]
\db{t_1\;t_2}{E} &= \db{t_1}{E}\;\db{t_2}{E}. & &
\end{array}
$$

Equality of nameless terms is plain syntactic equality. Note that $\db{t}{E}$ has the same outermost shape as $t$, except that a variable may become either a number or a name. Constants, introduced in [Chapter 7](07-inductive-nat.md), are left unchanged like universes and are compared by name; they add only trivial cases below and are omitted.

<aside class="intuition" markdown="1">

Writing $\db{t}{E}$ with a nonempty $E$ describes $t$ *as a subterm*, sitting under the binders listed in $E$. The whole-term case is $\db{t}{\cdot}$, with no enclosing binders. The reason to keep $E$ general is that every induction below has to pass through binders, and under a binder the subterm has one more enclosing binder than the term it came from.

</aside>

## The algorithm computes nameless forms

The first lemma relates the rules of Figure 11.1 to nameless forms. Its role is to replace the algorithmic judgment, which is defined by rules, by an equation between two terms, which is easier to reason about.

<div class="lemma" markdown="1">

**Lemma B.1 (The algorithm compares nameless forms).** For all $E_1$, $E_2$, $s$, and $t$: the judgment $E_1; E_2 \vdash s \alphaeq t$ is derivable if and only if $\db{s}{E_1} = \db{t}{E_2}$.

</div>

<div class="proof" markdown="1">

By induction on $s$, for all $t$, $E_1$, and $E_2$. For each shape of $s$, exactly one rule of Figure 11.1 can conclude the judgment, and its premises match the equations for $\db{\cdot}{}$.

If $s = \Sort{u}$, both sides hold exactly when $t = \Sort{u}$, by the rule $\alpha$-Sort and by the equation for universes.

If $s = x$, the nameless forms can be equal only if $t$ is a variable $y$, since a nameless variable (a number or a name) never equals a $\Pi$, a $\lambda$, an application, or a universe. If $x \in E_1$, then $\db{x}{E_1} = \#\mathrm{idx}(E_1, x)$, and equality holds exactly when $y \in E_2$ and $\mathrm{idx}(E_2, y) = \mathrm{idx}(E_1, x)$, which is the premise of $\alpha$-Bound. If $x \notin E_1$, then $\db{x}{E_1} = x$, and equality holds exactly when $y \notin E_2$ and $y = x$, which is the premise of $\alpha$-Free. A number never equals a name, matching the absence of a rule for a variable that is bound on one side only.

If $s = \tPi{x}{A}{B}$, equality holds exactly when $t = \tPi{y}{A'}{B'}$ with $\db{A}{E_1} = \db{A'}{E_2}$ and $\db{B}{E_1, x} = \db{B'}{E_2, y}$. By the induction hypothesis, applied to $A$ and to $B$, these two equations are exactly the premises of $\alpha$-Pi. The cases $\lambda$ and application are the same, using $\alpha$-Lam and $\alpha$-App.

</div>

## Two facts about renaming

The definition of $\alphaeq$ in Chapter 11 involves substitution: it allows replacing $\tPi{x}{A}{B}$ by $\tPi{y}{A}{\subst{B}{x}{y}}$ when $y \notin \FV(B)$. To relate it to nameless forms we need to know how $\db{\cdot}{}$ behaves when a bound variable is renamed. Two lemmas supply this.

The first says that $\db{t}{E}$ depends on $E$ only through the free variables of $t$. Its role is technical: it lets us swap one binder list for another as long as they agree on the variables that matter.

<div class="lemma" markdown="1">

**Lemma B.2 (Agreement).** If $\mathrm{idx}(E_1, v) = \mathrm{idx}(E_2, v)$ for every $v \in \FV(t)$, with both sides possibly undefined, then $\db{t}{E_1} = \db{t}{E_2}$.

</div>

<div class="proof" markdown="1">

By induction on $t$, for all $E_1$ and $E_2$. The variable case is exactly the assumption: a free variable $v$ becomes the same number, or stays the same name, on both sides. Universes are unaffected by $E$, and applications follow from the induction hypothesis for both parts.

Under a binder $x$, the lists $E_1, x$ and $E_2, x$ again agree on the free variables of the body. The variable $x$ has position $0$ in both. Any other free variable $v$ of the body is a free variable of $t$, so by assumption its position is the same in $E_1$ and $E_2$; appending $x$ increases that position by one on both sides, or leaves it undefined on both sides. The induction hypothesis for the body then applies, and the annotation is handled by the induction hypothesis with the original lists.

</div>

The second lemma does the main work of the appendix: renaming a binder does not change the nameless form. It is stated for a binder sitting at an arbitrary depth, with binder lists $E$ before it and $E'$ after it, because the induction has to go under further binders.

We use that substituting a variable for a variable preserves the size of a term, even when binders are renamed along the way; this is a routine induction on the definition of substitution.

<div class="lemma" markdown="1">

**Lemma B.3 (Renaming).** Let $y \neq x$, $y \notin \FV(B)$, and $x, y \notin E'$. Then $\db{B}{E, x, E'} = \db{\subst{B}{x}{y}}{E, y, E'}$ for every list $E$.

</div>

<div class="proof" markdown="1">

By induction on the size of $B$, for all $E$ and $E'$. Write $L_x = E, x, E'$ and $L_y = E, y, E'$; they differ in exactly one entry, at the same position.

If $B = x$, then $\subst{B}{x}{y} = y$. Since $x, y \notin E'$, the last occurrence of $x$ in $L_x$ and the last occurrence of $y$ in $L_y$ are both the distinguished entry, so $\mathrm{idx}(L_x, x)$ and $\mathrm{idx}(L_y, y)$ both equal the length of $E'$, and the nameless forms are the same number.

If $B = v$ with $v \neq x$, then $v \neq y$ because $y \notin \FV(B)$, and $\subst{B}{x}{y} = v$. The position of $v$ is the same in $L_x$ and $L_y$, since $v$ is neither of the entries that differ, or it is undefined in both.

Universes and applications are immediate from the definitions and the induction hypothesis.

Let $B = \tPi{w}{C}{D}$; the case of $\lambda$ is the same. The annotation $C$ is handled by the induction hypothesis in each case below, so we consider only the body. There are three cases, following the definition of substitution in Chapter 11.

*Case $w = x$.* The binder shadows $x$, so $\subst{B}{x}{y} = \tPi{x}{\subst{C}{x}{y}}{D}$, and we need $\db{D}{L_x, x} = \db{D}{L_y, x}$. We apply Lemma B.2. The variable $x$ has position $0$ in both lists, because it was just appended. Any other $v \in \FV(D)$ differs from $y$, since $y \notin \FV(B)$, so its position is the same in both lists, or undefined in both.

*Case $w \notin \{x, y\}$.* No renaming is needed, and $\subst{B}{x}{y} = \tPi{w}{\subst{C}{x}{y}}{\subst{D}{x}{y}}$. The induction hypothesis for $D$, with $E'$ extended by $w$ (which is allowed since $w$ is neither $x$ nor $y$), gives $\db{D}{L_x, w} = \db{\subst{D}{x}{y}}{L_y, w}$, which is what the body requires.

*Case $w = y$.* The binder would capture $y$, so substitution renames it to a fresh $z \notin \FV(D) \cup \{x, y\}$:

$$
\subst{B}{x}{y} = \tPi{z}{\subst{C}{x}{y}}{\subst{(\subst{D}{y}{z})}{x}{y}}.
$$

We need $\db{D}{L_x, y} = \db{\subst{(\subst{D}{y}{z})}{x}{y}}{L_y, z}$, and we get there in two steps. First, the induction hypothesis for $D$, renaming its last binder $y$ to $z$ (with $E$ taken as $L_x$ and $E'$ empty; the hypotheses hold because $z \neq y$, $z \notin \FV(D)$, and the list after the binder is empty), gives $\db{D}{L_x, y} = \db{\subst{D}{y}{z}}{L_x, z}$. Second, the induction hypothesis for $\subst{D}{y}{z}$, which has the size of $D$ and has no free $y$, with $E'$ extended by $z$, gives $\db{\subst{D}{y}{z}}{L_x, z} = \db{\subst{(\subst{D}{y}{z})}{x}{y}}{L_y, z}$. Chaining the two equations gives the claim.

</div>

<aside class="note" markdown="1">

The induction in Lemma B.3 is on size rather than on structure because the third case applies the induction hypothesis to $\subst{D}{y}{z}$, which is not a subterm of $B$. It has the same size as $D$, which is smaller than the size of $B$, so the induction is well founded.

</aside>

## The definition computes nameless forms

With the two renaming facts in hand, we can show that the mathematical definition of $\alphaeq$ also amounts to equality of nameless forms. The two directions are proved differently: one by the minimality of $\alphaeq$ as a congruence, the other by induction on size.

<div class="lemma" markdown="1">

**Lemma B.4 (The definition compares nameless forms).** If $s \alphaeq t$ in the sense of the definition in Chapter 11, then $\db{s}{E} = \db{t}{E}$ for every $E$. Conversely, if $\db{s}{E} = \db{t}{E}$ for some $E$, then $s \alphaeq t$.

</div>

<div class="proof" markdown="1">

*First part.* Let $s \sim t$ mean that $\db{s}{E} = \db{t}{E}$ for every $E$. This relation is an equivalence, since equality is. It is a congruence, because $\db{\cdot}{}$ is defined constructor by constructor: if the parts of two terms have equal nameless forms under the appropriate lists, so do the terms. Finally, $\sim$ contains the defining equation of $\alphaeq$: if $y \notin \FV(B)$, then

$$
\db{\tPi{x}{A}{B}}{E} = \Pi\,\db{A}{E}.\,\db{B}{E, x}
\qquad\text{and}\qquad
\db{\tPi{y}{A}{\subst{B}{x}{y}}}{E} = \Pi\,\db{A}{E}.\,\db{\subst{B}{x}{y}}{E, y},
$$

and the bodies are equal by Lemma B.3 with $E'$ empty; the case $y = x$ is trivial, since then the two terms are identical. The same holds for $\lambda$. Since $\alphaeq$ is the smallest congruence containing that equation, and $\sim$ is a congruence containing it, $s \alphaeq t$ implies $s \sim t$.

*Second part.* We use induction on the size of $s$, for all $t$ and $E$, assuming $\db{s}{E} = \db{t}{E}$.

If $s$ is a variable, so is $t$, since nameless forms of other shapes are never a number or a name. If both nameless forms are the number $\#i$, both variables are the entry at position $i$ of $E$, so $s = t$. If both are names, then $s = t$ directly. In either case $s \alphaeq t$ by reflexivity.

Universes are equal outright. For applications, the nameless forms of the two parts agree, so the induction hypothesis gives $\alphaeq$ for each part, and the congruence property of $\alphaeq$ gives it for the whole.

Let $s = \tPi{x}{A}{B}$, so that $t = \tPi{y}{A'}{B'}$ with $\db{A}{E} = \db{A'}{E}$ and $\db{B}{E, x} = \db{B'}{E, y}$. The induction hypothesis gives $A \alphaeq A'$. For the bodies, choose $z \notin \FV(B) \cup \FV(B') \cup \{x, y\}$. Lemma B.3 with $E'$ empty gives $\db{B}{E, x} = \db{\subst{B}{x}{z}}{E, z}$ and $\db{B'}{E, y} = \db{\subst{B'}{y}{z}}{E, z}$, so

$$
\db{\subst{B}{x}{z}}{E, z} = \db{\subst{B'}{y}{z}}{E, z}.
$$

Since $\subst{B}{x}{z}$ has the size of $B$, which is smaller than the size of $s$, the induction hypothesis gives $\subst{B}{x}{z} \alphaeq \subst{B'}{y}{z}$. Then

$$
\tPi{x}{A}{B} \;\alphaeq\; \tPi{z}{A}{\subst{B}{x}{z}} \;\alphaeq\; \tPi{z}{A'}{\subst{B'}{y}{z}} \;\alphaeq\; \tPi{y}{A'}{B'},
$$

by the defining equation (valid since $z \notin \FV(B)$), by congruence, and by the defining equation read backwards (valid since $z \notin \FV(B')$). The case of $\lambda$ is the same.

</div>

## Proof of Theorem 11.1

<div class="theorem" markdown="1">

**Theorem 11.1 (Correctness of algorithmic alpha-equivalence).** For all terms $s$ and $t$, $s \alphaeq t$ in the sense of the definition in Chapter 11 if and only if $\cdot\,;\cdot \vdash s \alphaeq t$ is derivable by the rules of Figure 11.1.

</div>

<div class="proof" markdown="1">

If $s \alphaeq t$, then $\db{s}{\cdot} = \db{t}{\cdot}$ by the first part of Lemma B.4 (taking $E$ empty), and then $\cdot\,;\cdot \vdash s \alphaeq t$ by Lemma B.1.

Conversely, if $\cdot\,;\cdot \vdash s \alphaeq t$, then $\db{s}{\cdot} = \db{t}{\cdot}$ by Lemma B.1, and then $s \alphaeq t$ by the second part of Lemma B.4.

</div>

<aside class="note" markdown="1">

The theorem is stated for whole terms, with empty binder lists, because that is how the kernel calls the comparison. Lemma B.1 is more general and describes what the algorithm computes at every recursive call, which is what one needs when reading the implementation of `alpha` in `src/substitution.rs`: the two vectors of bound names it carries are $E_1$ and $E_2$, and `binder_distance` computes $\mathrm{idx}$.

</aside>

<div class="summary-box" markdown="1">

What to remember

- Both definitions of alpha-equivalence compute the same thing: equality of de Bruijn (nameless) forms. The nameless form is the bridge between them.
- The algorithm matches nameless forms directly (Lemma B.1), rule by rule.
- The key fact about the mathematical definition is that renaming a bound variable does not change the nameless form (Lemma B.3), which needs an induction on size because substitution can itself rename binders.
- A kernel that uses de Bruijn indices gets this theorem for free: alpha-equivalent terms are syntactically identical.

</div>
