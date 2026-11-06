<div class="lead" markdown="1">

Every symbol, judgment, and technical term used in the book, with the chapter that introduces it. Use this appendix as a reference while reading, or as a checklist of what the book covers.

</div>

## Notation

### Terms

| Notation | Meaning | Chapter |
|---|---|---|
| $\Sort{u}$ | the universe at level $u$; $\Sort{0}$ is the universe of propositions | [2](02-syntax.md) |
| $x, y, z$ | variables | [2](02-syntax.md) |
| $c$ | a constant from the signature | [7](07-inductive-nat.md) |
| $\tPi{x}{A}{B}$ | dependent function type ($\Pi$-type) | [2](02-syntax.md) |
| $A \to B$ | non-dependent function type, $\tPi{\_}{A}{B}$ | [2](02-syntax.md) |
| $\tLam{x}{A}{t}$ | function ($\lambda$-abstraction) | [2](02-syntax.md) |
| $t\;s$ | application, left-associative | [2](02-syntax.md) |
| $h\;a_1 \cdots a_n$ | a spine: head $h$ applied to arguments | [2](02-syntax.md) |
| $(\vec{x} : \vec{A})$, $\tPi{\vec{x}}{\vec{A}}{B}$ | a telescope of bindings and a $\Pi$ over it | [8](08-inductive-recipe.md) |
| $\FV(t)$ | the free variables of $t$ | [11](11-substitution-alpha.md) |
| $\subst{t}{x}{s}$ | capture-avoiding substitution of $s$ for $x$ in $t$ | [11](11-substitution-alpha.md) |
| $\db{t}{E}$ | the nameless (de Bruijn) form of $t$ under binders $E$ | [B](b-proof-alpha.md) |
| $\hole{m}$ | a hole (metavariable) in a partial proof term | [10](10-tactics.md) |

### Judgments and relations

| Notation | Meaning | Chapter |
|---|---|---|
| $\Gamma$ | a context, an ordered list of assumptions $x : A$ | [3](03-typing-rules.md) |
| $\cdot$ | the empty context | [3](03-typing-rules.md) |
| $\dom(\Gamma)$ | the names assumed in $\Gamma$ | [3](03-typing-rules.md) |
| $\ctxok{\Gamma}$ | $\Gamma$ is well formed | [3](03-typing-rules.md) |
| $\Gamma \vdash t : A$ | $t$ has type $A$ in $\Gamma$ | [3](03-typing-rules.md) |
| $\Sigma$ | the signature of constants | [7](07-inductive-nat.md) |
| $c : C \mathrel{:=} t$ | a definition with body $t$ | [7](07-inductive-nat.md) |
| $\imax(u, v)$ | $0$ if $v = 0$, else $\max(u, v)$ | [3](03-typing-rules.md), [13](13-universes.md) |
| $s \alphaeq t$ | alpha-equivalence | [11](11-substitution-alpha.md) |
| $E_1; E_2 \vdash s \alphaeq t$ | algorithmic alpha-equivalence under binder lists $E_1$, $E_2$ | [11](11-substitution-alpha.md) |
| $\mathrm{idx}(E, x)$ | position of the last $x$ in $E$, from the right | [11](11-substitution-alpha.md) |
| $t \betared t'$, $t \deltared t'$, $t \iotared t'$ | beta-, delta-, iota-reduction | [3](03-typing-rules.md), [7](07-inductive-nat.md) |
| $t \to t'$ | one reduction step of any kind | [12](12-reduction-conversion.md) |
| $s \conv t$ | definitional equality (conversion) | [3](03-typing-rules.md), [12](12-reduction-conversion.md) |
| $\Delta \vdash \varphi$ | provability in second-order propositional logic | [4](04-logic.md) |
| $\varphi^\ast$, $\Delta^\ast$ | translation of a formula, of a hypothesis list | [4](04-logic.md) |
| $\goal{\Gamma}{\hole{m}}{T}$ | a goal: find a term of type $T$ in $\Gamma$ for hole $m$ | [10](10-tactics.md) |

### Constants of the standard kernel

| Notation | Type | leanmini name | Chapter |
|---|---|---|---|
| $\Nat$ | $\Sort{1}$ | `Nat` | [7](07-inductive-nat.md) |
| $\zero$ | $\Nat$ | `Nat.zero` | [7](07-inductive-nat.md) |
| $\suc$ | $\Nat \to \Nat$ | `Nat.succ` | [7](07-inductive-nat.md) |
| $\NatRec{u}$ | see Figure 7.1 | `Nat.rec0`, `Nat.rec1` | [7](07-inductive-nat.md) |
| $\Eq{u}$ | $\tPi{A}{\Sort{u}}{A \to A \to \Sort{0}}$ | `Eq` | [9](09-equality.md) |
| $\refl{u}$ | $\tPi{A}{\Sort{u}}{\tPi{a}{A}{\Eq{u}\;A\;a\;a}}$ | `Eq.refl` | [9](09-equality.md) |
| $\EqRecDep{u,v}$ | dependent eliminator, Figure 9.1 | `Eq.rec0`, `Eq.rec1` | [9](09-equality.md) |
| $\EqRec{u,v}$ | non-dependent eliminator (a definition) | not predeclared | [9](09-equality.md) |
| $\add$, $m + n$ | $\Nat \to \Nat \to \Nat$ | `add` (defined in scripts) | [7](07-inductive-nat.md) |

### Algorithms

| Name | Role | Rust | Chapter |
|---|---|---|---|
| $\Infer(\Gamma, t)$ | compute the type of $t$ | `Kernel::infer` | [5](05-algorithm.md) |
| $\Check(\Gamma, t, T)$ | verify $t : T$ | `Kernel::check` | [5](05-algorithm.md) |
| $\InferSort(\Gamma, A)$ | verify $A$ is a type, return its level | `Kernel::infer_sort` | [5](05-algorithm.md) |
| $\Freshen(\Gamma, x, b)$ | rename a binder that would shadow $\Gamma$ | `rename_binder_if_needed` | [5](05-algorithm.md) |
| $\Whnf(t)$ | weak head normal form | `Kernel::whnf` | [12](12-reduction-conversion.md) |
| $\Normalize(t)$ | full normal form | `Kernel::normalize` | [12](12-reduction-conversion.md) |
| $\IsDefEq(s, t)$ | decide $s \conv t$ | `Kernel::is_def_eq` | [12](12-reduction-conversion.md) |

## Glossary

**Alpha-equivalence.** Equality of terms up to renaming of bound variables. Decided by comparing bound variables by binder position and free variables by name. [Chapter 11](11-substitution-alpha.md).

**Beta-reduction.** The computation step $(\tLam{x}{A}{t})\;s \to \subst{t}{x}{s}$. [Chapters 3](03-typing-rules.md) and [12](12-reduction-conversion.md).

**Capture.** The error of substituting a term under a binder that binds one of the term's free variables, changing its meaning. Avoided by renaming the binder. [Chapter 11](11-substitution-alpha.md).

**Confluence.** The property that different orders of reduction reach the same normal form. It is what lets conversion be decided by normalizing. [Chapter 12](12-reduction-conversion.md).

**Consistency.** No closed term has type $\tPi{P}{\Sort{0}}{P}$. The property that makes the kernel's acceptance meaningful. [Chapters 4](04-logic.md) and [14](14-properties.md).

**Constructor.** A constant that builds values of an inductive type, such as $\zero$ and $\suc$. Constructors never reduce. [Chapter 7](07-inductive-nat.md).

**Context.** An ordered list of typing assumptions. [Chapter 3](03-typing-rules.md).

**Conversion.** See definitional equality.

**Curry-Howard correspondence.** Propositions are types, proofs are terms, proof checking is type checking. [Chapter 1](01-propositions-as-types.md).

**De Bruijn index.** A representation of a bound variable by the number of binders between its occurrence and its binder, which makes alpha-equivalent terms identical. [Chapter 11](11-substitution-alpha.md), [Appendix B](b-proof-alpha.md).

**Definitional equality.** The equivalence on terms generated by reduction and alpha-equivalence; decided by the kernel. Contrasted with propositional equality. [Chapters 9](09-equality.md) and [12](12-reduction-conversion.md).

**Delta-reduction.** Unfolding a defined constant into its body. [Chapter 7](07-inductive-nat.md).

**Dependent function type.** A $\Pi$-type whose result type may mention the argument; the type of proofs of a universal statement. [Chapter 1](01-propositions-as-types.md).

**Elimination (large).** Using the recursor of a proposition to build data, allowed only for subsingletons. [Chapter 8](08-inductive-recipe.md).

**Field.** An argument of a constructor other than the parameters. [Chapter 8](08-inductive-recipe.md).

**Goal.** A context together with a type for which a term is still to be found. [Chapter 10](10-tactics.md).

**Impredicative.** A universe that contains types quantifying over that same universe. $\Sort{0}$ is impredicative; higher universes are not. [Chapter 13](13-universes.md).

**Index.** An argument of an inductive type former that may differ between constructors, such as the length of a vector or the right side of an equation. [Chapter 8](08-inductive-recipe.md).

**Induction hypothesis.** In a minor premise, the assumption that the motive already holds for a recursive field. [Chapter 7](07-inductive-nat.md).

**Inductive type.** A type specified by its constructors, from which the kernel generates a recursor and iota-rules. [Chapters 7](07-inductive-nat.md) and [8](08-inductive-recipe.md).

**Iota-reduction.** Running a recursor on a constructor application. [Chapters 7](07-inductive-nat.md) and [12](12-reduction-conversion.md).

**Kernel.** The trusted component that decides $\Gamma \vdash t : A$. Everything else only produces terms for it. [Chapter 1](01-propositions-as-types.md).

**Major premise.** The argument of a recursor whose constructor selects the iota-rule. [Chapter 7](07-inductive-nat.md).

**Metavariable.** Lean's name for a hole in a partial term. [Chapter 10](10-tactics.md).

**Minor premise.** The argument of a recursor giving the case for one constructor. [Chapter 7](07-inductive-nat.md).

**Motive.** The function $M$ that gives the result type of a recursor for each element; a predicate, for induction. [Chapter 7](07-inductive-nat.md).

**Neutral term.** A normal term headed by a variable (or, with constants, a stuck constant). [Chapter 14](14-properties.md), [Appendix D](d-proof-consistency.md).

**Normal form.** A term to which no reduction step applies. [Chapter 12](12-reduction-conversion.md).

**Parameter.** An argument of an inductive type former that is the same in every constructor, such as the element type of a list. [Chapter 8](08-inductive-recipe.md).

**Positivity (strict).** The condition that a recursive field mentions the inductive type only as the result of a function, never as an argument. Required for termination and consistency. [Chapter 8](08-inductive-recipe.md).

**Predicative.** A universe that does not contain types quantifying over it. $\Sort{u}$ for $u \ge 1$. [Chapter 13](13-universes.md).

**Proof irrelevance.** Lean's rule that any two proofs of a proposition are definitionally equal. Not implemented in MiniLean4. [Chapter 13](13-universes.md).

**Propositional equality.** The inductive type $\Eq{}$. Its proofs are terms; contrast with definitional equality. [Chapter 9](09-equality.md).

**Recursor.** The constant generated for an inductive type that expresses structural recursion and induction. [Chapter 7](07-inductive-nat.md).

**Signature.** The table of constants and their types, with bodies for definitions. [Chapter 7](07-inductive-nat.md).

**Spine.** The view of a term as a head applied to a list of arguments. [Chapter 2](02-syntax.md).

**Strong normalization.** Every reduction sequence from a well-typed term is finite. [Chapter 14](14-properties.md).

**Subject reduction.** Reduction preserves types. [Chapter 14](14-properties.md).

**Subsingleton.** A proposition with at most one constructor whose fields are all proofs or indices; it may eliminate into any universe. [Chapter 8](08-inductive-recipe.md).

**Syntax-directed.** A rule system in which the shape of the term determines the applicable rule. All typing rules except T-Conv. [Chapter 5](05-algorithm.md).

**Tactic.** A program outside the kernel that assigns terms to holes in a proof state. [Chapter 10](10-tactics.md).

**Telescope.** A sequence of bindings in which later types may mention earlier variables. [Chapter 8](08-inductive-recipe.md).

**Transport.** Moving a fact about $a$ to a fact about $b$ along a proof of $a = b$, via the recursor of $\Eq{}$. [Chapter 9](09-equality.md).

**Universe.** A type whose elements are types: $\Sort{u}$. [Chapters 2](02-syntax.md) and [13](13-universes.md).

**Weak head normal form.** The result of reducing only at the head of a term until its outermost shape is visible. [Chapter 12](12-reduction-conversion.md).

<div class="summary-box" markdown="1">

What to remember

- Terms, judgments, and algorithms each have a fixed notation used consistently throughout the book; the tables above map each to its Rust counterpart.
- The two equalities (definitional and propositional) and the two kinds of universe (impredicative and predicative) are the distinctions to keep straight.

</div>
