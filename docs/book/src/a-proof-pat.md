<div class="lead" markdown="1">

Theorem 4.1 claims that every derivation in second-order propositional logic yields a term accepted by the kernel. Here we prove it by induction on the derivation. Each induction case follows one row of the translation table in [Chapter 4](04-logic.md).

</div>

## The idea

A derivation in the logic is a tree of rule applications. The translation in Chapter 4 pairs each logical rule with a typing rule. So the natural plan is: walk the derivation from the leaves up, and at each node build the typing derivation that the paired typing rule gives. A hypothesis becomes a variable lookup, an implication introduction becomes a $\lambda$, an implication elimination becomes an application, and the two quantifier rules become a $\lambda$ over $\Sort{0}$ and an application to a type.

Two details need care, and both are about contexts.

- The logical rules do not say which proposition variables are in scope. The typing side needs to know, because a proposition variable $P$ is only usable after the assumption $P : \Sort{0}$ is in the context. The precise statement therefore carries an explicit list $\Theta$ of proposition variables.
- The typing rules extend contexts on the right, but the translation $\Delta^\ast$ of Chapter 4 puts all proposition variables before all hypotheses. The proof is easier if any interleaving is allowed, so we prove the theorem for every context that *represents* the logical judgment, in a sense defined below.

## The precise statement

Theorem 4.1 leaves implicit which proposition variables are in scope. For the proof we make them explicit and write

$$
\Theta; \Delta \vdash \varphi,
$$

where $\Theta$ is a list of distinct proposition variables, and every proposition variable free in $\Delta$ or in $\varphi$ belongs to $\Theta$. With this bookkeeping the rules of Chapter 4 read as follows.

$$
\dfrac{\varphi \in \Delta}{\Theta; \Delta \vdash \varphi}\rulename{Hyp}
\qquad
\dfrac{\Theta; \Delta, \varphi \vdash \psi}{\Theta; \Delta \vdash \varphi \to \psi}\rulename{$\to$-intro}
\qquad
\dfrac{\Theta; \Delta \vdash \varphi \to \psi \qquad \Theta; \Delta \vdash \varphi}{\Theta; \Delta \vdash \psi}\rulename{$\to$-elim}
$$

$$
\dfrac{\Theta, P; \Delta \vdash \varphi \qquad P \notin \Theta}{\Theta; \Delta \vdash \forall P.\,\varphi}\rulename{$\forall$-intro}
\qquad
\dfrac{\Theta; \Delta \vdash \forall P.\,\varphi \qquad \FV(\psi) \subseteq \Theta}{\Theta; \Delta \vdash \subst{\varphi}{P}{\psi}}\rulename{$\forall$-elim}
$$

The side condition $P \notin \FV(\Delta)$ of Chapter 4 is now implied by $P \notin \Theta$: every proposition variable free in $\Delta$ is in $\Theta$, and $P$ is not. Formulas are taken up to $\alpha$-equivalence, so a bound $P$ can always be renamed to satisfy the side condition. As in Chapter 4, $\varphi^\ast \to \psi^\ast$ stands for $\tPi{x}{\varphi^\ast}{\psi^\ast}$ with $x$ fresh.

The context $\Delta^\ast$ of Chapter 4 lists the proposition variables first and the hypotheses after them. The proof has to extend contexts on the right, so it is convenient to allow any order.

<div class="definition" markdown="1">

**Definition A.1 (Representation).** A context $\Gamma$ *represents* $(\Theta; \Delta)$ if $\ctxok{\Gamma}$ and $\Gamma$ consists of one assumption $P : \Sort{0}$ for each $P \in \Theta$ and one assumption $h : \chi^\ast$ for each $\chi \in \Delta$, in some order.

</div>

<div class="theorem" markdown="1">

**Theorem A.2 (Theorem 4.1, precise form).** If $\Theta; \Delta \vdash \varphi$ and $\Gamma$ represents $(\Theta; \Delta)$, then $\Gamma \vdash t : \varphi^\ast$ for some term $t$.

</div>

Theorem 4.1 is the special case $\Gamma = \Delta^\ast$. When $\Theta$ lists the free proposition variables, the context $\Delta^\ast$ contains exactly the required assumptions; it is well formed by Lemma A.3 below together with the rule C-Ext, since each hypothesis type $\chi^\ast$ is a proposition once the proposition variables are in scope.

## Facts about the translation

The translation $\varphi \mapsto \varphi^\ast$ commutes with substitution:

$$
(\subst{\varphi}{P}{\psi})^\ast = \subst{\varphi^\ast}{P}{\psi^\ast}.
$$

This is a routine induction on $\varphi$: both sides replace the free occurrences of $P$ by $\psi^\ast$, and the translation does nothing to a proposition variable except keep its name. The $\forall$-elim case of the main proof depends on this equation.

The next lemma is the one place where the universe structure of [Chapter 13](13-universes.md) enters. It says that every translated formula is a proposition, that is, has type $\Sort{0}$. Without it, the typing rule T-Lam could not be applied to a hypothesis, and the $\forall$-elim case could not instantiate a quantifier with an arbitrary formula.

<div class="lemma" markdown="1">

**Lemma A.3 (Formulas are propositions).** If $\ctxok{\Gamma}$ and $(P : \Sort{0}) \in \Gamma$ for every $P \in \FV(\varphi)$, then $\Gamma \vdash \varphi^\ast : \Sort{0}$.

</div>

<div class="proof" markdown="1">

By induction on $\varphi$.

For a proposition variable $P$, the assumption gives $(P : \Sort{0}) \in \Gamma$, so $\Gamma \vdash P : \Sort{0}$ by T-Var.

For $\varphi \to \psi$, the induction hypothesis gives $\Gamma \vdash \varphi^\ast : \Sort{0}$, so $\Gamma, x : \varphi^\ast$ is well formed by C-Ext for a fresh $x$. The induction hypothesis for $\psi$ in that extended context gives $\Gamma, x : \varphi^\ast \vdash \psi^\ast : \Sort{0}$, and T-Pi gives $\Gamma \vdash \tPi{x}{\varphi^\ast}{\psi^\ast} : \Sort{\imax(0, 0)} = \Sort{0}$.

For $\forall Q.\,\chi$, rename $Q$ so that $Q \notin \dom(\Gamma)$. T-Sort gives $\Gamma \vdash \Sort{0} : \Sort{1}$, so $\Gamma, Q : \Sort{0}$ is well formed by C-Ext. The induction hypothesis for $\chi$ in that context gives $\Gamma, Q : \Sort{0} \vdash \chi^\ast : \Sort{0}$, and T-Pi gives $\Gamma \vdash \tPi{Q}{\Sort{0}}{\chi^\ast} : \Sort{\imax(1, 0)} = \Sort{0}$.

</div>

<aside class="note" markdown="1">

The last case is where impredicativity is used. The domain $\Sort{0}$ lives in $\Sort{1}$, so with $\max$ in place of $\imax$ the type $(\forall Q.\,\chi)^\ast$ would land in $\Sort{1}$ rather than $\Sort{0}$. Then the $\forall$-elim case below would hold only for formulas $\psi$ without $\forall$, because only those would have type $\Sort{0}$ and be allowed as arguments. Chapter 13 discusses this design choice.

</aside>

## The proof

<div class="proof" markdown="1">

We prove Theorem A.2 by induction on the derivation of $\Theta; \Delta \vdash \varphi$, for all representing contexts $\Gamma$ at once. Each case builds the typing derivation shown in the right column of the table in Chapter 4.

*Hypothesis.* The rule concludes $\Theta; \Delta \vdash \varphi$ from $\varphi \in \Delta$. Since $\Gamma$ represents $(\Theta; \Delta)$, it contains an assumption $h : \varphi^\ast$, so $\Gamma \vdash h : \varphi^\ast$ by T-Var.

*$\to$-intro.* The premise is $\Theta; \Delta, \varphi \vdash \psi$ and the conclusion is $\Theta; \Delta \vdash \varphi \to \psi$. By Lemma A.3, $\Gamma \vdash \varphi^\ast : \Sort{0}$. For a fresh $h$, the context $\Gamma, h : \varphi^\ast$ is therefore well formed by C-Ext, and it represents $(\Theta; \Delta, \varphi)$. The induction hypothesis, applied to the premise and this context, gives $\Gamma, h : \varphi^\ast \vdash t : \psi^\ast$ for some $t$, and T-Lam gives

$$
\Gamma \vdash \tLam{h}{\varphi^\ast}{t} : \tPi{h}{\varphi^\ast}{\psi^\ast}.
$$

This type is $\varphi^\ast \to \psi^\ast$: the free variables of $\psi^\ast$ are proposition variables, and $h$ is not one of them, so $h$ does not occur in $\psi^\ast$ and the $\Pi$ is non-dependent.

*$\to$-elim.* The premises are $\Theta; \Delta \vdash \varphi \to \psi$ and $\Theta; \Delta \vdash \varphi$. The induction hypotheses give $\Gamma \vdash f : \tPi{x}{\varphi^\ast}{\psi^\ast}$ with $x \notin \FV(\psi^\ast)$, and $\Gamma \vdash a : \varphi^\ast$. T-App gives $\Gamma \vdash f\;a : \subst{\psi^\ast}{x}{a}$, and since $x$ does not occur in $\psi^\ast$ the substitution does nothing: $\subst{\psi^\ast}{x}{a} = \psi^\ast$.

*$\forall$-intro.* The premise is $\Theta, P; \Delta \vdash \varphi$ with $P \notin \Theta$, and the conclusion is $\Theta; \Delta \vdash \forall P.\,\varphi$. Renaming $P$ if necessary, assume $P \notin \dom(\Gamma)$; a routine induction shows that renaming a variable of $\Theta$ to a fresh one preserves derivations. By T-Sort and C-Ext, $\Gamma, P : \Sort{0}$ is well formed, and it represents $(\Theta, P; \Delta)$. The induction hypothesis gives $\Gamma, P : \Sort{0} \vdash t : \varphi^\ast$, and T-Lam gives

$$
\Gamma \vdash \tLam{P}{\Sort{0}}{t} : \tPi{P}{\Sort{0}}{\varphi^\ast},
$$

which is the translation of $\forall P.\,\varphi$.

*$\forall$-elim.* The premise is $\Theta; \Delta \vdash \forall P.\,\varphi$ with $\FV(\psi) \subseteq \Theta$, and the conclusion is $\Theta; \Delta \vdash \subst{\varphi}{P}{\psi}$. The induction hypothesis gives $\Gamma \vdash f : \tPi{P}{\Sort{0}}{\varphi^\ast}$. Since every proposition variable of $\psi$ is in $\Theta$ and hence has an assumption $Q : \Sort{0}$ in $\Gamma$, Lemma A.3 gives $\Gamma \vdash \psi^\ast : \Sort{0}$. T-App gives

$$
\Gamma \vdash f\;\psi^\ast : \subst{\varphi^\ast}{P}{\psi^\ast} = (\subst{\varphi}{P}{\psi})^\ast,
$$

where the last step is the substitution equation from the previous section.

Every rule of the logic has been covered, so the theorem holds for every derivation.

</div>

The proof never needs T-Conv. Every typing derivation it builds compares types only syntactically, up to the names of bound variables. Conversion becomes necessary only when the logic is extended with computation, as the inductive types of Part II do.

<aside class="history" markdown="1">

The converse direction, that every term of type $\varphi^\ast$ comes from a proof of $\varphi$, is called *conservativity*. As Chapter 4 notes, it is harder, because $\Sort{0}$ contains types that are not translations of formulas, and a term may pass through them. The book does not need it: what the kernel must guarantee is consistency, which is proved in [Appendix D](d-proof-consistency.md).

</aside>

<div class="summary-box" markdown="1">

What to remember

- The precise form of the theorem carries an explicit list $\Theta$ of proposition variables, and proves the claim for every context that represents $(\Theta; \Delta)$, in any order.
- Every translated formula lives in $\Sort{0}$ (Lemma A.3). This uses impredicativity in the $\forall$ case, and it is what lets $\forall$-elim instantiate a quantifier with any formula.
- The proof is an induction on the derivation; each logical rule maps to exactly one typing rule: Hyp to T-Var, the two introductions to T-Lam, the two eliminations to T-App.
- T-Conv is never used, because the logic has no computation.

</div>
