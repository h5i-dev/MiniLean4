<div class="lead" markdown="1">

With the rule $\mathsf{Type} : \mathsf{Type}$, there is a closed term of type $\tPi{p}{\mathsf{Type}}{p}$: a proof of every proposition. Here is the term behind the claim in [Chapter 13](13-universes.md), including the step that depends on a universe containing itself.

</div>

## The setting

Throughout this appendix the universes of the kernel are replaced by one universe $\mathsf{Type}$ with the two rules

$$
\dfrac{\ctxok{\Gamma}}{\Gamma \vdash \mathsf{Type} : \mathsf{Type}}
\qquad
\dfrac{\Gamma \vdash A : \mathsf{Type} \qquad \Gamma, x : A \vdash B : \mathsf{Type}}{\Gamma \vdash \tPi{x}{A}{B} : \mathsf{Type}}
$$

in place of T-Sort and T-Pi. Everything else, including T-Lam, T-App, T-Conv, substitution, and $\beta$-reduction, is unchanged. The goal is a closed term $t_{\mathrm{H}}$ with

$$
\vdash t_{\mathrm{H}} : \bot, \qquad \bot = \tPi{p}{\mathsf{Type}}{p}.
$$

Such a term proves every proposition $C$, because $t_{\mathrm{H}}\;C : C$.

The construction is due to Girard, who adapted the Burali-Forti paradox of set theory to the type theory with $\mathsf{Type} : \mathsf{Type}$ [Girard 1972]. The term below is Hurkens' simplification [Hurkens 1995], which fits on one page and uses nothing beyond $\Pi$, $\lambda$, and application.

## Power sets in type theory

Read a function $p : S \to \mathsf{Type}$ as a *predicate* on $S$, or equivalently as a *subset* of $S$: the elements $x$ for which $p\;x$ has a proof are the members. The type of all such predicates is the *power set* of $S$:

$$
\wp S \;=\; S \to \mathsf{Type}.
$$

Applying this twice, $\wp\wp S = (S \to \mathsf{Type}) \to \mathsf{Type}$ is the type of families of subsets of $S$.

In set theory, Cantor's theorem says that no set contains a copy of its own power set, let alone of its double power set: $\wp S$ is always strictly larger than $S$. The paradox is built on a type $U$ that violates this. It contains a copy of $\wp\wp U$, with a function $\tau : \wp\wp U \to U$ that packs a family of subsets of $U$ into a single element of $U$, and a function $\sigma : U \to \wp\wp U$ that unpacks it again. The type

$$
U \;=\; \tPi{X}{\mathsf{Type}}{\bigl((\wp\wp X \to X) \to \wp\wp X\bigr)}
$$

achieves this by quantifying over *all* of $\mathsf{Type}$. For $U$ to be a member of $\mathsf{Type}$ while quantifying over $\mathsf{Type}$ is exactly what $\mathsf{Type} : \mathsf{Type}$ permits and the hierarchy of [Chapter 13](13-universes.md) forbids.

## The term

The following abbreviations are expanded in place; the kernel sees only $\Pi$, $\lambda$, variables, and application. We write $\neg\varphi$ for $\varphi \to \bot$.

$$
\begin{array}{rcl}
\bot &=& \tPi{p}{\mathsf{Type}}{p} \\[4pt]
\wp S &=& S \to \mathsf{Type} \\[4pt]
U &=& \tPi{X}{\mathsf{Type}}{((\wp\wp X \to X) \to \wp\wp X)} \\[4pt]
\tau &=& \tLam{t}{\wp\wp U}{\tLam{X}{\mathsf{Type}}{\tLam{f}{\wp\wp X \to X}{\tLam{p}{\wp X}{t\;(\tLam{x}{U}{p\;(f\;(x\;X\;f))})}}}} \\[4pt]
\sigma &=& \tLam{s}{U}{s\;U\;\tau} \\[4pt]
\Delta &=& \tLam{y}{U}{\neg\,(\tPi{p}{\wp U}{\sigma\;y\;p \to p\;(\tau\;(\sigma\;y))})} \\[4pt]
\Omega &=& \tau\;(\tLam{p}{\wp U}{\tPi{x}{U}{\sigma\;x\;p \to p\;x}})
\end{array}
$$

With these abbreviations, the term of type $\bot$ is

$$
\begin{array}{rcl}
t_{\mathrm{H}} &=& (\lambda (h_0 : \tPi{p}{\wp U}{(\tPi{x}{U}{\sigma\;x\;p \to p\;x}) \to p\;\Omega}).\; \\
&& \qquad h_0\;\Delta\;(\tLam{x}{U}{\tLam{h_2}{\sigma\;x\;\Delta}{\tLam{h_3}{\tPi{p}{\wp U}{\sigma\;x\;p \to p\;(\tau\;(\sigma\;x))}}{
     h_3\;\Delta\;h_2\;(\tLam{p}{\wp U}{h_3\;(\tLam{y}{U}{p\;(\tau\;(\sigma\;y))})})}}}) \\
&& \qquad\phantom{h_0\;\Delta\;}(\tLam{p}{\wp U}{h_0\;(\tLam{y}{U}{p\;(\tau\;(\sigma\;y))})})) \\
&& (\tLam{p}{\wp U}{\tLam{h_1}{\tPi{x}{U}{\sigma\;x\;p \to p\;x}}{h_1\;\Omega\;(\tLam{x}{U}{h_1\;(\tau\;(\sigma\;x))})}})
\end{array}
$$

The shape is an application: a $\lambda$ binding $h_0$, applied (on the last line) to an argument of the type that $h_0$ expects. Inside, $h_0$ is applied to two arguments, $\Delta$ and a proof about $\Delta$, and the result is applied to one more argument. Everything is explained below.

## How the term works

**Packing and unpacking.** The two functions $\tau : \wp\wp U \to U$ and $\sigma : U \to \wp\wp U$ are inverse enough for the argument. Unfolding the definitions and $\beta$-reducing gives, for every $t : \wp\wp U$ and $p : \wp U$,

$$
\sigma\;(\tau\;t)\;p \;\conv\; t\;(\tLam{x}{U}{p\;(\tau\;(\sigma\;x))}).
$$

This equation is used by the kernel through T-Conv at several points in $t_{\mathrm{H}}$; it is a computation, not an axiom.

**An ordering on $U$.** Read $\sigma\;x\;p$ as "the predicate $p$ holds of everything below $x$". This gives $U$ something like an order, and lets us say two things about predicates and elements.

- A predicate $p : \wp U$ is *inductive* if whenever it holds of everything below $x$, it holds of $x$: that is, $\tPi{x}{U}{\sigma\;x\;p \to p\;x}$.
- An element $x : U$ is *well-founded* if every inductive predicate holds of $x$: that is, $\tPi{p}{\wp U}{(\tPi{x}{U}{\sigma\;x\;p \to p\;x}) \to p\;x}$.

The element $\Omega$ is built to play the part of "the collection of all well-founded elements": it packs the family consisting of all inductive predicates. In Burali-Forti's paradox this is the set of all ordinals, which is itself an ordinal, hence a member of itself, hence not well-founded although all ordinals are.

**The three ingredients.** Reading $t_{\mathrm{H}}$ from the bottom up:

1. The last line, $\tLam{p}{\wp U}{\tLam{h_1}{\cdots}{h_1\;\Omega\;(\tLam{x}{U}{h_1\;(\tau\;(\sigma\;x))})}}$, proves that $\Omega$ is well-founded. Its type is $\tPi{p}{\wp U}{(\tPi{x}{U}{\sigma\;x\;p \to p\;x}) \to p\;\Omega}$, which is the type of $h_0$. So $h_0$ stands for "$\Omega$ is well-founded".
2. The predicate $\Delta\;y$ says "$y$ is not below itself" (strictly, it speaks of $\tau\;(\sigma\;y)$, which behaves like $y$ by the equation above). The second argument of $h_0$, the long $\lambda$ beginning $\tLam{x}{U}{\tLam{h_2}{\cdots}{\cdots}}$, proves that $\Delta$ is inductive. Hence $h_0\;\Delta\;(\cdots) : \Delta\;\Omega$, that is, $\Omega$ is not below itself.
3. The remaining argument, $\tLam{p}{\wp U}{h_0\;(\tLam{y}{U}{p\;(\tau\;(\sigma\;y))})}$, proves that $\Omega$ *is* below itself, by applying the well-foundedness of $\Omega$ to a predicate transformed through the packing equation.

Since $\Delta\;\Omega$ is the negation of "$\Omega$ is below itself", applying the result of step 2 to the result of step 3 yields a term of type $\bot$.

<aside class="intuition" markdown="1">

The argument is Burali-Forti's in disguise. Ordinals are well-founded; the collection $\Omega$ of all ordinals is an ordinal, so it is a member of itself; but no well-founded thing is a member of itself. Set theory escapes by refusing to let the collection of all ordinals be a set. The type theory with $\mathsf{Type} : \mathsf{Type}$ has no such refusal, because $U$ can quantify over everything, including itself.

</aside>

## Where Type : Type is used

Every typing step in $t_{\mathrm{H}}$ is ordinary except one. In $\sigma = \tLam{s}{U}{s\;U\;\tau}$, the variable $s : U$ is applied to the type $U$ itself. The type of $s$ begins $\tPi{X}{\mathsf{Type}}{\cdots}$, so T-App requires $U : \mathsf{Type}$. But $U$ is a $\Pi$ type that quantifies over $\mathsf{Type}$, and in a system with a universe hierarchy such a type lives one level *above* the universe it quantifies over:

$$
\dfrac{\Gamma \vdash \Sort{u} : \Sort{(u+1)} \qquad \Gamma, X : \Sort{u} \vdash B : \Sort{v}}{\Gamma \vdash \tPi{X}{\Sort{u}}{B} : \Sort{\max(u+1, v)}}
$$

With the T-Pi rule of [Chapter 13](13-universes.md), $U$ is in $\Sort{(u+1)}$ at best, never in $\Sort{u}$, so $s\;U$ is ill typed and $\sigma$ cannot be written. The whole construction collapses at this one application. Impredicativity of $\Sort{0}$ does not reopen the door: $U$ has body $(\wp\wp X \to X) \to \wp\wp X$, whose result $\wp\wp X$ is a function type into a universe and therefore is not a proposition, so $\mathrm{imax}$ does not place $U$ in $\Sort{0}$. Coquand showed that one impredicative universe at the bottom is consistent [Coquand 1988]; Hurkens' term shows that two impredicative levels are already too many [Hurkens 1995].

## Reproducing it with the kernel

You can watch the kernel accept and reject this term. The only rule to change is T-Sort, implemented by the `Term::Sort(u)` case of `infer` in `src/typecheck.rs`:

```rust
// T-Sort, as shipped: every universe lives in the next one.
Term::Sort(u) => Ok(Term::Sort(u.checked_add(1).ok_or("universe overflow")?)),
```

Replace the right-hand side by `Ok(Term::Sort(*u))`, so that $\Sort{0} : \Sort{0}$, and use $\Sort{0}$ as $\mathsf{Type}$ throughout. Nothing else needs to change: with every type in $\Sort{0}$, the T-Pi rule with $\mathrm{imax}$ already assigns $\Sort{0}$ to every $\Pi$ type, which is the second rule of this appendix. With that one-line change, `infer` returns exactly $\tPi{p}{\Sort{0}}{p}$ for $t_{\mathrm{H}}$. The unmodified kernel rejects the term with a type mismatch at the application $s\;U$ inside $\sigma$, as predicted above.

<aside class="warning" markdown="1">

Do not leave the modification in. Besides making the kernel inconsistent, it breaks termination: as [Chapter 13](13-universes.md) explains, $t_{\mathrm{H}}$ has no normal form, so asking the modified kernel to normalize it runs until the reduction fuel of [Chapter 12](12-reduction-conversion.md) is exhausted.

</aside>

## Why there is no normal form

[Chapter 14](14-properties.md) proves consistency of the real system by showing that no *normal* closed term has type $\tPi{P}{\Sort{0}}{P}$. The part of that proof that analyses the shapes of normal terms does not use strong normalization and goes through unchanged for $\mathsf{Type} : \mathsf{Type}$. So if $t_{\mathrm{H}}$ had a normal form, that normal form would be a closed normal term of type $\bot$, which cannot exist. Subject reduction still holds, so reduction cannot escape the type $\bot$ either. The only remaining possibility is that $t_{\mathrm{H}}$ reduces forever: strong normalization fails, and with it the termination of the type checker. Girard's paradox is therefore not only a logical defect but a computational one, and it is the reason the design of universes in [Chapter 13](13-universes.md) matters for the algorithm as much as for the logic.

<div class="summary-box" markdown="1">

What to remember

- With $\mathsf{Type} : \mathsf{Type}$, the type $U$ quantifies over all types while being one of them, so it contains a copy of its own double power set, which no set can do.
- Hurkens' term $t_{\mathrm{H}}$ turns this into Burali-Forti's paradox: $\Omega$, the packed family of all inductive predicates, is both well-founded and below itself.
- The rule $\mathsf{Type} : \mathsf{Type}$ is used in exactly one place, the application $s\;U$ in $\sigma$; a universe hierarchy makes that application ill typed.
- The term has no normal form, so the paradox breaks termination of the kernel as well as consistency.

</div>
