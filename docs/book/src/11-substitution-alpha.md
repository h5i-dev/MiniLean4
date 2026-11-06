<div class="lead" markdown="1">

The previous chapters treated three operations on terms as black boxes: substitution, used by T-App, by Freshen, and by every computation step; weak head normalization, used to expose a $\Pi$ or a universe; and definitional equality, used by Check. These operations are part of the trusted kernel, and most kernel bugs hide in them, because they must handle the names of bound variables correctly. This chapter opens the first box, substitution, shows the same naming problem in contexts, and then defines when two terms are equal up to the names of their bound variables.

</div>

## Free variables and substitution

$\Pi$ and $\lambda$ *bind* their variable: in $\tLam{x}{A}{t}$, occurrences of $x$ inside $t$ refer to the argument. The binder's scope is the body only; $x$ is not bound in the annotation $A$. A variable occurrence that is not bound by an enclosing $\Pi$ or $\lambda$ is *free*.

<div class="definition" markdown="1">

**Definition 11.1 (Free variables).**

$$
\begin{array}{rclcrcl}
\FV(\Sort{u}) &=& \emptyset &\qquad& \FV(\tPi{x}{A}{B}) &=& \FV(A) \cup (\FV(B) \setminus \{x\}) \\[2pt]
\FV(x) &=& \{x\} && \FV(\tLam{x}{A}{t}) &=& \FV(A) \cup (\FV(t) \setminus \{x\}) \\[2pt]
\FV(t\;s) &=& \FV(t) \cup \FV(s) && \FV(c) &=& \emptyset
\end{array}
$$

</div>

For example, $\FV(\tLam{x}{P}{f\;x\;y}) = \{P, f, y\}$, and $\FV(\tPi{P}{\Sort{0}}{P \to P}) = \emptyset$, so the latter is a *closed* term. Constants are never bound, so they contribute nothing.

The explorer colours each bound variable like its binder and underlines free ones; hover a variable to see its binder. Try a term with shadowing, such as `fun (x : A) => fun (x : A) => x`.

<div class="explorer" data-kind="scope" data-term="fun (x : P) => f x y"></div>

We write $\subst{t}{x}{s}$ for the result of replacing the free occurrences of $x$ in $t$ with $s$. Binders make this subtle: in $\subst{(\tLam{y}{A}{x})}{x}{y}$, the body means "ignore the argument and return the outer $x$". Replacing $x$ with $y$ naively gives $\tLam{y}{A}{y}$, the identity function, because the binder has **captured** the formerly free $y$. To preserve the meaning, substitution must rename the binder first.

<div class="definition" markdown="1">

**Definition 11.2 (Capture-avoiding substitution).** For $\square \in \{\Pi, \lambda\}$:

$$
\begin{array}{rcll}
\subst{x}{x}{s} &=& s \\[2pt]
\subst{y}{x}{s} &=& y & (y \neq x) \\[2pt]
\subst{\Sort{u}}{x}{s} &=& \Sort{u} \\[2pt]
\subst{c}{x}{s} &=& c \\[2pt]
\subst{(t_1\;t_2)}{x}{s} &=& \subst{t_1}{x}{s}\;\;\subst{t_2}{x}{s} \\[2pt]
\subst{(\square(x{:}A).\,B)}{x}{s} &=& \square(x{:}\subst{A}{x}{s}).\,B & \text{($x$ is shadowed)} \\[2pt]
\subst{(\square(y{:}A).\,B)}{x}{s} &=& \square(y{:}\subst{A}{x}{s}).\,\subst{B}{x}{s} & (y \neq x,\; y \notin \FV(s)) \\[2pt]
\subst{(\square(y{:}A).\,B)}{x}{s} &=& \square(z{:}\subst{A}{x}{s}).\,\subst{(\subst{B}{y}{z})}{x}{s} & (y \neq x,\; y \in \FV(s),\; z \text{ fresh})
\end{array}
$$

Here "$z$ fresh" means $z \notin \FV(s) \cup \FV(B) \cup \{x\}$.

</div>

The following examples exercise each binder case.

| Substitution | Result | Why |
|---|---|---|
| $\subst{(\tPi{h}{P}{P})}{P}{Q}$ | $\tPi{h}{Q}{Q}$ | no capture possible; the T-App step of Chapter 6 |
| $\subst{(\tLam{x}{A}{x})}{x}{s}$ | $\tLam{x}{A}{x}$ | $x$ is shadowed; the body is untouched |
| $\subst{(\tLam{y}{x}{y})}{x}{s}$ | $\tLam{y}{s}{y}$ | the annotation is outside the scope of $y$ |
| $\subst{(\tLam{y}{A}{x\;y})}{x}{f\;y}$ | $\tLam{z}{A}{f\;y\;z}$ | $y \in \FV(f\;y)$, so the binder is renamed to $z$ |

In the last example, the free $y$ of the replacement still refers to the outer $y$, and the bound variable, now $z$, still refers to the argument. Without the renaming, the result would be $\tLam{y}{A}{f\;y\;y}$, which passes its argument twice. The explorer performs both substitutions side by side; the colours show whether the $y$ in the result is the free one from the replacement or the one the binder captured.

<div class="explorer" data-kind="subst" data-term="fun (y : A) => x y" data-var="x" data-with="f y"></div>

<aside class="code" markdown="1">

Definitions 11.1 and 11.2 are `fv` and `subst` in `src/substitution.rs`. The binder case of `subst` is below. It has one extra shortcut compared with the definition: if $x$ does not occur free in the body at all, the body is returned unchanged, which saves a traversal and never changes the result.

```rust
Term::Pi(y, domain, body) | Term::Lam(y, domain, body) => {
    let substituted_domain = subst(domain, x, replacement);
    let (renamed_binder, substituted_body) = if y == x || !fv(body).contains(x) {
        (y.clone(), (**body).clone())                       // shadowed, or nothing to do
    } else if !fv(replacement).contains(y) {
        (y.clone(), subst(body, x, replacement))            // no capture possible
    } else {
        let mut avoid = all_names(body);                    // capture: rename y to a fresh z
        avoid.extend(all_names(domain));
        avoid.extend(all_names(replacement));
        avoid.insert(x.to_string());
        let z = fresh(y, &avoid);
        let body_with_z = subst(body, y, &var(&z));
        (z, subst(&body_with_z, x, replacement))
    };
    // ... rebuild the Pi or Lam with renamed_binder, substituted_domain, substituted_body
}
```

The `fresh` function appends primes to the hint until the name is unused. The avoid set is `all_names`, every name in the terms involved rather than just the free ones, which is more than the definition requires but makes the output easier to read.

</aside>

## Variable capture in contexts

It is tempting to drop the side condition $x \notin \dom(\Gamma)$ of C-Ext and let a new assumption simply shadow an old one, as most programming languages do. Doing so makes the kernel unsound. Consider

$$
t = \tLam{x}{\Sort{0}}{\tLam{y}{x}{\tLam{x}{\Sort{0}}{y}}}.
$$

The variable $y$ has the *outer* $x$ as its type, and the innermost $\lambda$ ignores its argument. So the correct type of $t$ is

$$
\tPi{x}{\Sort{0}}{\tPi{y}{x}{\tPi{x'}{\Sort{0}}{x}}}.
$$

A checker without $\Freshen$ looks up $y$ in the context $x : \Sort{0},\; y : x,\; x : \Sort{0}$ and returns its type, the bare name $x$. At that point $x$ refers to the inner binder, and the checker returns

$$
\tPi{x}{\Sort{0}}{\tPi{y}{x}{\tPi{x}{\Sort{0}}{x}}},
$$

which says "from any element of any type, produce an element of every type". Given $A : \Sort{0}$ and $a : A$, the term $t\;A\;a$ then has type $\tPi{B}{\Sort{0}}{B}$, a proof of False. Such $A$ and $a$ exist even in the empty context: $A = \tPi{P}{\Sort{0}}{P \to P}$ is itself a proposition, and the identity function $a = \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}}$ proves it.

With $\Freshen$, the innermost binder is renamed to $x'$ before it enters the context, so the context becomes $x : \Sort{0},\; y : x,\; x' : \Sort{0}$, the lookup of $y$ returns $x$, which still refers to the outer binder, and $\Infer$ returns the correct type above. The derivation explorer shows the renaming happen: the note on the innermost T-Lam node reports it, and the context of the leaf contains $x'$.

<div class="explorer" data-kind="derive" data-term="fun (x : Sort 0) => fun (y : x) => fun (x : Sort 0) => y"></div>

<div class="playground" data-file="capture"><pre># The kernel renames the inner x to x' and infers the correct type.
# A kernel that let the inner x shadow the outer one would accept this
# as a proof of the second statement, which is false.
goal forall (x : Sort 0), forall (y : x), forall (x' : Sort 0), x
exact fun (x : Sort 0) => fun (y : x) => fun (x : Sort 0) => y
qed
goal forall (x : Sort 0), forall (y : x), forall (x' : Sort 0), x'
exact fun (x : Sort 0) => fun (y : x) => fun (x : Sort 0) => y
qed</pre></div>

The problem is the same as in substitution: a name is moved into a scope where it means something else. It affects any representation that identifies variables by name, whether the context is a list or a hash map. There are three common remedies.

1. Reject shadowing outright. This is the simplest option, but the reserved name `_` used by $A \to B$ must be exempt and never added to the context.
2. Rename on entry, as $\Freshen$ does. This is our choice.
3. Represent bound variables by position (**de Bruijn indices** [de Bruijn 1972]) or use the *locally nameless* style, in which bound variables are indices and free variables carry unique identifiers. Lean 4 takes the latter approach.

A test suite should include $t$ above and check that the kernel either rejects it or assigns it the correct type.

<aside class="warning" markdown="1">

This bug is easy to write and hard to notice, because every ordinary proof still checks. Only a term that deliberately reuses a name in a nested binder exposes it. A kernel's test suite needs adversarial terms, not just correct proofs.

</aside>

## Alpha-equivalence

The names of bound variables carry no meaning. $\tLam{x}{A}{x}$ and $\tLam{y}{A}{y}$ are the same function, and $\tPi{P}{\Sort{0}}{P \to P}$ and $\tPi{Q}{\Sort{0}}{Q \to Q}$ are the same proposition. Terms that differ only in the names of bound variables are called **alpha-equivalent**. A kernel cannot compare types with plain syntactic equality, which would reject the second pair.

<div class="definition" markdown="1">

**Definition 11.3 (Alpha-equivalence).** $\alphaeq$ is the smallest congruence on terms containing, for $\square \in \{\Pi, \lambda\}$,

$$
\square(x{:}A).\,B \;\alphaeq\; \square(y{:}A).\,\subst{B}{x}{y}
\qquad \text{whenever } y \notin \FV(B).
$$

</div>

(A *congruence* is an equivalence relation that is preserved by every term constructor: if the parts are related, so are the wholes.) This definition is easy to state but not directly executable, since it does not say which names to choose. An implementation instead walks both terms in lockstep and remembers, for each side, the list of binders passed so far. A bound variable is then identified by *which* binder it refers to, not by its name.

To describe this walk, we use a judgment of the form $E_1; E_2 \vdash s \alphaeq t$, where $E_1$ and $E_2$ are lists of names. The list $E_1$ records the binders that enclose $s$, from the outermost to the innermost, and $E_2$ records those that enclose $t$. The judgment reads: "$s$, placed inside the binders $E_1$, and $t$, placed inside the binders $E_2$, are the same term up to the names of bound variables". Two lists are needed because the two terms may use different names for corresponding binders. For example, comparing $\tLam{x}{A}{\tLam{y}{B}{x}}$ with $\tLam{a}{A}{\tLam{b}{B}{a}}$ passes two binders on each side and arrives at

$$
x, y;\; a, b \vdash x \alphaeq a,
$$

which holds because $x$ and $a$ both refer to the outer of the two binders. Comparing two whole terms starts from empty lists, $\cdot\,;\cdot \vdash s \alphaeq t$.

To say "the same binder" precisely, let $\mathrm{idx}(E, x)$ be the position of the *last* occurrence of $x$ in $E$, counted from the right starting at $0$, or undefined if $x \notin E$. In the example, $\mathrm{idx}((x, y), x) = \mathrm{idx}((a, b), a) = 1$. Taking the last occurrence handles shadowing: in $\tLam{x}{A}{\tLam{x}{B}{x}}$ the body refers to the inner $x$.

<div class="rulebox" markdown="1">

<p class="caption">Figure 11.1. Algorithmic alpha-equivalence. By Theorem 11.4, two terms $s$ and $t$ are alpha-equivalent iff $\cdot\,;\cdot \vdash s \alphaeq t$.</p>

$$
\dfrac{}{E_1; E_2 \vdash \Sort{u} \alphaeq \Sort{u}}\rulename{$\alpha$-Sort}
\qquad
\dfrac{}{E_1; E_2 \vdash c \alphaeq c}\rulename{$\alpha$-Const}
$$

$$
\dfrac{\mathrm{idx}(E_1, x) = \mathrm{idx}(E_2, y) = i}{E_1; E_2 \vdash x \alphaeq y}\rulename{$\alpha$-Bound}
\qquad
\dfrac{x \notin E_1 \qquad x \notin E_2}{E_1; E_2 \vdash x \alphaeq x}\rulename{$\alpha$-Free}
$$

$$
\dfrac{E_1; E_2 \vdash A \alphaeq A' \qquad E_1, x;\; E_2, y \vdash B \alphaeq B'}{E_1; E_2 \vdash \tPi{x}{A}{B} \alphaeq \tPi{y}{A'}{B'}}\rulename{$\alpha$-Pi}
$$

$$
\dfrac{E_1; E_2 \vdash A \alphaeq A' \qquad E_1, x;\; E_2, y \vdash t \alphaeq t'}{E_1; E_2 \vdash \tLam{x}{A}{t} \alphaeq \tLam{y}{A'}{t'}}\rulename{$\alpha$-Lam}
\qquad
\dfrac{E_1; E_2 \vdash t_1 \alphaeq t_1' \qquad E_1; E_2 \vdash t_2 \alphaeq t_2'}{E_1; E_2 \vdash t_1\;t_2 \alphaeq t_1'\;t_2'}\rulename{$\alpha$-App}
$$

</div>

Free variables are compared by name ($\alpha$-Free), bound variables by position ($\alpha$-Bound), and constants by name ($\alpha$-Const). A variable that is bound on one side and free on the other is never equal to anything, which is why there is no rule for that case. Because both sides descend through binders together, $E_1$ and $E_2$ always have the same length. So comparing positions counted from the right is the same as comparing positions counted from the left, and an implementation may store each list as a map from names to binding depths, provided it restores the previous entry when it leaves a binder. Using positions instead of names *everywhere* gives the **de Bruijn representation**, in which alpha-equivalent terms are syntactically identical.

### Examples

The first example of Chapter 6 ended by comparing the inferred type with the stated one, where $P \to P$ abbreviates $\tPi{\_}{P}{P}$:

<ul class="trace">
<li>$\cdot\,;\cdot \vdash \tPi{P}{\Sort{0}}{\tPi{h}{P}{P}} \alphaeq \tPi{P}{\Sort{0}}{\tPi{\_}{P}{P}}$ <span class="rule">$\alpha$-Pi</span>
  <ul>
  <li>$\cdot\,;\cdot \vdash \Sort{0} \alphaeq \Sort{0}$: holds <span class="rule">$\alpha$-Sort</span></li>
  <li>$P;\, P \vdash \tPi{h}{P}{P} \alphaeq \tPi{\_}{P}{P}$ <span class="rule">$\alpha$-Pi</span>
    <ul>
    <li>$P;\, P \vdash P \alphaeq P$: holds, both have index $0$ <span class="rule">$\alpha$-Bound</span></li>
    <li>$P, h;\; P, \_ \vdash P \alphaeq P$: holds, both have index $1$ <span class="rule">$\alpha$-Bound</span></li>
    </ul>
  </li>
  </ul>
</li>
</ul>

The names $h$ and $\_$ differ, but neither is ever looked up, so they do not matter. The wrong proof of Chapter 6 fails at the last step instead:

<ul class="trace">
<li>$\cdot\,;\cdot \vdash \tPi{P}{\Sort{0}}{\tPi{h}{P}{\Sort{0}}} \alphaeq \tPi{P}{\Sort{0}}{\tPi{\_}{P}{P}}$ <span class="rule">$\alpha$-Pi</span>
  <ul>
  <li>$\cdot\,;\cdot \vdash \Sort{0} \alphaeq \Sort{0}$: holds <span class="rule">$\alpha$-Sort</span></li>
  <li>$P;\, P \vdash \tPi{h}{P}{\Sort{0}} \alphaeq \tPi{\_}{P}{P}$ <span class="rule">$\alpha$-Pi</span>
    <ul>
    <li>$P;\, P \vdash P \alphaeq P$: holds <span class="rule">$\alpha$-Bound</span></li>
    <li class="fail">$P, h;\; P, \_ \vdash \Sort{0} \alphaeq P$: no rule applies</li>
    </ul>
  </li>
  </ul>
</li>
</ul>

Positions also tell apart terms that a careless comparison of names would confuse. $\tLam{x}{A}{\tLam{y}{A}{x}}$ and $\tLam{a}{A}{\tLam{b}{A}{b}}$ are *not* alpha-equivalent: the bodies reach $x, y;\, a, b \vdash x \alphaeq b$, and $\mathrm{idx}$ gives $1$ for $x$ but $0$ for $b$. Conversely, $\tLam{x}{A}{\tLam{x}{A}{x}}$ and $\tLam{a}{A}{\tLam{b}{A}{b}}$ *are* alpha-equivalent, because the last occurrence of $x$ in $(x, x)$ has index $0$, the same as $b$ in $(a, b)$.

The rules of Figure 11.1 are a different definition from Definition 11.3, so we must check that they agree.

<div class="theorem" markdown="1">

**Theorem 11.4 (Correctness of algorithmic alpha-equivalence).** For all terms $s$ and $t$, $s \alphaeq t$ in the sense of Definition 11.3 if and only if $\cdot\,;\cdot \vdash s \alphaeq t$ is derivable by the rules of Figure 11.1.

</div>

The idea of the proof is that both sides say the same thing: $s$ and $t$ have the same de Bruijn representation. For the algorithm this is almost immediate, since its rules compare positions exactly as de Bruijn indices do. For Definition 11.3, the key fact is that renaming a bound variable does not change the de Bruijn representation. [Appendix B](b-proof-alpha.md) gives the full proof.

<aside class="code" markdown="1">

Figure 11.1 is the function `alpha` in `src/substitution.rs`. The two binder lists are `Vec<String>`s pushed and popped around the recursive call on bodies, and `binder_distance` is $\mathrm{idx}$: it searches the list from the end, so the distance to the nearest enclosing binder of that name is found first.

```rust
(Term::Var(x), Term::Var(y)) => {
    match (binder_distance(bound_a, x), binder_distance(bound_b, y)) {
        (Some(i), Some(j)) => i == j,     // alpha-Bound
        (None, None) => x == y,           // alpha-Free
        _ => false,                       // bound on one side only
    }
}
```

</aside>

## Exercises

<div class="exercise" markdown="1">

Compute $\subst{(\tLam{y}{A}{\tLam{x}{B}{x\;y}})}{x}{y}$ step by step.

<details markdown="1">
<summary>Solution</summary>

The outer binder is $y$, which is free in the replacement $y$, so the capture case applies: rename $y$ to a fresh $z$, giving body $\tLam{x}{B}{x\;z}$, then substitute. The inner binder is $x$, the variable being replaced, so the inner body is untouched. Result: $\tLam{z}{A}{\tLam{x}{B}{x\;z}}$. Note that the inner $x$ was never a free occurrence, so nothing was replaced at all; the only effect was the renaming forced by capture avoidance.

</details>

</div>

<div class="exercise" markdown="1">

Decide whether $\tLam{x}{A}{\tLam{y}{A}{y\;x}}$ and $\tLam{y}{A}{\tLam{x}{A}{x\;y}}$ are alpha-equivalent by running Figure 11.1.

<details markdown="1">
<summary>Solution</summary>

Yes. After two $\alpha$-Lam steps, the binder lists are $x, y$ and $y, x$, while the bodies are $y\;x$ and $x\;y$. The two $\alpha$-App comparisons match $y$ with $x$ at indices $0$ and $0$, then $x$ with $y$ at indices $1$ and $1$. The names are swapped, but their positions agree.

</details>

</div>

<div class="summary-box" markdown="1">

What to remember

- Substitution replaces free occurrences only, and must rename a binder when the replacement mentions the binder's name (capture).
- The same capture problem arises in contexts. A kernel that lets a binder shadow a context entry can prove False; Freshen prevents it.
- Alpha-equivalence compares bound variables by the position of their binder and free variables by name. Figure 11.1 is the algorithm; Theorem 11.4 says it matches the definition.
- All three live in `src/substitution.rs`: `subst`, `fv`, and `alpha`.

</div>
