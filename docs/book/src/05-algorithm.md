<div class="lead" markdown="1">

The typing rules say which judgments hold; they do not say how to find out. This chapter turns them into an algorithm. The standard trick is to split the work into two mutually recursive functions, one that computes the type of a term and one that compares a computed type with an expected one, and to use definitional equality only in the second. The result is a few dozen lines of Rust.

</div>

## From rules to an algorithm

Seven of the eight rules of Figure 3.1 are *syntax-directed*: looking at the term tells you which rule applies. A universe triggers T-Sort, a variable T-Var, a $\Pi$ T-Pi, a $\lambda$ T-Lam, an application T-App. T-Conv is the exception. It can be applied to any term at any point, so a program cannot tell from the term when to use it, and a naive search for a derivation would have to guess.

The standard solution [Barendregt 1992] is to split type checking into two functions:

- $\Infer(\Gamma, t)$ computes *the* type of $t$ in $\Gamma$, following the syntax-directed rules, or fails.
- $\Check(\Gamma, t, T)$ verifies that $t$ has the expected type $T$: it infers a type and compares it with $T$ using definitional equality.

T-Conv is applied in exactly one place, inside $\Check$. There are two further places where a type must have a particular shape, a $\Pi$ in T-App and a universe in the premises of T-Pi and T-Lam. There the algorithm computes the inferred type just far enough to see its outermost form.

The algorithm uses two functions on terms whose definitions are postponed to [Chapter 12](12-reduction-conversion.md):

- $\Whnf(T)$ computes $T$ until its outermost shape is visible. For example, $\Whnf(\mathit{Id}\;(P \to P)) = P \to P$, which is a $\Pi$.
- $\IsDefEq(A, B)$ decides $A \conv B$.

## The algorithm

Algorithm 5.1 is written in pseudocode close to the Rust. Each case of $\Infer$ is annotated with the rule it implements.

<div class="rulebox" markdown="1">

<p class="caption">Algorithm 5.1. Type inference and checking.</p>

```text
Infer(Γ, t):
  if t = Sort u:                                        -- T-Sort
      return Sort (u + 1)
  if t = x:                                             -- T-Var
      if (x : A) ∈ Γ: return A  else fail "unbound variable"
  if t = Π(x : A). B:                                   -- T-Pi
      u ← InferSort(Γ, A)
      (x', B') ← Freshen(Γ, x, B)
      v ← InferSort((Γ, x' : A), B')
      return Sort (imax(u, v))
  if t = λ(x : A). s:                                   -- T-Lam
      InferSort(Γ, A)
      (x', s') ← Freshen(Γ, x, s)
      B ← Infer((Γ, x' : A), s')
      return Π(x' : A). B
  if t = f a:                                           -- T-App
      T ← Whnf(Infer(Γ, f))
      if T = Π(x : A). B:
          Check(Γ, a, A)
          return B[x ↦ a]
      else fail "not a function"

Check(Γ, t, T):                                         -- T-Conv
  T' ← Infer(Γ, t)
  if IsDefEq(T', T): return  else fail "type mismatch"

InferSort(Γ, A):
  T ← Whnf(Infer(Γ, A))
  if T = Sort u: return u  else fail "expected a type"

Freshen(Γ, x, b):
  if x ∈ dom(Γ):
      choose x' ∉ dom(Γ) ∪ FV(b)
      return (x', b[x ↦ x'])
  else return (x, b)
```

</div>

The algorithm has the following properties.

- **Syntax-directed.** Each case of $\Infer$ corresponds to exactly one rule of Figure 3.1. Finding a proof may be hard, but checking a given proof is mechanical: there is never a choice to make.
- **T-Conv is never applied on its own.** It happens inside $\Check$, the only place where an inferred type meets an expected one.
- **$\InferSort$ is how the kernel decides whether a term is a type.** A term $A$ is a type exactly when its type computes to a universe. A $\lambda$-abstraction, for instance, is never a type, because its inferred type is always a $\Pi$.
- **$\Freshen$ implements the side condition of C-Ext.** It renames a binder whose name is already in the context. [Chapter 11](11-substitution-alpha.md#variable-capture-in-contexts) shows a term that makes the kernel unsound without this step.
- **Contexts stay well formed.** Starting from the empty context, every context the algorithm builds is well formed, because an assumption is added only after $\InferSort$ has succeeded on its type. A caller that starts from a non-empty context must check that context separately.
- **Termination** depends on $\Whnf$ and $\IsDefEq$ terminating, which holds for well-typed terms by strong normalization ([Chapter 14](14-properties.md)).

<aside class="intuition" markdown="1">

The division into $\Infer$ and $\Check$ is sometimes called *bidirectional* type checking. The intuition is that information flows in two directions. Inference flows *up* from the leaves: a variable knows its type, an application computes its type from its parts. Checking flows *down* from an expectation: the user says "this term should have this type", and the comparison happens at the root. In our kernel, every term can be inferred, so checking is just inference plus one comparison; in richer systems some terms can only be checked, not inferred.

</aside>

## In the code

<aside class="code" markdown="1">

Algorithm 5.1 is `Kernel::infer`, `Kernel::check`, and `Kernel::infer_sort` in `src/typecheck.rs`; `Freshen` is the helper `rename_binder_if_needed` in the same file. Below is the complete `infer`, with the constants case of Part II included.

</aside>

```rust
pub fn infer(&self, ctx: &Context, t: &Term) -> Result<Term> {
    match t {
        // T-Sort
        Term::Sort(u) => Ok(Term::Sort(u.checked_add(1).ok_or("universe overflow")?)),
        // T-Var
        Term::Var(x) => ctx
            .iter()
            .rev()
            .find(|(name, _)| name == x)
            .map(|(_, ty)| ty.clone())
            .ok_or_else(|| format!("unbound local: {x}")),
        // T-Const (Chapter 7)
        Term::Const(c) => self
            .decls
            .get(c)
            .map(|decl| decl.ty.clone())
            .ok_or_else(|| format!("unknown constant: {c}")),
        // T-Pi: Sort 0 is impredicative.
        Term::Pi(x, domain, body) => {
            let domain_level = self.infer_sort(ctx, domain)?;
            let (x, body) = rename_binder_if_needed(ctx, x, body);
            let mut extended = ctx.clone();
            extended.push((x, (**domain).clone()));
            let body_level = self.infer_sort(&extended, &body)?;
            Ok(Term::Sort(if body_level == 0 {
                0
            } else {
                domain_level.max(body_level)
            }))
        }
        // T-Lam
        Term::Lam(x, domain, body) => {
            self.infer_sort(ctx, domain)?;
            let (x, body) = rename_binder_if_needed(ctx, x, body);
            let mut extended = ctx.clone();
            extended.push((x.clone(), (**domain).clone()));
            let body_type = self.infer(&extended, &body)?;
            Ok(Term::Pi(x, domain.clone(), Box::new(body_type)))
        }
        // T-App
        Term::App(f, a) => match self.whnf(&self.infer(ctx, f)?)? {
            Term::Pi(x, domain, codomain) => {
                self.check(ctx, a, &domain)?;
                Ok(subst(&codomain, &x, a))
            }
            ty => Err(format!("application of non-function: {ty:?}")),
        },
    }
}
```

A few details are worth noticing against the pseudocode.

- The context lookup in the variable case searches from the end (`.rev()`). Because `rename_binder_if_needed` keeps names distinct, there is never more than one match, but searching from the end is the right behaviour if a caller passes a context with repeated names.
- The $\imax$ of T-Pi is the `if body_level == 0` expression: a $\Pi$ whose body is a proposition is a proposition, otherwise it lives in the maximum of the two levels.
- The universe level is a `u64` and `checked_add` guards against overflow. No real proof comes anywhere near level $2^{64}$, but a kernel should not have undefined behaviour on any input.
- The application case calls `whnf` on the inferred type of `f` before matching on it, exactly as the pseudocode does. Without this, a function whose type is written as $\mathit{Id}\;(A \to B)$ could not be applied.

The remaining two functions are short.

```rust
/// Gamma |- t : expected, using T-Conv to compare the inferred type.
pub fn check(&self, ctx: &Context, t: &Term, expected: &Term) -> Result<()> {
    self.infer_sort(ctx, expected)?;
    let actual = self.infer(ctx, t)?;
    if self.is_def_eq(&actual, expected)? {
        Ok(())
    } else {
        Err(format!("type mismatch: actual {actual:?}, expected {expected:?}"))
    }
}

/// Infers the type of t and requires it to be a universe Sort u. Returns u.
pub fn infer_sort(&self, ctx: &Context, t: &Term) -> Result<u64> {
    match self.whnf(&self.infer(ctx, t)?)? {
        Term::Sort(u) => Ok(u),
        other => Err(format!("expected a type, got {other:?}")),
    }
}
```

`check` begins with `infer_sort(ctx, expected)`. That is the premise $\Gamma \vdash B : \Sort{u}$ of T-Conv: the expected type must itself be a type. The pseudocode omits it because callers inside the algorithm always pass types that have already been checked, but the public `check` is also called with user-supplied statements, so the Rust version verifies it.

Finally, `Freshen`:

```rust
fn rename_binder_if_needed(ctx: &Context, x: &str, body: &Term) -> (String, Term) {
    if !ctx.iter().any(|(name, _)| name == x) {
        return (x.into(), body.clone());
    }
    let mut used = all_names(body);
    for (name, ty) in ctx {
        used.insert(name.clone());
        used.extend(all_names(ty));
    }
    let renamed = fresh(x, &used);
    let renamed_body = subst(body, x, &var(&renamed));
    (renamed, renamed_body)
}
```

The set of names to avoid is larger than the pseudocode's $\dom(\Gamma) \cup \FV(b)$: it includes every name appearing anywhere in the body and in the context's types, bound or free. Avoiding more names than necessary is always safe, and it keeps the renamed term readable. `fresh` appends primes until the name is unused, so a clash on `x` produces `x'`.

## How a proof is checked

To verify that a term $t$ proves a theorem $T$, the kernel runs $\Check(\cdot, t, T)$ in the empty context. In the script language this is what `qed` does: the tactics of [Chapter 10](10-tactics.md) assemble a term, and `qed` hands it to `check` together with the statement given by `goal`. Everything between is untrusted.

The next chapter runs $\Infer$ and $\Check$ by hand on several terms, including one that is well typed but does not prove what it claims to.

## Exercises

<div class="exercise" markdown="1">

Trace $\Infer(\cdot, \tLam{A}{\Sort{1}}{\tLam{a}{A}{a}})$ and give the result and its universe.

<details markdown="1">
<summary>Solution</summary>

$\InferSort(\cdot, \Sort{1})$ returns $2$. The context becomes $A : \Sort{1}$. For the inner $\lambda$, $\InferSort(A : \Sort{1}, A)$ returns $1$, the context becomes $A : \Sort{1}, a : A$, and $\Infer$ returns $A$ for the body. So the inner result is $\tPi{a}{A}{A}$ and the outer result is $\tPi{A}{\Sort{1}}{\tPi{a}{A}{A}}$. Running $\InferSort$ on that type gives $\imax(2, \imax(1, 1)) = 2$, so the type lives in $\Sort{2}$.

</details>

</div>

<div class="exercise" markdown="1">

Why does the $\Pi$ case of $\Infer$ call $\Freshen$ even though a $\Pi$-type is "just a type"? Give a term where skipping it would change the result.

<details markdown="1">
<summary>Solution</summary>

The body of a $\Pi$ is checked in an extended context, so the same shadowing problem arises as for $\lambda$. For $\Gamma = x : \Sort{0}, y : x$, the type $\tPi{x}{\Sort{1}}{y}$ should fail, because $y : x$ where $x$ is the outer proposition and a proposition is not a universe. Without renaming, the inner $x : \Sort{1}$ would be found first by the reversed lookup, making $y$'s type appear to be $\Sort{1}$-valued, and the result would be wrong. With renaming the inner binder becomes $x'$ and the body still refers to the outer $x$.

</details>

</div>

<div class="summary-box" markdown="1">

What to remember

- $\Infer$ follows the shape of the term; $\Check$ infers and then compares with $\IsDefEq$. T-Conv lives only inside $\Check$.
- $\Whnf$ exposes the outermost shape of a type where a $\Pi$ or a universe is required.
- $\InferSort$ is the test "is this term a type?": its type must compute to a universe.
- $\Freshen$ renames binders that would shadow a context entry. It is a correctness requirement, not a convenience.
- `src/typecheck.rs` is a direct transcription, about one hundred lines.

</div>
