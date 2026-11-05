<div class="lead" markdown="1">

Lean users rarely write terms like the one at the end of Chapter 9 by hand. They write a tactic script, a sequence of commands that build the term step by step while the system displays what remains to be proved. This chapter shows how the common tactics construct terms in our system, and why none of them needs to be trusted.

</div>

In Lean, the theorem of Chapter 9 is proved like this:

```lean
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
```

Each tactic is a small program that builds part of the proof term. Tactics run *outside* the kernel. Their output is an ordinary term, which the kernel checks with Algorithm 5.1 like any other term.

## Goals and proof states

A **goal** $\goal{\Gamma}{\hole{m}}{T}$ asks for a term of type $T$ in the context $\Gamma$. The **hole** $\hole{m}$ stands for the term still to be found; Lean calls it a *metavariable*. A **proof state** is a list of goals together with a **partial proof term**, a term that may contain holes.

To prove $T$, we start from the partial term $\hole{0}$ and the single goal $\goal{\cdot}{\hole{0}}{T}$. A tactic works on the first goal $\goal{\Gamma}{\hole{m}}{T}$. It **assigns** to $\hole{m}$ a term that may contain fresh holes, and replaces the goal by one new goal for each fresh hole. When no goals remain, the partial term contains no holes, and the kernel checks it against $T$. A hole may sit under binders, as $\hole{1}$ does in $\tLam{x}{A}{\hole{1}}$, and the term that fills it may use those bound variables. That is why each goal carries its own context.

Each tactic must make sure that its assignment has type $T$ in $\Gamma$, assuming each fresh hole is later filled with a term of the type its goal states. We write $\goal{\Gamma}{\hole{m}}{T} \leadsto \text{new goals}$, followed by the assignment.

### A first example

The script `examples/identity.leanmini` proves the opening example of Chapter 1. The explorer below runs it one command at a time.

<div class="explorer" data-kind="proof" data-title="proof explorer: identity"><pre class="script">goal forall (P : Sort 0), P -> P
intro P
intro p
exact p
qed</pre></div>

Step through it with the buttons or the arrow keys. The middle panel is the list of goals after each command, and the right panel is the partial proof term, with the hole for the current goal highlighted. The three panels always agree: a tactic changes the goals *because* it assigns a term to a hole.

A list of goals alone would not be enough: after `intro p`, the goal $P$ does not remember that its solution must be wrapped in two $\lambda$s. The partial term records exactly that.

## Basic tactics

**`intro x`.** If $T$ normalizes to a $\Pi$-type, the tactic moves its argument into the context:

$$
\goal{\Gamma}{\hole{m}}{\tPi{y}{A}{B}} \;\leadsto\; \goal{\Gamma, x : A}{\hole{1}}{\subst{B}{y}{x}},
\qquad
\hole{m} \mathrel{:=} \tLam{x}{A}{\hole{1}}.
$$

The assignment has the right type by T-Lam. The name $x$ must not be in $\dom(\Gamma)$; otherwise the new assumption would shadow an existing one, which makes the kernel unsound ([Chapter 11](11-substitution-alpha.md#variable-capture-in-contexts)). Our `intro` refuses such a name with the message "binder name already in context"; Lean renames it.

**`exact t`.** The tactic closes the goal with a given term:

$$
\goal{\Gamma}{\hole{m}}{T} \;\leadsto\; \text{no goals},
\qquad
\hole{m} \mathrel{:=} t,
$$

after running $\Check(\Gamma, t, T)$ itself. The kernel would reject an ill-typed $t$ at the end anyway; checking early only gives a better error message.

**`apply f`.** If $f$ has type $A_1 \to \cdots \to A_n \to B$ with $B \conv T$, the tactic leaves the arguments as new goals:

$$
\goal{\Gamma}{\hole{m}}{T} \;\leadsto\; \goal{\Gamma}{\hole{1}}{A_1}, \ldots, \goal{\Gamma}{\hole{n}}{A_n},
\qquad
\hole{m} \mathrel{:=} f\;\hole{1} \cdots \hole{n}.
$$

The assignment has type $B$ by $n$ uses of T-App, and type $T$ by T-Conv. When the type of $f$ is a dependent $\Pi$, later $A_i$ and $B$ mention earlier arguments, and the tactic must find those arguments by matching $B$ against $T$. Lean does this by *unification*, solving for metavariables. Our restricted version handles only non-dependent arrows, and reports "dependent apply requires elaboration/unification" otherwise. (With $n = 0$, that is, when the type of $f$ is already convertible to $T$, `apply f` behaves like `exact f`.)

For example, transitivity of implication, the second exercise of Chapter 6, works backwards from the conclusion:

<div class="explorer" data-kind="proof" data-title="proof explorer: transitivity with apply"><pre class="script">goal forall (P : Sort 0), forall (Q : Sort 0), forall (R : Sort 0), (P -> Q) -> (Q -> R) -> P -> R
intro P
intro Q
intro R
intro f
intro g
intro p
apply g
apply f
exact p
qed</pre></div>

After the six `intro`s the goal is $\goal{\Gamma}{\hole{6}}{R}$ with $\Gamma = P, Q, R : \Sort{0},\; f : P \to Q,\; g : Q \to R,\; p : P$. No hypothesis has type $R$, so `exact` cannot close it, but $g$ *ends in* $R$: `apply g` assigns $\hole{6} \mathrel{:=} g\;\hole{7}$ and leaves $\hole{7} : Q$. Likewise `apply f` assigns $\hole{7} \mathrel{:=} f\;\hole{8}$ and leaves $\hole{8} : P$, which `exact p` closes. The body of the resulting term is $g\;(f\;p)$. Note the difference between the two tactics: `exact g` fails, because $g$ has type $Q \to R$, not $R$, whereas `apply g` turns the missing argument of $g$ into a new goal.

**`change T'`.** The tactic replaces the goal by a definitionally equal one:

$$
\goal{\Gamma}{\hole{m}}{T} \;\leadsto\; \goal{\Gamma}{\hole{1}}{T'},
\qquad
\hole{m} \mathrel{:=} \hole{1},
$$

provided $T'$ is a type and $T' \conv T$. It adds nothing to the term; it only changes how the goal is displayed, and T-Conv justifies it. `change` is needed because `rw` (below) finds subterms only up to alpha-equivalence: a subterm that appears only after computation must first be exposed with `change`, as in the example at the end of this chapter.

**`rfl`.** If $T$ normalizes to $\Eq{u}\;A\;a\;b$ with $a \conv b$, the tactic closes the goal:

$$
\goal{\Gamma}{\hole{m}}{\Eq{u}\;A\;a\;b} \;\leadsto\; \text{no goals},
\qquad
\hole{m} \mathrel{:=} \refl{u}\;A\;a.
$$

The assignment has type $\Eq{u}\;A\;a\;a$, which is convertible to the goal. So `rfl` proves exactly the equations that hold by definitional equality ([Chapter 9](09-equality.md)).

## Induction

Let $n : \Nat$ be a variable in $\Gamma$, and let $\Gamma \vdash T : \Sort{u}$. The tactic `induction n` abstracts $n$ in the goal to form the motive, and produces one goal per constructor:

$$
\begin{array}{l}
\goal{\Gamma}{\hole{m}}{T}
\;\leadsto\;
\goal{\Gamma}{\hole{z}}{\subst{T}{n}{\zero}},\;
\goal{\Gamma, k : \Nat, \mathit{ih} : \subst{T}{n}{k}}{\hole{s}}{\subst{T}{n}{\suc\;k}}, \\[4pt]
\hole{m} \mathrel{:=} \NatRec{u}\;(\tLam{z}{\Nat}{\subst{T}{n}{z}})\;\hole{z}\;(\tLam{k}{\Nat}{\tLam{\mathit{ih}}{\subst{T}{n}{k}}{\hole{s}}})\;n.
\end{array}
$$

With the motive $M = \tLam{z}{\Nat}{\subst{T}{n}{z}}$, the type of $\NatRec{u}\;M$ asks for $M\;\zero$ and $\tPi{k}{\Nat}{M\;k \to M\;(\suc\;k)}$, and the result has type $M\;n$. These are convertible to the types of the two goals and to $T$, by beta. The construction is correct only if the names are fresh, the level $u$ is right, and no other hypothesis mentions $n$.

- The motive binds a fresh name $z$, not $n$: since $n$ is already in $\Gamma$, writing $\tLam{n}{\Nat}{T}$ would shadow it, which is the pitfall of Chapter 11. Likewise $k$ and $\mathit{ih}$ must be fresh. (Our implementation names the motive's variable `ind_x`, the successor's field `k` when `n` is taken, and the hypothesis `ih`.)
- The level $u$ of the motive comes from the type of the goal, found by $\InferSort$. For a proposition it is $0$, and $\NatRec{0}$ is induction.
- If another hypothesis mentions $n$, for example $h : n = 2$, the new goals still contain $h$ about the original $n$, and $\mathit{ih}$ says nothing about it. The goals are then correct but may be unprovable. Lean's `induction` first moves such hypotheses into the goal (it *reverts* them), so that they become part of the motive. Our version requires that no later hypothesis mentions $n$, and says "induction: revert dependent hypotheses first" otherwise.

The implementation is not specific to $\Nat$. It works for any inductive type without indices: it reads the recursor's type from the signature, peels one minor premise per constructor, and turns each into a goal whose context contains the constructor's fields and induction hypotheses. The script `examples/generic-list.leanmini` uses it on a user-declared list type.

## Rewriting

Let $h : \Eq{u}\;A\;a\;b$, and let the goal $T$ be a proposition. The tactic `rw h` replaces $a$ by $b$ in the goal in three steps.

1. **Abstract.** Choose a fresh $x$ and let $C$ be $T$ with every occurrence of $a$ replaced by $x$. Occurrences are found up to alpha-equivalence, not up to conversion, and an occurrence under a binder that binds a free variable of $a$ is skipped, since there it denotes something else.
2. **Check the motive.** Check that $\Gamma, x : A \vdash C : \Sort{0}$. This can fail, as shown below.
3. **Build the term.** The new goal is $\subst{C}{x}{b}$, the goal with $a$ replaced by $b$:
   $$
   \goal{\Gamma}{\hole{m}}{T} \;\leadsto\; \goal{\Gamma}{\hole{1}}{\subst{C}{x}{b}},
   \qquad
   \hole{m} \mathrel{:=} \EqRec{u,0}\;A\;a\;(\tLam{x}{A}{C \to T})\;(\tLam{p}{T}{p})\;b\;h\;\hole{1}.
   $$

To see that the assignment has type $T$, write $N = \tLam{x}{A}{C \to T}$ for the motive. Since $\subst{C}{x}{a} = T$, the term $N\;a$ is convertible to $T \to T$, which the identity $\tLam{p}{T}{p}$ inhabits. Transport along $h$ then gives $N\;b$, which is convertible to $\subst{C}{x}{b} \to T$, and applying it to $\hole{1}$ gives $T$. Lean builds a different term, `Eq.mpr (congrArg (fun x => C) h)`, from the same idea, and additionally tries to close the new goal with `rfl`; ours leaves that to an explicit `rfl`, so the two steps are visible in the script.

**When the motive is ill typed.** Abstracting $a$ can break the goal. Let $\Gamma = n : \Nat,\; h : n = 2,\; q : n = 0$, and suppose we run `rw h` on the goal $\Eq{0}\;(n = 0)\;q\;q$, a statement about the proof $q$. Abstracting $n$ gives $C = \Eq{0}\;(x = 0)\;q\;q$, which is ill typed: $q$ has type $n = 0$, not $x = 0$, and $q$ itself cannot be abstracted. Step 2 fails, and Lean reports the same situation as "motive is not type correct". Without step 2 the tactic would produce a term that the kernel rejects, which is harmless for soundness but unhelpful for the user.

<aside class="code" markdown="1">

Tactics are methods of `ProofState` in `src/proof.rs`. The partial proof term is a `Template` (`src/template.rs`), a term with `Hole(i)` nodes; `materialize` substitutes the solutions and fails if any hole is unsolved. `ProofState::replace` performs an assignment: it records the solution for the current goal and splices the new goals in at the front. `intro`, `exact`, `apply`, `change`, `rfl`, `induction`, and `rw` each follow the description above; `rw` uses `replace_exact` for step 1 and `check_transport` for step 2, and `finish` is `qed`: it materializes the term and calls `Kernel::check` against the original goal.

</aside>

## Example: 0 + n = n with tactics

In our system the proof of Chapter 9 becomes the following script, which is `examples/zero-add.leanmini` with the definition of $\add$ included (the script writes `add Nat.zero n` for $0 + n$).

<div class="explorer" data-kind="proof" data-title="proof explorer: 0 + n = n"><pre class="script">def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n
goal forall (n : Nat), Eq Nat (add Nat.zero n) n
intro n
induction n
rfl
change Eq Nat (Nat.succ (add Nat.zero k)) (Nat.succ k)
rw ih
rfl
qed</pre></div>

Watch the partial term grow: `induction n` inserts $\NatRec{0}$ with two holes, `rfl` fills the first, `change` leaves the term alone and only rewrites the goal, and `rw ih` inserts the transport with one hole left for the final `rfl`. Delete the `change` line and apply the script to see `rw` fail to find its left-hand side.

<div class="playground" data-file="examples/zero-add.leanmini"><pre># Addition by recursion on the second argument:
#   add m zero     = m
#   add m (succ k) = succ (add m k)
def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n

# add zero n = n is not definitional, so it needs induction on n.
goal forall (n : Nat), Eq Nat (add Nat.zero n) n
intro n
induction n
# Base case: add zero zero reduces to zero.
rfl
# Step case: unfold add zero (succ k) to succ (add zero k), then use ih.
change Eq Nat (Nat.succ (add Nat.zero k)) (Nat.succ k)
rw ih
rfl
qed</pre></div>

The term differs from the hand-written one of Chapter 9 in two places: it starts with $\tLam{n}{\Nat}{\ldots\;n}$ because of `intro`, and its step uses the motive built by `rw`. Both are proofs of the same proposition, and the kernel does not care which one it receives. Try deleting the `change` line in the playground and read the error `rw` gives.

## Why tactics need not be trusted

The kernel checks the final term, so tactics do not have to be correct for the system to be sound. A buggy tactic can fail, or it can produce an ill-typed term, which the kernel rejects; it cannot make the kernel accept a false theorem. The checks that tactics perform themselves, such as $\Check$ in `exact` or the motive check in `rw`, exist only to report errors early and clearly.

The trusted part of the system is therefore small: Algorithm 5.1, the reduction and comparison functions of Part III, and the signature-building procedure of Chapter 8. Everything in `src/proof.rs` and `src/syntax.rs` is outside it.

Lean's tactic framework is far richer than the one sketched here. It has metavariables solved by unification, an elaborator that fills in implicit arguments and expands notation such as `0 + n`, an `induction` that reverts dependent hypotheses and handles indexed families, and automation such as `simp`. All of this lives on the untrusted side: Lean's kernel, like ours, only ever sees complete terms [de Moura and Ullrich 2021].

## Exercises

<div class="exercise" markdown="1">

Prove $\tPi{n}{\Nat}{n = n}$ with tactics, by induction, and explain why `rfl` closes both cases.

<details markdown="1">
<summary>Solution</summary>

This is `examples/nat-reflexivity.leanmini`: `intro n`, `induction n`, `rfl`, `rfl`, `qed`. The base goal is $0 = 0$ and the step goal is $\suc\;k = \suc\;k$; both sides are syntactically identical, so definitional equality holds trivially. The induction is unnecessary here (a single `rfl` after `intro n` would do) but shows the shape of the goals.

</details>

</div>

<div class="exercise" markdown="1">

Write the term that `rw` produces when the goal is $\Eq{}\;\Nat\;a\;c$, the hypothesis is $h : a = b$, and the context is $a, b, c : \Nat$.

<details markdown="1">
<summary>Solution</summary>

Abstracting $a$ gives $C = (x = c)$ and the new goal $b = c$. The assignment is
$\EqRec{1,0}\;\Nat\;a\;(\tLam{x}{\Nat}{(x = c) \to (a = c)})\;(\tLam{p}{a = c}{p})\;b\;h\;\hole{1}$ with $\hole{1} : b = c$.

</details>

</div>

<div class="summary-box" markdown="1">

What to remember

- A proof state is a list of goals plus a partial term with holes. A tactic assigns a term to the first hole and opens one new goal per fresh hole.
- `intro` builds a $\lambda$, `exact` plugs in a term, `apply` builds an application with holes for the arguments, `change` uses T-Conv, `rfl` uses $\refl{}$.
- `induction` abstracts the variable into a motive and applies the recursor; `rw` abstracts the left side into a motive and applies transport.
- The kernel re-checks the complete term, so tactics are outside the trusted base.

</div>
