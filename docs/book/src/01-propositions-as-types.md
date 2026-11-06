<div class="lead" markdown="1">

A theorem prover has to decide whether a proof is correct. A proof written in English cannot be checked by a computer, so we need a representation of proofs that a program can inspect. This chapter introduces the idea that makes everything else possible: a proof is a program, a proposition is its type, and checking a proof is type checking.

</div>

## Proofs as programs

Here is a proof, in ordinary mathematical prose, of the proposition "$A$ implies $B$":

> Assume $A$. Then ... (some argument) ... so $B$ holds.

The shape of this proof is a function. It takes something, a reason to believe $A$, and produces something else, a reason to believe $B$. If we take this literally and treat "a reason to believe $A$" as a value of type $A$, then a proof of $A \to B$ is a function from $A$ to $B$, and the proposition $A \to B$ is the type of that function.

This observation is the **Curry-Howard correspondence**. It says that

- a proposition is a type,
- a proof of the proposition is a term of that type, and
- the proposition $A$ is true exactly when some term $t$ of type $A$ exists, written $t : A$.

Three examples show how far this already goes. On the left is a proposition, in the middle a proof of it written as a function, and on the right the idea of the proof in words. Here $\lambda x.\,e$ denotes the function that takes $x$ and returns $e$.

| Proposition | Proof | In words |
|---|---|---|
| $P \to P$ | $\lambda p.\,p$ | Return the assumption. |
| $A \to B \to A$ | $\lambda a.\,\lambda b.\,a$ | Ignore the second assumption. |
| $(A \to B) \to (B \to C) \to A \to C$ | $\lambda f.\,\lambda g.\,\lambda a.\,g\,(f\,a)$ | Compose the two implications. |

Look at the third row again. To prove that implication is transitive, you assume $A \to B$ and $B \to C$, and then, given $A$, you apply the first assumption to get $B$ and the second to get $C$. The proof term says exactly that: $f$ and $g$ are the assumptions, $a$ is the proof of $A$, and $g\,(f\,a)$ applies them in order. *Using* an assumption is *applying* a function; this is the step that distinguishes real reasoning from merely restating hypotheses, and we will return to it in [Chapter 3](03-typing-rules.md).

<aside class="intuition" markdown="1">

Think of a type as a specification and of a term as something that meets it. "There is a term of type $A$" means "the specification $A$ can be met". When $A$ is a proposition, meeting it is proving it. A type with no terms is an unprovable proposition, which is precisely the role that $\mathsf{False}$ will play later.

</aside>

## Quantifiers become dependent functions

The same idea extends to "for all". To prove that $B(x)$ holds for every $x : A$, we give a method that, handed any particular $x$, produces a proof of $B(x)$. That is again a function, with one twist: its return type depends on the argument. For $x = 3$ it returns a proof of $B(3)$, for $x = 7$ a proof of $B(7)$. A function type whose result type may mention the argument is called a **dependent function type**, or a **$\Pi$-type**, and is written

$$
\Pi(x : A).\,B(x).
$$

The ordinary function type $A \to B$ is the special case in which $B$ does not mention $x$.

For example, "every proposition implies itself" quantifies over propositions. If $\Sort{0}$ is the type of propositions, the statement is

$$
\tPi{P}{\Sort{0}}{P \to P},
$$

and its proof is the function that takes a proposition $P$, then a proof $p$ of $P$, and returns $p$:

$$
\tLam{P}{\Sort{0}}{\tLam{p}{P}{p}}.
$$

Notice that the binders now carry types: $\lambda(P : \Sort{0})$ says that $P$ ranges over propositions, and $\lambda(p : P)$ says that $p$ is a proof of the particular $P$ that was passed in. A type checker will need these annotations.

## What the kernel does

This gives us the central idea behind a theorem prover.

<div class="theorem" markdown="1">

**Proving a theorem means constructing a term of the required type, and verifying a proof means type checking that term.**

</div>

The kernel does not reason about truth. It implements typing rules, which say when a term has a type, and it mechanically checks that a given term has a given type under those rules. Whether that counts as proof checking depends on whether the typing rules faithfully implement a logic, which is the subject of [Chapter 4](04-logic.md). Whether the rules are *sound*, so that no term inhabits the type of a false proposition, is the subject of [Chapter 13](13-universes.md) and [Chapter 14](14-properties.md).

This division of labour shapes the design of every serious prover: tactics, automation, decision procedures, and even a large language model may search for proofs and may contain bugs, because the kernel checks the term they produce. Only the kernel must be correct, so the goal is to keep it small. The kernel in this book is under fifteen hundred lines of Rust, comments included.

<aside class="lean" markdown="1">

Lean 4 works the same way. The `theorem` command elaborates your statement into a type, tactics build a term of that type, and the kernel checks the term before the theorem is added to the environment. Lean's kernel is larger than ours because it supports universe polymorphism, mutual and nested inductive types, definitional proof irrelevance, and performance features such as caching and lazy unfolding, but its job is the same: decide $\Gamma \vdash t : A$.

</aside>

## The plan

The chapters of Part I build the kernel for a type theory that is just large enough to serve as a logic.

1. [Chapter 2](02-syntax.md) fixes the language: universes, variables, $\Pi$-types, $\lambda$-abstractions, and application.
2. [Chapter 3](03-typing-rules.md) gives the typing rules, one per kind of term plus one that lets computation happen inside types.
3. [Chapter 4](04-logic.md) shows that these rules are the rules of a logic, and defines consistency.
4. [Chapter 5](05-algorithm.md) turns the rules into an algorithm and matches it against the Rust implementation.
5. [Chapter 6](06-worked-examples.md) runs the algorithm by hand on correct proofs, incorrect proofs, and proofs that need computation.

Two operations are deliberately treated as black boxes until Part III: substitution and definitional equality. Both are easy to state and easy to get wrong, and the kernel's correctness depends on them.

<div class="summary-box" markdown="1">

What to remember

- Propositions are types; proofs are terms; $t : A$ means that $t$ proves $A$.
- Implication is the function type. Using a hypothesis is applying a function.
- Universal quantification is the dependent function type $\Pi(x : A).\,B(x)$.
- A theorem prover's kernel is a type checker. Everything else only produces terms for it to check.

</div>
