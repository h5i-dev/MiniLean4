<div class="lead" markdown="1">

The scripts in this book are written in a small language called leanmini, read by the parser in `src/syntax.rs` and the command loop in `src/main.rs`. It is deliberately explicit: every binder carries its type, every argument is written out, and nothing is inferred. This appendix is the complete reference, derived line by line from the code, together with every example script of the repository in a runnable form.

</div>

## Running scripts

The runner is the binary `mini-lean` built from `src/main.rs`.

```text
cargo run -- examples/identity.leanmini    # run a script file
cargo run                                  # interactive session on stdin
cargo test                                 # the kernel's own test suite
```

A script is a sequence of lines. The runner processes them from top to bottom and stops at the first error, printing the message and exiting with status 1. Blank lines and lines beginning with `#` are comments and are skipped.

```leanmini
# This is a comment.
goal forall (P : Sort 0), P -> P
```

Without a file argument the runner reads the same commands from standard input, one per line, after printing a reminder of the available commands. Errors are reported with the prefix `error:` and the session continues. The command `quit` (or `exit`) ends it. One command differs between the two modes: in a file, an `inductive` block is the header line followed by its `|` lines; interactively, the block is closed by a line containing only `end`.

<aside class="note" markdown="1">

The command-line runner prints terms in Rust's `Debug` format, for example `App(Const("Nat.succ"), Const("Nat.zero"))`, because the kernel has no pretty-printer. The playgrounds in this book run the same kernel compiled to WebAssembly, with a small pretty-printer added on top that writes terms back in leanmini syntax, and they echo each command before its output so that the transcript can be read on its own.

</aside>

## Terms

A term is written in one of the following forms. `A`, `B`, `t` stand for terms and `x` for a name.

| Syntax | Meaning | Notation in the book |
|---|---|---|
| `Sort 0`, `Sort 1`, ... | A universe; the number is required | $\Sort{u}$ |
| `x` | A variable or a constant, depending on scope | $x$ or $c$ |
| `forall (x : A), B` | A dependent function type | $\tPi{x}{A}{B}$ |
| `A -> B` | A non-dependent function type | $A \to B$ |
| `fun (x : A) => t` | A function | $\tLam{x}{A}{t}$ |
| `f a` | Application | $f\;a$ |
| `(t)` | Grouping | |

Application associates to the left and binds tightest: `f a b` is `(f a) b`. Arrows associate to the right: `A -> B -> C` is `A -> (B -> C)`. A `forall` or `fun` extends as far to the right as possible, and so does the right-hand side of an arrow, so `A -> forall (x : B), C` needs no parentheses. A `forall` or `fun` used as an *argument* must be parenthesized, as in `Nat.rec1 (fun (_n : Nat) => Nat) m`. The arrow `A -> B` is read as `forall (_ : A), B`; the name `_` is reserved for this purpose and may not be used as a binder in an inductive declaration.

The tokenizer splits on whitespace and on the characters `(`, `)`, `,`, `:`, and the two-character symbols `->` and `=>`. A name is a run of letters, digits, `_`, `'`, and `.`, so `Nat.succ`, `List.rec1`, and `x'` are single names. Three Unicode characters are accepted as aliases: `→` for `->`, `λ` for `fun`, and `∀` for `forall`. Any other character is rejected with `unexpected character: ...`.

Names are resolved when the term is parsed, not later.

- A name bound by an enclosing `fun` or `forall`, or present in the current goal's context, is a **local variable**.
- Otherwise, a name declared in the kernel (by `inductive`, `def`, `axiom`, or `recursor`, or built in) is a **constant**.
- Otherwise the parse fails with `unknown identifier: x`. This is also the error you get for a misspelled constructor or for using a hypothesis that has not been introduced yet.

A local shadows a constant of the same name. The parser never guesses types: `Sort` must be followed by a numeral, and a binder must be written `(x : A)` with its type.

## Declarations

### Inductive types

```leanmini
inductive List (A : Sort 1) : Sort 1 where
  | nil
  | cons (head : A) (tail : List A)
```

The header has the form `inductive Name (p : P) ... (index i : J) ... : Sort u where`. Each parenthesized binder is a **parameter**, or an **index** if it starts with the word `index`. Parameters must come before indices (`parameters must precede indices`). The universe after the colon must be a literal `Sort u` (`inductive result must be Sort u`), and the line must end with `where`.

Each following line begins with `|` and declares one constructor: `| ctor (field : T) ... [: Name params indices]`. Field types may mention the parameters, the earlier fields, and `Name` itself. The result type after the optional colon must be `Name` applied to the parameters, in order and unchanged (`constructor parameters must be uniform`), followed by one index term per index. If the type has indices, every constructor must give its result type (`indexed constructor requires explicit result type`); if it has none, the result type may be omitted. The `index` keyword is not allowed on constructor fields.

```leanmini
inductive Vec (A : Sort 1) (index n : Nat) : Sort 1 where
  | nil : Vec A Nat.zero
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)
```

Constructors are registered under qualified names: the declaration above adds `Vec.nil` and `Vec.cons`, and the constructors of `List` are `List.nil` and `List.cons`. Scripts must use the qualified form.

Accepting the declaration runs the four conditions of [Chapter 8](08-inductive-recipe.md): the type of `Name` is a type, each constructor type is a type that ends in `Name` applied to the parameters, every field that mentions `Name` is strictly positive, and no field lives in a universe above `Sort u` when `u` is at least 1. The messages for failures include `non-strictly-positive / unsupported recursive field`, `field f lives in Sort w, exceeding inductive universe Sort u`, and `inductive occurrence inside result index`. Binder names starting with `_` or `__` are refused (`reserved binder name`), because the kernel uses such names for the binders it generates.

On success the runner prints `inductive Name registered` and the kernel adds the type former, the constructors, the recursor `Name.rec0`, and, when large elimination is allowed, `Name.rec1`. A proposition (`Sort 0`) gets `Name.rec1` only if it is a subsingleton, as [Chapter 8](08-inductive-recipe.md) explains.

<aside class="warning" markdown="1">

In a script file, the constructor lines of an `inductive` block must follow the header without any intervening comment line. The runner collects lines that start with `|` or are blank; a `#` line ends the block early, and the first constructor line after it is then reported as `start with 'goal <type>'` (or `unknown command: ...` if a proof is in progress).

</aside>

### Definitions and axioms

```leanmini
def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n
axiom em : forall (P : Sort 0), P -> P
```

`def name : T := t` checks that `T` is a type and that `t : T` in the empty context, then adds `name` with the body `t`; the kernel unfolds it during reduction ($\delta$-reduction, [Chapter 12](12-reduction-conversion.md)). The runner prints `defined name`. A definition must fit on one line, and the first `:=` separates type from body.

`axiom name : T` adds `name : T` without a body, after checking that `T` is a type. It prints `added axiom name`. Axioms never unfold. Nothing prevents you from assuming something false this way; the kernel checks that the type is well formed, not that it is true.

Names must be new: redeclaring one fails with `duplicate declaration: name`, and nothing may be declared inside the namespace `Name.rec...` of an existing inductive type.

### Extra recursors

```leanmini
recursor Nat 2
```

`recursor I v` generates `I.recv` for the elimination universe `v`, if it does not exist yet, and prints `generated I.recv`. Levels 0 and 1 are generated automatically by `inductive`; use this command when a motive needs to return a type in `Sort 2` or higher. It fails for a proposition that does not allow large elimination (`I is not a subsingleton proposition; cannot eliminate into Sort v`).

## The standard kernel

Every session starts with `Nat` and `Eq` already declared, exactly as if the following declarations had been run. The generated binder names begin with `__`; they are shown here as `M` and `m` for readability, and renaming bound variables does not change a type.

```leanmini
Nat      : Sort 1
Nat.zero : Nat
Nat.succ : Nat -> Nat
Nat.rec0 : forall (M : Nat -> Sort 0), M Nat.zero -> (forall (n : Nat), M n -> M (Nat.succ n)) -> forall (x : Nat), M x
Nat.rec1 : forall (M : Nat -> Sort 1), M Nat.zero -> (forall (n : Nat), M n -> M (Nat.succ n)) -> forall (x : Nat), M x

Eq       : forall (A : Sort 1), A -> A -> Sort 0
Eq.refl  : forall (A : Sort 1), forall (a : A), Eq A a a
Eq.rec0  : forall (A : Sort 1), forall (a : A), forall (M : forall (b : A), Eq A a b -> Sort 0), M a (Eq.refl A a) -> forall (b : A), forall (h : Eq A a b), M b h
Eq.rec1  : forall (A : Sort 1), forall (a : A), forall (M : forall (b : A), Eq A a b -> Sort 1), M a (Eq.refl A a) -> forall (b : A), forall (h : Eq A a b), M b h
```

`Nat.rec1` is recursion into types and `Nat.rec0` is induction into propositions ([Chapter 7](07-inductive-nat.md)). `Eq` takes its type argument `A` explicitly, so the equation $a = b$ in $\Nat$ is written `Eq Nat a b`, and its proof by reflexivity is `Eq.refl Nat a` ([Chapter 9](09-equality.md)). Because `Eq` is declared with `A : Sort 1`, equality is available for types in `Sort 1` such as `Nat` and `List Nat`, not for propositions.

In general the recursor of an inductive type `I` into `Sort v` is named `I.recv`: `List.rec0`, `List.rec1`, `Vec.rec1`, and so on. Its argument order is parameters, motive, one minor premise per constructor in declaration order, indices, and finally the major premise ([Chapter 8](08-inductive-recipe.md)).

## Proofs

### Starting a goal

```leanmini
goal forall (n : Nat), Eq Nat n n
```

`goal T` checks that `T` is a type in the empty context and starts a proof with the single goal `?0 : T`. It prints nothing in the command-line runner (the playgrounds print the goal). Any tactic given before a `goal` fails with `start with 'goal <type>'`. Starting a new `goal` abandons an unfinished proof.

After every tactic, the runner prints the remaining goals, each as its number, its hypotheses, and its target after a turnstile:

```text
?3:
  n : Nat
  k : Nat
  ih : Eq Nat (add Nat.zero k) k
  ⊢ Eq Nat (add Nat.zero (Nat.succ k)) (Nat.succ k)
```

When no goals are left it prints `No goals. Run 'qed' to kernel-check.` The command `show` prints the goals without changing anything.

Tactics always act on the first goal. Terms given to tactics are parsed in that goal's context, so hypothesis names are in scope. [Chapter 10](10-tactics.md) explains what each tactic does to the partial proof term; this section states the interface.

### Tactics

**`intro x`** requires the target to reduce to a `forall` or an arrow. It adds `x : A` to the context, where `A` is the domain, and makes the body the new target. The name must not already be in the context (`binder name already in context`); otherwise the message is `intro expects a Pi/arrow goal`.

**`exact t`** closes the goal with `t`, after checking `t` against the target. A mismatch is reported by the kernel as `type mismatch: actual ..., expected ...`.

**`apply f`** infers the type of `f` and peels off non-dependent arrows until the result is definitionally equal to the target; each peeled domain becomes a new goal, in order. If the type of `f` already matches the target, `apply f` behaves like `exact f`. Dependent binders are refused with `dependent apply requires elaboration/unification`, and a result that never matches gives `apply result does not match the goal`.

**`change T`** replaces the target by `T`, which must be a type definitionally equal to it (`change expects definitionally equal target`). It is used to expose a subterm that only appears after computation, before `rw`.

**`rfl`** requires the target to reduce to `Eq A a b` (`rfl expects Eq A lhs rhs`) with `a` and `b` definitionally equal (`rfl: sides are not definitionally equal`), and closes it with `Eq.refl A a`.

**`rw h`** requires `h` to have a type that reduces to `Eq A a b` (`rw expects proof of equality`). It replaces every occurrence of `a` in the target by `b` and leaves the rewritten target as the new goal. Occurrences are found syntactically, up to the names of bound variables; a term that is only equal after computation is not found, which gives `rw: no syntactic occurrence of lhs in goal; use change first`. Unlike Lean's `rw`, it does not try `rfl` afterwards, so a goal of the form `Eq A x x` must still be closed explicitly. If abstracting `a` produces an ill-typed motive, the kernel's type error is reported before the proof state changes.

**`induction x`** requires `x` to be a hypothesis whose type reduces to an inductive type without indices, and no later hypothesis may mention `x` (`induction: revert dependent hypotheses first`). It creates one goal per constructor, in declaration order. Each goal's context gains the constructor's fields, under their declared names, and one induction hypothesis per recursive field, named `ih` (with primes appended if `ih` is taken). The field named `n` of `Nat.succ` is renamed to `k` when `n` is already in use, which is why the goals of the examples below mention `k` and `ih`. The recursor used is `I.recv`, where `v` is the universe of the target; if that recursor does not exist, the message is `no elimination recursor at target universe`. Indexed families are not supported (`indexed induction requires motive/index elaboration (not implemented)`).

**`qed`** fails if goals remain (`N goals remain`). Otherwise it assembles the proof term from the tactic steps, sends it to the kernel to be checked against the original goal, prints `QED. Kernel checked proof:` followed by the term, and ends the proof. This final check is the only step that the soundness of the system depends on.

Any other line gives `unknown command: ...`.

### Errors from the kernel

Some messages come from the kernel rather than from the tactic layer, and can appear under any command.

| Message | Meaning |
|---|---|
| `unbound local: x` | A variable is used outside its binder; this cannot be produced by the parser, only by a term built incorrectly. |
| `unknown constant: c` | A constant was removed or never declared. |
| `application of non-function: ...` | The function position of an application does not have a `forall` type. |
| `expected a type, got ...` | A binder annotation, goal, or declared type is not a type. |
| `type mismatch: actual ..., expected ...` | The inferred type is not definitionally equal to the required one. |
| `universe overflow` | The universe level does not fit in 64 bits. |
| `reduction fuel exhausted` | A single reduction exceeded 20,000 steps; this happens for very large computations such as adding big numerals. |

## The example scripts

Every script of the `examples/` directory follows, as a playground. Each one has been checked by the kernel; edit it and press run to see what changes.

### identity.leanmini

<div class="playground" data-file="examples/identity.leanmini"><pre># The polymorphic identity on propositions: for every P, P -&gt; P.
goal forall (P : Sort 0), P -&gt; P
intro P
intro p
exact p
qed</pre></div>

### nat-reflexivity.leanmini

<div class="playground" data-file="examples/nat-reflexivity.leanmini"><pre># Every natural number equals itself, proved by induction on Nat.
# Each case closes by rfl because both sides are syntactically the same.
goal forall (n : Nat), Eq Nat n n
intro n
induction n
rfl
rfl
qed</pre></div>

### zero-add.leanmini

<div class="playground" data-file="examples/zero-add.leanmini"><pre># Addition by recursion on the second argument:
#   add m zero     = m
#   add m (succ k) = succ (add m k)
def add : Nat -&gt; Nat -&gt; Nat := fun (m : Nat) =&gt; fun (n : Nat) =&gt; Nat.rec1 (fun (_n : Nat) =&gt; Nat) m (fun (k : Nat) =&gt; fun (r : Nat) =&gt; Nat.succ r) n

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

### generic-list.leanmini

<div class="playground" data-file="examples/generic-list.leanmini"><pre># A user-declared polymorphic list. Declaring it generates List.rec0, List.rec1, ...
inductive List (A : Sort 1) : Sort 1 where
  | nil
  | cons (head : A) (tail : List A)

# induction works for any non-indexed inductive, not only Nat.
goal forall (xs : List Nat), Eq (List Nat) xs xs
intro xs
induction xs
rfl
rfl
qed</pre></div>

### generic-vec.leanmini

<div class="playground" data-file="examples/generic-vec.leanmini"><pre># Length-indexed vectors. The index n varies between constructors,
# so it is declared with the `index` keyword in the header.
inductive Vec (A : Sort 1) (index n : Nat) : Sort 1 where
  | nil : Vec A Nat.zero
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

# Constructors take the parameter A explicitly.
def one : Vec Nat (Nat.succ Nat.zero) := Vec.cons Nat Nat.zero Nat.zero (Vec.nil Nat)

# The tactic `induction` does not support indexed families yet,
# but the kernel still checks terms that use Vec directly.
goal Eq (Vec Nat (Nat.succ Nat.zero)) one (Vec.cons Nat Nat.zero Nat.zero (Vec.nil Nat))
rfl
qed</pre></div>

## What is missing compared with Lean 4

leanmini is a vehicle for understanding the kernel, not a proof assistant. The table lists what Lean's front end does for you and this language does not.

| Lean 4 | leanmini |
|---|---|
| Implicit arguments, filled in by the elaborator | Every argument is explicit; `Eq Nat a b`, not `a = b` |
| Unification to solve for metavariables | None; tactics work only when the term fixes everything |
| Universe polymorphism (`Sort u` with a level variable) | Every level is a numeral; one recursor per level |
| Mutual and nested inductive types | A single inductive type at a time; `List Tree` as a field is rejected |
| Definitional proof irrelevance | Proofs of a proposition are compared like any terms |
| `induction` on indexed families, with reverting | Non-indexed types only; dependent hypotheses must be reverted by hand (which no tactic does) |
| `apply` with dependent arguments | Non-dependent arrows only |
| `rw` up to instances, with `rfl` afterwards | Syntactic matching only; no automatic `rfl` |
| `simp`, `omega`, and other automation | None |
| Notation, numerals, and `theorem` with named results | `Nat.succ (Nat.succ Nat.zero)`; a finished proof is not saved under a name |

The last row has a practical consequence: a `qed` prints the proof term and discards it. To reuse a result, state it as a `def` with the term written out, or as an `axiom`.

<aside class="lean" markdown="1">

Everything in the right column is work that Lean's elaborator and tactic framework perform before a term reaches the kernel. Lean's kernel, like ours, only ever sees complete terms. The limitations above are limitations of the front end in this repository, not of the type theory.

</aside>

<div class="summary-box" markdown="1">

What to remember

- A leanmini script is a list of commands: `inductive`, `def`, `axiom`, `recursor`, `goal`, and the tactics `intro`, `exact`, `apply`, `change`, `rw`, `rfl`, `induction`, closed by `qed`.
- Terms are fully explicit: `Sort u`, `forall (x : A), B`, `fun (x : A) => t`, `A -> B`, and left-associative application.
- Constructors and recursors are qualified: `List.cons`, `List.rec1`. `Nat` and `Eq` are predeclared.
- The front end is minimal by design; only the final `qed` check, performed by the kernel, matters for soundness.

</div>
