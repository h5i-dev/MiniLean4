# Mini Lean 4: generic inductive declarations (educational prototype)

The source uses named variables to mirror the textbook rules. Inductive declarations now enter through **both** the checked Rust `Kernel::add_inductive` API and a source-level `inductive ... where` parser. The recursor and ι-reduction are generated from constructor metadata; Nat and Eq are installed using the same API, not by recursor-name special cases.

## Commands

```sh
cargo test
cargo run -- examples/zero-add.leanmini
cargo run -- examples/generic-list.leanmini
cargo run -- examples/generic-vec.leanmini
cargo run -- examples/identity.leanmini
cargo run -- examples/nat-reflexivity.leanmini
```

## Source-level inductive syntax

```text
inductive List (A : Sort 1) : Sort 1 where
  | nil
  | cons (head : A) (tail : List A)

goal forall (xs : List Nat), Eq (List Nat) xs xs
intro xs
induction xs
rfl
rfl
qed
```

Indexed inductives are expressible with explicit index binders and constructor result indices:

```text
inductive Vec (A : Sort 1) (index n : Nat) : Sort 1 where
  | nil : Vec A Nat.zero
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)
```

The file-mode parser collects lines beginning with `|` as constructors until the next command. The Rust API offers richer explicit AST construction without surface syntax. `induction` is constructor-generic for **non-indexed** inductive types. Indexed recursor generation and reduction are supported, but indexed tactic elaboration is not. `rw` currently targets the built-in `Eq` declaration, which itself is generated through the general inductive API.

## Safety / missing features

- The conservative strict positivity validator supports direct recursive fields and function-valued recursive fields; nested strictly positive recursive occurrences are **rejected**, not accepted without checking.
- Recursors are generated on demand for any concrete admissible universe level, using `Kernel::ensure_recursor_level("Nat", 5)` or the CLI `recursor Nat 5` command. `rec0` and applicable `rec1` are generated at declaration time for compatibility. Symbolic universe polymorphism is not implemented.
- For proposition-valued inductives, large elimination is granted when there is at most one constructor and every field is a proposition or appears among result-index terms. This follows the simplified criterion in §12.6, not all of Lean 4's elimination rules.
- Mutual/nested inductives and Lean 4's complete universe-polymorphism and proof-irrelevance rules remain outside scope. Unsupported higher-order positivity cases are conservatively rejected.
- Source syntax needs explicit binders. It does not support Lean's normal `:= by`, implicit arguments, pattern matching, elaboration/unification, or a full interactive `inductive` editor.
- Recursive `def` bodies cannot reference the name being defined, avoiding unrestricted recursion. The system is not a full totality checker.
- Axioms are trusted assumptions. The named-variable core and higher-order ι evaluator have not received a formal soundness proof.
- **Build status: not compiled or tested in this environment.** Rust toolchain is unavailable and internet resolution for downloading it is disabled. Run `cargo test` before using the code. Tests are included for generated Nat, Eq, List, Vec, negative recursive occurrences, basic tactics, the new declaration parser and general List induction.

This is an implementation of a conservative **subset** of the textbook general induction algorithm, not a faithful full implementation of every Lean 4 inductive type. Unsupported cases fail explicitly.

## Textbook coverage additions (§12.6 and §13.5)

- Checks `w <= u` for each constructor field when the inductive lives in `Sort u` for `u >= 1`. `Sort 0` allows impredicative fields.
- Enforces uniform parameters, constructor result index arity, simple strict positivity, and type checks result indices through the constructor result.
- Computes the §12.6 subsingleton condition to decide whether recursors may eliminate a proposition into higher universes.
- Provides `ensure_recursor_level` to generate `I.rec_v` for arbitrary **concrete** admissible `v`; the generated metadata drives generic ι reduction.
- `examples/zero-add.leanmini` implements the full §13.5 sequence. An extra final `rfl` is explicit because this small `rw` tactic does not automatically run reflexivity.
- `textbook_zero_add_tactic_proof`, `arbitrary_recursor_levels`, `reject_constructor_universe_overflow`, and `proposition_elimination_policy` are regression tests, but have **not** been executed here.

**Implementation caveats:** the positivity checker supports only the paper's stated direct/function-valued recursive-field fragment; names are still used internally, and kernel soundness has not been formally proved. The recursor generation and new tests need local compilation and debugging.
