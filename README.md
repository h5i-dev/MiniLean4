# Mini Lean 4

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
