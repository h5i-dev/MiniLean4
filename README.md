# MiniLean4

A minimal, self-contained implementation of a Lean 4-style theorem prover kernel in Rust.

`MiniLean4` is built from scratch to illustrate the core foundations of dependent type theory, inductive types, and kernel type checking without the complexity of a full production prover.

## Features

- **Dependent Type Theory Core**: Dependent function types ($\Pi$-types), universe hierarchy, and term representation (`src/term.rs`).
- **Type Checking & Reduction**: Type inference (`src/typecheck.rs`), $\beta/\delta/\iota$-reduction (`src/reduction.rs`), capture-avoiding substitution, and $\alpha$-equivalence (`src/substitution.rs`).
- **Inductive Types**: Support for inductive declarations, strict positivity checking (`src/inductive/positivity.rs`), and recursor generation (`src/inductive/recursor.rs`).
- **Minimal DSL (`.leanmini`)**: Custom syntax parser (`src/syntax.rs`) and CLI runner for verifying `.leanmini` proof scripts.

## Quick Start

### Run Examples

Verify the example proofs in the [`examples/`](./examples) directory using Cargo:

```bash
cargo run -- examples/identity.leanmini
cargo run -- examples/nat-reflexivity.leanmini
cargo run -- examples/zero-add.leanmini
cargo run -- examples/generic-list.leanmini
cargo run -- examples/generic-vec.leanmini
```

### Run Tests

```bash
cargo test
```

## License

See [LICENSE](./LICENSE) for details.
