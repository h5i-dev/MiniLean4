# MiniLean4

A minimal, self-contained implementation of a Lean 4-style theorem prover kernel in Rust. This repository is built from scratch to illustrate the core foundations of dependent type theory, inductive types, and kernel type checking without the complexity of a full production prover.

## Features

- **Dependent Type Theory Core**: Dependent function types ($\Pi$-types), universe hierarchy, and term representation (`src/term.rs`).
- **Type Checking & Reduction**: Type inference (`src/typecheck.rs`), $\beta/\delta/\iota$-reduction (`src/reduction.rs`), capture-avoiding substitution, and $\alpha$-equivalence (`src/substitution.rs`).
- **Inductive Types**: Support for inductive declarations, strict positivity checking (`src/inductive/positivity.rs`), and recursor generation (`src/inductive/recursor.rs`).
- **Minimal DSL (`.leanmini`)**: Custom syntax parser (`src/syntax.rs`) and CLI runner for verifying `.leanmini` proof scripts.

## Book

The directory [`docs/ebook/`](./docs/ebook) contains a complete ebook, *Implementing an Interactive Theorem Prover from Scratch*, that explains this kernel chapter by chapter, with the real kernel compiled to WebAssembly so that every example can be run and edited in the browser. Open `docs/ebook/index.html` through a local web server (for example `python3 -m http.server` inside `docs/ebook`) to use the interactive playgrounds. The sources and build script are in [`docs/book/`](./docs/book).

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
