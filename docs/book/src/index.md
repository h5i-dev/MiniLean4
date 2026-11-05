<header class="hero" markdown="1">
<div class="hero-head" markdown="1">

<h1 class="logo">MiniLean4</h1>

</div>
<div class="hero-text" markdown="1">

<p class="hero-title">Implementing an Interactive Theorem Prover from Scratch</p>

<p class="byline">Hideaki Takahashi</p>

<div class="lead" markdown="1">

a Lean 4-style proof kernel, built from nothing. five kinds of terms and eight typing rules to start; inductive types, a tactic language, and the universe hierarchy that keeps it all consistent by the end. every piece is tied to a small Rust implementation you can read in an afternoon.

</div>

<p class="punch">proofs are programs. the kernel checks them. that's the whole trick.</p>

</div>
<div class="hero-term" markdown="1">
<div class="playground" data-file="examples/identity.leanmini"><pre># the polymorphic identity on propositions: for every P, P -> P.
goal forall (P : Sort 0), P -> P
intro P
intro p
exact p
qed</pre></div>
<p class="hero-caption">this is the real kernel, compiled to webassembly, checking the first theorem of the book. edit the script and run it again.</p>
</div>
</header>

## What this book is

Interactive theorem provers such as Lean, Coq, and Agda rest on a surprisingly small core: a *kernel* that decides whether a term has a given type. Everything else, including tactics, notation, and automation, is scaffolding that produces terms for the kernel to check. If the kernel is right, a bug anywhere else can make the system fail to prove a theorem, but never make it accept a false one.

The goal here is to make that kernel concrete. Each chapter introduces one idea on paper, states it precisely, and then shows the Rust code that implements it. The whole implementation, kernel plus tactics and parser, is under three thousand lines with no dependencies, and this book covers all of it.

The book is self-contained. You need to be comfortable reading a recursive function and a little set notation. No prior exposure to type theory or to Lean is assumed, although readers who know Lean will recognize much of what they see.

## How to read it

<p>CONTENTS_GO_HERE</p>

**Part I** builds a type checker for a dependent type theory and shows that it is a proof checker for a logic. **Part II** adds inductive types (natural numbers, trees, lists, vectors, and equality) and a tactic language that writes proof terms for you. **Part III** opens the black boxes that Parts I and II relied on: substitution, alpha-equivalence, and reduction, where kernel bugs hide. **Part IV** explains why universes are structured as they are, and states the metatheory. The appendices contain the full proofs, the paradox that justifies the universe design, and a reference for the script language.

Throughout the book you will meet three kinds of interactive element.

- **Playgrounds** run the kernel. Edit the script, press run, and read the transcript.
- **Explorers** show the kernel's own view of a term: its syntax tree, its typing derivation rule by rule, its reduction one step at a time, which binder each variable belongs to, and the proof state after every tactic. Every explorer is live: change the term and the kernel recomputes.
- **Steppers** walk through an algorithm one step at a time, showing the state after each step.
- **Trace trees** show the exact sequence of recursive calls the type checker makes on a term, with the typing rule each call corresponds to.

Callouts marked *in the code* point to the Rust function that implements what was just defined. Exercises come with solutions, folded away until you want them.

## Running the code yourself

The repository contains the kernel, a command-line runner, and the example scripts used in this book.

```text
cargo run -- examples/identity.leanmini
cargo run -- examples/nat-reflexivity.leanmini
cargo run -- examples/zero-add.leanmini
cargo run -- examples/generic-list.leanmini
cargo run -- examples/generic-vec.leanmini
cargo test
```

Running `cargo run` with no arguments starts an interactive session that accepts the same commands one line at a time. [Appendix E](e-leanmini-reference.md) describes the language.

The source is organized to follow the book.

| File | Contents | Chapters |
|---|---|---|
| `src/term.rs` | The term representation | 2 |
| `src/typecheck.rs` | Type inference and checking | 5, 6 |
| `src/substitution.rs` | Free variables, substitution, alpha-equivalence | 11 |
| `src/reduction.rs` | Weak head normal form, normalization, definitional equality | 12 |
| `src/declaration.rs` | The signature: constants, definitions, inductive metadata | 7, 8 |
| `src/inductive/` | Checking inductive declarations and generating recursors | 8 |
| `src/proof.rs` | Goals, proof states, and tactics | 10 |
| `src/syntax.rs` | The parser for the script language | Appendix E |
| `src/main.rs` | The command-line runner | Appendix E |
