# Translation guide for the MiniLean4 ebook

The English sources in `docs/book/src/*.md` are the reference. Translations go to
`docs/book/src-ja/` (Japanese) and `docs/book/src-zh/` (Simplified Chinese), one
file per English file, same file name.

## What must stay byte-for-byte identical

- Every line of HTML: tags, attributes, `markdown="1"`, class names, `data-*`
  attributes. Exception: the value of `data-title="..."` on explorers may be
  translated.
- All math: `$...$` and `$$...$$` blocks, including the `\text{...}` inside them.
  Do not translate anything between dollar signs.
- Fenced code blocks (```rust, ```leanmini, ```lean, ```text) and the scripts
  inside `<pre class="script">`, `<pre class="prelude">`, and
  `<div class="playground"><pre>`. Only lines that start with `#` (comments in
  leanmini scripts) or `//` (Rust comments) may be translated. Never add or
  remove lines in a script.
- Link targets: `[text](03-typing-rules.md#anchor)` keeps its target; the text
  is translated. Anchors are generated from the English headings, so a link
  with `#anchor` must keep that English anchor. (Headings are translated; the
  build does not rely on anchors matching.)
- Identifiers and names: rule names (T-Pi, T-App, C-Ext, alpha-Pi), constants
  (`Nat.rec1`, `Eq.refl`), leanmini keywords, file paths (`src/typecheck.rs`),
  function names (`infer`, `whnf`), figure and theorem numbers (Figure 3.1,
  Theorem 14.5, Algorithm 5.1, Lemma B.3), bibliography keys ([Barendregt 1992]).
- The marker `CONTENTS_GO_HERE` in `index.md`, the byline name, the word
  `MiniLean4`, and the `<h1 class="logo">`.
- Markdown structure: headings keep their level, lists keep their shape, tables
  keep their columns, `<details><summary>` stays.

## What to translate

All prose: paragraphs, headings, list items, table cells, `<summary>` text,
`<p class="step-label">` text, captions (`<p class="caption">`), the first line
of summary boxes ("What to remember"), exercise text and solutions, alt text,
leanmini comment lines, and the explorer `data-title`.

## Style

- No em dashes. Use the language's own punctuation.
- Japanese: である体 (常体). Full-width punctuation (。、). Half-width spaces
  between Japanese and Latin words or math. Short sentences, one idea each,
  conclusion first. Avoid the stiff patterns of machine translation
  (「〜することができる」「〜と言えるだろう」, every sentence ending the same way).
  Keep technical terms consistent with the glossary and add the English term in
  parentheses on first use in each chapter when the Japanese term is not
  standard.
- Chinese: Simplified characters, written register, full-width punctuation
  (，。：；“”). Half-width spaces between Chinese and Latin words or math.
  Terminology per the glossary; add the English term in parentheses on first
  use in each chapter when a term is not standard.
- Rule names, keywords, and identifiers are not translated and not transliterated.
- Keep the author's voice: direct, concrete, no filler.

## Checking

After translating a file, run

    python3 docs/book/tools/check-translation.py docs/book/src/FILE.md docs/book/src-ja/FILE.md

and fix every reported difference until it prints `ok`. Then build:

    python3 docs/book/build.py --only ja

and confirm there is no `KaTeX error` line in the output.
