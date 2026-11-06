# Book sources

This directory holds the sources of the ebook *Implementing an Interactive
Theorem Prover from Scratch*. The built site lives in `../ebook/`.

## Layout

| Path | Contents |
|---|---|
| `src/*.md` | One Markdown file per chapter and appendix, plus `index.md` (the cover), in English. |
| `src-ja/*.md`, `src-zh/*.md` | The Japanese and Simplified Chinese translations, same file names. |
| `locales.py` | Chapter order, titles, part names, and interface strings per language. |
| `i18n/` | The translation guide, the two glossaries. |
| `tools/check-translation.py` | Verifies that a translated file keeps the structure (HTML, math, code, scripts) of its English source. |
| `build.py` | Builds `../ebook/` from `src/`, `template.html`, and `assets/`. |
| `template.html` | The page template (sidebar, topbar, content, footer). |
| `assets/book.css`, `assets/book.js` | Styling and the interactive widgets (steppers, trace trees, theme). |
| `assets/playground.js`, `assets/minilean.wasm` | The in-browser kernel playground and the shared wasm loader (`window.MiniLean`). |
| `assets/explorers.js` | The live explorers (syntax trees, derivations, reduction, scope, substitution, proof states, constructor trees, universes). |
| `assets/katex/`, `assets/fonts/` | Vendored KaTeX and webfonts, so the book works offline. |
| `tools/render-math.mjs`, `tools/katex.mjs` | Build-time KaTeX rendering (Node). |
| `playground/` | A `cdylib` crate that compiles the root kernel to WebAssembly. `src/lib.rs` runs scripts; `src/explore.rs` answers the explorers' structured queries with JSON. |

## Building

Requirements: Python 3 with the `markdown` package, Node.js (for KaTeX), and,
only if the kernel changed, a Rust toolchain with the `wasm32-unknown-unknown`
target.

```text
python3 docs/book/build.py            # rebuild docs/ebook/, docs/ebook/ja/, docs/ebook/zh/ (math is pre-rendered)
python3 docs/book/build.py --only ja  # one language
docs/book/playground/build.sh         # rebuild assets/minilean.wasm after kernel changes
node docs/book/playground/test.mjs    # run every examples/*.leanmini through the wasm kernel
```

Then serve the output: `cd docs/ebook && python3 -m http.server`. The
playgrounds fetch the `.wasm` file, which browsers refuse to do from `file://`.

## Writing conventions

- Math uses `$...$` and `$$...$$`; the macros available are listed in
  `tools/render-math.mjs`. KaTeX errors are printed by `build.py`.
- Block widgets are plain HTML inside the Markdown: `<aside class="note|intuition|warning|lean|code|history" markdown="1">`,
  `<div class="theorem|definition|lemma|proof|exercise|summary-box|rulebox" markdown="1">`,
  `<div class="stepper" data-title="..." markdown="1">` with `<div class="step" markdown="1">` children,
  `<ul class="trace">` for call trees, and `<div class="playground"><pre>script</pre></div>` for runnable scripts.
- Explorers are `<div class="explorer" data-kind="KIND" ...></div>` with kind one of
  `ast` (`data-term`), `derive` (`data-term`, optional `data-ctx="x : A; y : B"`, optional `data-view="tree"`),
  `reduce` (`data-term`, optional `data-ctx`), `scope` (`data-term`), `subst` (`data-term`, `data-var`, `data-with`),
  `proof` (a child `<pre class="script">` with a leanmini script, optional `data-title`), `ctree` (`data-term`), and `universes`.
  A child `<pre class="prelude">` holds `def`/`inductive` lines the term may use. Every explorer is editable by the reader
  and recomputed by the kernel; the request format is documented at the top of `playground/src/explore.rs`.
- Cross-references are written as `[Chapter 3](03-typing-rules.md#anchor)`; the build rewrites them to `.html`.
- The order of chapters and their descriptions are the `TOC` list at the top of `build.py`.

## Translating

Edit the English source first, then port the change to `src-ja/` and `src-zh/`.
The rules (what may change, what must stay byte-identical) are in
`i18n/TRANSLATION-GUIDE.md`, and the glossaries fix the terminology. Check every
translated file with

```text
python3 docs/book/tools/check-translation.py docs/book/src/FILE.md docs/book/src-ja/FILE.md
```

The build produces a language switcher in the top bar for every language whose
source directory exists.
