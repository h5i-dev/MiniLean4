#!/usr/bin/env python3
"""Builds the MiniLean4 ebook.

Sources:   docs/book/src/*.md   (Markdown with embedded HTML widgets and $math$)
Template:  docs/book/template.html
Assets:    docs/book/assets/    (CSS, JS, fonts, KaTeX, kernel wasm)
Output:    docs/ebook/          (one HTML page per chapter, index, print view)

Math is pre-rendered with KaTeX through Node (tools/render-math.mjs), so the
output pages need no JavaScript to display formulas.

Usage:  python3 docs/book/build.py [--check]
"""

import hashlib
import html
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

import markdown

ROOT = Path(__file__).resolve().parent
SRC = ROOT / "src"
OUT = ROOT.parent / "ebook"
ASSETS = ROOT / "assets"
TOOLS = ROOT / "tools"
TEMPLATE = (ROOT / "template.html").read_text(encoding="utf-8")
CACHE_FILE = ROOT / ".mathcache.json"

# ---------------------------------------------------------------------------
# Table of contents. (kind, slug, title, one-line description)
# ---------------------------------------------------------------------------

TOC = [
    ("part", "Part I", "A Kernel for Propositional Logic"),
    ("ch", "01-propositions-as-types", "Propositions as Types",
     "Why checking a proof is the same job as type checking a program."),
    ("ch", "02-syntax", "The Language of Terms",
     "Five kinds of terms, and the Rust enum that represents them."),
    ("ch", "03-typing-rules", "Typing Rules",
     "Contexts, judgments, and the eight rules that define well-typed terms."),
    ("ch", "04-logic", "The Typing Rules as a Logic",
     "Natural deduction, the translation of formulas to types, and what consistency means."),
    ("ch", "05-algorithm", "A Type Checking Algorithm",
     "Turning the rules into Infer and Check, line by line against typecheck.rs."),
    ("ch", "06-worked-examples", "Worked Examples",
     "Step-by-step traces of the checker on right proofs, wrong proofs, and conversions."),
    ("part", "Part II", "Growing the Kernel"),
    ("ch", "07-inductive-nat", "Inductive Types I: Natural Numbers",
     "Constants, definitions, and the recursor that gives both recursion and induction."),
    ("ch", "08-inductive-recipe", "Inductive Types II: The General Recipe",
     "Trees, lists, vectors, and the procedure that generates any recursor."),
    ("ch", "09-equality", "Equality Is an Inductive Type Too",
     "Eq, transport, definitional versus propositional equality, and the proof of 0 + n = n."),
    ("ch", "10-tactics", "Tactics: Building Proof Terms Interactively",
     "Goals, holes, and how intro, apply, induction, and rw construct terms."),
    ("part", "Part III", "Under the Hood"),
    ("ch", "11-substitution-alpha", "Substitution, Capture, and Alpha-Equivalence",
     "The operations where kernel bugs hide, and how substitution.rs avoids them."),
    ("ch", "12-reduction-conversion", "Reduction and Conversion",
     "Beta, delta, iota; computation rules as data; weak head normal form."),
    ("part", "Part IV", "Foundations"),
    ("ch", "13-universes", "Universes: Why Sort u?",
     "Type-in-Type is inconsistent; a hierarchy with an impredicative bottom is not."),
    ("ch", "14-properties", "Properties of the System",
     "Uniqueness, subject reduction, strong normalization, consistency."),
    ("part", "Appendices", ""),
    ("app", "a-proof-pat", "Proof that Proofs Are Terms", "The full proof of the translation theorem."),
    ("app", "b-proof-alpha", "Correctness of Alpha-Equivalence", "Both definitions compute de Bruijn forms."),
    ("app", "c-hurkens", "Hurkens' Paradox", "A closed term of type False under Type : Type."),
    ("app", "d-proof-consistency", "Proof of Consistency", "No closed term inhabits forall P, P."),
    ("app", "e-leanmini-reference", "The leanmini Language", "Syntax, commands, and tactics of the script language."),
    ("app", "f-notation-glossary", "Notation and Glossary", "Every symbol and term used in the book."),
    ("app", "bibliography", "Bibliography", ""),
]


def numbered_entries():
    """Yields dicts for every chapter/appendix with its label and neighbours."""
    entries = []
    chapter = 0
    appendix = 0
    part = None
    for item in TOC:
        if item[0] == "part":
            part = item[2] or item[1]
            continue
        kind, slug, title, desc = item
        if kind == "ch":
            chapter += 1
            label = f"Chapter {chapter}"
            short = str(chapter)
        else:
            appendix += 1
            letter = chr(ord("A") + appendix - 1)
            label = f"Appendix {letter}" if slug != "bibliography" else ""
            short = letter if slug != "bibliography" else ""
        entries.append({
            "kind": kind, "slug": slug, "title": title, "desc": desc,
            "label": label, "short": short, "part": part, "file": f"{slug}.html",
        })
    for i, e in enumerate(entries):
        e["prev"] = entries[i - 1] if i > 0 else None
        e["next"] = entries[i + 1] if i + 1 < len(entries) else None
    return entries


ENTRIES = numbered_entries()
BY_SLUG = {e["slug"]: e for e in ENTRIES}

# ---------------------------------------------------------------------------
# Math extraction and pre-rendering
# ---------------------------------------------------------------------------

# Fenced code, inline code, display math, inline math. Order matters: code is
# matched first so that dollars inside code are never treated as math.
TOKEN_RE = re.compile(
    r"(```.*?```|`[^`\n]*`|\$\$.*?\$\$|\$(?!\s)(?:\\.|[^$\\\n])+?(?<!\s)\$)",
    re.S,
)


def extract_math(text, store):
    def repl(m):
        tok = m.group(0)
        if tok.startswith("```") or tok.startswith("`"):
            return tok
        if tok.startswith("$$"):
            tex, display = tok[2:-2].strip(), True
        else:
            tex, display = tok[1:-1], False
        key = f"MATHX{len(store)}X"
        store.append({"tex": tex, "display": display})
        return key
    return TOKEN_RE.sub(repl, text)


def load_cache():
    if CACHE_FILE.exists():
        try:
            return json.loads(CACHE_FILE.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            return {}
    return {}


def render_math(items, cache):
    todo = []
    keys = []
    for it in items:
        key = hashlib.sha1(f"{int(it['display'])}:{it['tex']}".encode()).hexdigest()
        keys.append(key)
        if key not in cache:
            todo.append(it)
    if todo:
        proc = subprocess.run(
            ["node", str(TOOLS / "render-math.mjs")],
            input=json.dumps(todo), capture_output=True, text=True, check=True,
        )
        results = json.loads(proc.stdout)
        for it, res in zip(todo, results):
            key = hashlib.sha1(f"{int(it['display'])}:{it['tex']}".encode()).hexdigest()
            if res["error"]:
                print(f"  KaTeX error: {res['error']}\n    in: {it['tex'][:120]}", file=sys.stderr)
                res["html"] = f'<code class="math-error">{html.escape(it["tex"])}</code>'
            cache[key] = res["html"]
    return [cache[k] for k in keys]


def insert_math(body, rendered, items):
    for i, (h, it) in enumerate(zip(rendered, items)):
        key = f"MATHX{i}X"
        if it["display"]:
            body = body.replace(f"<p>{key}</p>", f'<div class="math-display">{h}</div>')
            body = body.replace(key, f'<div class="math-display">{h}</div>')
        else:
            body = body.replace(key, h)
    return body


# ---------------------------------------------------------------------------
# Code highlighting (tiny, regex based; enough for leanmini, Rust, shell)
# ---------------------------------------------------------------------------

LEANMINI_KW = {
    "inductive", "where", "def", "axiom", "recursor", "goal", "intro", "induction",
    "exact", "apply", "change", "rw", "rfl", "qed", "show", "fun", "forall", "Sort",
    "index", "end", "quit", "theorem", "by", "with",
}
RUST_KW = {
    "fn", "let", "mut", "pub", "struct", "enum", "impl", "match", "if", "else",
    "return", "use", "mod", "for", "in", "while", "loop", "self", "Self", "crate",
    "super", "ref", "const", "static", "type", "where", "as", "move", "true",
    "false", "Some", "None", "Ok", "Err", "dyn", "trait", "break", "continue",
}


def highlight(code, lang):
    out = []
    if lang == "leanmini":
        pattern = re.compile(r"(#.*$)|([A-Za-z_][A-Za-z0-9_.']*)|(\S)|(\s+)", re.M)
        for m in pattern.finditer(code):
            comment, ident, sym, ws = m.groups()
            if comment is not None:
                out.append(f'<span class="c">{html.escape(comment)}</span>')
            elif ident is not None:
                if ident in LEANMINI_KW:
                    out.append(f'<span class="k">{html.escape(ident)}</span>')
                elif "." in ident:
                    out.append(f'<span class="n">{html.escape(ident)}</span>')
                else:
                    out.append(html.escape(ident))
            else:
                out.append(html.escape(sym or ws))
        return "".join(out)
    if lang == "rust":
        pattern = re.compile(
            r"(//.*$)|(\"(?:\\.|[^\"\\])*\")|(#!?\[[^\]]*\])|([A-Za-z_][A-Za-z0-9_]*!?)|(\S)|(\s+)",
            re.M,
        )
        for m in pattern.finditer(code):
            comment, string, attr, ident, sym, ws = m.groups()
            if comment is not None:
                out.append(f'<span class="c">{html.escape(comment)}</span>')
            elif string is not None:
                out.append(f'<span class="s">{html.escape(string)}</span>')
            elif attr is not None:
                out.append(f'<span class="a">{html.escape(attr)}</span>')
            elif ident is not None:
                if ident in RUST_KW:
                    out.append(f'<span class="k">{html.escape(ident)}</span>')
                elif ident.endswith("!"):
                    out.append(f'<span class="m">{html.escape(ident)}</span>')
                elif ident[0].isupper():
                    out.append(f'<span class="t">{html.escape(ident)}</span>')
                else:
                    out.append(html.escape(ident))
            else:
                out.append(html.escape(sym or ws))
        return "".join(out)
    if lang in ("lean", "lean4"):
        kws = {"inductive", "where", "def", "theorem", "by", "induction", "with", "rfl",
               "rw", "fun", "forall", "Prop", "Type", "Sort", "intro", "exact", "apply"}
        pattern = re.compile(r"(--.*$)|([A-Za-z_][A-Za-z0-9_.']*)|(\S)|(\s+)", re.M)
        for m in pattern.finditer(code):
            comment, ident, sym, ws = m.groups()
            if comment is not None:
                out.append(f'<span class="c">{html.escape(comment)}</span>')
            elif ident is not None and ident in kws:
                out.append(f'<span class="k">{html.escape(ident)}</span>')
            else:
                out.append(html.escape(ident or sym or ws))
        return "".join(out)
    return html.escape(code)


CODE_RE = re.compile(r'<pre><code class="language-([a-z0-9]+)">(.*?)</code></pre>', re.S)


def highlight_blocks(body):
    def repl(m):
        lang, inner = m.group(1), html.unescape(m.group(2))
        return (f'<div class="codeblock" data-lang="{lang}"><pre><code class="language-{lang}">'
                f"{highlight(inner, lang)}</code></pre></div>")
    return CODE_RE.sub(repl, body)


# ---------------------------------------------------------------------------
# Page assembly
# ---------------------------------------------------------------------------

def make_markdown():
    return markdown.Markdown(extensions=[
        "fenced_code", "tables", "toc", "attr_list", "md_in_html", "footnotes",
        "def_list", "sane_lists",
    ], extension_configs={"toc": {"toc_depth": "2-3", "permalink": False}})


def render_markdown(text, cache):
    store = []
    protected = extract_math(text, store)
    md = make_markdown()
    body = md.convert(protected)
    rendered = render_math(store, cache)
    body = insert_math(body, rendered, store)
    body = highlight_blocks(body)
    return body, md.toc_tokens


def sidebar_html(current_slug):
    parts = []
    parts.append('<nav class="toc" aria-label="Table of contents">')
    parts.append('<a class="toc-cover" href="index.html">Cover and contents</a>')
    current_part = None
    current_index = next((i for i, e in enumerate(ENTRIES) if e["slug"] == current_slug), None)
    for i, e in enumerate(ENTRIES):
        if e["part"] != current_part:
            if current_part is not None:
                parts.append("</ol>")
            current_part = e["part"]
            parts.append(f'<h3 class="toc-part">{html.escape(current_part)}</h3><ol class="toc-list">')
        if e["slug"] == current_slug:
            cls = ' class="current"'
        elif current_index is not None and i < current_index:
            cls = ' class="past"'
        else:
            cls = ""
        num = f'<span class="toc-num">{e["short"]}</span>' if e["short"] else '<span class="toc-num"></span>'
        parts.append(f'<li{cls}><a href="{e["file"]}">{num}<span class="toc-title">{html.escape(e["title"])}</span></a></li>')
    parts.append("</ol>")
    parts.append('<a class="toc-print" href="print.html">Single-page version</a>')
    parts.append("</nav>")
    return "\n".join(parts)


def on_this_page(toc_tokens):
    items = [t for t in toc_tokens if t["level"] == 2]
    if not items:
        return ""
    lis = "".join(f'<li><a href="#{t["id"]}">{t["name"]}</a></li>' for t in items)
    return f'<nav class="onpage" aria-label="On this page"><h4>On this page</h4><ol>{lis}</ol></nav>'


def pager_html(entry):
    prev_html = next_html = ""
    if entry["prev"]:
        p = entry["prev"]
        prev_html = (f'<a class="pager-prev" href="{p["file"]}"><span class="pager-dir">Previous</span>'
                     f'<span class="pager-title">{html.escape(p["title"])}</span></a>')
    if entry["next"]:
        n = entry["next"]
        next_html = (f'<a class="pager-next" href="{n["file"]}"><span class="pager-dir">Next</span>'
                     f'<span class="pager-title">{html.escape(n["title"])}</span></a>')
    return f'<div class="pager">{prev_html}{next_html}</div>'


def fill(template, **kv):
    out = template
    for k, v in kv.items():
        out = out.replace("{{" + k + "}}", v)
    return out


def build_page(entry, body, toc_tokens):
    heading = (f'<header class="chapter-head">'
               f'<p class="chapter-label">{html.escape(entry["label"])}</p>'
               f'<h1>{html.escape(entry["title"])}</h1></header>')
    return fill(
        TEMPLATE,
        title=f'{entry["title"]} | Implementing an Interactive Theorem Prover from Scratch',
        body_class=f'page-{entry["kind"]}',
        sidebar=sidebar_html(entry["slug"]),
        onpage=on_this_page(toc_tokens),
        content=heading + body,
        pager=pager_html(entry),
    )


def build_index(body, toc_tokens):
    cards = []
    current_part = None
    for e in ENTRIES:
        if e["part"] != current_part:
            if current_part is not None:
                cards.append("</ol>")
            current_part = e["part"]
            cards.append(f'<h3 class="contents-part">{html.escape(current_part)}</h3><ol class="contents-list">')
        num = f'<span class="contents-num">{e["short"]}</span>' if e["short"] else '<span class="contents-num"></span>'
        desc = f'<span class="contents-desc">{html.escape(e["desc"])}</span>' if e["desc"] else ""
        cards.append(f'<li><a href="{e["file"]}">{num}<span class="contents-title">{html.escape(e["title"])}</span></a>{desc}</li>')
    cards.append("</ol>")
    body = body.replace("<p>CONTENTS_GO_HERE</p>", '<div class="contents">' + "".join(cards) + "</div>")
    return fill(
        TEMPLATE,
        title="Implementing an Interactive Theorem Prover from Scratch",
        body_class="page-cover",
        sidebar=sidebar_html(None),
        onpage="",
        content=body,
        pager="",
    )


def build_print(pages):
    sections = []
    for entry, body in pages:
        sections.append(f'<section class="print-chapter" id="{entry["slug"]}">'
                        f'<header class="chapter-head"><p class="chapter-label">{html.escape(entry["label"])}</p>'
                        f'<h1>{html.escape(entry["title"])}</h1></header>{body}</section>')
    cover = ('<header class="print-cover"><h1>Implementing an Interactive Theorem Prover from Scratch</h1>'
             '<p>A guided tour of MiniLean4, a small Lean 4-style proof kernel written in Rust.</p>'
             '<p>Hideaki Takahashi</p></header>')
    return fill(
        TEMPLATE,
        title="Implementing an Interactive Theorem Prover from Scratch (single page)",
        body_class="page-print",
        sidebar=sidebar_html(None),
        onpage="",
        content=cover + "".join(sections),
        pager="",
    )


def rewrite_links(body):
    """Chapter cross-references are written as [text](03-typing-rules.md#anchor)."""
    return re.sub(r'href="([0-9a-z\-]+)\.md(#[^"]*)?"', lambda m: f'href="{m.group(1)}.html{m.group(2) or ""}"', body)


def main():
    check_only = "--check" in sys.argv
    cache = load_cache()
    OUT.mkdir(parents=True, exist_ok=True)
    pages = []
    missing = []
    for entry in ENTRIES:
        src = SRC / f'{entry["slug"]}.md'
        if not src.exists():
            missing.append(src.name)
            continue
        text = src.read_text(encoding="utf-8")
        body, toc_tokens = render_markdown(text, cache)
        body = rewrite_links(body)
        pages.append((entry, body))
        if not check_only:
            (OUT / entry["file"]).write_text(build_page(entry, body, toc_tokens), encoding="utf-8")
        print(f"  {entry['file']}  ({len(body) // 1024} KB)")
    index_src = SRC / "index.md"
    if index_src.exists():
        body, toc_tokens = render_markdown(index_src.read_text(encoding="utf-8"), cache)
        body = rewrite_links(body)
        if not check_only:
            (OUT / "index.html").write_text(build_index(body, toc_tokens), encoding="utf-8")
        print("  index.html")
    if not check_only:
        (OUT / "print.html").write_text(build_print(pages), encoding="utf-8")
        print("  print.html")
        if (OUT / "assets").exists():
            shutil.rmtree(OUT / "assets")
        shutil.copytree(ASSETS, OUT / "assets")
        print("  assets/")
    CACHE_FILE.write_text(json.dumps(cache), encoding="utf-8")
    if missing:
        print("Missing sources: " + ", ".join(missing), file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
