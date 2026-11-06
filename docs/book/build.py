#!/usr/bin/env python3
"""Builds the MiniLean4 ebook in every language that has sources.

Sources:   docs/book/src/*.md (English), docs/book/src-ja/*.md, docs/book/src-zh/*.md
Template:  docs/book/template.html
Assets:    docs/book/assets/    (CSS, JS, fonts, KaTeX, kernel wasm)
Output:    docs/ (English), docs/ja/, docs/zh/   (GitHub Pages serves docs/)

Math is pre-rendered with KaTeX through Node (tools/render-math.mjs), so the
output pages need no JavaScript to display formulas. Chapter order, titles,
and interface strings per language live in locales.py.

Usage:  python3 docs/book/build.py [--check] [--only en|ja|zh]
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

sys.path.insert(0, str(Path(__file__).resolve().parent))
from locales import LOCALES, ORDER, SITE_URL, SITE_NAME, AUTHOR, AUTHOR_URL, REPO_URL  # noqa: E402

ROOT = Path(__file__).resolve().parent
OUT_ROOT = ROOT.parent  # docs/, served by GitHub Pages
ASSETS = ROOT / "assets"
TOOLS = ROOT / "tools"
TEMPLATE = (ROOT / "template.html").read_text(encoding="utf-8")
CACHE_FILE = ROOT / ".mathcache.json"


# ---------------------------------------------------------------------------
# Table of contents per locale
# ---------------------------------------------------------------------------

def numbered_entries(loc):
    """Chapter/appendix entries for a locale, with labels and neighbours."""
    L = LOCALES[loc]
    entries = []
    chapter = 0
    appendix = 0
    part = None
    for kind, slug in ORDER:
        if kind == "part":
            part = L["parts"][slug]
            continue
        title, desc = L["chapters"][slug]
        if kind == "ch":
            chapter += 1
            label = L["ui"]["chapter"].format(n=chapter)
            short = str(chapter)
        else:
            appendix += 1
            letter = chr(ord("A") + appendix - 1)
            if slug == "bibliography":
                label, short = "", ""
            else:
                label, short = L["ui"]["appendix"].format(n=letter), letter
        entries.append({
            "kind": kind, "slug": slug, "title": title, "desc": desc,
            "label": label, "short": short, "part": part, "file": f"{slug}.html",
        })
    for i, e in enumerate(entries):
        e["prev"] = entries[i - 1] if i > 0 else None
        e["next"] = entries[i + 1] if i + 1 < len(entries) else None
    return entries


# ---------------------------------------------------------------------------
# Math extraction and pre-rendering
# ---------------------------------------------------------------------------

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


def math_key(it):
    return hashlib.sha1(f"{int(it['display'])}:{it['tex']}".encode()).hexdigest()


def render_math(items, cache):
    todo = [it for it in items if math_key(it) not in cache]
    if todo:
        proc = subprocess.run(
            ["node", str(TOOLS / "render-math.mjs")],
            input=json.dumps(todo), capture_output=True, text=True, check=True,
        )
        for it, res in zip(todo, json.loads(proc.stdout)):
            if res["error"]:
                print(f"  KaTeX error: {res['error']}\n    in: {it['tex'][:120]}", file=sys.stderr)
                res["html"] = f'<code class="math-error">{html.escape(it["tex"])}</code>'
            cache[math_key(it)] = res["html"]
    return [cache[math_key(it)] for it in items]


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


def rewrite_links(body):
    """Chapter cross-references are written as [text](03-typing-rules.md#anchor)."""
    return re.sub(r'href="([0-9a-z\-]+)\.md(#[^"]*)?"', lambda m: f'href="{m.group(1)}.html{m.group(2) or ""}"', body)


class Site:
    """Everything needed to render one locale."""

    def __init__(self, loc):
        self.loc = loc
        self.L = LOCALES[loc]
        self.ui = self.L["ui"]
        self.src = ROOT / self.L["src"]
        self.out = OUT_ROOT / self.L["out"] if self.L["out"] else OUT_ROOT
        self.root = "../" if self.L["out"] else ""
        self.entries = numbered_entries(loc)

    def sidebar_html(self, current_slug):
        parts = ['<nav class="toc" aria-label="Table of contents">',
                 f'<a class="toc-cover" href="index.html">{html.escape(self.ui["cover"])}</a>']
        current_part = None
        current_index = next((i for i, e in enumerate(self.entries) if e["slug"] == current_slug), None)
        for i, e in enumerate(self.entries):
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
            num = f'<span class="toc-num">{e["short"]}</span>'
            parts.append(f'<li{cls}><a href="{e["file"]}">{num}<span class="toc-title">{html.escape(e["title"])}</span></a></li>')
        parts.append("</ol>")
        parts.append("</nav>")
        return "\n".join(parts)

    def on_this_page(self, toc_tokens):
        items = [t for t in toc_tokens if t["level"] == 2]
        if not items:
            return ""
        lis = "".join(f'<li><a href="#{t["id"]}">{t["name"]}</a></li>' for t in items)
        return f'<nav class="onpage" aria-label="{html.escape(self.ui["onpage"])}"><h4>{html.escape(self.ui["onpage"])}</h4><ol>{lis}</ol></nav>'

    def pager_html(self, entry):
        prev_html = next_html = ""
        if entry["prev"]:
            p = entry["prev"]
            prev_html = (f'<a class="pager-prev" href="{p["file"]}"><span class="pager-dir">{html.escape(self.ui["prev"])}</span>'
                         f'<span class="pager-title">{html.escape(p["title"])}</span></a>')
        if entry["next"]:
            n = entry["next"]
            next_html = (f'<a class="pager-next" href="{n["file"]}"><span class="pager-dir">{html.escape(self.ui["next"])}</span>'
                         f'<span class="pager-title">{html.escape(n["title"])}</span></a>')
        return f'<div class="pager">{prev_html}{next_html}</div>'

    def langswitch(self, page):
        """Links to the same page in every locale that has it."""
        links = []
        for other, L in LOCALES.items():
            target = OUT_ROOT / L["out"] / page if L["out"] else OUT_ROOT / page
            if not (ROOT / L["src"]).exists():
                continue
            if other == self.loc:
                links.append(f'<span class="lang current">{html.escape(L["name"])}</span>')
            else:
                href = (self.root + (L["out"] + "/" if L["out"] else "")) + page
                links.append(f'<a class="lang" href="{href}" hreflang="{L["html_lang"]}">{html.escape(L["name"])}</a>')
            _ = target
        return '<nav class="langs" aria-label="Language">' + "".join(links) + "</nav>"

    def page_url(self, page, loc=None):
        L = LOCALES[loc or self.loc]
        return SITE_URL + (L["out"] + "/" if L["out"] else "") + page

    def head_extra(self, page, title, description, kind, entry=None):
        """Per-page metadata: description, canonical, hreflang alternates,
        Open Graph and Twitter cards, and JSON-LD structured data."""
        url = self.page_url(page)
        og_image = SITE_URL + f"assets/og/{self.loc}.png"
        lines = [
            f'<meta name="description" content="{html.escape(description)}">',
            f'<meta name="author" content="{html.escape(AUTHOR)}">',
            '<meta name="robots" content="index, follow, max-image-preview:large">',
            f'<meta name="keywords" content="{html.escape(", ".join(self.L.get("keywords", [])))}">',
            f'<link rel="canonical" href="{url}">',
        ]
        for other, L in LOCALES.items():
            if (ROOT / L["src"]).exists():
                lines.append(f'<link rel="alternate" hreflang="{L["html_lang"]}" href="{self.page_url(page, other)}">')
        lines.append(f'<link rel="alternate" hreflang="x-default" href="{self.page_url(page, "en")}">')
        lines += [
            f'<meta property="og:type" content="{"book" if kind == "cover" else "article"}">',
            f'<meta property="og:site_name" content="{SITE_NAME}">',
            f'<meta property="og:title" content="{html.escape(title)}">',
            f'<meta property="og:description" content="{html.escape(description)}">',
            f'<meta property="og:url" content="{url}">',
            f'<meta property="og:image" content="{og_image}">',
            '<meta property="og:image:width" content="1200">',
            '<meta property="og:image:height" content="630">',
            f'<meta property="og:locale" content="{ {"en": "en_US", "ja": "ja_JP", "zh": "zh_CN"}[self.loc] }">',
            '<meta name="twitter:card" content="summary_large_image">',
            f'<meta name="twitter:title" content="{html.escape(title)}">',
            f'<meta name="twitter:description" content="{html.escape(description)}">',
            f'<meta name="twitter:image" content="{og_image}">',
        ]
        book = {
            "@type": "Book", "name": self.L["title"], "url": self.page_url("index.html"),
            "author": {"@type": "Person", "name": AUTHOR, "url": AUTHOR_URL},
            "inLanguage": self.L["html_lang"], "isAccessibleForFree": True,
            "license": REPO_URL + "/blob/main/LICENSE",
            "about": ["type theory", "theorem proving", "Lean 4", "dependent types", "Rust"],
            "keywords": ", ".join(self.L.get("keywords", [])),
        }
        if kind == "cover":
            data = {"@context": "https://schema.org", **book, "description": description}
        else:
            data = {
                "@context": "https://schema.org", "@type": "TechArticle",
                "headline": title, "description": description, "url": url,
                "inLanguage": self.L["html_lang"], "author": book["author"],
                "isPartOf": {"@type": "Book", "name": self.L["title"], "url": book["url"]},
                "keywords": book["keywords"],
                "position": entry["short"] if entry else None,
            }
            data = {k: v for k, v in data.items() if v is not None}
        lines.append('<script type="application/ld+json">' + json.dumps(data, ensure_ascii=False) + '</script>')
        return "\n".join(lines)

    def fill(self, page, **kv):
        out = TEMPLATE
        values = {
            "root": self.root,
            "lang": self.L["html_lang"],
            "subtitle": html.escape(self.L["subtitle"]),
            "description": html.escape(self.L["description"]),
            "ui_contents": html.escape(self.ui["contents"]),
            "ui_theme": html.escape(self.ui["theme_light"]),
            "footer": self.ui["footer"],
            "langswitch": self.langswitch(page),
            "notice": (f'<div class="notice" role="note">{self.L["notice"]}</div>' if self.L.get("notice") else ""),
            "i18n": json.dumps({"ui": {"contents": self.ui["contents"], "close": self.ui["close"],
                                       "theme_light": self.ui["theme_light"], "theme_dark": self.ui["theme_dark"]},
                                "js": self.L["js"]}, ensure_ascii=False),
        }
        values.update(kv)
        for k, v in values.items():
            out = out.replace("{{" + k + "}}", v)
        return out

    def build_page(self, entry, body, toc_tokens):
        heading = (f'<header class="chapter-head">'
                   f'<p class="chapter-label">{html.escape(entry["label"])}</p>'
                   f'<h1>{html.escape(entry["title"])}</h1></header>')
        desc = entry["desc"] or self.L["description"]
        return self.fill(
            entry["file"],
            title=f'{entry["title"]} | {self.L["title"]}',
            head_extra=self.head_extra(entry["file"], f'{entry["label"]}: {entry["title"]}'.strip(": "), desc, "chapter", entry),
            body_class=f'page-{entry["kind"]}',
            sidebar=self.sidebar_html(entry["slug"]),
            onpage=self.on_this_page(toc_tokens),
            content=heading + body,
            pager=self.pager_html(entry),
        )

    def build_index(self, body, toc_tokens):
        cards = []
        current_part = None
        for e in self.entries:
            if e["part"] != current_part:
                if current_part is not None:
                    cards.append("</ol>")
                current_part = e["part"]
                cards.append(f'<h3 class="contents-part">{html.escape(current_part)}</h3><ol class="contents-list">')
            num = f'<span class="contents-num">{e["short"]}</span>'
            desc = f'<span class="contents-desc">{html.escape(e["desc"])}</span>' if e["desc"] else ""
            cards.append(f'<li><a href="{e["file"]}">{num}<span class="contents-title">{html.escape(e["title"])}</span></a>{desc}</li>')
        cards.append("</ol>")
        body = body.replace("<p>CONTENTS_GO_HERE</p>", '<div class="contents">' + "".join(cards) + "</div>")
        return self.fill(
            "index.html",
            title=f'{self.L["title"]} | {SITE_NAME}',
            head_extra=self.head_extra("index.html", self.L["title"], self.L["description"], "cover"),
            body_class="page-cover",
            sidebar=self.sidebar_html(None),
            onpage="",
            content=body,
            pager="",
        )

    def build_print(self, pages):
        sections = []
        for entry, body in pages:
            sections.append(f'<section class="print-chapter" id="{entry["slug"]}">'
                            f'<header class="chapter-head"><p class="chapter-label">{html.escape(entry["label"])}</p>'
                            f'<h1>{html.escape(entry["title"])}</h1></header>{body}</section>')
        cover = (f'<header class="print-cover"><h1>{html.escape(self.L["title"])}</h1>'
                 f'<p>{html.escape(self.ui["print_lead"])}</p>'
                 f'<p>{html.escape(self.ui["author"])}</p></header>')
        return self.fill(
            "print.html",
            title=f'{self.L["title"]} {self.ui["single_page_title"]}',
            body_class="page-print",
            sidebar=self.sidebar_html(None),
            onpage="",
            content=cover + "".join(sections),
            pager="",
        )

    def build(self, cache, check_only):
        if not self.src.exists():
            return []
        print(f"[{self.loc}] -> {self.out.relative_to(ROOT.parent)}")
        self.out.mkdir(parents=True, exist_ok=True)
        pages = []
        missing = []
        for entry in self.entries:
            src = self.src / f'{entry["slug"]}.md'
            if not src.exists():
                missing.append(src.name)
                continue
            body, toc_tokens = render_markdown(src.read_text(encoding="utf-8"), cache)
            body = rewrite_links(body)
            pages.append((entry, body))
            if not check_only:
                (self.out / entry["file"]).write_text(self.build_page(entry, body, toc_tokens), encoding="utf-8")
        index_src = self.src / "index.md"
        if index_src.exists():
            body, toc_tokens = render_markdown(index_src.read_text(encoding="utf-8"), cache)
            body = rewrite_links(body)
            if not check_only:
                (self.out / "index.html").write_text(self.build_index(body, toc_tokens), encoding="utf-8")
        else:
            missing.append("index.md")
        if not check_only:
            print_page = self.out / "print.html"
            if print_page.exists():
                print_page.unlink()
        print(f"  {len(pages)} chapters" + (f", missing: {', '.join(missing)}" if missing else ""))
        return missing


def write_sitemap():
    """sitemap.xml and robots.txt for every page of every built locale."""
    urls = []
    for loc, L in LOCALES.items():
        if not (ROOT / L["src"]).exists():
            continue
        site = Site(loc)
        pages = ["index.html"] + [e["file"] for e in site.entries]
        for page in pages:
            alts = "".join(
                f'<xhtml:link rel="alternate" hreflang="{LOCALES[o]["html_lang"]}" href="{site.page_url(page, o)}"/>'
                for o in LOCALES if (ROOT / LOCALES[o]["src"]).exists()
            )
            urls.append(f'<url><loc>{site.page_url(page)}</loc>{alts}</url>')
    xml = ('<?xml version="1.0" encoding="UTF-8"?>\n'
           '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9" xmlns:xhtml="http://www.w3.org/1999/xhtml">\n'
           + "\n".join(urls) + "\n</urlset>\n")
    (OUT_ROOT / "sitemap.xml").write_text(xml, encoding="utf-8")
    (OUT_ROOT / "robots.txt").write_text(f"User-agent: *\nAllow: /\nSitemap: {SITE_URL}sitemap.xml\n", encoding="utf-8")
    print(f"  sitemap.xml ({len(urls)} urls), robots.txt")


def main():
    check_only = "--check" in sys.argv
    only = None
    if "--only" in sys.argv:
        only = sys.argv[sys.argv.index("--only") + 1]
    cache = load_cache()
    OUT_ROOT.mkdir(parents=True, exist_ok=True)
    missing = {}
    for loc in LOCALES:
        if only and loc != only:
            continue
        m = Site(loc).build(cache, check_only)
        if m:
            missing[loc] = m
    if not check_only:
        write_sitemap()
        if (OUT_ROOT / "assets").exists():
            shutil.rmtree(OUT_ROOT / "assets")
        shutil.copytree(ASSETS, OUT_ROOT / "assets")
        print("  assets/")
    CACHE_FILE.write_text(json.dumps(cache), encoding="utf-8")
    if missing:
        for loc, m in missing.items():
            print(f"Missing sources [{loc}]: " + ", ".join(m), file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
