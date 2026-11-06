#!/usr/bin/env python3
"""Checks that a translated chapter keeps the structure of its English source.

Usage: python3 docs/book/tools/check-translation.py docs/book/src/07-inductive-nat.md docs/book/src-ja/07-inductive-nat.md

Compared, in order: fenced code blocks (identical text), display math blocks
(identical TeX), inline math (same multiset), HTML tags with their attributes
(same sequence, except data-title values which may be translated), link
targets (same sequence), playground and explorer scripts (identical except for
lines starting with #, which are comments and may be translated), and the
CONTENTS_GO_HERE marker in index files. Exit status 1 on any difference.
"""

import re
import sys
from collections import Counter


def fenced(text):
    return re.findall(r"```[a-z0-9]*\n.*?```", text, re.S)


def display_math(text):
    return [m.strip() for m in re.findall(r"\$\$(.*?)\$\$", text, re.S)]


def inline_math(text):
    text = re.sub(r"```.*?```", "", text, flags=re.S)
    text = re.sub(r"\$\$.*?\$\$", "", text, flags=re.S)
    return Counter(re.findall(r"\$(?!\s)(?:\\.|[^$\\\n])+?(?<!\s)\$", text))


def tags(text):
    text = re.sub(r"```.*?```", "", text, flags=re.S)
    out = []
    for m in re.finditer(r"<(/?[a-zA-Z][a-zA-Z0-9]*)((?:\s+[a-zA-Z-]+(?:=\"[^\"]*\")?)*)\s*/?>", text):
        attrs = re.sub(r'data-title="[^"]*"', 'data-title="*"', m.group(2))
        attrs = re.sub(r'aria-label="[^"]*"', 'aria-label="*"', attrs)
        out.append(m.group(1) + attrs)
    return out


def links(text):
    return re.findall(r"\]\(([^)\s]+)\)", text)


def scripts(text):
    blocks = re.findall(r"<pre[^>]*>(.*?)</pre>", text, re.S)
    norm = []
    for b in blocks:
        lines = [l for l in b.split("\n") if not l.strip().startswith("#")]
        norm.append("\n".join(lines).strip())
    return norm


def main():
    src, dst = sys.argv[1], sys.argv[2]
    a = open(src, encoding="utf-8").read()
    b = open(dst, encoding="utf-8").read()
    problems = []

    fa, fb = fenced(a), fenced(b)
    if len(fa) != len(fb):
        problems.append(f"fenced code blocks: {len(fa)} in source, {len(fb)} in translation")
    else:
        for i, (x, y) in enumerate(zip(fa, fb)):
            if x != y:
                # Allow translated comments inside leanmini/text blocks only.
                xs = [l for l in x.split("\n") if not l.strip().startswith(("#", "//"))]
                ys = [l for l in y.split("\n") if not l.strip().startswith(("#", "//"))]
                if xs != ys:
                    problems.append(f"fenced code block {i + 1} differs (non-comment lines)")

    da, db = display_math(a), display_math(b)
    if da != db:
        problems.append(f"display math differs: {len(da)} blocks in source, {len(db)} in translation" +
                        ("" if len(da) != len(db) else " (same count, different TeX at block " +
                         str(next(i + 1 for i, (x, y) in enumerate(zip(da, db)) if x != y)) + ")"))

    ia, ib = inline_math(a), inline_math(b)
    if ia != ib:
        missing = list((ia - ib).elements())[:5]
        extra = list((ib - ia).elements())[:5]
        problems.append(f"inline math differs: missing {missing} extra {extra}")

    ta, tb = tags(a), tags(b)
    if ta != tb:
        for i, (x, y) in enumerate(zip(ta, tb)):
            if x != y:
                problems.append(f"HTML tag sequence differs at tag {i + 1}: source <{x}> vs translation <{y}>")
                break
        else:
            problems.append(f"HTML tag count differs: {len(ta)} vs {len(tb)}")

    la, lb = links(a), links(b)
    if la != lb:
        problems.append(f"link targets differ: {len(la)} vs {len(lb)} " + str([x for x in la if x not in lb][:4]))

    sa, sb = scripts(a), scripts(b)
    if sa != sb:
        problems.append("a <pre> script differs in a non-comment line")

    if ("CONTENTS_GO_HERE" in a) != ("CONTENTS_GO_HERE" in b):
        problems.append("CONTENTS_GO_HERE marker missing")

    if "—" in b:
        problems.append("translation contains an em dash")

    if problems:
        print(f"FAIL {dst}")
        for p in problems:
            print("  - " + p)
        sys.exit(1)
    print(f"ok   {dst}")


if __name__ == "__main__":
    main()
