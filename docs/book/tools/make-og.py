#!/usr/bin/env python3
"""Renders the social preview images (1200x630) for each language into
docs/book/assets/og/<locale>.png. Run once after changing titles."""
import sys
from pathlib import Path
from PIL import Image, ImageDraw, ImageFont

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from locales import LOCALES  # noqa: E402

MONO = "/usr/share/fonts/truetype/dejavu/DejaVuSansMono-Bold.ttf"
LATIN = "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"
LATIN_BOLD = "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf"
CJK = {"ja": "/usr/share/fonts/opentype/ipafont-gothic/ipag.ttf", "zh": "/usr/share/fonts/truetype/arphic-gbsn00lp/gbsn00lp.ttf"}
BG, FG, MUTED, ACCENT, RED, PANEL, BORDER = "#0b0d10", "#e8e6e1", "#8a9099", "#62d38f", "#e0241b", "#111419", "#23272e"

def font(path, size):
    return ImageFont.truetype(path, size)

def wrap(draw, text, fnt, width, cjk):
    """Greedy wrap; CJK breaks between characters, Latin between words."""
    units = list(text) if cjk else text.split(" ")
    lines, cur = [], ""
    for u in units:
        cand = cur + u if cjk or not cur else cur + " " + u
        if draw.textlength(cand, font=fnt) <= width or not cur:
            cur = cand
        else:
            lines.append(cur); cur = u
    if cur: lines.append(cur)
    return lines

for loc, L in LOCALES.items():
    cjk = loc in CJK
    im = Image.new("RGB", (1200, 630), BG)
    d = ImageDraw.Draw(im)
    # logo
    logo = font(MONO, 72)
    d.text((80, 70), "MiniLean4", font=logo, fill=FG)
    w = d.textlength("MiniLean4", font=logo)
    d.rectangle([80 + w + 14, 70 + 50, 80 + w + 14 + 22, 70 + 72], fill=RED)
    # title
    tf = font(CJK[loc] if cjk else LATIN_BOLD, 54 if cjk else 50)
    lines = wrap(d, L["title"], tf, 1040, cjk)
    y = 200
    for ln in lines[:3]:
        d.text((80, y), ln, font=tf, fill=FG); y += 72 if cjk else 64
    # tagline
    tag = {"en": "A Lean 4-style proof kernel in Rust, explained chapter by chapter, with the kernel running in your browser.",
           "ja": "Rust で書いた Lean 4 風の証明カーネルを章ごとに解説。カーネルはブラウザの中で動く。",
           "zh": "用 Rust 写成的 Lean 4 风格证明内核，逐章讲解；内核就在你的浏览器里运行。"}[loc]
    sf = font(CJK[loc] if cjk else LATIN, 28)
    y += 18
    for ln in wrap(d, tag, sf, 1040, cjk)[:2]:
        d.text((80, y), ln, font=sf, fill=MUTED); y += 40
    # terminal strip at the bottom
    d.rectangle([80, 500, 1120, 580], fill=PANEL, outline=BORDER)
    for i, c in enumerate(["#ff5f57", "#febc2e", "#28c840"]):
        d.ellipse([98 + i * 20, 514, 110 + i * 20, 526], fill=c)
    mf = font(MONO, 24)
    d.text((100, 538), "goal forall (P : Sort 0), P -> P", font=mf, fill=ACCENT)
    d.text((620, 538), "QED. Kernel checked proof.", font=mf, fill=MUTED)
    out = ROOT / "assets" / "og" / f"{loc}.png"
    im.save(out, optimize=True)
    print(out, im.size)
