# /// script
# requires-python = ">=3.11"
# dependencies = ["reportlab==4.4.10", "pypdf==6.6.2"]
# ///
"""Build or check the EHMX specification PDF against its Lean sources.

Run: uv run tools/build_ehmx_spec.py [--check]
--check is read-only and uses only the Python standard library.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import textwrap
from pathlib import Path
from xml.sax.saxutils import escape

ROOT = Path(__file__).resolve().parents[1]
PDF = ROOT / "output/pdf/ehmx-spec.pdf"
MANIFEST = ROOT / "docs/ehmx-spec-manifest.json"
SPEC = ROOT / "docs/ehmx-spec.md"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inputs() -> dict[str, str]:
    paths = sorted((ROOT / "EHMX").rglob("*.lean"))
    paths += [ROOT / "EHMX.lean", ROOT / "lakefile.toml", ROOT / "lean-toolchain",
              SPEC, ROOT / "docs/ehmx-todo.md", Path(__file__).resolve()]
    return {str(p.relative_to(ROOT)): sha(p) for p in paths}


def check() -> None:
    if not MANIFEST.exists() or not PDF.exists():
        raise SystemExit("Missing EHMX specification PDF or manifest; regenerate it.")
    old = json.loads(MANIFEST.read_text())
    current = inputs()
    changed = sorted(k for k in old["sources"].keys() | current.keys()
                     if old["sources"].get(k) != current.get(k))
    if changed or old["pdf_sha256"] != sha(PDF):
        raise SystemExit("EHMX PDF is stale: " + ", ".join(changed or [str(PDF)]))
    print("EHMX specification PDF matches all recorded sources.")


SUBSTITUTIONS = {
    "∀": "forall ", "∃": "exists ", "→": "->", "↔": "<->", "∧": "/\\",
    "∨": "\\/", "¬": "not ", "∈": " in ", "∉": " notin ", "⊆": " subset ",
    "∅": "empty", "≠": "!=", "≤": "<=", "≥": ">=", "⟨": "<", "⟩": ">",
    "Δ": "Delta", "Γ": "Gamma", "Σ": "Sigma", "ε": "eps", "η": "eta",
    "ρ": "rho", "ι": "iota", "θ": "theta", "σ": "sigma", "κ": "kappa",
    "₂": "2", "₁": "1", "₀": "0", "₃": "3", "·": ".", "∪": " union ",
}


def lean_excerpt(path: str, start: str, stop: str) -> str:
    source = (ROOT / path).read_text()
    a = source.index(start)
    b = source.index(stop, a + len(start))
    result = re.sub(r"/-.*?-/", "", source[a:b], flags=re.S)
    result = re.sub(r"--[^\n]*", "", result)
    for symbol, replacement in SUBSTITUTIONS.items():
        result = result.replace(symbol, replacement)
    if not result.isascii():
        bad = sorted(set(c for c in result if not c.isascii()))
        raise ValueError(f"Unmapped code characters in {path}: {bad}")
    lines = []
    for line in result.strip().splitlines():
        lines.extend(textwrap.wrap(line, width=104, subsequent_indent="    ",
                                   replace_whitespace=False, drop_whitespace=False) or [""])
    return "\n".join(lines)


EXCERPTS = [
    ("項と型", "EHMX/Syntax.lean", "inductive Ty where", "def Ty.fv"),
    ("項の構文", "EHMX/Syntax.lean", "inductive PVar where", "def Expr.LCAt"),
    ("操作宣言と整形式性", "EHMX/Syntax.lean", "structure OpDecl where", "inductive Predicate"),
    ("制約とスキーム", "EHMX/Syntax.lean", "mutual\ninductive Constraint", "def Constraint.le"),
    ("制約の意味", "EHMX/Semantics.lean", "mutual\ndef Constraint.Holds", "def Entails"),
    ("モデルの全前提", "EHMX/Semantics.lean", "structure EffectFramework", "def Scheme.instanceConstraint"),
    ("型付けの全規則", "EHMX/Typing.lean", "def JudgmentWF", "theorem typingWF"),
    ("継続と簡約", "EHMX/Operational.lean", "def Expr.resume", "theorem resumeValue"),
    ("制約生成", "EHMX/Inference.lean", "def resultConstraint", "end EHMX"),
    ("証明済み：型・効果代入", "EHMX/Proofs/TypingTypeSubstitution.lean",
     "theorem typingTypeEffectSubstitution", " := by"),
    ("証明済み：スキーム値代入", "EHMX/Proofs/ValueSubstitution.lean",
     "theorem schemeValueSubstitution", " := by"),
    ("最終目標の全前提と結論", "EHMX/Goals.lean", "def Assumptions", "end EHMX"),
]


def build() -> None:
    from reportlab.lib import colors
    from reportlab.lib.enums import TA_LEFT
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.styles import ParagraphStyle
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.cidfonts import UnicodeCIDFont
    from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Preformatted, PageBreak
    from pypdf import PdfReader

    pdfmetrics.registerFont(UnicodeCIDFont("HeiseiMin-W3"))
    body = ParagraphStyle("Body", fontName="HeiseiMin-W3", fontSize=10.2, leading=16,
                          spaceAfter=8, wordWrap="CJK", alignment=TA_LEFT,
                          allowWidows=0, allowOrphans=0)
    h1 = ParagraphStyle("Title", parent=body, fontSize=19, leading=27, spaceAfter=20)
    h2 = ParagraphStyle("Section", parent=body, fontSize=13, leading=20, spaceBefore=13,
                        spaceAfter=8, keepWithNext=True, textColor=colors.HexColor("#183c55"))
    code = ParagraphStyle("Code", fontName="Courier", fontSize=8, leading=10.5,
                          spaceAfter=10, leftIndent=6, backColor=colors.HexColor("#f3f5f7"))
    story = []
    def prose(text: str) -> str:
        # CID Japanese fonts and Latin fonts have different advance widths.
        # Use Helvetica for Latin runs so Lean identifiers remain legible.
        return "".join(
            f'<font name="Helvetica">{escape(part)}</font>' if part.isascii() else escape(part)
            for part in re.split(r"([ -~]+)", text) if part
        )

    for block in SPEC.read_text().strip().split("\n\n"):
        if block.startswith("# "):
            style, text = h1, block[2:]
        elif block.startswith("## "):
            style, text = h2, block[3:]
        else:
            style, text = body, block
        text = text.replace("**", "").replace("`", "").replace("\n", " ")
        story.append(Paragraph(prose(text), style))

    story += [PageBreak(), Paragraph("付録 Lean の定義と証明済み定理の型", h1),
              Paragraph("以下はコード表示のため記号を ASCII に置換したもの。"
                        "forall は全称、exists は存在、-&gt; は矢印、subset は包含、"
                        "empty は空集合、Delta と Gamma は文脈、eps は効果を表す。"
                        "Goal は命題の定義であり、証明済みを意味しない。", body)]
    for title, path, start, stop in EXCERPTS:
        story.append(Paragraph(title, h2))
        story.append(Paragraph(prose(path), body))
        story.append(Preformatted(lean_excerpt(path, start, stop), code))
        story.append(Spacer(1, 4))

    def footer(canvas, doc):
        canvas.saveState()
        canvas.setFont("Helvetica", 8)
        canvas.setFillColor(colors.HexColor("#506070"))
        canvas.drawString(43, 26, "EHMX specification - implementation in progress")
        canvas.drawRightString(A4[0] - 43, 26, str(doc.page))
        canvas.restoreState()

    PDF.parent.mkdir(parents=True, exist_ok=True)
    doc = SimpleDocTemplate(str(PDF), pagesize=A4, rightMargin=43, leftMargin=43,
                            topMargin=42, bottomMargin=42, title="EHMX 仕様と証明状況",
                            author="lean-ehmx", invariant=1)
    doc.build(story, onFirstPage=footer, onLaterPages=footer)
    pages = PdfReader(PDF).pages
    if not pages or any(not p.extract_text().strip() for p in pages):
        raise RuntimeError("Empty PDF page detected")
    MANIFEST.write_text(json.dumps({"sources": inputs(), "pdf_sha256": sha(PDF),
                                    "pages": len(pages)}, ensure_ascii=False, indent=2) + "\n")
    print(f"Created {PDF.relative_to(ROOT)} ({len(pages)} pages)")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    check() if args.check else build()
