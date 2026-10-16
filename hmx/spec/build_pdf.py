# /// script
# requires-python = ">=3.10"
# dependencies = ["reportlab>=4,<5"]
# ///
"""Generate the review report from the inventory, with exact Lean file hashes."""
import hashlib
import json
import os
import subprocess
import sys
from collections import defaultdict
from itertools import groupby
from pathlib import Path
from xml.sax.saxutils import escape

from reportlab.lib import colors
from reportlab.lib.enums import TA_LEFT
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.units import mm
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.cidfonts import UnicodeCIDFont
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak, KeepTogether

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_audit import load_audit, lean_hashes, record_digest, record_key, validate, GROUPS

# Never publish an audit against Lean files or comparison records changed since review.
audit = load_audit(ROOT)
review = audit['review']
source_pages = subprocess.check_output(['pdftotext', '-layout', str(ROOT / audit['source']['file']), '-'], text=True).split('\f')
errors = validate(audit, source_pages, lean_hashes(ROOT), complete=True)
if errors:
    raise SystemExit('Cannot publish an incomplete audit:\n' + '\n'.join(errors))
if review.get('lean_sha256') != lean_hashes(ROOT):
    raise SystemExit('Lean changed since source comparison; review before generating PDF.')
if review.get('reviewed_records') != {
        record_key(g, r): record_digest(r) for g in GROUPS for r in audit[g]}:
    raise SystemExit('Comparison records changed since review; review before generating PDF.')
OUT = ROOT / 'output/pdf/hmx-statement-audit.pdf'
OUT.parent.mkdir(parents=True, exist_ok=True)
pdfmetrics.registerFont(UnicodeCIDFont('HeiseiKakuGo-W5'))
math_candidates = [os.environ.get('HMX_AUDIT_MATH_FONT', ''),
    '/System/Library/Fonts/Apple Symbols.ttf',
    '/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf']
math_font_path = next((f for f in math_candidates if f and Path(f).is_file()), None)
if not math_font_path:
    raise SystemExit('Set HMX_AUDIT_MATH_FONT to a TrueType font with mathematical symbols.')
pdfmetrics.registerFont(TTFont('AuditMath', math_font_path))
body = ParagraphStyle('body', fontName='HeiseiKakuGo-W5', fontSize=9, leading=14, wordWrap='CJK', spaceAfter=7)
small = ParagraphStyle('small', parent=body, fontSize=7.5, leading=11, spaceAfter=3)
issue_body = ParagraphStyle('issue_body', parent=body, fontSize=8.5, leading=13, spaceAfter=5)
title = ParagraphStyle('title', parent=body, fontSize=22, leading=30, spaceAfter=18, textColor=colors.HexColor('#17374d'))
heading = ParagraphStyle('heading', parent=body, fontSize=14, leading=21, spaceBefore=10, spaceAfter=10, textColor=colors.HexColor('#17374d'))
subheading = ParagraphStyle('subheading', parent=body, fontSize=10, leading=15, spaceBefore=8, spaceAfter=5)

def read(name):
    return json.loads((ROOT / f'audit/{name}.json').read_text())

def p(text, style=body):
    # The Japanese CID font lacks turnstiles and some order/composition symbols.
    # Embed a symbol font rather than replacing the source's mathematical notation.
    text = str(text).translate(str.maketrans({'–': '-', '—': '-', '‑': '-'}))
    def font(c):
        if ord(c) < 128:
            return 'Helvetica'
        if 0x300 <= ord(c) <= 0x3ff or 0x2100 <= ord(c) <= 0x2aff:
            return 'AuditMath'
        return 'HeiseiKakuGo-W5'
    parts = []
    for name, chars in groupby(text, font):
        run = ''.join(chars)
        if name == 'AuditMath':
            missing = [c for c in run if ord(c) not in pdfmetrics.getFont(name).face.charToGlyph]
            if missing:
                raise ValueError(f'Missing mathematical glyphs: {missing}')
        parts.append(f'<font name="{name}">' + escape(run).replace('\n', '<br/>') + '</font>')
    return Paragraph(''.join(parts), style)

def table(rows, widths):
    t = Table([[p(c, small) for c in row] for row in rows], colWidths=widths, repeatRows=1, hAlign='LEFT')
    t.setStyle(TableStyle([
        ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#e4edf3')),
        ('VALIGN', (0, 0), (-1, -1), 'TOP'),
        ('LINEBELOW', (0, 0), (-1, 0), .5, colors.HexColor('#8aa3b3')),
        ('LINEBELOW', (0, 1), (-1, -1), .25, colors.HexColor('#d8e0e5')),
        ('LEFTPADDING', (0, 0), (-1, -1), 5), ('RIGHTPADDING', (0, 0), (-1, -1), 5),
        ('TOPPADDING', (0, 0), (-1, -1), 4), ('BOTTOMPADDING', (0, 0), (-1, -1), 4),
    ]))
    return t

source = read('source')
items = read('items')
groups = defaultdict(list)
for item in items:
    groups[item['id']].append(item)
mapped = sum(any(r['lean'] for r in rows) for rows in groups.values())
story = [p('HMX ステートメント照合', title), p('定義・仮定・定理文の転記完了 / 証明未着手', heading)]
story += [p('この資料は、指定された博士論文と独立した Lean プロジェクトの対応を記録します。対象範囲の定義・仮定・定理文を照合し、見つかった実装上の不足を修正しました。原典の表記差や未指定記号は明示して保持しています。定理・補題の証明、背景モデルの構成・存在証明、採用した読みの数学的妥当性の検証は含めません。'),
          p(f'原典: {source["author"]}, {source["title"]}, {source["dissertation_date"]}.'),
          p('原典ファイル: main.pdf / PDF 268ページ。本文の印刷ページ番号に12を加えたものがPDFページ番号です。'),
          p('SHA-256: ' + source['sha256'], small),
          p('対象: 第3・4章（印刷17-113ページ）と必要な背景・付録。第5章の具体的応用は今回の本体に含めません。'),
          p(f'番号付き項目（例を含む）: {len(groups)}項目 / {len(items)}出現（記述・再掲{sum(r["occurrence_kind"] == "statement" for r in items)}、既出番号への参照{sum(r["occurrence_kind"] == "reference" for r in items)}）。図{len(audit["figures"])}件、番号のない条件・規約{len(audit["conventions"])}件。Lean の対応がある項目: {mapped}。この数は証明済みの数ではありません。'),
          p('状態の意味', heading),
          p('transcribed: 宣言を収録。reviewed: 照合記録あり。reviewed_with_source_note: 原文の問題・読みを伴う照合。recorded_for_proof_review: 数学的検討を後に残す。印刷どおりの命題が常に成立するとは限りません。補題13は原典自身が一般には成立しないと説明し、Conjecture 1は予想として述べています。'),
          p('収録と内容確認の区別', heading),
          p('対象範囲の番号付き項目・図・条件を対応付けました。原文の誤記候補は修正せず、未定義記号は明示的な引数にしています。原文の意味が一意でない場合の読みは別に記録します。転記の完了は、数学的な成立性・原典との同値性の認証ではありません。'),
          p('各出現の式・条件・参照先を audit/items.json に記録しています。PDFのテキスト抽出を照合し、不鮮明な数式はページ画像で確認しました。抽出テキストには否定記号・添字の文字化けがあるため、main.pdf が正本です。'),
          p('ビルド・対応検査とハッシュは構文、参照、照合後の変更を確認します。機械検査だけで原文との一致や命題の正しさを証明するものではありません。'), PageBreak()]

story.append(p('再照合の結果', heading))
story.append(p('番号の対応に加え、定義の適用範囲、節の条件、式の成分、本文と付録の差を照合しました。以下の corrected は転記の修正済み、source_ambiguity_recorded は原文の用語の読みを記録した状態です。後者の数学的妥当性を解決済みとは扱いません。'))
for row in read('review')['findings']:
    story.append(KeepTogether([p(row['id'] + ' / ' + row['status'], subheading),
        p('原典の印刷ページ: ' + ', '.join(map(str, row['printed_pages'])), small),
        p(row['finding'], issue_body), p(row['action'], issue_body)]))
story.append(p('定理7・16・17・系7', heading))
for row in read('review')['four_main_statements']:
    story.append(KeepTogether([p(row['id'], subheading), p(row['result'], issue_body)]))
story.append(p(f'{len(items)}出現それぞれに照合内容を記録しました。定理の結論から証明できるかの検証は行っていません。定理17の付録はW、本文はWtermと印刷されるため別の命題として収録しています。'))
story.append(PageBreak())

story.append(p('番号付き項目の対応', heading))
rows = [['原典の項目', '印刷ページ', '状態 / Lean 宣言']]
order = {'Definition': 0, 'Lemma': 1, 'Theorem': 2, 'Corollary': 3, 'Conjecture': 4, 'Remark': 5, 'Example': 6}
for key, group in sorted(groups.items(), key=lambda kv: (order[kv[1][0]['kind']], kv[1][0]['number'])):
    first = group[0]
    locations = ', '.join(str(r['printed_page']) + ('(参照)' if r['occurrence_kind'] == 'reference' else '') for r in group)
    names = sorted({n for r in group for n in r['lean']})
    statuses = '転記・照合済み' + (' / 原文の注記あり' if any(r.get('source_issue_ids') for r in group) else '')
    rows.append([first['kind'] + ' ' + str(first['number']), locations, statuses + '\n' + ('\n'.join(names) if names else 'Lean 宣言は未登録')])
story.append(table(rows, [30*mm, 25*mm, 113*mm]))
story += [PageBreak(), p('図・推論規則', heading)]
story.append(table([['図', '印刷ページ', '状態 / 対応']] + [[r['id'], str(r['printed_page']), r['status']+'\n'+'\n'.join(r['lean'])] for r in read('figures')], [30*mm, 25*mm, 113*mm]))

story += [PageBreak(), p('原文の問題と転記での扱い', heading), p('原文の誤記候補、未指定記号、型を付ける際の読みを記録します。誤記候補を修正して成立する命題に置き換えてはいません。用語をLeanへ展開した読みを明示し、その数学的妥当性と背景モデルの構成・存在は後の検証に残しています。')]
for issue in read('ambiguities'):
    block = [p(issue['id']+' / '+issue['title'], subheading),
        p(f'原典: 印刷 {issue["printed_page"]} / PDF {issue["pdf_page"]}。状態: {issue["status"]}。', small),
        p(issue['observation'], issue_body)]
    if 'printed_formula' in issue:
        block.append(p('原文: '+issue['printed_formula'], small))
    if 'previous_proposed_reading' in issue:
        block.append(p('以前の修正案（現行版の採用条件ではない）: '+issue['previous_proposed_reading'], small))
    block.append(p('現状: '+issue['current_action'], issue_body))
    story.append(KeepTogether(block))

story += [PageBreak(), p('番号のない条件・表記規約', heading)]
for row in read('conventions'):
    story.append(KeepTogether([p(f'{row["id"]} / 印刷 {row["printed_page"]}', subheading), p(row['description'], small), p(row['implementation']+' / '+row['status'], small)]))

story += [PageBreak(), p('原典の条件と使用先の接続', heading),
    p('宣言が存在するだけでなく、以下の使用先の命題本体が必要な条件を参照することをLeanの展開結果で検査します。これは式全体の原典一致や数学的妥当性の証明ではありません。')]
for row in read('connections'):
    story.append(KeepTogether([p(row['declaration'], subheading),
        p('原典: ' + ', '.join(map(str,row['source_pages'])) + ' / ' + row['reason'], small),
        p('\n'.join(row['required']), small)]))

story += [PageBreak(), p('この PDF が参照する Lean ファイル', heading), p('以下は生成時点の SHA-256 です。ファイルが変わった場合は PDF を再生成します。ハッシュの一致は仕様の正しさの証明ではありません。')]
for file in sorted((ROOT/'HMX').glob('*.lean'))+[ROOT/'HMX.lean']:
    story.append(KeepTogether([p(str(file.relative_to(ROOT)), subheading), p(hashlib.sha256(file.read_bytes()).hexdigest(), small)]))

def footer(canvas, doc):
    canvas.saveState()
    canvas.setStrokeColor(colors.HexColor('#cbd5dc'))
    canvas.line(21*mm, 17*mm, 189*mm, 17*mm)
    canvas.setFont('HeiseiKakuGo-W5', 8)
    canvas.drawString(21*mm, 12*mm, 'HMX / 定義・仮定・定理文の転記 / 証明未着手')
    canvas.drawRightString(189*mm, 12*mm, str(doc.page))
    canvas.restoreState()

doc = SimpleDocTemplate(str(OUT), pagesize=A4, leftMargin=21*mm, rightMargin=21*mm,
    topMargin=19*mm, bottomMargin=23*mm, title='HMX dissertation transcription - unproved', author='HMX specification project')
doc.build(story, onFirstPage=footer, onLaterPages=footer)
print(OUT)
