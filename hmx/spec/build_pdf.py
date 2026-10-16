# /// script
# requires-python = ">=3.10"
# dependencies = ["reportlab>=4,<5"]
# ///
"""Generate the review report from the inventory, with exact Lean file hashes."""
import hashlib
import json
from collections import defaultdict
from pathlib import Path
from xml.sax.saxutils import escape

from reportlab.lib import colors
from reportlab.lib.enums import TA_LEFT
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.units import mm
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.cidfonts import UnicodeCIDFont
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak, KeepTogether

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'output/pdf/hmx-statement-audit.pdf'
OUT.parent.mkdir(parents=True, exist_ok=True)
pdfmetrics.registerFont(UnicodeCIDFont('HeiseiKakuGo-W5'))
body = ParagraphStyle('body', fontName='HeiseiKakuGo-W5', fontSize=9, leading=14, wordWrap='CJK', spaceAfter=7)
small = ParagraphStyle('small', parent=body, fontSize=7.5, leading=11, spaceAfter=3)
issue_body = ParagraphStyle('issue_body', parent=body, fontSize=8.5, leading=13, spaceAfter=5)
title = ParagraphStyle('title', parent=body, fontSize=22, leading=30, spaceAfter=18, textColor=colors.HexColor('#17374d'))
heading = ParagraphStyle('heading', parent=body, fontSize=14, leading=21, spaceBefore=10, spaceAfter=10, textColor=colors.HexColor('#17374d'))
subheading = ParagraphStyle('subheading', parent=body, fontSize=10, leading=15, spaceBefore=8, spaceAfter=5)

def read(name):
    return json.loads((ROOT / f'audit/{name}.json').read_text())

def p(text, style=body):
    return Paragraph(escape(str(text)).replace('\n', '<br/>'), style)

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
story = [p('HMX ステートメント照合', title), p('作成途中 / 証明開始前の確認資料', heading)]
story += [p('この資料は、指定された博士論文と独立した Lean プロジェクトの対応を確認するためのものです。仕様は未確定です。定理・補題の証明は追加していません。'),
          p(f'原典: {source["author"]}, {source["title"]}, {source["dissertation_date"]}.'),
          p('原典ファイル: main.pdf / PDF 268ページ。本文の印刷ページ番号に12を加えたものがPDFページ番号です。'),
          p('SHA-256: ' + source['sha256'], small),
          p('対象: 第3・4章（印刷17-113ページ）と必要な背景・付録。第5章の具体的応用は今回の本体に含めません。'),
          p(f'番号付き項目: {len(groups)}項目 / 本文・再掲を含め{len(items)}出現。Lean の草案への対応がある項目: {mapped}。この数は照合完了数ではありません。'),
          p('状態の意味', heading),
          p('draft: Lean に記述した草案。partial: 一部のみ記述。not_transcribed: 未実装。review_pending: 人による照合が未完了。印刷どおりの命題が常に成立するとは限りません。補題13は原典自身が一般には成立しないと説明し、Conjecture 1は予想として述べています。'),
          p('確定条件', heading),
          p('構文、定義、条件、節全体の前提、全ステートメントを転記し、原典からLeanとLeanから原典の両方向で照合します。未確定事項と未実装項目を解消し、全体ビルドと対応表検査を通してから、仕様確定を記録します。証明はその後です。'),
          p('ビルドと公理依存の確認は、命題の正しさや証明完了を保証しません。この資料はその区別を維持しています。'), PageBreak()]

story.append(p('番号付き項目の対応', heading))
rows = [['原典の項目', '印刷ページ', '状態 / Lean 宣言']]
order = {'Definition': 0, 'Lemma': 1, 'Theorem': 2, 'Corollary': 3, 'Conjecture': 4, 'Remark': 5}
for key, group in sorted(groups.items(), key=lambda kv: (order[kv[1][0]['kind']], kv[1][0]['number'])):
    first = group[0]
    locations = ', '.join(str(r['printed_page']) for r in group)
    names = sorted({n for r in group for n in r['lean']})
    statuses = ', '.join(sorted({r['status'] for r in group}))
    rows.append([first['kind'] + ' ' + str(first['number']), locations, statuses + '\n' + ('\n'.join(names) if names else 'Lean 宣言は未登録')])
story.append(table(rows, [30*mm, 25*mm, 113*mm]))
story += [PageBreak(), p('図・推論規則', heading)]
story.append(table([['図', '印刷ページ', '状態 / 対応']] + [[r['id'], str(r['printed_page']), r['status']+'\n'+'\n'.join(r['lean'])] for r in read('figures')], [30*mm, 25*mm, 113*mm]))

story += [PageBreak(), p('原文・採用した修正・未確定事項', heading), p('原文の誤記、採用した修正、実装の残りを区別して記録します。resolved は表記の扱いを決めたという意味であり、定理を証明したという意味ではありません。open の修正案は引き続き確認が必要です。')]
for issue in read('ambiguities'):
    block = [p(issue['id']+' / '+issue['title'], subheading),
        p(f'原典: 印刷 {issue["printed_page"]} / PDF {issue["pdf_page"]}。状態: {issue["status"]}。', small),
        p(issue['observation'], issue_body)]
    if 'printed_formula' in issue:
        block.append(p('原文: '+issue['printed_formula'], small))
    if 'adopted_reading' in issue:
        block.append(p('読み・修正理由: '+issue['adopted_reading'], small))
    block.append(p('現状: '+issue['current_action'], issue_body))
    story.append(KeepTogether(block))

story += [PageBreak(), p('番号のない条件・表記規約', heading)]
for row in read('conventions'):
    story.append(KeepTogether([p(f'{row["id"]} / 印刷 {row["printed_page"]}', subheading), p(row['description'], small), p(row['implementation']+' / '+row['status'], small)]))

story += [PageBreak(), p('この PDF が参照する Lean ファイル', heading), p('以下は生成時点の SHA-256 です。ファイルが変わった場合は PDF を再生成します。ハッシュの一致は仕様の正しさの証明ではありません。')]
for file in sorted((ROOT/'HMX').glob('*.lean'))+[ROOT/'HMX.lean']:
    story.append(KeepTogether([p(str(file.relative_to(ROOT)), subheading), p(hashlib.sha256(file.read_bytes()).hexdigest(), small)]))

def footer(canvas, doc):
    canvas.saveState()
    canvas.setStrokeColor(colors.HexColor('#cbd5dc'))
    canvas.line(21*mm, 17*mm, 189*mm, 17*mm)
    canvas.setFont('HeiseiKakuGo-W5', 8)
    canvas.drawString(21*mm, 12*mm, 'HMX / 未確定の草案 / main.pdf に固定')
    canvas.drawRightString(189*mm, 12*mm, str(doc.page))
    canvas.restoreState()

doc = SimpleDocTemplate(str(OUT), pagesize=A4, leftMargin=21*mm, rightMargin=21*mm,
    topMargin=19*mm, bottomMargin=23*mm, title='HMX statement audit - draft', author='HMX specification project')
doc.build(story, onFirstPage=footer, onLaterPages=footer)
print(OUT)
