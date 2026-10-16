#!/usr/bin/env python3
"""Structural coverage check. This does not establish mathematical fidelity."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--require-complete', action='store_true')
parser.add_argument('--lean-checks', action='store_true')
args = parser.parse_args()
source = json.loads((ROOT / 'audit/source.json').read_text())
pdf = ROOT / source['file']
errors = []
if hashlib.sha256(pdf.read_bytes()).hexdigest() != source['sha256']:
    errors.append('The fixed dissertation PDF has changed.')
text = subprocess.check_output(['pdftotext', '-layout', str(pdf), '-'], text=True)
pages = text.split('\f')
pattern = re.compile(r'(?m)^\s*(Definition|Theorem|Lemma|Corollary|Remark|Conjecture)\s+(\d+)\b')
actual = []
for page, content in enumerate(pages, 1):
    printed = page - 12
    if 8 <= printed <= 113 or 182 <= printed <= 226:
        actual.extend((m[1].lower() + m[2], page) for m in pattern.finditer(content))
items = json.loads((ROOT / 'audit/items.json').read_text())
recorded = [(r['id'], r['pdf_page']) for r in items]
if sorted(actual) != sorted(recorded):
    errors.append('Numbered source occurrences and the inventory differ.')

files = sorted((ROOT / 'HMX').glob('*.lean')) + [ROOT / 'HMX.lean']
for path in files:
    content = path.read_text()
    # Strip comments before checking declarations/tokens.
    code = re.sub(r'/-.*?-/', '', content, flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    if re.search(r'\b(sorry|admit|axiom|theorem|lemma)\b', code):
        errors.append(f'{path.relative_to(ROOT)}: proof/axiom token in statement-only phase')
    for imp in re.findall(r'^import\s+(\S+)', code, re.M):
        if not (imp == 'HMX' or imp.startswith('HMX.') or imp.startswith('Mathlib.')):
            errors.append(f'{path.relative_to(ROOT)}: unexpected import {imp}')

groups = {key: [r for r in items if r['id'] == key] for key in sorted({r['id'] for r in items})}
mapped = sum(any(r['lean'] for r in rows) for rows in groups.values())
unmapped = [key for key, rows in groups.items() if not any(r['lean'] for r in rows)]
issues = json.loads((ROOT / 'audit/ambiguities.json').read_text())
open_issues = [r['id'] for r in issues if r['status'] != 'resolved']
print(f'Numbered inventory: {len(items)} occurrences, {len(groups)} distinct items')
print(f'Items with draft Lean mappings: {mapped}')
print('Items without Lean mappings: ' + ', '.join(unmapped))
print('Open audit issues: ' + ', '.join(open_issues))
print('Freeze status: ' + source['status'])

if args.lean_checks:
    linked = items + json.loads((ROOT / 'audit/figures.json').read_text()) + json.loads((ROOT / 'audit/conventions.json').read_text())
    names = sorted({name for r in linked for name in r.get('lean', [])})
    generated = ROOT / '.lake/audit/Statements.lean'
    generated.parent.mkdir(parents=True, exist_ok=True)
    generated.write_text('import HMX\n\n' + '\n'.join('#check ' + n for n in names) + '\n' +
        '\n'.join('#print axioms HMX.Statement.' + n for n in ['theorem7', 'theorem16', 'theorem17', 'corollary7']) + '\n')
    result = subprocess.run(['lake', 'env', 'lean', str(generated)], cwd=ROOT, text=True, capture_output=True)
    print(result.stdout)
    if result.returncode:
        errors.append('A mapped Lean declaration did not elaborate: ' + result.stderr)
    if 'sorryAx' in result.stdout:
        errors.append('A checked statement definition depends on sorryAx.')

if args.require_complete:
    for group in ['items', 'figures', 'conventions']:
        data = json.loads((ROOT / f'audit/{group}.json').read_text())
        if any(r['status'] not in ['verified', 'excluded_with_reason', 'dependency_diagram_verified'] for r in data):
            errors.append(f'{group}: source review/transcription is incomplete')
        for row in data:
            if row['status'] == 'excluded_with_reason' and not row.get('exclusion_reason'):
                errors.append(f'{group}/{row["id"]}: exclusion has no recorded reason')
            if row['status'] == 'verified' and not row.get('second_source_review'):
                errors.append(f'{group}/{row["id"]}: second source comparison is not recorded')
    if open_issues:
        errors.append('Unresolved source or implementation issues remain.')
    if source['status'] != 'frozen':
        errors.append('The specification has not been frozen.')
if errors:
    for error in errors:
        print('ERROR: ' + error)
    raise SystemExit(1)
print('Structural checks passed. This is NOT a certification of source fidelity.')
