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
open_issues = [r['id'] for r in issues if r['status'] == 'recorded_for_proof_review']
print(f'Numbered inventory: {len(items)} occurrences, {len(groups)} distinct items')
print(f'Items with Lean mappings: {mapped}')
print('Items without Lean mappings: ' + ', '.join(unmapped))
print('Mathematical review deferred: ' + ', '.join(open_issues))
print('Transcription status: ' + source['status'])
print('Mathematical validation: ' + source.get('mathematical_validation', 'pending'))

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
    if unmapped:
        errors.append('Numbered items without a transcription remain.')
    for group in ['items', 'figures', 'conventions']:
        data = json.loads((ROOT / f'audit/{group}.json').read_text())
        for row in data:
            if row['status'] != 'transcribed' or not row.get('lean'):
                errors.append(f'{group}/{row["id"]}: missing transcription or mapping')
            if not 1 <= row['pdf_page'] <= source['pdf_pages']:
                errors.append(f'{group}/{row["id"]}: invalid source page')
            if group == 'items' and not row.get('source_excerpt'):
                errors.append(f'{group}/{row["id"]}: missing original text')
    for issue in issues:
        if issue['status'] != 'recorded_for_proof_review' or not issue.get('transcription_handling'):
            errors.append(f'{issue["id"]}: handling of the original text is not recorded')
    modules = json.loads((ROOT / 'audit/modules.json').read_text())
    if {r['file'] for r in modules} != {str(p.relative_to(ROOT)) for p in files}:
        errors.append('Reverse source mapping does not cover every Lean module.')
    if any(not r.get('source') or not r.get('role') for r in modules):
        errors.append('A module has no recorded source or implementation role.')
    if source['status'] != 'transcription_complete':
        errors.append('Transcription coverage has not been completed.')
    if source.get('mathematical_validation') != 'pending':
        errors.append('This statement-only check must not certify mathematical validity.')
if errors:
    for error in errors:
        print('ERROR: ' + error)
    raise SystemExit(1)
print('Structural checks passed. This is NOT a certification of source fidelity.')
