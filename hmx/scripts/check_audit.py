#!/usr/bin/env python3
"""Check coverage and freshness of source-comparison records, not mathematical truth."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
GROUPS = ('items', 'figures', 'conventions')
PATTERN = re.compile(r'(?m)^\s*(Definition|Theorem|Lemma|Corollary|Remark|Conjecture|Example)\s+(\d+)\b')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def record_key(group, row):
    return f'{group}/{row["id"]}@{row["printed_page"]}'


def record_digest(row):
    return digest(json.dumps(row, sort_keys=True, ensure_ascii=False).encode())


def load_audit(root=ROOT):
    return {name: json.loads((root / f'audit/{name}.json').read_text())
            for name in (*GROUPS, 'source', 'ambiguities', 'modules', 'connections', 'review')}


def lean_files(root=ROOT):
    return sorted((root / 'HMX').glob('*.lean')) + [root / 'HMX.lean']


def lean_hashes(root=ROOT):
    return {str(p.relative_to(root)): digest(p.read_bytes()) for p in lean_files(root)}


def strip_comments_and_strings(text):
    """Handle nested Lean comments; keep executable tokens and ignore quoted prose."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == '/-':
                depth += 1
                i += 2
            elif pair == '-/':
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif quoted:
            if text[i] == '\\':
                i += 2
            elif text[i] == '"':
                quoted = False
                out.append(' ')
                i += 1
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif pair == '/-':
            depth = 1
            out.append(' ')
            i += 2
        elif pair == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            quoted = True
            out.append(' ')
            i += 1
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


def validate(data, pages, hashes, complete=False):
    """Pure validator; tests corrupt copies without changing audit files."""
    errors = []
    source = data['source']
    actual = []
    for page, content in enumerate(pages, 1):
        printed = page - 12
        if 8 <= printed <= 113 or 182 <= printed <= 226:
            actual.extend((m[1].lower() + m[2], page) for m in PATTERN.finditer(content))
    recorded = [(r['id'], r['pdf_page']) for r in data['items']]
    if sorted(actual) != sorted(recorded):
        errors.append('Numbered source occurrences and inventory differ.')
    issue_ids = {r['id'] for r in data['ambiguities']}
    if len(issue_ids) != len(data['ambiguities']):
        errors.append('Duplicate source issue IDs.')
    for issue in data['ambiguities']:
        if issue['status'] != 'recorded_for_proof_review' or not issue.get('transcription_handling'):
            errors.append(f'{issue["id"]}: source handling is not recorded')
    keys = set()
    for group in GROUPS:
        for row in data[group]:
            key = record_key(group, row)
            if key in keys:
                errors.append(f'{key}: duplicate record')
            keys.add(key)
            if row['status'] not in ('transcribed', 'needs_revision') or not row.get('lean'):
                errors.append(f'{key}: missing transcription or mapping')
            if row['pdf_page'] != row['printed_page'] + 12 or not 1 <= row['pdf_page'] <= source['pdf_pages']:
                errors.append(f'{key}: invalid source page')
            if group == 'items' and not row.get('source_excerpt'):
                errors.append(f'{key}: missing original text')
            if not complete:
                continue
            if row['status'] != 'transcribed':
                errors.append(f'{key}: unresolved transcription')
            if row.get('source_review_status') not in ('reviewed', 'reviewed_with_source_note'):
                errors.append(f'{key}: missing individual comparison')
            if not row.get('transcription_note') or not row.get('review_method'):
                errors.append(f'{key}: missing comparison evidence')
            locations = row.get('source_pages', [])
            if not locations or locations[0] != row['printed_page'] or any(
                    p < 1 or p + 12 > source['pdf_pages'] for p in locations):
                errors.append(f'{key}: missing/invalid reviewed pages')
            for id in row.get('source_issue_ids', []):
                if id not in issue_ids:
                    errors.append(f'{key}: unknown source issue {id}')
            if data['review'].get('reviewed_records', {}).get(key) != record_digest(row):
                errors.append(f'{key}: comparison record changed since review')
            if group == 'items' and row.get('occurrence_kind') not in ('reference', 'statement'):
                errors.append(f'{key}: unknown occurrence kind')
    modules = data['modules']
    if len(modules) != len(hashes) or {r['file'] for r in modules} != set(hashes):
        errors.append('Reverse source mapping does not cover every Lean module exactly once.')
    if any(not r.get('source') or not r.get('role') for r in modules):
        errors.append('A module has no source or implementation role.')
    if source.get('coverage_status') != 'complete':
        errors.append('Inventory coverage is incomplete.')
    if source.get('mathematical_validation') != 'pending' or source.get('proof_phase_authorized') is not False:
        errors.append('Statement-only audit must not certify mathematical validity or authorize proofs.')
    if complete:
        review = data['review']
        if source.get('source_review_status') != 'complete' or source.get('status') != 'transcribed':
            errors.append('Source comparison has not been completed.')
        for finding in review['findings']:
            if finding['status'] not in ('corrected', 'source_ambiguity_recorded'):
                errors.append(f'{finding["id"]}: unresolved transcription finding')
            if finding['status'] == 'source_ambiguity_recorded' and (
                    not finding.get('source_issue_ids') or not set(finding['source_issue_ids']) <= issue_ids):
                errors.append(f'{finding["id"]}: source ambiguity has no recorded handling')
        if review.get('lean_sha256') != hashes:
            errors.append('Lean files changed since the recorded comparison.')
        if set(review.get('reviewed_records', {})) != keys:
            errors.append('Reviewed record inventory changed.')
        used_pages = {p for group in GROUPS for r in data[group] for p in r.get('source_pages', [])}
        expected = {str(p): digest(pages[p + 11].encode()) for p in used_pages}
        if review.get('source_page_sha256') != expected:
            errors.append('Reviewed source-page snapshot changed.')
        for name in ('ambiguities', 'modules', 'connections'):
            expected = digest(json.dumps(data[name], sort_keys=True, ensure_ascii=False).encode())
            if review.get('context_sha256', {}).get(name) != expected:
                errors.append(f'{name}: source-context record changed since review')
    return errors


def check_printed_connections(output, connections):
    """Check elaborated definitions, not comments or merely declared parameters.

    The required references are an independently recorded source checklist.
    This detects a dropped application but does not certify the whole formula.
    """
    errors = []
    for row in connections:
        name = row['declaration']
        start, stop = f'BEGIN_CONNECTION {name}\n', f'END_CONNECTION {name}\n'
        if start not in output or stop not in output:
            errors.append(f'{name}: missing elaborated dependency check')
            continue
        body = output.split(start, 1)[1].split(stop, 1)[0]
        # The body, rather than the declaration's type/parameter list, must use it.
        body = body.split(':=', 1)[-1]
        for required in row['required']:
            if not re.search(r'(?<![\w.])' + re.escape(required) + r'(?![\w.])', body):
                errors.append(f'{name}: source condition {required} is not connected')
    return errors


def check_lean(data, root=ROOT):
    names = sorted({n for group in GROUPS for r in data[group] for n in r.get('lean', [])})
    generated = root / '.lake/audit/Statements.lean'
    generated.parent.mkdir(parents=True, exist_ok=True)
    targets = ['HMX.Statement.' + n for n in ('theorem7', 'theorem16', 'theorem17', 'corollary7')]
    connections = data['connections']
    printed = ['set_option pp.fullNames true', 'set_option pp.fieldNotation false']
    for row in connections:
        name = row['declaration']
        printed += [f'#eval IO.println "BEGIN_CONNECTION {name}"', f'#print {name}',
                    f'#eval IO.println "END_CONNECTION {name}"']
    generated.write_text('import HMX\n\n' + '\n'.join('#check ' + n for n in names) + '\n' +
                         '\n'.join('#print axioms ' + n for n in targets) + '\n' + '\n'.join(printed) + '\n')
    result = subprocess.run(['lake', 'env', 'lean', str(generated)], cwd=root, text=True, capture_output=True)
    (root / '.lake/audit/lean-checks.log').write_text(result.stdout + result.stderr)
    errors = []
    if result.returncode:
        diagnostics = '\n'.join(line for line in (result.stdout + result.stderr).splitlines()
                                if 'error:' in line or 'warning:' in line)
        errors.append('A mapped declaration did not elaborate (see .lake/audit/lean-checks.log):\n' + diagnostics)
    if 'sorryAx' in result.stdout:
        errors.append('A checked statement depends on sorryAx.')
    errors += check_printed_connections(result.stdout, connections)
    print(f'Mapped Lean declarations checked: {len(names)}; log: .lake/audit/lean-checks.log')
    for line in result.stdout.splitlines():
        if 'depends on axioms' in line:
            print(line)
    print(f'Source-condition connections checked in elaborated bodies: {len(connections)}')
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--require-complete', action='store_true', help='Require current individual source comparisons.')
    parser.add_argument('--require-coverage', action='store_true', help='Permit recorded transcription defects; check coverage.')
    parser.add_argument('--lean-checks', action='store_true')
    args = parser.parse_args()
    data = load_audit()
    pdf = ROOT / data['source']['file']
    errors = []
    if digest(pdf.read_bytes()) != data['source']['sha256']:
        errors.append('The fixed source PDF has changed.')
    pages = subprocess.check_output(['pdftotext', '-layout', str(pdf), '-'], text=True).split('\f')
    errors += validate(data, pages, lean_hashes(), complete=args.require_complete)
    for path in lean_files():
        code = strip_comments_and_strings(path.read_text())
        if re.search(r'\b(sorry|admit|axiom|theorem|lemma)\b', code):
            errors.append(f'{path.relative_to(ROOT)}: proof/axiom token in statement-only phase')
        for imp in re.findall(r'^import\s+(\S+)', code, re.M):
            if not (imp == 'HMX' or imp.startswith('HMX.') or imp.startswith('Mathlib.')):
                errors.append(f'{path.relative_to(ROOT)}: unexpected import {imp}')
    if args.lean_checks:
        errors += check_lean(data)
    items = data['items']
    print(f'Numbered inventory: {len(items)} occurrences, {len({r["id"] for r in items})} distinct IDs; '
          f'{sum(r.get("occurrence_kind") == "reference" for r in items)} references')
    print(f'Figures: {len(data["figures"])}; conventions: {len(data["conventions"])}; Lean modules: {len(lean_files())}')
    print('Mathematical validation: pending; proofs added: no')
    for error in errors:
        print('ERROR: ' + error)
    if errors:
        return 1
    print('Coverage and recorded-comparison checks passed.' if args.require_complete else 'Coverage checks passed.')
    print('These checks do not prove fidelity, interpretation correctness, or theorem validity.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
