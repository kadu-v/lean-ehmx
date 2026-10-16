"""Check that incomplete or stale comparisons cannot pass as complete."""
import copy
import subprocess
import unittest
import check_audit as audit


class AuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = audit.load_audit()
        cls.hashes = audit.lean_hashes()
        pdf = audit.ROOT / cls.original['source']['file']
        cls.pages = subprocess.check_output(['pdftotext', '-layout', str(pdf), '-'], text=True).split('\f')

    def setUp(self):
        self.data = copy.deepcopy(self.original)

    def errors(self, complete=True, hashes=None):
        return audit.validate(self.data, self.pages, self.hashes if hashes is None else hashes, complete)

    def test_current_records_and_documented_source_ambiguities_pass(self):
        self.assertEqual([], self.errors())

    def test_missing_numbered_occurrence_fails(self):
        self.data['items'].pop()
        self.assertTrue(any('inventory' in e for e in self.errors()))

    def test_missing_example_fails_even_coverage(self):
        self.data['items'] = [r for r in self.data['items'] if r['id'] != 'example3']
        self.assertTrue(any('inventory' in e for e in self.errors(False)))

    def test_example_reference_is_included_separately(self):
        entries = [r for r in self.data['items'] if r['id'] == 'example17']
        self.assertEqual({'statement', 'reference'}, {r['occurrence_kind'] for r in entries})

    def test_parameter_or_comment_is_not_a_connected_assumption(self):
        rows = [{'declaration': 'HMX.Statement.theorem12', 'required': ['HMX.Normalizer.Effective']}]
        printed = ('BEGIN_CONNECTION HMX.Statement.theorem12\n'
                   'def HMX.Statement.theorem12 (unused : HMX.Normalizer.Effective) : Prop := True\n'
                   'END_CONNECTION HMX.Statement.theorem12\n')
        self.assertTrue(audit.check_printed_connections(printed, rows))
        printed = printed.replace(':= True', ':= HMX.Normalizer.Effective coding normalize → conclusion')
        self.assertEqual([], audit.check_printed_connections(printed, rows))

    def test_changed_connection_checklist_invalidates_review(self):
        self.data['connections'].pop()
        self.assertTrue(any('connections: source-context' in e for e in self.errors()))

    def test_missing_figure_or_convention_fails(self):
        for group in ('figures', 'conventions'):
            with self.subTest(group=group):
                self.data = copy.deepcopy(self.original)
                self.data[group].pop()
                self.assertTrue(self.errors())

    def test_missing_mapping_fails_even_coverage(self):
        self.data['items'][0]['lean'] = []
        self.assertTrue(any('mapping' in e for e in self.errors(False)))

    def test_unresolved_defect_cannot_pass_complete(self):
        self.data['items'][0]['status'] = 'needs_revision'
        self.assertEqual([], self.errors(False))
        self.assertTrue(any('unresolved transcription' in e for e in self.errors()))

    def test_unreviewed_or_unexplained_record_fails(self):
        for field in ('source_review_status', 'transcription_note', 'source_pages', 'review_method'):
            with self.subTest(field=field):
                self.data = copy.deepcopy(self.original)
                self.data['items'][0].pop(field)
                self.assertTrue(self.errors())

    def test_changed_lean_file_invalidates_review(self):
        hashes = dict(self.hashes)
        hashes['HMX/Semantics.lean'] = 'changed'
        self.assertTrue(any('Lean files changed' in e for e in self.errors(hashes=hashes)))

    def test_changed_mapping_invalidates_review(self):
        self.data['items'][0]['lean'] = ['HMX.Statement.theorem5']
        self.assertTrue(any('record changed' in e for e in self.errors()))

    def test_unresolved_finding_fails(self):
        self.data['review']['findings'][0]['status'] = 'needs_revision'
        self.assertTrue(any('unresolved transcription finding' in e for e in self.errors()))

    def test_changed_source_handling_fails(self):
        self.data['ambiguities'][0]['current_action'] = 'changed'
        self.assertTrue(any('source-context record changed' in e for e in self.errors()))

    def test_comment_scanner_handles_nesting_and_strings(self):
        code = audit.strip_comments_and_strings('/- outer /- theorem -/ sorry -/\ndef x := "axiom" -- admit\naxiom y : Prop')
        self.assertNotIn('sorry', code)
        self.assertNotIn('theorem', code)
        self.assertEqual(1, code.count('axiom'))


if __name__ == '__main__':
    unittest.main()
