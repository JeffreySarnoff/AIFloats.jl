"""Representation fidelity and rejection tests; numeric semantics stay in Maude."""
import copy
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import realize as r


class RealizationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.documents = [r.document(p, r.SOURCE) for p in r.source_paths(r.SOURCE)]

    def test_all_sources_and_formats(self):
        for doc in self.documents:
            with self.subTest(path=doc['path']):
                raw = (r.SOURCE / doc['path']).read_bytes()
                for fmt in ('yaml', 'json'):
                    self.assertEqual(r.restore(r.decode(r.encode(doc, fmt), fmt)), raw)

    def test_corrupt_text_and_fields_rejected(self):
        original = next(d for d in self.documents if d['path'] == 'lib/rounding.maude')
        doc = copy.deepcopy(original)
        axiom = next(a for a in doc['records'] if a['kind'] == 'ceq')
        axiom['fields']['rhs'] = 'deliberatelyChangedResult'
        with self.assertRaises(ValueError):
            r.restore(doc)
        doc = copy.deepcopy(original)
        doc['records'][0]['text'] += '\n'
        with self.assertRaises(ValueError):
            r.restore(doc)

    def test_unknown_and_unterminated_syntax(self):
        for source in ('rl a => b .\n', 'fmod X is\n', 'eq [x] : a = b\n',
                       'fmod X is\nendv\n'):
            with self.subTest(source=source), self.assertRaises(ValueError):
                r.records(source)

    def test_quoted_terms_attributes_and_conditional_terms(self):
        kind, data = r.fields('ceq [x] : f("a = b if c .") = if p then 1/3 else 2/7 fi '
                              'if q [metadata "clause=1; 2; page=3" nonexec] .\n')
        self.assertEqual(kind, 'ceq')
        self.assertEqual(data['lhs'], 'f("a = b if c .")')
        self.assertEqual(data['rhs'], 'if p then 1/3 else 2/7 fi')
        self.assertEqual(data['condition'], 'q')
        self.assertEqual(data['attributes'], 'metadata "clause=1; 2; page=3" nonexec')

    def test_partial_signature_and_membership(self):
        self.assertEqual(r.fields('op inverse : Real ~> Real .')[1]['arrow'], '~>')
        data = r.fields('cmb [x] : f(A) : Real if valid(A) .')[1]
        self.assertEqual(data['sort'], 'Real')
        self.assertEqual(data['condition'], 'valid(A)')

    def test_duplicate_keys(self):
        for fmt, text in [('json', '{"a":1,"a":2}'), ('yaml', 'a: 1\na: 2\n')]:
            with self.assertRaises(ValueError):
                r.decode(text, fmt)

    def test_unsafe_paths(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            for path in ('../escape', '/tmp/escape', 'a/../../escape'):
                with self.assertRaises(ValueError):
                    r.safe_path(root, path)
            (root / 'link').symlink_to('/tmp', target_is_directory=True)
            with self.assertRaises(ValueError):
                r.safe_path(root, 'link/escape')

    def test_broken_load_reference(self):
        docs = copy.deepcopy(self.documents)
        doc = next(d for d in docs if d['path'] == 'load-core.maude')
        doc['records'][0]['fields']['path'] = 'missing.maude'
        with self.assertRaises(ValueError):
            r.catalog(docs)

    def test_tsv_literal_headers_and_line_endings(self):
        raw = '    id\tstatus\r\nx\topen\r\n'
        self.assertEqual(r.support_data(raw, '.tsv'),
                         {'columns': ['    id', 'status'], 'rows': [['x', 'open']]})


if __name__ == '__main__':
    unittest.main()
