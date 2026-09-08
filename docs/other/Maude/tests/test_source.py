"""Validation tooling must preserve statements and reject stale generated data."""
import importlib.util
import json
import pathlib
import re
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from maude_source import format_equations, statements


def load_tool(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'tools' / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


generator = load_tool('generate-wrappers')
inventory = load_tool('check-inventory')


class SourceChecks(unittest.TestCase):
    def test_multiline_metadata_and_literals(self):
        source = '''  ceq [p3109-test] : f("a  b", X) = "a  b" if X == "c.d"
    [metadata "clause=4.3; page=19-20"] .
'''
        formatted = format_equations(source)
        self.assertEqual([], inventory.statement_errors(formatted))
        self.assertEqual(formatted, format_equations(formatted))
        self.assertIn('"a  b"', formatted)
        self.assertEqual(
            re.findall(r'"(?:\\.|[^"\\])*"|[^\s"]+', source),
            re.findall(r'"(?:\\.|[^"\\])*"|[^\s"]+', formatted),
        )

    def test_metadata_cannot_be_borrowed_from_next_statement(self):
        source = '''  eq [p3109-missing] : f(X) = X .
  eq [p3109-present] : g(X) = X
    [metadata "clause=4.3; page=19-20"] .
'''
        self.assertEqual(['Missing source metadata'], inventory.statement_errors(source))
        self.assertEqual(2, len(list(statements(source))))

    def test_unlabelled_and_unterminated_statements(self):
        self.assertIn('Unlabelled statement', inventory.statement_errors('eq f(X) = X .'))
        for source in ['eq [p3109-test] : f(X) = X', 'eq f(X) = X\neq g(X) = X .']:
            with self.subTest(source=source):
                self.assertTrue(any('Unterminated statement' in error for error in inventory.statement_errors(source)))

    def test_generated_tables_preserve_handwritten_entries(self):
        operations = json.loads((ROOT / 'inventory/operations.json').read_text())['operations']
        expected = json.loads((ROOT / 'tests/vectors/arity-tables.json').read_text())['tables']
        actual = generator.arity_entries(operations)
        self.assertEqual(expected, {name: [list(entry) for entry in entries] for name, entries in actual.items()})
        source = (ROOT / 'lib/conformance.maude').read_text()
        self.assertEqual(source, generator.generate_tables(source, operations))
        stale = source.replace('entry("ScaledConvert", 3)', 'entry("ScaledConvert", 9)', 1)
        self.assertNotEqual(source, stale)
        self.assertEqual(source, generator.generate_tables(stale, operations))
        with self.assertRaises(ValueError):
            generator.generate_tables(source.replace('BEGIN GENERATED numericArityTable', 'missing marker'), operations)


    def test_instance_exports_and_trace_labels(self):
        source = '''op scalar : Format Format ProjSpec Int ~> Nat .
ceq [p3109-template-scalar-1] : scalar(F, G, P, C) = C if validCode(F, C) .
including P3109-SCALAR-TEMPLATE1{ConvertKernel} * (
  op scalar to Convert,
  label p3109-template-scalar-1 to p3109-scalar-Convert) .
'''
        declarations, labels, errors = inventory.source_symbols(source)
        self.assertEqual([], errors)
        self.assertIn('Convert', declarations)
        self.assertEqual(['p3109-template-scalar-1', 'p3109-scalar-Convert'], labels)
        broken = source.replace('label p3109-template-scalar-1', 'label p3109-missing')
        self.assertEqual(['Undefined renamed label: p3109-missing'],
                         inventory.source_symbols(broken)[2])
        broken = source.replace('op scalar to', 'op missing to')
        self.assertEqual(['Undeclared renamed operator: missing'],
                         inventory.source_symbols(broken)[2])


if __name__ == '__main__':
    unittest.main()
