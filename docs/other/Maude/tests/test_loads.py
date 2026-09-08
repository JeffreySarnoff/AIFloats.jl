"""Regression checks for loader coverage and diagnostic-sensitive validation."""
import importlib.util
import pathlib
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('check_loads', ROOT / 'tools/check-loads.py')
loads = importlib.util.module_from_spec(spec)
spec.loader.exec_module(loads)


class LoadChecks(unittest.TestCase):
    def test_shared_loaders_include_core(self):
        for loader in loads.LOADERS:
            with self.subTest(loader=loader):
                modules = loads.reachable(ROOT / loader)
                self.assertIn('P3109-CORE', modules)
                self.assertIn('P3109-CODEC', modules)
                self.assertEqual(len(modules), len(set(modules)))

    def test_shared_dependencies_and_nonexecutable_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / 'base.maude').write_text('fmod P3109-BASE is\nendfm\n')
            (root / 'left.maude').write_text('sload base.maude\n')
            (root / 'right.maude').write_text('sload base.maude\n')
            (root / 'main.maude').write_text(
                'load left.maude\nsload right.maude\n'
                'fth P3109-CONTRACT is\nendfth\n'
                'fmod P3109-BRIDGE{B :: P3109-CONTRACT} is\nendfm\n'
                'fmod P3109-MAIN is\nendfm\n'
            )
            self.assertEqual(
                loads.reachable(root / 'main.maude'),
                ['P3109-BASE', 'P3109-MAIN'],
            )

    def test_multiline_result(self):
        output = 'result XReal: exprSqrt(\n    fin(2))\nBye.\n'
        proc = subprocess.CompletedProcess([], 0, stdout=output, stderr='')
        with patch.object(loads.subprocess, 'run', return_value=proc):
            loads.check('red exprSqrt(fin(2)) .', ['exprSqrt( fin(2))'], 'maude')

    def test_rejects_incomplete_or_unclean_results(self):
        success = 'result Bool: true\nBye.\n'
        for stdout, stderr, code in [
            ('Bye.\n', '', 0),
            ('result Bool: false\nBye.\n', '', 0),
            ('result Bool: true\n', '', 0),
            ('result Bool: true\n===\n' + success, '', 0),
            (success, 'Warning: bad input', 0),
            (success, 'Advisory: redefined module', 0),
            (success, 'Error: failed to load', 0),
            (success, '', 1),
        ]:
            with self.subTest(stdout=stdout, stderr=stderr, code=code):
                proc = subprocess.CompletedProcess([], code, stdout=stdout, stderr=stderr)
                with patch.object(loads.subprocess, 'run', return_value=proc):
                    with self.assertRaises(RuntimeError):
                        loads.check('red true .', ['true'], 'maude')


if __name__ == '__main__':
    unittest.main()
