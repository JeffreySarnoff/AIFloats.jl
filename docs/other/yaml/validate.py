#!/usr/bin/env python3
"""Check artifacts and execute the existing Maude suites on both restorations."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

import realize as r


def run(*args):
    subprocess.run([sys.executable, '-B', *map(str, args)], check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--engine', default='maude')
    args = parser.parse_args()
    run(r.ROOT / 'realize.py', 'check')
    run('-m', 'unittest', 'discover', '-s', r.ROOT / 'tests', '-v')
    for fmt in ('yaml', 'json'):
        with tempfile.TemporaryDirectory(prefix=f'maude-{fmt}-') as temporary:
            target = Path(temporary)
            run(r.ROOT / 'realize.py', 'restore', '--format', fmt, '--output', target)
            expected = {p.relative_to(r.SOURCE) for p in r.source_paths(r.SOURCE)}
            actual = {p.relative_to(target) for p in target.rglob('*') if p.is_file()}
            if actual != expected:
                raise ValueError('Restored coverage differs')
            for path in expected:
                if (target / path).read_bytes() != (r.SOURCE / path).read_bytes():
                    raise ValueError(f'Restored bytes differ: {path}')
            # Reuse the original independent test harness against restored inputs.
            # These Python programs are tooling, not part of the serialized spec.
            shutil.copytree(r.SOURCE / 'tools', target / 'tools',
                            ignore=shutil.ignore_patterns('__pycache__'))
            print(f'Validating {fmt} restoration with {args.engine}', flush=True)
            run(target / 'tools/check-loads.py', '--engine', args.engine)
            for suite in ('core', 'symbolic'):
                run(target / 'tools/run-tests.py', '--suite', suite, '--engine', args.engine)
    print('PASS: both serializations reconstruct and execute the specification.')


if __name__ == '__main__':
    main()
