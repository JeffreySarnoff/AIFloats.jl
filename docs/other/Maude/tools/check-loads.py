#!/usr/bin/env python3
"""Load each profile independently and reduce every reachable concrete module."""
import argparse
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[1]
LOADERS = (
    'load-core.maude',
    'load-symbolic.maude',
    'load-contracts.maude',
    'load-spec.maude',
)
EXAMPLES = {
    'core.maude': ['6', 'fin(2)', 'ccons(4, ccons(12, cnil))'],
    'symbolic.maude': [
        'fin(3/4)', 'exprSqrt(fin(2))', 'fin(3/4)', 'negInf',
        'xEq(exprExp(fin(1)), exprExp(fin(2)))',
    ],
}


def reachable(path, seen=None):
    """Collect concrete modules once, following both load and sload directives."""
    seen = set() if seen is None else seen
    path = path.resolve()
    if path in seen:
        return []
    seen.add(path)
    source = path.read_text()
    modules = []
    for relative in re.findall(r'^(?:sload|load) (\S+)\s*$', source, re.M):
        modules.extend(reachable(path.parent / relative, seen))
    modules.extend(re.findall(r'^fmod (P3109-[^\s{]+) is\s*$', source, re.M))
    return modules


def check(commands, expected, engine):
    """Require a clean process and the complete, ordered list of result terms."""
    proc = subprocess.run(
        [engine, '-no-banner', '-no-ansi-color'],
        input=commands + '\nquit\n', cwd=ROOT,
        text=True, capture_output=True, timeout=60,
    )
    output = proc.stdout + proc.stderr
    results = re.findall(
        r'^result [^:\n]+: (.*?)\n(?=(?:=|Bye))', output, re.M | re.S,
    )
    results = [' '.join(result.split()) for result in results]
    if proc.returncode or re.search(r'Warning:|Advisory:|Error:', output) or results != expected:
        raise RuntimeError(output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--engine', default='maude')
    args = parser.parse_args()
    for loader in LOADERS:
        modules = reachable(ROOT / loader)
        commands = f'load {loader}\n' + '\n'.join(
            f'red in {module} : true .' for module in modules
        )
        check(commands, ['true'] * len(modules), args.engine)
        print(f'PASS {loader}: {len(modules)} concrete modules compile/reduce; '
              'theories and parameters are not executable targets.')
    for example, expected in EXAMPLES.items():
        check(f'load examples/{example}', expected, args.engine)
        print('PASS example ' + example)


if __name__ == '__main__':
    main()
