"""Independent bounded regressions for partitions, arity metadata, and ordering."""
import itertools
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]


def code_sequence(values):
    term = 'cnil'
    for value in reversed(values):
        term = f'ccons({value}, {term})'
    return term


def fixtures(suite, decode):
    if suite == 'conformance':
        # Frozen handwritten tables, not expectations derived from the generator.
        tables = json.loads((ROOT / 'tests/vectors/arity-tables.json').read_text())['tables']
        names = sorted({name for entries in tables.values() for name, _ in entries})
        names += ['', 'unknown', 'add', 'ScaledCompareEqual', 'BlockClass']
        for table, entries in tables.items():
            expected = {tuple(entry) for entry in entries}
            predicate = table.removesuffix('Table')
            for name, arity in itertools.product(names, range(10)):
                answer = str((name, arity) in expected).lower()
                yield f'arity-{predicate}-{name}-{arity}', f'{predicate}({json.dumps(name)}, {arity}) == {answer}'

        # Include empty sequences, duplicate elements, differing order, and overlap.
        sequences = [values for size in range(3) for values in itertools.product([-1, 0, 1], repeat=size)]
        for index, (universe, left, right) in enumerate(itertools.product(sequences, repeat=3)):
            answer = (
                all(len(values) == len(set(values)) for values in (universe, left, right))
                and set(left).isdisjoint(right)
                and set(universe) == set(left) | set(right)
            )
            arguments = ', '.join(code_sequence(values) for values in (universe, left, right))
            yield f'partition2-exhaustive-{index}', f'partition2({arguments}) == {str(answer).lower()}'

    if suite == 'order-next':
        # Every code of all fourteen valid four-bit formats, including unsigned endpoints.
        for signedness, domain in itertools.product(['Signed', 'Unsigned'], ['Finite', 'Extended']):
            for precision in range(1, 4 if signedness == 'Signed' else 5):
                fmt = f'Binary(4, {precision}, {signedness}, {domain})'
                values = [decode(4, precision, signedness, domain, code) for code in range(16)]
                nan = values.index('nan')
                def key(code):
                    value = values[code]
                    if value == 'nan': return (0, 0)
                    if value == 'negInf': return (1, 0)
                    if value == 'posInf': return (3, 0)
                    return (2, value)
                ordered = sorted(range(16), key=key)
                rank = {code: index for index, code in enumerate(ordered)}
                numeric = ordered[1:]
                for left, right in itertools.product(range(16), repeat=2):
                    answer = str(rank[left] <= rank[right]).lower()
                    yield f'order4-{fmt}-{left}-{right}', f'TotalOrder({fmt}, {fmt}, {left}, {right}) == {answer}'
                for operation, offset in [('NextGreaterThan', 1), ('NextLessThan', -1)]:
                    for code in range(16):
                        index = numeric.index(code) + offset if code != nan else -1
                        answer = numeric[index] if 0 <= index < len(numeric) else nan
                        yield f'next4-{operation}-{fmt}-{code}', f'{operation}({fmt}, {code}) == {answer}'

    if suite == 'domains':
        valid = 'Binary(4, 2, Signed, Finite)'
        for fmt, code in [(valid, -1), (valid, 16), ('Binary(2, 1, Signed, Finite)', 0), ('binary32', 0)]:
            for operation in ['NextGreaterThan', 'NextLessThan']:
                yield f'next-domain-{operation}-{fmt}-{code}', f'({operation}({fmt}, {code}) :: Nat) == false'
            for args in [f'{fmt}, {valid}, {code}, 0', f'{valid}, {fmt}, 0, {code}']:
                yield f'order-domain-{args}', f'(TotalOrder({args}) :: Bool) == false'
