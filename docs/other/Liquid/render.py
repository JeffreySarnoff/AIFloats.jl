"""Render the Maude templates, checking existing sources by default."""
import argparse
from pathlib import Path

from liquid import Environment, FileSystemLoader, StrictUndefined

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true', help='compare with ../Maude (default)')
    mode.add_argument('--output-dir', type=Path, help='write generated files under this directory')
    args = parser.parse_args()
    environment = Environment(
        loader=FileSystemLoader(ROOT, ext='.liquid'), undefined=StrictUndefined,
    )
    # Only *.maude.liquid files are entry points; shared partials are loaded on demand.
    templates = sorted(ROOT.rglob('*.maude.liquid'))
    sources = ROOT.parent / 'Maude'
    expected = {path.relative_to(sources) for folder in ('lib', 'symbolic', 'contracts')
                for path in (sources / folder).glob('*.maude')}
    expected.add(Path('proofs/slices/saturation-cases.maude'))
    covered = {path.relative_to(ROOT).with_suffix('') for path in templates}
    missing = expected - covered
    if missing:
        raise SystemExit('Missing Maude templates: ' + ', '.join(map(str, sorted(missing))))
    failures = []
    for template in templates:
        relative = template.relative_to(ROOT)
        output = relative.with_suffix('')
        rendered = environment.get_template(relative.as_posix()).render().encode('utf-8')
        if args.output_dir is not None:
            target = args.output_dir / output
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(rendered)
            print('WROTE', target)
        elif rendered != (sources / output).read_bytes():
            failures.append(str(output))
        else:
            print('PASS', output, f'({len(rendered)} bytes)')
    if failures:
        raise SystemExit('Rendered output differs: ' + ', '.join(failures))


if __name__ == '__main__':
    main()
