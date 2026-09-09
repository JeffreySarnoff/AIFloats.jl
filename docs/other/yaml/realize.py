#!/usr/bin/env python3
"""Generate, check, and restore the lossless YAML/JSON Maude realization."""
import argparse
from collections import Counter
import csv
import hashlib
import io
import json
from pathlib import Path
import re

import yaml
from jsonschema import Draft202012Validator

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / 'Maude'
VERSION = 1


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f'Duplicate key: {key}')
        result[key] = value
    return result


class StrictLoader(yaml.SafeLoader):
    pass


def yaml_mapping(loader, node):
    return unique_pairs((loader.construct_object(k), loader.construct_object(v))
                        for k, v in node.value)


StrictLoader.add_constructor('tag:yaml.org,2002:map', yaml_mapping)


class Dumper(yaml.SafeDumper):
    pass


def yaml_string(dumper, value):
    return dumper.represent_scalar('tag:yaml.org,2002:str', value,
                                   style='|' if '\n' in value else None)


Dumper.add_representer(str, yaml_string)


def decode(text, fmt):
    if fmt == 'json':
        return json.loads(text, object_pairs_hook=unique_pairs)
    return yaml.load(text, Loader=StrictLoader)


def encode(data, fmt):
    if fmt == 'json':
        return json.dumps(data, ensure_ascii=False, indent=2, allow_nan=False) + '\n'
    return yaml.dump(data, Dumper=Dumper, sort_keys=False, allow_unicode=True,
                     width=100)


def safe_path(root, relative):
    rel = Path(relative)
    if rel.is_absolute() or '..' in rel.parts or not rel.parts:
        raise ValueError(f'Unsafe path: {relative}')
    target = (root / rel).resolve()
    if not target.is_relative_to(root.resolve()):
        raise ValueError(f'Path escapes root: {relative}')
    return target


def normalized(text):
    """Normalize whitespace outside quoted strings only."""
    return re.sub(r'"(?:\\.|[^"\\])*"|\s+',
                  lambda m: m[0] if m[0].startswith('"') else ' ', text).strip()


def split_top(text, separator):
    """Split a spaced delimiter outside strings and parenthesized terms."""
    depth = 0
    quoted = escaped = False
    for i, ch in enumerate(text):
        if quoted:
            if escaped:
                escaped = False
            elif ch == '\\':
                escaped = True
            elif ch == '"':
                quoted = False
        elif ch == '"':
            quoted = True
        elif ch in '({[':
            depth += 1
        elif ch in ')}]':
            depth -= 1
        elif depth == 0 and text.startswith(separator, i):
            return text[:i], text[i + len(separator):]
    raise ValueError(f'Missing top-level {separator!r}: {text}')


def attributes(text):
    match = re.search(r' \[((?:"(?:\\.|[^"\\])*"|[^"\[\]])*)\]$', text)
    if not match:
        return text, ''
    return text[:match.start()], match[1]


def split_condition(text):
    # An axiom guard's `if` has no matching `fi`; term-level conditionals do.
    stack = []
    for match in re.finditer(r'"(?:\\.|[^"\\])*"|\b(?:if|fi)\b', text):
        if match[0] == 'if':
            stack.append(match.start())
        elif match[0] == 'fi':
            if not stack:
                raise ValueError('Unmatched fi')
            stack.pop()
    if len(stack) != 1:
        raise ValueError('Expected one axiom condition')
    index = stack[0]
    return text[:index].rstrip(), text[index + 2:].lstrip()


def fields(text):
    """Extract this tree's declaration syntax; retain terms as Maude strings."""
    s = normalized(text)
    keyword = s.split(' ', 1)[0]
    if not s:
        return 'layout', {}
    if s.startswith('---'):
        return 'comment', {}
    if keyword in ('fmod', 'fth'):
        m = re.fullmatch(r'(fmod|fth) ([^\s{]+)(?:\{(.*)\})? is', s)
        if not m:
            raise ValueError(f'Invalid module header: {s}')
        params = []
        if m[3]:
            for item in m[3].split(','):
                name, theory = item.strip().split(' :: ')
                params.append({'name': name, 'theory': theory})
        return keyword, {'name': m[2], 'parameters': params}
    if keyword == 'view':
        m = re.fullmatch(r'view (\S+) from (.+) to (.+) is', s)
        if not m:
            raise ValueError(f'Invalid view: {s}')
        return 'view', {'name': m[1], 'from': m[2], 'to': m[3]}
    if s in ('endfm', 'endfth', 'endv', 'quit'):
        return s, {}
    if keyword in ('load', 'sload'):
        return keyword, {'path': s.split(' ', 1)[1]}
    if not s.endswith(' .'):
        raise ValueError(f'Unterminated statement: {s}')
    body = s[len(keyword) + 1:-2]
    if keyword in ('including', 'protecting', 'extending'):
        return keyword, {'expression': body}
    if keyword in ('sort', 'sorts'):
        return keyword, {'names': body.split()}
    if keyword in ('subsort', 'subsorts'):
        return keyword, {'chain': [part.split() for part in body.split(' < ')]}
    if keyword in ('var', 'vars'):
        names, sort = split_top(body, ' : ')
        return keyword, {'names': names.split(), 'sort': sort}
    if keyword in ('op', 'ops'):
        if ' : ' not in body:
            before, after = split_top(body, ' to ')
            return 'op-mapping', {'from': before, 'to': after}
        signature, attrs = attributes(body)
        names, signature = split_top(signature, ' : ')
        match = re.fullmatch(r'(.*?)\s*(->|~>) (\S+)', signature)
        if not match:
            raise ValueError(f'Invalid signature: {s}')
        return keyword, {'names': names.split(), 'domain': match[1].split(),
                         'arrow': match[2], 'range': match[3], 'attributes': attrs}
    if keyword in ('eq', 'ceq', 'mb', 'cmb'):
        body, attrs = attributes(body)
        match = re.fullmatch(r'\[([^]]+)\] : (.*)', body)
        if not match:
            raise ValueError(f'Expected labelled axiom: {s}')
        label, body = match.groups()
        condition = None
        if keyword in ('ceq', 'cmb'):
            body, condition = split_condition(body)
        lhs, rhs = split_top(body, ' = ' if keyword in ('eq', 'ceq') else ' : ')
        data = {'label': label, 'lhs': lhs,
                'rhs' if keyword in ('eq', 'ceq') else 'sort': rhs,
                'condition': condition, 'attributes': attrs}
        return keyword, data
    if keyword == 'red':
        module, term = split_top(body, ' : ')
        if not module.startswith('in '):
            raise ValueError(f'Expected reduction module: {s}')
        return keyword, {'module': module[3:], 'term': term}
    if keyword == 'set' and body in ('include BOOL off', 'include BOOL on'):
        return keyword, {'option': 'include BOOL', 'value': body.split()[-1]}
    raise ValueError(f'Unsupported syntax: {s}')


def records(text):
    result, pending, opened = [], '', None
    line_number = 1
    for line in text.splitlines(keepends=True):
        if not pending:
            start = line_number
        pending += line
        stripped = pending.strip()
        first = stripped.split(' ', 1)[0]
        immediate = (not stripped or stripped.startswith('---') or
                     first in ('load', 'sload', 'fmod', 'fth', 'view',
                               'endfm', 'endfth', 'endv', 'quit'))
        if immediate or stripped.endswith(' .'):
            kind, data = fields(pending)
            if kind in ('fmod', 'fth', 'view'):
                if opened:
                    raise ValueError('Nested module/view')
                opened = {'fmod': 'endfm', 'fth': 'endfth', 'view': 'endv'}[kind]
            elif kind in ('endfm', 'endfth', 'endv'):
                if kind != opened:
                    raise ValueError('Mismatched module/view end')
                opened = None
            result.append({'line': start, 'kind': kind, 'fields': data, 'text': pending})
            pending = ''
        line_number += line.count('\n')
    if pending or opened:
        raise ValueError('Unterminated source')
    return result


def support_data(text, suffix):
    if suffix == '.json':
        return decode(text, 'json')
    rows = list(csv.reader(io.StringIO(text), delimiter='\t'))
    if not rows or any(len(row) != len(rows[0]) for row in rows):
        raise ValueError('Ragged TSV')
    # Keep literal headers: obligations.tsv currently has leading spaces in id.
    return {'columns': rows[0], 'rows': rows[1:]}


def document(path, source):
    raw = path.read_bytes()
    text = raw.decode('utf-8')
    doc = {'version': VERSION, 'path': path.relative_to(source).as_posix(),
           'sha256': digest(raw)}
    if path.suffix == '.maude':
        doc.update(type='maude', records=records(text))
    else:
        doc.update(type='support', format=path.suffix[1:], text=text,
                   data=support_data(text, path.suffix))
    return doc


def restore(doc):
    """Validate fields against text before reconstructing any source bytes."""
    Draft202012Validator(schema()).validate(doc)
    if doc['version'] != VERSION:
        raise ValueError('Unsupported version')
    if doc['type'] == 'maude':
        text = ''.join(record['text'] for record in doc['records'])
        if records(text) != doc['records']:
            raise ValueError(f"Inconsistent structured records: {doc['path']}")
    elif doc['type'] == 'support':
        text = doc['text']
        if support_data(text, '.' + doc['format']) != doc['data']:
            raise ValueError(f"Inconsistent support data: {doc['path']}")
    else:
        raise ValueError('Unknown document type')
    raw = text.encode('utf-8')
    if digest(raw) != doc['sha256']:
        raise ValueError(f"Hash mismatch: {doc['path']}")
    return raw


def source_paths(source):
    paths = set(source.rglob('*.maude'))
    for folder in ('inventory', 'proofs', 'tests/vectors'):
        paths.update(p for p in (source / folder).rglob('*')
                     if p.suffix in ('.json', '.tsv'))
    return sorted(paths)


def catalog(documents):
    modules, loads, kinds = {}, {}, Counter()
    paths = {doc['path'] for doc in documents}
    entries = []
    for doc in documents:
        path = doc['path']
        entries.append({'path': path, 'type': doc['type'], 'sha256': doc['sha256']})
        for record in doc.get('records', []):
            kind, data = record['kind'], record['fields']
            kinds[kind] += 1
            if kind in ('fmod', 'fth', 'view'):
                if data['name'] in modules:
                    raise ValueError(f"Duplicate module/view: {data['name']}")
                modules[data['name']] = {'path': path, 'line': record['line'], 'kind': kind}
            if kind in ('load', 'sload'):
                target = (SOURCE / Path(path).parent / data['path']).resolve()
                if not target.is_relative_to(SOURCE.resolve()):
                    raise ValueError(f'External load: {target}')
                relative = target.relative_to(SOURCE.resolve()).as_posix()
                if relative not in paths:
                    raise ValueError(f'Missing load: {relative}')
                loads.setdefault(path, []).append({'kind': kind, 'path': relative})
    references = {}
    for doc in documents:
        for record in doc.get('records', []):
            kind, data = record['kind'], record['fields']
            terms = []
            if kind in ('including', 'protecting', 'extending'):
                terms = [data['expression']]
            elif kind in ('fmod', 'fth'):
                terms = [p['theory'] for p in data['parameters']]
            elif kind == 'view':
                terms = [data['from'], data['to']]
            elif kind == 'red':
                terms = [data['module']]
            for term in terms:
                for name in re.findall(r'\bP3109-[A-Z0-9-]+\b', term):
                    if name not in modules:
                        raise ValueError(f'Unresolved definition: {name}')
                references.setdefault(doc['path'], []).append(term)
    return {'version': VERSION, 'source': '../Maude', 'files': entries,
            'definitions': modules, 'loads': loads, 'references': references,
            'record_counts': dict(sorted(kinds.items()))}


def schema():
    string = {'type': 'string'}
    strings = {'type': 'array', 'items': string}
    def obj(props):
        return {'type': 'object', 'additionalProperties': False,
                'required': list(props), 'properties': props}
    by_kind = {}
    def group(kinds, props):
        for kind in kinds.split():
            by_kind[kind] = obj(props)
    group('layout comment endfm endfth endv quit', {})
    group('fmod fth', {'name': string, 'parameters': {'type': 'array',
          'items': obj({'name': string, 'theory': string})}})
    group('view', {'name': string, 'from': string, 'to': string})
    group('load sload', {'path': string})
    group('including protecting extending', {'expression': string})
    group('sort sorts', {'names': strings})
    group('subsort subsorts', {'chain': {'type': 'array', 'items': strings}})
    group('var vars', {'names': strings, 'sort': string})
    group('op ops', {'names': strings, 'domain': strings,
          'arrow': {'enum': ['->', '~>']}, 'range': string, 'attributes': string})
    group('op-mapping', {'from': string, 'to': string})
    for kind in ('eq', 'ceq', 'mb', 'cmb'):
        group(kind, {'label': string, 'lhs': string,
              'rhs' if kind in ('eq', 'ceq') else 'sort': string,
              'condition': string if kind in ('ceq', 'cmb') else {'type': 'null'},
              'attributes': string})
    group('red', {'module': string, 'term': string})
    group('set', {'option': {'const': 'include BOOL'}, 'value': {'enum': ['on', 'off']}})
    record = {'type': 'object', 'additionalProperties': False,
              'required': ['line', 'kind', 'fields', 'text'], 'properties': {
                  'line': {'type': 'integer', 'minimum': 1},
                  'kind': {'enum': ['layout', 'comment', 'fmod', 'fth', 'view',
                      'endfm', 'endfth', 'endv', 'quit', 'load', 'sload', 'including',
                      'protecting', 'extending', 'sort', 'sorts', 'subsort', 'subsorts',
                      'var', 'vars', 'op', 'ops', 'op-mapping', 'eq', 'ceq', 'mb', 'cmb',
                  'red', 'set']}, 'fields': {'type': 'object'}, 'text': string}}
    record['allOf'] = [
        {'if': {'properties': {'kind': {'const': kind}}},
         'then': {'properties': {'fields': field_schema}}}
        for kind, field_schema in by_kind.items()]
    common = {'version': {'const': VERSION}, 'path': {'type': 'string',
              'pattern': r'^(?!/)(?!.*(?:^|/)\.\.(?:/|$)).+$'},
              'sha256': {'type': 'string', 'pattern': '^[0-9a-f]{64}$'}}
    def variant(kind, extra):
        props = dict(common, type={'const': kind}, **extra)
        return {'type': 'object', 'additionalProperties': False,
                'required': list(props), 'properties': props}
    return {'$schema': 'https://json-schema.org/draft/2020-12/schema',
            'title': 'Lossless P3109 Maude source document',
            'description': 'Structural schema; realize.py also checks text/field agreement.',
            'oneOf': [variant('maude', {'records': {'type': 'array', 'items': record}}),
                      variant('support', {'format': {'enum': ['json', 'tsv']},
                                          'text': string, 'data': {}})]}


def build(source):
    for name in ('load-core.maude', 'load-symbolic.maude', 'load-contracts.maude', 'load-spec.maude'):
        if not (source / name).is_file():
            raise ValueError(f'Missing specification loader: {name}')
    docs = [document(path, source) for path in source_paths(source)]
    for doc in docs:
        if restore(doc) != safe_path(source, doc['path']).read_bytes():
            raise ValueError('Round-trip failed')
    result = {'manifest': catalog(docs), 'schema': schema()}
    result.update({'sources/' + doc['path']: doc for doc in docs})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['generate', 'check', 'restore'])
    parser.add_argument('--source', type=Path, default=SOURCE)
    parser.add_argument('--artifacts', type=Path, default=ROOT)
    parser.add_argument('--format', choices=['yaml', 'json'], default='yaml')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.command == 'restore':
        if args.output is None:
            parser.error('restore requires --output (a new or empty directory)')
        if args.output.exists() and any(args.output.iterdir()):
            parser.error('restore output must be empty')
        manifest = decode((args.artifacts / ('manifest.' + args.format)).read_text(), args.format)
        pending, documents = {}, []
        for entry in manifest['files']:
            path = entry['path']
            artifact = safe_path(args.artifacts, 'sources/' + path + '.' + args.format)
            doc = decode(artifact.read_text(), args.format)
            if {k: doc[k] for k in ('path', 'type', 'sha256')} != entry:
                raise ValueError('Manifest disagreement')
            target = safe_path(args.output, path)
            if target in pending:
                raise ValueError('Duplicate output path')
            pending[target] = restore(doc)
            documents.append(doc)
        if catalog(documents) != manifest:
            raise ValueError('Inconsistent manifest')
        for target, raw in pending.items():
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
        print(f'Restored {len(pending)} files from {args.format}.')
        return
    expected = build(args.source)
    names = {name + '.' + fmt for name in expected for fmt in ('yaml', 'json')}
    present = {p.relative_to(args.artifacts).as_posix()
               for p in (args.artifacts / 'sources').rglob('*')
               if p.is_file()}
    stale = present - names
    if stale:
        raise ValueError(f'Unexpected artifacts (remove explicitly): {sorted(stale)}')
    for name, data in expected.items():
        for fmt in ('yaml', 'json'):
            path = safe_path(args.artifacts, name + '.' + fmt)
            rendered = encode(data, fmt)
            if decode(rendered, fmt) != data:
                raise ValueError(f'Serialization failed: {path}')
            if args.command == 'generate':
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(rendered, encoding='utf-8')
            elif not path.exists() or path.read_bytes() != rendered.encode('utf-8'):
                raise ValueError(f'Missing or stale artifact: {path}')
    print(f'{args.command}: {len(expected) - 2} source documents; YAML/JSON agree; '
          'source bytes and structured fields verified.')


if __name__ == '__main__':
    main()
