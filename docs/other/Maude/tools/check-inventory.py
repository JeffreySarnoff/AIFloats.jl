#!/usr/bin/env python3
"""Check operation declarations, generated schemas, equation labels and trace links."""
import csv,hashlib,json,pathlib,re,subprocess,sys
sys.dont_write_bytecode = True
from maude_source import statements
ROOT=pathlib.Path(__file__).resolve().parents[1]


def statement_errors(source):
    errors = []
    try:
        for statement in statements(source):
            if not re.match(r'\s*(?:eq|ceq|mb|cmb)\s+\[p3109-', statement):
                errors.append('Unlabelled statement')
            if not re.search(r'\bmetadata\s+"clause=[^"]*page=[^"]*"', statement):
                errors.append('Missing source metadata')
    except ValueError as error:
        errors.append(str(error))
    return errors

def source_symbols(source):
    """Collect declarations and the names exported by generated instance renamings."""
    declarations = set()
    for names in re.findall(r'\bops?\s+([^:\n]+)\s*:', source):
        declarations.update(names.split())
    labels = re.findall(r'\b(?:eq|ceq|mb|cmb)\s+\[([^]]+)\]', source)
    original_labels = set(labels)
    errors = []
    for kind, old, new in re.findall(r'\b(op|label)\s+([\w-]+)\s+to\s+([\w-]+)', source):
        if kind == 'op':
            if old not in declarations:
                errors.append('Undeclared renamed operator: ' + old)
            declarations.add(new)
        else:
            if old not in original_labels:
                errors.append('Undefined renamed label: ' + old)
            labels.append(new)
    return declarations, labels, errors


def main():
    data=json.loads((ROOT/'inventory/operations.json').read_text());ops=data['operations'];errors=[]
    files=[p for folder in ['lib','symbolic','contracts'] for p in (ROOT/folder).glob('*.maude')]
    text='\n'.join(p.read_text() for p in files)
    declarations,labels,symbol_errors=source_symbols(text)
    errors.extend(symbol_errors)
    for p in files:
        body=p.read_text()
        errors.extend(f'{error} in {p}' for error in statement_errors(body))
        for name in re.findall(r'\b(?:fmod|fth)\s+(\S+)',body):
            if not name.startswith('P3109-'):errors.append('Unprefixed module: '+name)
    if len(labels)!=len(set(labels)):errors.append('Duplicate equation/membership labels')
    if len(ops)!=len({o['name'] for o in ops}):errors.append('Duplicate inventory operation names')
    for o in ops:
        for field in ['name','arity','clause','pages','parameters','operands','result','block','scaled','profile','wrapper']:
            if field not in o:errors.append(f'{o["name"]}: missing {field}')
        if o['arity']!=len(o['operands']):errors.append('Operand arity mismatch: '+o['name'])
        for name in [o['name']]+(['Block'+o['name'],'Scaled'+o['name']] if o['block'] else []):
            if name not in declarations:errors.append('Missing declaration: '+name)
    rows=list(csv.DictReader((ROOT/'inventory/traceability.tsv').open(),delimiter='\t'))
    for row in rows:
        for label in row['equations'].split(','):
            if label and label not in labels:errors.append('Dangling trace label: '+label)
    for o in ops:
        if not any(r['requirement']=='operation:'+o['name'] for r in rows):errors.append('Missing operation trace: '+o['name'])
    manifest=json.loads((ROOT/'inventory/source.json').read_text())
    for source in [manifest['plan'],manifest['arithmetic_source']]:
        path=ROOT/source['path']
        if hashlib.sha256(path.read_bytes()).hexdigest()!=source['sha256']:errors.append('Source hash changed: '+source['path'])
    proc=subprocess.run([sys.executable,str(ROOT/'tools/generate-wrappers.py'),'--check'],capture_output=True,text=True)
    if proc.returncode:errors.append(proc.stdout+proc.stderr)
    if errors:sys.exit('\n'.join(errors))
    print(f'PASS inventory: {len(ops)} operations, {len(labels)} source/instance labels, {len(rows)} trace rows.')
    print('Required §4.5 identities for |FX|=1,2,3: 341, 443, 549; external implementation obligations remain pending.')
if __name__=='__main__':main()
