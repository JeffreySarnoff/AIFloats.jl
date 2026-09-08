#!/usr/bin/env python3
"""Check operation declarations, generated schemas, equation labels and trace links."""
import argparse,csv,hashlib,json,pathlib,re,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]

def main():
    data=json.loads((ROOT/'inventory/operations.json').read_text());ops=data['operations'];errors=[]
    files=[p for folder in ['lib','symbolic','contracts'] for p in (ROOT/folder).glob('*.maude')]
    text='\n'.join(p.read_text() for p in files)
    declarations=set()
    for names in re.findall(r'\bops?\s+([^:\n]+)\s*:',text):declarations.update(names.split())
    labels=[]
    for p in files:
        body=p.read_text()
        labels+=re.findall(r'\b(?:eq|ceq|mb|cmb)\s+\[([^]]+)\]',body)
        for line in body.splitlines():
            if re.match(r'\s*(?:eq|ceq|mb|cmb)\s',line):
                if not re.match(r'\s*(?:eq|ceq|mb|cmb)\s+\[p3109-',line):errors.append(f'Unlabelled statement in {p}')
                if 'metadata "clause=' not in line or 'page=' not in line:errors.append(f'Missing source metadata in {p}')
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
    print(f'PASS inventory: {len(ops)} operations, {len(labels)} labelled statements, {len(rows)} trace rows.')
    print('Required §4.5 identities for |FX|=1,2,3: 341, 443, 549; external implementation obligations remain pending.')
if __name__=='__main__':main()
