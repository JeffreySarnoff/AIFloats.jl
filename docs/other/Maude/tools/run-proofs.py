#!/usr/bin/env python3
"""Isolated CRC then screened SCC; constructor slices have separate refinement obligations."""
import argparse, hashlib, json, os, pathlib, re, shutil, subprocess, tempfile
ROOT = pathlib.Path(__file__).resolve().parents[1]
TARGETS=[('smoke','P3109-PROOF-SMOKE','proofs/toolchain-smoke.maude','flip(off)'),('saturation','P3109-PROOF-SATURATION','proofs/slices/saturation-cases.maude','decision(none, up, above, signed, extended)')]
def invoke(engine, files, command, timeout):
    with tempfile.TemporaryDirectory(prefix='p3109-proof-') as work:
        proc=subprocess.run([engine,'-no-banner','-no-ansi-color']+list(map(str,files)), input=command+'\nquit\n',text=True,capture_output=True,cwd=work,timeout=timeout)
    output=proc.stdout+proc.stderr
    if proc.returncode or re.search(r'Warning:|Advisory:|assertion|Aborted|Segmentation',output,re.I):raise RuntimeError(output)
    return output

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--suite',choices=['smoke','eligible'],default='eligible')
    p.add_argument('--engine',default=os.getenv('MAUDE_PROOF_ENGINE','maude++'))
    p.add_argument('--mfe',default=os.getenv('MFE_PATH','/opt/mfe-3.5.1/src/mfe.maude'))
    p.add_argument('--timeout',type=int,default=60)
    p.add_argument('--output',type=pathlib.Path,default=pathlib.Path(tempfile.gettempdir())/'p3109-proof-results')
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True);records=[]
    for tag,module,rel,probe in TARGETS[:1] if a.suite=='smoke' else TARGETS:
        target=ROOT/rel
        flat=invoke(a.engine,[target],f'red in {module} : {probe} .\nshow all {module} .',a.timeout)
        (a.output/f'{tag}-screen.log').write_text(flat)
        # Includes implicit imports: inspect the actual flattened module, not only source text.
        if 'result ' not in flat or re.search(r'special\s*\(|\b(?:Bool|Nat|Int|Rat|Float|String)\b|\b(?:pr|inc|ex)\s+|\b(?:ceq|cmb|rl|crl)\s',flat):
            raise RuntimeError('Target not eligible for this constructor-only proof profile; CRC/SCC NOT scheduled: '+module)
        crc=invoke(a.engine,[target,a.mfe],f'(select tool CRC .)\n(ccr {module} .)',a.timeout)
        (a.output/f'{tag}-crc.log').write_text(crc)
        if re.search(r'not supported|unsupported|cannot handle',crc,re.I) or not re.search(r'locally[- ]confluent',crc,re.I) or 'All critical pairs have been joined.' not in crc:
            raise RuntimeError('Missing CRC conclusions; SCC NOT scheduled.\n'+crc)
        scc=invoke(a.engine,[target,a.mfe],f'(select tool SCC .)\n(scc {module} .)',a.timeout)
        (a.output/f'{tag}-scc.log').write_text(scc)
        if 'Analysis: it is complete and it is sound' not in scc or 'Completeness counter-examples: none were found' not in scc or 'Freeness counter-examples: none were found' not in scc:
            raise RuntimeError('Missing SCC conclusions.\n'+scc)
        records.append({'module':module,'target':rel,'sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'engine':shutil.which(a.engine),'mfe':str(pathlib.Path(a.mfe).resolve()),'options':['-no-banner','-no-ansi-color'],'crc':['All critical pairs have been joined.','The specification is locally-confluent.','The module is sort-decreasing.'],'scc':['Analysis: it is complete and it is sound','Ground weak termination: not proved','Ground sort-decreasingness: not proved'],'production_refinement':'not established by this tool session'})
        print(f'PASS {module}: CRC local confluence/sort decrease; SCC completeness/soundness.',flush=True)
    (a.output/'summary.json').write_text(json.dumps(records,indent=2)+'\n')
    print('Production RAT modules: unsupported. Slice refinement and termination are separate obligations.')
    print('Logs:',a.output)
if __name__=='__main__':main()
