#!/usr/bin/env python3
"""Fresh independent loads; force compilation of every reachable concrete module."""
import argparse,pathlib,re,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[1]
def reachable(path,seen=None):
    seen=set() if seen is None else seen
    path=path.resolve()
    if path in seen:raise RuntimeError('Repeated loader file: '+str(path))
    seen.add(path);text=path.read_text();mods=[]
    for rel in re.findall(r'^load (\S+)\s*$',text,re.M):mods+=reachable(path.parent/rel,seen)
    mods+=re.findall(r'^fmod (P3109-[^\s{]+) is\s*$',text,re.M)
    return mods

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--engine',default='maude');a=p.parse_args()
    for loader in ['load-core.maude','load-symbolic.maude','load-contracts.maude']:
        modules=reachable(ROOT/loader)
        command=f'load {loader}\n'+''.join(f'red in {m} : true .\n' for m in modules)+'quit\n'
        proc=subprocess.run([a.engine,'-no-banner','-no-ansi-color'],input=command,cwd=ROOT,text=True,capture_output=True,timeout=60)
        out=proc.stdout+proc.stderr
        if proc.returncode or re.search(r'Warning:|Advisory:|Error:',out) or out.count('result Bool: true')!=len(modules):raise RuntimeError(out)
        print(f'PASS {loader}: {len(modules)} concrete modules compile/reduce; theories and parameters are not executable targets.')
    for example,expected in [('core.maude',['6','2','ccons(4, ccons(12, cnil))']),('symbolic.maude',['3/4','exprSqrt(2)','3/4','negInf','xEq(exprExp(1), exprExp(2))'])]:
        proc=subprocess.run([a.engine,'-no-banner','-no-ansi-color',f'examples/{example}'],cwd=ROOT,text=True,capture_output=True,timeout=60)
        out=proc.stdout+proc.stderr
        results=re.findall(r'^result [^:\n]+: (.*?)\n(?=(?:=|Bye))',out,re.M|re.S)
        results=[' '.join(r.split()) for r in results]
        if proc.returncode or re.search(r'Warning:|Advisory:|Error:',out) or results!=expected:raise RuntimeError(out)
        print('PASS example '+example)
if __name__=='__main__':main()
