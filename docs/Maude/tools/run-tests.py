#!/usr/bin/env python3
"""Exact independent fixtures, diagnostic-sensitive fresh Maude processes."""
import argparse, itertools, json, os, pathlib, re, subprocess, tempfile, time, sys
sys.dont_write_bytecode = True
from fractions import Fraction as Q
ROOT=pathlib.Path(__file__).resolve().parents[1]
F4='Binary(4, 2, Signed, Finite)'; F8='Binary(8, 4, Signed, Extended)'
PS='proj(NearestTiesToEven, SatNone)'
MODES=['NearestTiesToEven','NearestTiesToAway','TowardPositive','TowardNegative','TowardZero','ToOdd','StochasticA(2, 1)','StochasticB(2, 1)','StochasticC(2, 1)']
def value(v): return str(v)
def independent_decode(k,p,s,d,c):
    """Enumerate exponent/significand fields directly, independently of Maude."""
    half=2**(k-1); mask=2**(p-1); bias=2**(k-p-(s=='Signed'))
    if c==(half if s=='Signed' else 2**k-1):return 'nan'
    if d=='Extended' and c==(half-1 if s=='Signed' else 2**k-2):return 'posInf'
    if d=='Extended' and s=='Signed' and c==2**k-1:return 'negInf'
    sign=-1 if s=='Signed' and c>half else 1
    mag=c%half if s=='Signed' else c
    e,t=divmod(mag,mask)
    return sign*Q(t if e==0 else mask+t)*Q(2)**((1 if e==0 else e)-bias-(p-1))
def key(v):return (0,0) if v=='nan' else (1,0) if v=='negInf' else (3,0) if v=='posInf' else (2,Q(v))
def fixtures(suite):
    rows=json.loads((ROOT/'tests/vectors/tables-3-7.json').read_text())['tables_4_to_7']
    if suite in ['smoke','codec']:
        for r in rows if suite=='codec' else rows[:16]:
            f,c,v=r['format'],r['code'],r['value']
            yield f'table-{r["table"]}-{f}-{c}',f'decode({f}, {c}) == {v}'
            yield f'roundtrip-{f}-{c}',f'encode({f}, decode({f}, {c})) == {c}'
            yield f'datum-{f}-{c}',f'datum({f}, {v})'
            yield f'subnormal-{f}-{c}',f'IsSubnormal({f}, {c}) == {str(r["subnormal"]).lower()}'
        yield 'convert-two',f'Convert({F8}, {F8}, {PS}, 72) == 72'
    if suite=='domains':
        for f in ['Binary(2, 1, Signed, Finite)','Binary(4, 4, Signed, Finite)','Binary(4, 5, Unsigned, Finite)','Binary(4, 0, Signed, Finite)','Binary(-1, 1, Signed, Finite)']:
            yield 'invalid-format-'+f,f'validFormat({f}) == false'
        for c in [-1,16]:yield 'invalid-code-'+str(c),f'validCode({F4}, {c}) == false'
        for x in ['240','1/3','-240']:yield 'invalid-datum-'+x,f'datum({F8}, {x}) == false'
        for m in ['StochasticA(-1, 0)','StochasticB(2, 4)','StochasticC(2, -1)']:yield m,f'validRound({m}) == false'
        yield 'invalid-encoder-residual',f'encode({F8}, 240) :: Nat == false'
        yield 'invalid-decode-residual',f'decode({F4}, 16) :: XReal == false'
        yield 'nonpositive-log-residual','floorLog2(0) :: Int == false'
    if suite=='projection':
        # Bracket exact rational inputs by independently constructed unbounded precision grids.
        for f in sorted({r['format'] for r in rows}):
            k,p=map(int,re.findall(r'\d+',f)[:2]);s='Unsigned' if 'Unsigned' in f else 'Signed';d='Extended' if 'Extended' in f else 'Finite'
            vals=[independent_decode(k,p,s,d,c) for c in range(2**k)]
            finite=[v for v in vals if isinstance(v,Q)];lo,hi=min(finite),max(finite)
            bias=2**(k-p-(s=='Signed'));step=Q(2)**(2-p-bias)
            inputs=[0,step/4,-step/4,step/2,-step/2,3*step/2,-3*step/2,hi,hi+step,hi*2,lo-step,-hi*2,Q(5,4),Q(-5,4)]
            for m,sat,x in itertools.product(MODES,['SatNone','SatFinite','SatPropagate'],inputs):
                rounded=round_reference(Q(x),p,bias,m)
                expected=rounded
                if rounded<lo or rounded>hi:
                    high=rounded>hi
                    clip=(high and m in ['TowardZero','TowardNegative']) or (not high and m in ['TowardZero','TowardPositive'])
                    expected=(hi if high else lo) if sat!='SatNone' or clip else ('nan' if d=='Finite' or (not high and s=='Unsigned') else 'posInf' if high else 'negInf')
                c=vals.index(expected)
                yield f'project-{f}-{m}-{sat}-{x}',f'project({f}, proj({m}, {sat}), {x}) == {c}'
            for x in ['nan','posInf','negInf']:
                for m,sat in itertools.product(MODES,['SatNone','SatFinite','SatPropagate']):
                    ex='nan' if x=='nan' else (hi if x=='posInf' else lo) if sat=='SatFinite' else (x if d=='Extended' and (x=='posInf' or s=='Signed') else (hi if x=='posInf' else lo)) if sat=='SatPropagate' else (x if d=='Extended' and (x=='posInf' or s=='Signed') else 'nan')
                    yield f'exception-{f}-{m}-{sat}-{x}',f'project({f}, proj({m}, {sat}), {x}) == {vals.index(ex)}'
    if suite in ['order-next','order-full']:
        formats=[(4,2,'Signed','Finite'),(8,4,'Signed','Extended'),(8,3,'Signed','Extended')]
        decoded=[]
        for k,p,s,d in formats:
            f=f'Binary({k}, {p}, {s}, {d})';vs=[independent_decode(k,p,s,d,c) for c in range(2**k)]
            ordered=sorted(range(2**k),key=lambda c:key(vs[c]));nan=vs.index('nan');numeric=[c for c in ordered if c!=nan]
            for i,c in enumerate(numeric):
                for op,expected in [('NextGreaterThan',numeric[i+1] if i+1<len(numeric) else nan),('NextLessThan',numeric[i-1] if i else nan)]:yield f'{op}-{f}-{c}',f'{op}({f}, {c}) == {expected}'
            for op in ['NextGreaterThan','NextLessThan']:yield f'{op}-{f}-nan',f'{op}({f}, {nan}) == {nan}'
            decoded.extend((f,c,key(v)) for c,v in enumerate(vs))
        pairs=itertools.product(decoded,repeat=2) if suite=='order-full' else itertools.product(decoded[::17],repeat=2)
        for (f,c,k1),(g,d,k2) in pairs:yield f'order-{f}-{c}-{g}-{d}',f'TotalOrder({f}, {g}, {c}, {d}) == {str(k1<=k2).lower()}'
    from suites import extra_fixtures
    yield from extra_fixtures(suite, independent_decode, round_reference)
    path=ROOT/f'tests/vectors/{suite}.json'
    if path.exists():
        for r in json.loads(path.read_text()):yield r['id'],r['expression']

def round_reference(x,p,b,m):
    if not x:return x
    # Find adjacent grid values by scaling, with no logarithm.
    a=abs(x);e=1-b
    while Q(2)**(e+1)<=a:e+=1
    q=e-p+1;t=a/Q(2)**q;n=t.numerator//t.denominator;v=t-n
    even=(n%2==0) if p>1 else n==0 or (q+b)%2==0
    if m=='TowardZero':up=False
    elif m=='TowardPositive':up=v>0 and x>0
    elif m=='TowardNegative':up=v>0 and x<0
    elif m=='NearestTiesToAway':up=v>=Q(1,2)
    elif m=='NearestTiesToEven':up=v>Q(1,2) or v==Q(1,2) and not even
    elif m=='ToOdd':up=v>0 and even
    elif 'StochasticA' in m:up=int(v*4)+1>=4
    elif 'StochasticB' in m:up=int(v*8)+3>=8
    else:up=round(v*4)+1>=4
    return (1 if x>0 else -1)*(n+up)*Q(2)**q

def run_suite(suite,engine,timeout,chunk=1000,profile=None):
    count=0;start=time.monotonic();iterator=iter(fixtures(suite))
    loader='load-symbolic.maude' if suite=='symbolic' or profile=='symbolic' else 'load-core.maude'
    facade='P3109-SYMBOLIC' if suite=='symbolic' or profile=='symbolic' else 'P3109-CORE'
    while cases:=list(itertools.islice(iterator,chunk)):
        commands=f'load {loader}\nload tests/support.maude\nfmod P3109-TEST is including {facade} . including P3109-TEST-SUPPORT . endfm\n'
        commands+='\n'.join(f'red in P3109-TEST : check({json.dumps(i)}, ({e})) .' for i,e in cases)+f'\nred in P3109-TEST : suiteComplete({len(cases)}) .\nquit\n'
        proc=subprocess.run([engine,'-no-banner','-no-ansi-color'],input=commands,cwd=ROOT,text=True,capture_output=True,timeout=timeout)
        out=proc.stdout+proc.stderr
        passed=re.findall(r'result TestResult: passed\(\s*"((?:[^"\\]|\\.)*)"\)',out)
        if f'result TestResult: suiteComplete({len(cases)})' not in out or proc.returncode or re.search(r'Warning:|Advisory:|Error:',out) or len(passed)!=len(cases) or passed!=[i for i,e in cases]:
            log=pathlib.Path(tempfile.gettempdir())/f'p3109-{suite}-failure.log';log.write_text(out)
            failures=[i for i,e in cases if i not in passed]
            raise RuntimeError(f'{suite}: {len(passed)}/{len(cases)} checks; failures {failures[:5]}; see {log}')
        count+=len(cases)
        if suite=='order-full' and count % 25000==0: print(f'  {suite}: {count} checks',flush=True)
    if not count:raise RuntimeError('Empty suite: '+suite)
    print(f'PASS {suite}: expected={count} executed={count} ({time.monotonic()-start:.2f}s)',flush=True)
    return count

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--suite',default='core');p.add_argument('--engine',default=os.getenv('MAUDE_ENGINE','maude'));p.add_argument('--timeout',type=int,default=60)
    p.add_argument('--profile',choices=['core','symbolic']);a=p.parse_args();suites=['smoke','domains','codec','projection','scalar','order-next','blocks','conformance'] if a.suite=='core' else [a.suite]
    total=sum(run_suite(s,a.engine,a.timeout,profile=a.profile) for s in suites);print(f'TOTAL expected={total} executed={total}')
if __name__=='__main__':main()
