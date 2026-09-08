"""Exhaustive bounded scalar checks and independent §4.5 product fixtures."""
import itertools,json,pathlib
from fractions import Fraction as Q
from reference import evaluate,finite,fv
ROOT=pathlib.Path(__file__).resolve().parents[1]
F4='Binary(4, 2, Signed, Finite)';E4='Binary(4, 2, Signed, Extended)';F8='Binary(8, 4, Signed, Extended)';G8='Binary(8, 3, Signed, Extended)';S8='Binary(8, 1, Unsigned, Finite)';PS='proj(NearestTiesToEven, SatNone)';BP='bproj(NearestTiesToEven, SatNone)'
def seq(items,cons='fcons',nil='fnil'):
    t=nil
    for x in reversed(items):t=f'{cons}({x}, {t})'
    return t

def extra_fixtures(suite,decode,rounder):
    ops=json.loads((ROOT/'inventory/operations.json').read_text())['operations']
    if suite=='projection':
        # Exhaust all supplied random integers for N=0..3 on a fixed fractional grid.
        # Expected choices are direct integer threshold calculations, independent of the rounder.
        for p,n in itertools.product([1,2,4],range(4)):
            for r,j,sgn in itertools.product(range(2**n),range(17),[-1,1]):
                fraction=Q(j,16);x=sgn*(Q(1)+fraction)*Q(2)**(1-p)
                for variant in 'ABC':
                    scaled=fraction*2**n
                    rounded=(scaled.numerator//scaled.denominator if variant=='A' else (2*scaled).numerator//(2*scaled).denominator if variant=='B' else round(scaled))
                    up=rounded+r>=2**n if variant!='B' else rounded+2*r+1>=2**(n+1)
                    expected=sgn*(1+up)*Q(2)**(1-p)
                    # Choose bias=1, so this entire grid lies at the minimum exponent.
                    yield f'stochastic-{p}-{n}-{r}-{j}-{sgn}-{variant}',f'roundToPrecision({p}, 1, Stochastic{variant}({n}, {r}), {fv(x)}) == {fv(expected)}'
    if suite=='codec':
        for r in json.loads((ROOT/'tests/vectors/tables-3-7.json').read_text())['tables_4_to_7']:
            f,c,v=r['format'],r['code'],r['value']
            if v=='nan':cls='ClsNaN'
            elif v in ['posInf','negInf']:cls='ClsPositiveInfinity' if v=='posInf' else 'ClsNegativeInfinity'
            elif Q(v)==0:cls='ClsZero'
            else:cls='Cls'+('Negative' if Q(v)<0 else 'Positive')+('Subnormal' if r['subnormal'] else 'Normal')
            yield f'class-{f}-{c}',f'Class({f}, {c}) == {cls}'

        for k,p,sg,d in [(8,4,'Signed','Extended'),(8,3,'Signed','Extended'),(8,1,'Unsigned','Finite')]:
            f=f'Binary({k}, {p}, {sg}, {d})'
            for c in range(2**k):
                v=decode(k,p,sg,d,c)
                yield f'codec8-{f}-{c}',f'decode({f}, {c}) == {fv(v)}'
                yield f'roundtrip8-{f}-{c}',f'encode({f}, decode({f}, {c})) == {c}'
            yield f'table3-one-{f}',f'encode({f}, fin(1)) == {2**(k-2 if sg=="Signed" else k-1)}'
    if suite=='domains':
        yield 'invalid-code-format', 'validCode(Binary(2, 1, Signed, Finite), 0) == false'
        yield 'invalid-round-query','(RoundOf(proj(StochasticA(-1, 0), SatNone)) :: RoundMode) == false'
        yield 'invalid-sat-query','(SatOf(proj(StochasticA(-1, 0), SatNone)) :: SatMode) == false'
        yield 'invalid-project',f'(project({F4}, proj(StochasticA(-1, 0), SatNone), nan) :: Nat) == false'
        yield 'invalid-block-application',f'(blockDecode(0, {F4}, {F4}, 4, cnil) :: XSeq) == false'
        for m in ['StochasticA','StochasticB','StochasticC']:
            yield f'zero-random-bits-{m}',f'validRound({m}(0, 0))'
    if suite=='scalar':
        vals=[decode(4,2,'Signed','Extended',i) for i in range(16)]
        def projected(x):
            if finite(x):
                x=rounder(x,2,2,'NearestTiesToEven')
                if x>2:x='posInf'
                elif x< -2:x='negInf'
            return vals.index(x)
        for c,d in itertools.product(range(16),repeat=2):
            from reference import lt,negative
            x,y=vals[c],vals[d];eq=x==y and x!='nan'
            for name,answer in [('CompareLess',lt(x,y)),('CompareLessEqual',lt(x,y) or eq),('CompareEqual',eq),('CompareGreater',lt(y,x)),('CompareGreaterEqual',lt(y,x) or eq)]:
                yield f'comparison-{name}-{c}-{d}',f'{name}({E4}, {E4}, {c}, {d}) == {str(answer).lower()}'
        for c,x in enumerate(vals):
            for name,answer in [('IsZero',x==0),('IsOne',x==1),('IsNaN',x=='nan'),('IsFinite',finite(x)),('IsInfinite',x in ['posInf','negInf']),('IsSignMinus',negative(x))]:
                yield f'predicate-{name}-{c}',f'{name}({E4}, {c}) == {str(answer).lower()}'
        for o in ops:
            if o['profile']!='core' or o['result']!='code' or not o.get('wrapper',True):continue
            name=o['name'];n=o['arity']
            for codes in itertools.product(range(16),repeat=n):
                values=[vals[c] for c in codes];ans=evaluate(name,*values)
                cargs=', '.join(map(str,codes));fargs=', '.join([E4]*(n+1))
                yield f'omega-{name}-{cargs}',f'omega{name}('+', '.join(map(fv,values))+f') == {fv(ans)}'
                yield f'scalar-{name}-{cargs}',f'{name}({fargs}, {PS}, {cargs}) == {projected(ans)}'
    if suite in ['blocks','symbolic']:
        for o in ops:
            if not o.get('block') or o['profile']!=('symbolic' if suite=='symbolic' else 'core') or not o.get('wrapper',True):continue
            name=o['name'];n=o['arity']
            fmt=E4 if suite=='symbolic' else F4
            inputs=['4']*n
            if suite=='symbolic':
                if name in 'Exp Exp2 LogOnePlus ExpMinusOne Sin Cos Tan ArcSin ArcTan Sinh Cosh Tanh ArcSinh ArcTanh'.split(): inputs=['0']
                if name=='Softplus': inputs=['15']
                if name in ['Hypot','ArcTan2']: inputs=['0','4']
            # Unit-scale equivalence checks both generated schemas and scalar/block random lift.
            for m in ['NearestTiesToEven','StochasticC(2, 1)']:
                ps=f'proj({m}, SatNone)';bp=f'singletonLift({ps})'
                expected=f'{name}('+', '.join([fmt]*(n+1)+[ps]+inputs)+')'
                scaled=f'Scaled{name}('+', '.join([fmt]*(2*n+1)+[ps]+[v for c in inputs for v in ['4',c]])+')'
                block=f'Block{name}('+', '.join(['1']+[fmt]*(2*n+2)+[bp]+[v for c in inputs for v in ['4',f'ccons({c}, cnil)']]+['4'])+')'
                yield f'unit-scaled-{name}-{m}',f'{scaled} == {expected}'
                yield f'unit-block-{name}-{m}',f'{block} == block(4, ccons({expected}, cnil))'
    if suite=='conformance':
        base=[F4,F8,G8];external=['binary32','binary16','BFloat16'];minmax='Minimum Maximum MinimumNumber MaximumNumber MinimumMagnitude MaximumMagnitude MinimumMagnitudeNumber MaximumMagnitudeNumber MinimumFinite MaximumFinite'.split()
        predicates='IsZero IsOne IsNaN IsInfinite IsFinite IsSignMinus IsNormal IsSubnormal NextGreaterThan NextLessThan'.split()
        queries='BitwidthOf PrecisionOf SignednessOf DomainOf ExponentBitwidthOf TrailingSignificandBitwidthOf ExponentBiasOf MaxFiniteOf MinFiniteOf MinPositiveOf MaxSubnormalOf MinNormalOf'.split()
        for o in ops:
            if o['wrapper'] and o['block']:
                n=o['arity'];ident=f'blockElements("Block{o["name"]}", 2, {seq([F4]*(2*n+2))}, {BP})'
                yield f'block-declaration-{o["name"]}',f'wellFormedDeclaration(approximate({ident}, "myBlock{o["name"]}", steps(1), sampleEvidence))'
        ident=f'blockScale("ConvertToBlockMaxAbsFinite", 2, {seq([F4,F8,F4])}, {PS}, {BP})'
        yield 'scale-declaration',f'wellFormedDeclaration(exact({ident}, "maxabs", pendingEvidence))'
        yield 'dot-declaration',f'validSpecialization(blockReduction("BlockDotProduct", 8, {seq([S8,F8,S8,F8,"binary32"])}, {PS}))'
        yield 'bad-block-size-declaration',f'validSpecialization(blockElements("BlockAdd", 0, {seq([F4]*6)}, {BP})) == false'
        yield 'bad-block-random-length-declaration',f'validSpecialization(blockElements("BlockAdd", 2, {seq([F4]*6)}, bproj(BlockStochasticA(1, rcons(0, rnil)), SatNone))) == false'
        unit=seq(['0','1','2'],'ccons','cnil'); parts=seq([seq([str(i)],'ccons','cnil') for i in range(3)],'pcons','pnil')
        yield 'three-way-partition',f'partition({unit}, {parts})'
        yield 'partition-duplicates',f'partition({unit}, pcons({unit}, pcons(ccons(0, cnil), pnil))) == false'
        ident=f'numeric("Add", {seq([F4,F4,F8])}, {PS})'
        parts=f'kcons(kappaPart(ccons(0, cnil), steps(4)), kcons(kappaPart(ccons(1, cnil), steps(3)), knil))'
        record=f'partitioned({ident}, "partitionAdd", ccons(0, ccons(1, cnil)), {parts}, sampleEvidence)'
        yield 'partitioned-declaration',f'wellFormedDeclaration({record})'
        yield 'partitioned-bound',f'declarationKappa({record}) == steps(4)'
        yield 'partitioned-invalid-cover',f'wellFormedDeclaration(partitioned({ident}, "partitionAdd", ccons(2, cnil), {parts}, sampleEvidence)) == false'
        yield 'declarations-cover',f'declarationsCover(scons({ident}, snil), dcons(exact({ident}, "myAdd", pendingEvidence), dnil))'
        yield 'missing-declaration',f'declarationsCover(scons({ident}, snil), dnil) == false'
        for size in range(1,4):
            for fx in itertools.combinations(external,size):
                fxs=seq(fx);allf=base+list(fx);outputs=[F8,G8]+list(fx);specs=[]
                for name in ['Convert','Recip']:
                    specs += [(name,fs) for fs in itertools.product(allf,repeat=2)]
                specs += [(name,[f,f]) for name in ['Abs','Negate'] for f in base]
                specs += [(name,[a,b,r]) for name in ['Add','Subtract','Multiply'] for a,b,r in itertools.product(base,base,outputs)]
                specs += [(name,[a,b,r,r]) for name in ['FMA','FAA'] for a,b,r in itertools.product(base,base,fx)]
                specs += [(name,[f,f,f]) for name in minmax for f in base]
                specs += [(name,[S8,a,S8,b,r]) for name in ['ScaledAdd','ScaledSubtract','ScaledMultiply'] for a,b,r in itertools.product(base,base,outputs)]
                for i,(name,fs) in enumerate(specs):
                    yield f'required-{fx}-{i}',f'required(numeric("{name}", {seq(fs)}, {PS}), {fxs})'
                    yield f'declaration-required-{fx}-{i}',f'wellFormedDeclaration(exact(numeric("{name}", {seq(fs)}, {PS}), "implementation", pendingEvidence))'
                plain=[(n,[f,f]) for n in ['CompareLess','CompareLessEqual','CompareEqual','CompareGreater','CompareGreaterEqual'] for f in base]+[(n,[f]) for n in predicates for f in base]+[(n,[f]) for n in queries for f in allf]
                for i,(name,fs) in enumerate(plain):yield f'required-plain-{fx}-{i}',f'required(plain("{name}", {seq(fs)}), {fxs})'
                yield f'not-required-divide-{fx}',f'required(numeric("Divide", {seq([F4,F4,F8])}, {PS}), {fxs}) == false'
                yield f'not-required-result-f4-{fx}',f'required(numeric("Add", {seq([F4,F4,F4])}, {PS}), {fxs}) == false'
                yield f'not-required-wrong-round-{fx}',f'required(numeric("Abs", {seq([F4,F4])}, proj(TowardZero, SatNone)), {fxs}) == false'
                yield f'not-required-wrong-scale-{fx}',f'required(numeric("ScaledAdd", {seq([F4,F4,F4,F4,F8])}, {PS}), {fxs}) == false'
        for fx in ['fnil',seq(['binary64']),seq(['binary32','binary32'])]:yield 'invalid-fx-'+fx,f'validFX({fx}) == false'
        for k,p,sg,d in [(4,2,'Signed','Finite'),(8,4,'Signed','Extended'),(8,1,'Unsigned','Finite')]:
            f=f'Binary({k}, {p}, {sg}, {d})';vals=[decode(k,p,sg,d,c) for c in range(2**k)];ordered=sorted(c for c,v in enumerate(vals) if finite(v));ordered.sort(key=lambda c:vals[c])
            for rank,c in enumerate(ordered):yield f'rank-{f}-{c}',f'finiteRank({f}, {c}) == {rank}'
        spec=f'numeric("Add", {seq([F4,F4,F8])}, {PS})'
        for name,k in [('nan-precedence','mergeKappa(kInfinity, kNaN) == kNaN'),('multi-result','mergeKappa(steps(3), steps(4)) == steps(4)'),('sample-not-proof','evidenceComplete(sampleEvidence) == false'),('approx-name',f'wellFormedDeclaration(approximate({spec}, "Add", steps(0), sampleEvidence)) == false'),('approx-good-name',f'wellFormedDeclaration(approximate({spec}, "myAdd", steps(3), sampleEvidence))'),('nonnumeric-exact-only',f'wellFormedDeclaration(approximate(plain("IsZero", {seq([F4])}), "myIsZero", steps(0), sampleEvidence)) == false')]:yield name,k
        yield 'invalid-operation-name',f'wellFormedDeclaration(exact(numeric("NotAnOperation", {seq([F4,F4])}, {PS}), "name", pendingEvidence)) == false'
        yield 'invalid-operation-arity',f'validSpecialization(numeric("FMA", {seq([F4,F4])}, {PS})) == false'
        for c,d,ans in [(127,126,'kInfinity'),(128,0,'kNaN'),(128,128,'steps(0)'),(127,255,'kInfinity'),(127,127,'steps(0)'),(4,0,'steps(4)'),(129,1,'steps(2)')]:yield f'kappa-{c}-{d}',f'observationKappa(observation("case", cnil, {F8}, {c}, {d})) == {ans}'
        universe=seq(['0','1','2'],'ccons','cnil');a=seq(['0'],'ccons','cnil');b=seq(['1','2'],'ccons','cnil')
        yield 'partition-cover',f'partition2({universe}, {a}, {b})'
        yield 'partition-overlap',f'partition2({universe}, {a}, {universe}) == false'
        yield 'partition-gap',f'partition2({universe}, {a}, cnil) == false'
        yield 'batch-nan-precedence',f'batchKappa(ocons(observation("inf", cnil, {F8}, 127, 0), ocons(observation("nan", cnil, {F8}, 128, 0), onil))) == kNaN'
        for r in json.loads((ROOT/'tests/vectors/regressions.json').read_text()):yield r['id'],r['expression']
