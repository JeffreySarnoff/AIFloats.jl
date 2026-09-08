"""Independent rational oracle: original first-match scalar rows from D1 pp.33-52.

Test-only. Semantic modules never load this file. FMA and FAA use their
original special cases rather than the composed implementation equations.
"""
from fractions import Fraction as Q
NAN='nan';PI='posInf';NI='negInf'
def fv(v):
    """Maude spelling of an XReal: exceptionals stand alone, finite rationals are embedded by fin."""
    s=str(v);return s if s in (NAN,PI,NI) else f'fin({s})'
def finite(x):return isinstance(x,Q)
def inf(x):return x in (PI,NI)
def negative(x):return x==NI or finite(x) and x<0
def neg(x):return NAN if x==NAN else NI if x==PI else PI if x==NI else -x
def magnitude(x):return NAN if x==NAN else PI if inf(x) else abs(x)
def lt(x,y):return False if NAN in (x,y) else (x==NI and y!=NI) or (y==PI and x!=PI) or (finite(x) and finite(y) and x<y)
def add(x,y):
    if NAN in (x,y) or (x,y) in [(PI,NI),(NI,PI)]:return NAN
    if PI in (x,y):return PI
    if NI in (x,y):return NI
    return x+y

def mul(x,y):
    if NAN in (x,y):return NAN
    if inf(x) or inf(y):
        if x==0 or y==0:return NAN
        return NI if negative(x)!=negative(y) else PI
    return x*y

def divide(x,y):
    if NAN in (x,y) or inf(x) and inf(y) or y==0:return NAN
    if inf(x):return NI if negative(x)!=negative(y) else PI
    if inf(y):return Q(0)
    return x/y

def original_fma(x,y,z):
    # pp.38 rows 1-17: NaN; zero*infinity; opposite infinite addend.
    if NAN in (x,y,z):return NAN
    if x==0 and inf(y) or inf(x) and y==0:return NAN
    if finite(x) and inf(y) and inf(z):
        if (y==PI and z==PI and x<0) or (y==NI and z==PI and x>0) or (y==NI and z==NI and x<0) or (y==PI and z==NI and x>0):return NAN
    if inf(x) and finite(y) and inf(z):
        if (x==PI and z==PI and y<0) or (x==NI and z==PI and y>0) or (x==NI and z==NI and y<0) or (x==PI and z==NI and y>0):return NAN
    if (x,y,z) in [(NI,PI,PI),(PI,NI,PI),(PI,PI,NI),(NI,NI,NI)]:return NAN
    if (x,y) in [(PI,PI),(NI,NI)]:return PI
    if (x,y) in [(PI,NI),(NI,PI)]:return NI
    if inf(z):return z
    if inf(x) or inf(y):return NI if negative(x)!=negative(y) else PI
    return x*y+z

def original_faa(x,y,z):
    if NAN in (x,y,z):return NAN
    if PI in (x,y,z) and NI in (x,y,z):return NAN
    if PI in (x,y,z):return PI
    if NI in (x,y,z):return NI
    return x+y+z

def evaluate(name,*args):
    x=args[0];y=args[1] if len(args)>1 else None
    if name=='Convert':return x
    if name=='Abs':return magnitude(x)
    if name=='Negate':return neg(x)
    if name=='Recip':return divide(Q(1),x)
    if name=='Add':return add(x,y)
    if name=='Subtract':return add(x,neg(y))
    if name=='Multiply':return mul(x,y)
    if name=='Divide':return divide(x,y)
    if name=='CopySign':return NAN if NAN in (x,y) else neg(magnitude(x)) if negative(y) else magnitude(x)
    if name=='FMA':return original_fma(*args)
    if name=='FAA':return original_faa(*args)
    if name=='Clamp':
        lo,hi=args[1:]
        if NAN in args or lt(hi,lo):return NAN
        return lo if lt(x,lo) else hi if lt(hi,x) else x
    if name.startswith(('Minimum','Maximum')):
        minimum=name.startswith('Minimum')
        if 'Number' in name or 'Finite' in name:
            if x==NAN:return y
            if y==NAN:return x
        elif NAN in (x,y):return NAN
        if 'Finite' in name:
            if inf(x) and finite(y):return y
            if finite(x) and inf(y):return x
        if 'Magnitude' in name:
            a,b=magnitude(x),magnitude(y)
            if lt(a,b):return x if minimum else y
            if lt(b,a):return y if minimum else x
        return (x if lt(x,y) else y) if minimum else (y if lt(x,y) else x)
    raise ValueError(name)
