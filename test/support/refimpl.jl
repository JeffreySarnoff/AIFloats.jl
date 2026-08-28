# the independent reference implementation
#
# Every other check compares the engine against a wider float, valid only
# while "wide enough". This one shares no code and no representation with the
# engine: test values are exact dyadic rationals carried as (num::BigInt, q2),
# and rounding is reimplemented from the draft in pure BigInt arithmetic —
# shifts and comparisons, no floats. Every comparison is a decision, not an
# estimate.

module RefImpl

export RefRounded, refround, refsaturate_code, dyadic_to_bigfloat

struct RefRounded
    kind::Symbol      # :finite | :nan | :pinf | :ninf
    sign::Int
    S::BigInt         # 0 <= S < 2^P (finite)
    Q::Int
end

# exact BigFloat of num · 2^q2
function dyadic_to_bigfloat(num::BigInt, q2::Int)
    setprecision(BigFloat, max(64, ndigits(abs(num), base = 2) + 8)) do
        ldexp(BigFloat(num), q2)
    end
end

_nbits(a::BigInt) = ndigits(a, base = 2)

# tie / evenness helpers on exact remainders: value fraction is rem / 2^t
_gt0(rem) = rem > 0
_cmphalf(rem::BigInt, t::Int) = cmp(rem << 1, BigInt(1) << t)   # sign of ν − ½

_codeiseven(S::BigInt, Q::Int, B::Int, P::Int) =
    P > 1 ? iseven(S) : (S == 0 || iseven(Q + B))

# ⌊ν · 2^N⌋ with ν = rem / 2^t, exactly
_floorscaled(rem::BigInt, t::Int, N::Int) = (rem << N) >> t

# round-nearest-ties-even of ν · 2^N, exactly
function _rnite(rem::BigInt, t::Int, N::Int)
    num = rem << N                    # ν·2^N = num / 2^t
    k = num >> t
    r2 = (num - (k << t)) << 1        # 2·fractional numerator vs 2^t
    c = cmp(r2, BigInt(1) << t)
    if c > 0 || (c == 0 && isodd(k))
        k + 1
    else
        k
    end
end

function _away(mode::Symbol, N::Int, R::Int, rem::BigInt, t::Int,
               S::BigInt, Q::Int, B::Int, P::Int, sign::Int)
    if mode === :RTZ
        false
    elseif mode === :RTP
        _gt0(rem) && sign > 0
    elseif mode === :RTN
        _gt0(rem) && sign < 0
    elseif mode === :RTA
        _cmphalf(rem, t) >= 0
    elseif mode === :RTE
        c = _cmphalf(rem, t)
        c > 0 || (c == 0 && !_codeiseven(S, Q, B, P))
    elseif mode === :RTO
        _gt0(rem) && _codeiseven(S, Q, B, P)
    elseif mode === :RSA
        _floorscaled(rem, t, N) + R >= BigInt(1) << N
    elseif mode === :RSB
        _floorscaled(rem, t, N + 1) + (2R + 1) >= BigInt(1) << (N + 1)
    elseif mode === :RSC
        _rnite(rem, t, N) + R >= BigInt(1) << N
    else
        error("unknown mode $mode")
    end
end

"""
    refround(P, B, mode, N, R, num, q2) -> RefRounded

Round the exact dyadic value `num · 2^q2` to the (P, B) grid under `mode`
(`:RTE :RTA :RTP :RTN :RTZ :RTO :RSA :RSB :RSC`, stochastic with budget `N`
and draw `R`). Pure BigInt arithmetic.
"""
function refround(P::Int, B::Int, mode::Symbol, N::Int, R::Int,
                  num::BigInt, q2::Int)
    num == 0 && return RefRounded(:finite, 1, BigInt(0), 0)
    sign = num > 0 ? 1 : -1
    a = abs(num)
    e = (_nbits(a) - 1) + q2                    # ⌊log₂|v|⌋, exact
    Q = max(e, 1 - B) - P + 1
    t = Q - q2                                  # bits dropped by the grid scaling
    local S::BigInt, rem::BigInt, teff::Int
    if t <= 0
        S = a << (-t)
        rem = BigInt(0)
        teff = 1                                # any positive width; rem is 0
    else
        S = a >> t
        rem = a & ((BigInt(1) << t) - 1)
        teff = t
    end
    if _away(mode, N, R, rem, teff, S, Q, B, P, sign)
        S += 1
    end
    if S == BigInt(1) << P                      # next-binade carry
        S = BigInt(1) << (P - 1)
        Q += 1
    end
    S == 0 && return RefRounded(:finite, 1, BigInt(0), 0)
    RefRounded(:finite, sign, S, Q)
end

# the saturation rows, restated independently. Returns the reference CODE
# POINT for a rounded result on a format described by its raw parameters plus
# its (independently derived) special codes.
function refsaturate_code(r::RefRounded, mode::Symbol, satmode::Symbol;
                          P::Int, B::Int, signed::Bool, extended::Bool,
                          nan::Integer, pinf::Integer, ninf::Integer,
                          maxfin::Integer, minfin::Integer, K::Int)
    r.kind === :nan && return nan
    hidden = BigInt(1) << (P - 1)
    # the extremal magnitude in (S, Q): the top finite datum's canonical form —
    # derived from the format algebra, not from the engine.
    #   maxfinite = (2^P - 1 - extended·signed-layout slack) ... restated via
    #   its code below instead, split independently:
    c = BigInt(maxfin)
    tsig = c & (hidden - 1)
    Eb = Int(c >> (P - 1))
    Shi = Eb == 0 ? tsig : tsig + hidden
    Qhi = (Eb == 0 ? 1 : Eb) - B - (P - 1)

    over = false; under = false
    if r.kind === :finite
        r.S == 0 && return 0
        overmag = (r.Q > Qhi) || (r.Q == Qhi && r.S > Shi)
        over = overmag && r.sign > 0
        under = signed ? (overmag && r.sign < 0) : (r.sign < 0)
        if !over && !under
            # independent encode: subnormal codes ARE S; normal write Eb field
            local code::BigInt
            if r.S < hidden
                code = r.S
            else
                Eb2 = r.Q + P - 1 + B
                code = (r.S & (hidden - 1)) + (BigInt(Eb2) << (P - 1))
            end
            (signed && r.sign < 0) && (code += BigInt(1) << (K - 1))
            return Int(code)
        end
    end
    if satmode === :SF
        r.kind === :pinf && return maxfin
        r.kind === :ninf && return minfin
        over && return maxfin
        under && return minfin
        return nan
    elseif satmode === :SP
        r.kind === :pinf && return extended ? pinf : maxfin
        r.kind === :ninf && return (signed && extended) ? ninf : minfin
        over && return maxfin
        under && return minfin
        return nan
    else # :SN
        if r.kind === :finite
            over  && (mode === :RTZ || mode === :RTN) && return maxfin
            under && (mode === :RTZ || mode === :RTP) && return minfin
        end
        if extended
            (over || r.kind === :pinf) && return pinf
            if under || r.kind === :ninf
                return signed ? ninf : nan
            end
        end
        return nan
    end
end

end # module RefImpl