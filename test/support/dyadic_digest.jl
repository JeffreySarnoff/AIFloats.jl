# the Dyadic differential-digest harness (plan §9.9)
#
# `dyadic_digests(D)` walks a deterministic sweep over a DyadicNumbers module
# `D` (SmallFloats' original or AIFloats' adaptation — same API) and returns
# section digests of every observable: field triples (S, Q, kind), sticky
# signs, comparison results, conversions. `dyadic_capture.jl` writes them from
# the ORIGINAL; test-dyadic.jl recomputes them from the adaptation and
# compares. No RNG anywhere; the sweep is enumerated.

using SHA

struct DySink
    io::IOBuffer
end
DySink() = DySink(IOBuffer())
dyemit!(s::DySink, x::Integer) = (write(s.io, Int64(x % Int64)); s)
dyemit!(s::DySink, x::Bool) = dyemit!(s, Int64(x))
dyemit!(s::DySink, x::Float64) = (write(s.io, isnan(x) ? 0x7ff8000000000000 : reinterpret(UInt64, x)); s)
dyemit!(s::DySink, x::Float32) = dyemit!(s, Float64(x))
dyemit!(s::DySink, x::BigFloat) = (write(s.io, isnan(x) ? "nan" : string(x)); write(s.io, 0x00); s)
dyemit!(s::DySink, x::Rational{BigInt}) = (write(s.io, string(x)); write(s.io, 0x00); s)
function dyemit!(s::DySink, x)                     # a Dyadic of either module
    write(s.io, Int128(x.S)); write(s.io, Int64(x.Q)); write(s.io, UInt8(x.kind)); s
end
dydigest(s::DySink) = bytes2hex(SHA.sha256(take!(s.io)))

# the structured value set: significands at every width class the engine
# forms (datums ≤ 16 bits, products ≤ 32, sums ≤ 33), exponents spanning the
# alignment bands and the rung-3 range, both signs, zero, the three specials
function _dy_values(D::Module)
    Dy = D.Dyadic
    vals = Dy[D.DYADIC_ZERO, D.DYADIC_POSINF, D.DYADIC_NEGINF, D.DYADIC_NAN,
              Dy(Int128(1), Int64(0)), Dy(Int128(-1), Int64(0))]
    sigs = Int128[1, 3, 5, 7, 15, 17, 255, 257, 4095, 65535, 65537, 2^20 + 3,
                  2^31 - 1, 2^32 + 1, 2^40 + 7, typemax(Int64), Int128(2)^96 - 1]
    exps = Int64[0, 1, -1, 2, -2, 5, -5, 40, -40, 93, -93, 94, -94, 95, -95, 96,
                 -96, 127, -127, 128, -128, 200, -200, 8192, -8192, 16383, -16383,
                 32767, -32768]
    for S in sigs, Q in exps, sgn in (1, -1)
        push!(vals, Dy(sgn * S, Q))
    end
    vals
end

function dyadic_digests(D::Module)
    vals = _dy_values(D)
    fin = filter(v -> v.kind == D.DY_FINITE, vals)
    out = Pair{String, String}[]
    # unary observables
    s = DySink()
    for v in vals
        dyemit!(s, v)
        dyemit!(s, isfinite(v)); dyemit!(s, isnan(v)); dyemit!(s, isinf(v)); dyemit!(s, iszero(v))
        dyemit!(s, sign(v)); dyemit!(s, signbit(v)); dyemit!(s, -v); dyemit!(s, abs(v))
        dyemit!(s, floor(v)); dyemit!(s, ceil(v)); dyemit!(s, trunc(v)); dyemit!(s, round(v))
        dyemit!(s, ldexp(v, 3)); dyemit!(s, ldexp(v, -200))
        dyemit!(s, BigFloat(v)); dyemit!(s, Float64(v)); dyemit!(s, Float32(v))
        n, p, d = Base.decompose(v); dyemit!(s, n); dyemit!(s, p); dyemit!(s, d)
        if v.kind == D.DY_FINITE && !iszero(v.S)
            dyemit!(s, exponent(v))
        end
        if v.kind != D.DY_NAN
            dyemit!(s, D.dyadic_to_rational(v))
            dyemit!(s, D.rational_to_dyadic(D.dyadic_to_rational(v)))
        end
    end
    push!(out, "unary" => dydigest(s))
    # binary kernels over every ordered pair: sticky add, checked add where
    # the band admits it, multiply where the width admits it, comparisons
    s = DySink()
    for x in vals, y in vals
        v, sg = D.add_sticky_dy(x, y)
        dyemit!(s, v); dyemit!(s, sg)
        dyemit!(s, D.cmp_dy(x, y))
        dyemit!(s, x == y); dyemit!(s, x < y); dyemit!(s, x <= y)
        dyemit!(s, isless(x, y)); dyemit!(s, isequal(x, y))
        dyemit!(s, max(x, y)); dyemit!(s, min(x, y))
        if x.kind == D.DY_FINITE && y.kind == D.DY_FINITE
            if D.nbits_dy(x.S) + D.nbits_dy(y.S) <= 96
                dyemit!(s, D.mul_dy(x, y))
            end
            d = abs(x.Q - y.Q)
            nb = max(D.nbits_dy(x.S), D.nbits_dy(y.S))
            if d <= D.DYADIC_ALIGN_MAX && nb + d <= 126
                dyemit!(s, D.add_dy(x, y)); dyemit!(s, D.add_dy_checked(x, y))
            end
        else
            dyemit!(s, D.add_dy(x, y)); dyemit!(s, D.mul_dy(x, y))
        end
    end
    push!(out, "binary" => dydigest(s))
    # from-float conversions over a structured float set
    s = DySink()
    fl = Float64[0.0, 1.0, -1.0, 0.5, 1.5, 0.1, -0.1, 3.0e-320, 5.0e-324, 1.0e308,
                 -1.0e308, 2.0^-1074, 2.0^1023, 1.0 + 2.0^-52, Inf, -Inf, NaN]
    for x in fl
        dyemit!(s, D.dyadic_from(x))
        dyemit!(s, D.Dyadic(x))
        dyemit!(s, D.Dyadic(Float32(x)))
        b = setprecision(() -> BigFloat(x), BigFloat, 300)
        dyemit!(s, D.Dyadic(b))
    end
    for q in (1//2, -3//8, 5//1, 7//1024, 1//0, -1//0)
        dyemit!(s, D.rational_to_dyadic(Rational{BigInt}(q)))
        dyemit!(s, D.isdyadic(q))
    end
    dyemit!(s, D.isdyadic(1//3))
    push!(out, "convert" => dydigest(s))
    out
end
