using AIFloats
using Test
using Random
using Quadmath: Float128
using BFloat16s: BFloat16

# Phase 5 gate, surface side: every Base veneer is one register call; the
# op ↔ Base partition is exhaustive; NaN-first ordering pinned; the
# AbstractFloat contract holds on every rung; promotion targets the public
# carrier; inference pinned at the public entry points.

const F8  = Binary(8, 4, SIGNED, EXTENDED)
const F5  = Binary(5, 3, SIGNED, EXTENDED)
const F5U = Binary(5, 2, UNSIGNED, FINITE)
const F9  = Binary(9, 4, SIGNED, EXTENDED)          # UInt16-coded, rung 1
const F16 = Binary(16, 4, SIGNED, EXTENDED)         # rung 2 (Float128 carrier)
const F16X = Binary(16, 1, SIGNED, EXTENDED)        # rung 3 (exact carrier)
const B8 = BinaryValue(F8)

isdefined(Main, :allcodes) || include(joinpath(@__DIR__, "support", "helpers.jl"))
finites(F) = filter(isfinite, allcodes(F))

@testset "op ↔ Base partition is exhaustive" begin
    mapped = Set{Symbol}()
    for (op, _) in AIFloats._BASE_UNARY; push!(mapped, op); end
    for (op, _) in AIFloats._BASE_BINARY; push!(mapped, op); end
    for op in AIFloats._BASE_OPERATOR; push!(mapped, op); end
    for op in AIFloats._BASE_TERNARY; push!(mapped, op); end
    nobase = Set(AIFloats._NO_BASE_COUNTERPART)
    registry = Set(o.name for o in AIFloats.OP_REGISTRY)
    @test isempty(intersect(mapped, nobase))
    @test union(mapped, nobase) == registry
end

@testset "veneers are the register under the session default" begin
    DefaultProjection!(RTE_SN)
    xs = allcodes(F5)
    for (op, bf) in AIFloats._BASE_UNARY
        f = getfield(Base, bf); g = getfield(AIFloats, op)
        @test all(codepoint(f(x)) == codepoint(g(x)) for x in xs)
    end
    for (op, bf) in AIFloats._BASE_BINARY
        f = getfield(Base, bf); g = getfield(AIFloats, op)
        @test all(codepoint(f(x, y)) == codepoint(g(x, y)) for x in xs, y in xs)
    end
    @test all(codepoint(-x) == codepoint(Negate(x)) for x in xs)
    @test all(codepoint(x + y) == codepoint(Add(x, y)) for x in xs, y in xs)
    @test all(codepoint(x - y) == codepoint(Subtract(x, y)) for x in xs, y in xs)
    @test all(codepoint(x * y) == codepoint(Multiply(x, y)) for x in xs, y in xs)
    @test all(codepoint(x / y) == codepoint(Divide(x, y)) for x in xs, y in xs)
    @test all(codepoint(atan(y, x)) == codepoint(ArcTan2(y, x)) for x in xs, y in xs)
    @test all(codepoint(fma(x, y, x)) == codepoint(FMA(x, y, x)) for x in xs, y in xs)
    @test all(codepoint(muladd(x, y, y)) == codepoint(FMA(x, y, y)) for x in xs, y in xs)
    lo, hi = BinaryValue(F5)(-1.0), BinaryValue(F5)(1.0)
    @test all(codepoint(clamp(x, lo, hi)) == codepoint(Clamp(x, lo, hi)) for x in xs)
    x = B8(0.75)
    @test sincos(x) == (Sin(x), Cos(x))
    @test sincospi(x) == (SinPi(x), CosPi(x))
    @test minmax(x, B8(2.0)) == (B8(0.75), B8(2.0))
    # the session default is honored, not RTE_SN by fiat
    DefaultProjection!(RTZ_SF)
    @test all(codepoint(x + y) == codepoint(Add(F5, RTZ_SF, x, y)) for x in xs, y in xs)
    DefaultProjection!(RTE_SN)
    # projection-first convenience, scalar and array
    @test codepoint(Exp(RTZ_SF, x)) == codepoint(Exp(F8, RTZ_SF, x))
    A = B8.(randn(MersenneTwister(1), 16))
    @test codepoint.(Exp(RTZ_SF, A)) == codepoint.(Exp(F8, RTZ_SF, A))
    # broadcasting rides the scalar veneers
    @test codepoint.(A .+ A) == codepoint.(Add(F8, RTE_SN, A, A))
end

@testset "NaN-first total order" begin
    nan = B8(NaN)
    @test isless(nan, typemin(B8))
    @test !isless(nan, nan)
    @test !isless(typemin(B8), nan)
    @test isless(typemin(B8), B8(-1.0)) && isless(B8(-1.0), zero(B8)) &&
          isless(zero(B8), B8(1.0)) && isless(B8(1.0), typemax(B8))
    @test !(nan == nan) && !(nan < nan) && !(nan <= nan) && !(nan < B8(1.0))
    @test isequal(nan, nan) && hash(nan) == hash(nan)
    @test B8(1.5) == B8(1.5) && B8(1.5) <= B8(1.5) && B8(1.0) < B8(1.5)
    @test hash(B8(1.5)) == hash(B8(1.5)) && hash(B8(1.5)) == hash(1.5)
    d = Dict(B8(1.5) => :a); d[B8(1.5)] = :b
    @test length(d) == 1 && d[B8(1.5)] === :b
    @test length(Set(allcodes(F8))) == 256
    for F in (F8, F5U, F9)
        BV = BinaryValue(F)
        xs = allcodes(F)
        keysorted = sort(xs; by = AIFloats.order_key, alg = Base.Sort.DEFAULT_STABLE)
        # both paths: the counting sort (length ≥ 2^K) and the short fallback
        long = shuffle(MersenneTwister(2), vcat(xs, xs))
        @test Base.Sort.defalg(long) isa AIFloats.CodeCountingSort
        s = sort(long)
        @test codepoint.(s) == codepoint.(vcat(keysorted, keysorted)[sortperm(AIFloats.order_key.(vcat(keysorted, keysorted)))])
        @test isnan(s[1]) && isnan(s[2]) && issorted(s; lt = isless)
        r = sort(long; rev = true)
        @test isnan(r[end]) && codepoint.(r) == codepoint.(reverse(s))
        short = shuffle(MersenneTwister(3), xs[1:min(end, 7)])
        @test issorted(sort(short); lt = isless)
        @test issorted(sort(short; rev = true); lt = (a, b) -> isless(b, a))
        # sortperm (Perm ordering) takes the fallback and agrees
        @test codepoint.(long[sortperm(long)]) == codepoint.(s)
    end
    @test nextfloat(B8(1.0)) === NextGreaterThan(B8(1.0))
    @test prevfloat(B8(1.0)) === NextLessThan(B8(1.0))
end

@testset "AbstractFloat contract: constants on all 504 formats" begin
    for (_, F) in AIFloats._NAMED
        # _NAMED holds FORMAT types (improveapi.md §4.1.2); these
        # assertions are about the datum type
        BV = BinaryValue(F)
        @test iszero(decode(zero(BV))) && codepoint(zero(BV)) == 0
        @test isone(decode(one(BV)))
        @test BigFloat(decode(eps(BV))) == 2.0^(1 - Int(PrecisionOf(BV)))
        @test floatmax(BV) === MaxFiniteOf(BV) && floatmin(BV) === MinNormalOf(BV)
        @test typemax(BV) === (is_extended(BV) ? nextfloat(MaxFiniteOf(BV)) : MaxFiniteOf(BV))
        @test typemin(BV) === ((is_signed(BV) && is_extended(BV)) ?
                                prevfloat(MinFiniteOf(BV)) : MinFiniteOf(BV))
        @test precision(BV) == Int(PrecisionOf(BV))
    end
    @test precision(B8; base = 4) == 2
    @test_throws DomainError precision(B8; base = 1)
end

@testset "decompose reconstructs every datum" begin
    for F in (F8, F5U, F9, F16, F16X)
        BV = BinaryValue(F)
        for x in allcodes(F)
            n, p, d = Base.decompose(x)
            if isnan(x)
                @test (n, p, d) == (0, 0, 0)
            elseif isinf(x)
                @test (n, p, d) == (signbit(x) ? -1 : 1, 0, 0)
            else
                @test d == 1
                @test Rational{BigInt}(big(n)) * Rational{BigInt}(big(2))^p == Rational{BigInt}(BigFloat(x))
            end
        end
    end
end

@testset "exponent / significand / frexp / ldexp / eps(x)" begin
    for F in (F8, F5U, F9, F16)
        BV = BinaryValue(F)
        for x in finites(F)
            if iszero(x)
                @test_throws DomainError exponent(x)
                @test_throws DomainError significand(x)
                @test eps(x) === MinPositiveOf(BV)
                continue
            end
            d = decode(x)                           # the carrier: Float64(x) overflows at rung 2
            @test exponent(x) == exponent(d)
            @test decode(significand(x)) == significand(d)
            s, e = frexp(x)
            @test (decode(s), e) == frexp(d)
            # ldexp IS one projection of the exact carrier scaling (it rounds only
            # where the result leaves the datum set: below the subnormal step or
            # past the range)
            @test ldexp(x, 2) === project(F, RTE_SN, ldexp(d, 2))
            @test ldexp(x, -1) === project(F, RTE_SN, ldexp(d, -1))
            # the ulp: distance to the next datum up, wherever that datum exists
            up = NextGreaterThan(x)
            if isfinite(up) && !isnan(up) && !signbit(x)
                @test decode(eps(x)) == decode(up) - d
            end
        end
        @test isnan(eps(BV(NaN)))
        @test isnan(ldexp(BV(NaN), 3))
        is_extended(F) && @test isinf(ldexp(typemax(BV), -1))
    end
    # B == 1, extended: the binade [1, 2) is truncated by Inf, so significand refuses
    T = BinaryValue(Binary(3, 2, SIGNED, EXTENDED))
    @test ExponentBiasOf(T) == 1
    @test_throws ArgumentError significand(T(1.0))
    @test exponent(T(1.0)) == 0
    # ldexp saturates by the session saturation mode
    DefaultProjection!(RTE_SF)
    @test ldexp(MaxFiniteOf(B8), 1) === MaxFiniteOf(B8)
    DefaultProjection!(RTE_SN)
    @test isinf(ldexp(MaxFiniteOf(B8), 1))
end

@testset "round family" begin
    for F in (F8, F5U, F9, F16, F16X)
        BV = BinaryValue(F)
        for x in finites(F)
            b = BigFloat(x)
            @test BigFloat(round(x)) == round(b)
            @test BigFloat(floor(x)) == floor(b)
            @test BigFloat(ceil(x)) == ceil(b)
            @test BigFloat(trunc(x)) == trunc(b)
            for r in (RoundNearest, RoundNearestTiesAway, RoundUp, RoundDown, RoundToZero)
                @test BigFloat(round(x, r)) == round(b, r)
            end
        end
        @test isnan(round(BV(NaN))) && isnan(floor(BV(NaN)))
        is_extended(F) && @test isinf(ceil(typemax(BV)))
    end
    @test round(Int, B8(2.5)) == 2 && round(Int, B8(3.5)) == 4
    @test Int(B8(3.0)) == 3 && Bool(one(B8)) && !Bool(zero(B8))
    @test_throws InexactError Int(B8(1.5))
    @test isinteger(B8(3.0)) && !isinteger(B8(1.5))
end

@testset "refusals say why" begin
    x, y = B8(3.0), B8(2.0)
    for (f, name) in ((rem, "rem"), (mod, "mod"))
        e = try f(x, y); nothing catch e; e end
        @test e isa ArgumentError && occursin("not defined for Binary8p4se", e.msg) &&
              occursin("project", e.msg)
    end
    for r in (RoundNearestTiesUp, RoundFromZero)
        e = try round(x, r); nothing catch e; e end
        @test e isa ArgumentError && occursin("no such rounding mode", e.msg)
    end
    @test_throws ArgumentError B8(1//3)
    @test_throws ArgumentError BinaryValue{F8}(1//3)
    @test_throws ArgumentError convert(B8, 1//3)
end

@testset "conversion and promotion" begin
    for x in finites(F8)
        d = decode(x)
        @test Float64(x) === d && Float32(x) === Float32(d) && Float16(x) === Float16(d)
        @test BFloat16(x) === BFloat16(d) && Float128(x) == Float128(d) && BigFloat(x) == d
    end
    @test isnan(Float64(B8(NaN))) && Float64(typemax(B8)) == Inf
    for BV in (B8, BinaryValue(F16), BinaryValue(F16X))
        C = AIFloats.promotecarrier(BV)
        @test C === AIFloats.promotecarrier(BinaryFormatOf(BV))
        @test promote_type(BV, Float64) === C && promote_type(BV, Float32) === C
        @test promote_type(BV, Float16) === C && promote_type(BV, BFloat16) === C
        @test promote_type(BV, Int) === C && promote_type(BV, UInt8) === C
        @test promote_type(BV, Float128) === (C === BigFloat ? BigFloat : Float128)
        @test promote_type(BV, BigFloat) === BigFloat
        @test widen(BV) === C
        x = BV(2.0)                                 # a datum of every P, P == 1 included
        @test x + 1.0 == 3.0 && x * 2 == 4.0 && (x < 3) && (1 < x) && x == 2.0
        @test typeof(x + 1.0) === C
    end
    @test AIFloats.promotecarrier(F8) === Float64
    @test AIFloats.promotecarrier(F16) === Float128
    @test AIFloats.promotecarrier(F16X) === BigFloat
    # Unsigned is a code point at the constructor, a value at convert
    @test codepoint(fromcode(B8, 0x05)) == 0x05
    @test convert(B8, 0x05) == 5 && convert(B8, 5) == 5 && convert(B8, 2.5) == 2.5
    v = Vector{B8}(undef, 1); v[1] = 0x05
    @test v[1] == 5
    v[1] = 1.25; @test v[1] == 1.25
    @test B8(B8(1.5)) === B8(1.5) && convert(B8, B8(1.5)) === B8(1.5)
    @test BinaryValue{F8}(1.5) === B8(1.5)
    S = BinaryValue(Binary(8, 3, SIGNED, EXTENDED))
    @test convert(S, B8(1.5)) === S(1.5) && S(B8(1.5)) === S(1.5)
    @test B8(1.6; projection = RTZ_SF) == 1.5
    # mixed formats do NOT promote — an explicit Convert is the route
    @test_throws Union{MethodError, ErrorException} B8(1.5) + S(1.5)
end

@testset "similar and reinterpret" begin
    A = Vector{BinaryValue{F8}}(undef, 3)
    @test !isconcretetype(eltype(A))
    @test eltype(similar(A)) === B8
    M = Matrix{BinaryValue{F8}}(undef, 2, 2)
    @test eltype(similar(M)) === B8 && size(similar(M)) == (2, 2)
    V = view(A, 1:2)
    @test eltype(similar(V)) === B8
    @test eltype(similar(B8[])) === B8
    @test reinterpret(B8, 0x45) === fromcode(B8, 0x45)
    @test reinterpret(UInt8, fromcode(B8, 0x45)) === 0x45
    @test_throws ArgumentError reinterpret(B8, 0x0045)
    T5 = BinaryValue(F5)
    @test_throws ArgumentError reinterpret(T5, 0xFF)
    @test reinterpret(T5, 0x1F) === fromcode(T5, 0x1F)
end

@testset "inference pins" begin
    x, y = B8(1.5), B8(0.25)
    @test (@inferred x + y) isa B8
    @test (@inferred x * y) isa B8
    @test (@inferred exp(x)) isa B8
    @test (@inferred x < y) isa Bool
    @test (@inferred isless(x, y)) isa Bool
    @test (@inferred round(x)) isa B8
    @test (@inferred round(x, RoundUp)) isa B8
    @test (@inferred eps(x)) isa B8
    @test (@inferred ldexp(x, 2)) isa B8
    @test (@inferred Float64(x)) isa Float64
    @test (@inferred x + 1.0) isa Float64
    @test (@inferred Base.decompose(x)) isa Tuple{Int, Int, Int}
    @test (@inferred hash(x)) isa UInt
    @test (@inferred AIFloats.order_key(x)) isa UInt16
    @test (@inferred zero(B8)) isa B8 && (@inferred one(B8)) isa B8
    v = B8.(randn(MersenneTwister(4), 300))
    @test (@inferred sort!(v)) isa Vector{B8}
    @test issorted(v; lt = isless)
    @test (@inferred sum(v)) isa B8
end

@testset "Integer conversion is exact at every width" begin
    # implmentplan.md Step 3: |x| ≤ 2^53 widens exactly to Float64 and skips
    # the BigFloat route. The reference is that BigFloat route itself, at a
    # width that cannot round anything.
    refconvert(F, ρ, n) = Convert(F, ρ, setprecision(() -> BigFloat(n), BigFloat, 4096))
    ints = vcat(collect(-300:300),
                [2^53 - 1, 2^53, 2^53 + 1, -2^53 - 1,
                 typemax(Int64), typemin(Int64), typemax(UInt64),
                 big(2)^80, -big(2)^80, UInt8(3), Int8(-7), Int16(-1), true, false])
    for F in (F8, F9, Binary(8, 1, UNSIGNED, FINITE), Binary(6, 3, SIGNED, EXTENDED)),
        ρ in (RTE_SN, RTZ_SF, RTP_SN, RTN_SF, RTA_SP),
        n in ints
        @test Convert(F, ρ, n) === refconvert(F, ρ, n)
    end
    # the constructor seam agrees with Convert under the session default
    for n in (-3, 0, 3, 17, 2^53, -2^53)
        @test B8(n) === Convert(F8, DefaultProjection(), n)
    end

    # float128use.md §2: a Float128 rung sits between the Float64 gate and the
    # BigFloat route. Its predicate is significant bits after the trailing
    # zeroes, NOT magnitude — 2^10000 is exactly representable and must be
    # accepted, a 114-bit odd significand must not.
    @test AIFloats._exact_in_float128(0)
    @test AIFloats._exact_in_float128(big(2)^113)
    @test AIFloats._exact_in_float128(big(2)^10000)          # magnitude alone would reject
    @test AIFloats._exact_in_float128(big(2)^113 - 1)        # exactly 113 significant bits
    @test !AIFloats._exact_in_float128(big(2)^114 + 1)       # 115 significant bits
    @test !AIFloats._exact_in_float128(big(2)^20000)         # past the exponent range
    @test AIFloats._exact_in_float128(typemax(Int64))        # 63 significant bits
    @test AIFloats._exact_in_float128(typemin(Int64))
    @test AIFloats._exact_in_float128(typemax(UInt64))
    # whenever it accepts, the Float128 value must equal the integer exactly
    let rng = MersenneTwister(11)
        pool = vcat([big(2)^k for k in 0:400], [big(2)^k + 1 for k in 0:400],
                    [big(rand(rng, Int64)) * big(2)^rand(rng, 0:300) for _ in 1:400],
                    [rand(rng, Int128) for _ in 1:400])
        for x in pool
            AIFloats._exact_in_float128(x) || continue
            v = Float128(x)
            @test isfinite(v)
            @test Rational{BigInt}(setprecision(() -> BigFloat(v), BigFloat, 20000)) ==
                  Rational{BigInt}(big(x))
        end
    end
    # and the whole ladder still equals a reference that never leaves MPFR
    let ref(F, ρ, n) = project(F, ρ, setprecision(() -> BigFloat(n), BigFloat, 20000)),
        wide = [2^53 + 1, -2^53 - 1, typemax(Int64), typemin(Int64), typemax(UInt64),
                typemax(Int128), typemin(Int128), big(2)^113, big(2)^113 + 1,
                big(2)^114 + 1, big(2)^200, big(2)^200 + 1, big(2)^16383,
                big(2)^20000, -big(2)^200]
        for F in (F8, F9, Binary(16, 5, SIGNED, EXTENDED)),
            ρ in (RTE_SN, RTZ_SF, RTP_SN, RTN_SF, RTA_SP), n in wide
            @test codepoint(Convert(F, ρ, n)) == codepoint(ref(F, ρ, n))
        end
    end
end
