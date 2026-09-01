using AIFloats
using Test

using Random
using Quadmath: Float128
using BFloat16s: BFloat16
using AIFloats: DyadicNumbers, Dyadic, lift, rung, HeadF64, HeadF128, HeadExact, fma128, faa128

@testset "constructor invariants" begin
    @test_throws ArgumentError Dyadic(Int128(0), Int64(0), UInt8(0xff))
    @test_throws ArgumentError Dyadic(Int128(1), Int64(0), AIFloats.DyadicNumbers.DY_NAN)
    @test isnan(Dyadic(AIFloats.DyadicNumbers.DY_NAN))
end

# The adapted Dyadic carrier is the ORIGINAL: golden digests captured from
# SmallFloats' DyadicNumbers (test/support/dyadic_golden.sha256) must match
# byte for byte (plan §9.9). Then the carrier's own contracts, the lift
# lattice, the per-op rung join, and the vendored Float128 fused ops.

include(joinpath(@__DIR__, "support", "dyadic_digest.jl"))
const GOLDEN = joinpath(@__DIR__, "support", "dyadic_golden.sha256")

@testset "golden digests ≡ SmallFloats' original" begin
    @test isfile(GOLDEN)
    want = Dict{String, String}()
    for line in eachline(GOLDEN)
        (isempty(line) || startswith(line, '#')) && continue
        d, name = split(line)
        want[String(name)] = String(d)
    end
    got = dyadic_digests(DyadicNumbers)
    @test length(got) == length(want) == 3
    for (name, d) in got
        @test (name, d) == (name, want[name])
    end
end

@testset "carrier contracts" begin
    # the add bands cover every (P, N) the grid admits — asserted, not commented
    @test Int(AIFloats.KMAX) + 60 <= DyadicNumbers.DYADIC_ADD_COVERAGE
    @test DyadicNumbers.DYADIC_ALIGN_MAX > Int(AIFloats.KMAX) - 1 + 60 + 2
    @test_throws ArgumentError Dyadic(0x7f)
    x = Dyadic(3, -1)
    @test x == Dyadic(6, -2) && x + x == BigFloat(3) && x * x == BigFloat(2.25)
    @test isless(x, DyadicNumbers.DYADIC_NAN) && !isless(DyadicNumbers.DYADIC_NAN, x)
    @test isnan(max(x, DyadicNumbers.DYADIC_NAN))
    @test_throws ArgumentError DyadicNumbers.add_dy(Dyadic(1, 0), Dyadic(1, -200))
    @test DyadicNumbers.add_sticky_dy(Dyadic(1, 0), Dyadic(1, -200)) == (Dyadic(1, 0), 1)
    @test DyadicNumbers.add_sticky_dy(Dyadic(1, 0), Dyadic(-1, -200)) == (Dyadic(1, 0), -1)
    @test_throws ArgumentError DyadicNumbers.mul_dy_checked(Dyadic(Int128(2)^60, 0), Dyadic(Int128(2)^60, 0))
    # AIFloats additions: the veneers' needs at rung 3
    @test copysign(x, Dyadic(-1, 0)) == Dyadic(-3, -1) && copysign(-x, Dyadic(1, 0)) == Dyadic(3, -1)
    @test significand(Dyadic(12, 0)) == Dyadic(3, -1) && frexp(Dyadic(12, 0)) == (Dyadic(3, -2), 4)
    @test round(Dyadic(5, -1), RoundNearestTiesAway) == Dyadic(3, 0) && round(Dyadic(-5, -1), RoundNearestTiesAway) == Dyadic(-3, 0)
    @test round(Dyadic(5, -1)) == Dyadic(2, 0) && round(Dyadic(3, -1)) == Dyadic(2, 0)
    @test Int(Dyadic(7, 1)) == 14 && Bool(Dyadic(1, 0))
    @test Float128(Dyadic(3, -1)) == Float128(1.5)
    # exactness of the decode→Dyadic seam over every datum of a rung-3 format
    F = Binary(16, 1, SIGNED, EXTENDED)
    for c in 0:(2^16 - 1)
        v = fromcode(F, c)
        d = decode(v)
        @test d isa Dyadic
        isfinite(v) && @test Rational{BigInt}(d) == Rational{BigInt}(BigFloat(d))
    end
end

@testset "lift is upward only; rung(op) is the join" begin
    @test lift(HeadF64(), 1.5) === 1.5
    @test lift(HeadF128(), 1.5) === Float128(1.5)
    @test lift(HeadExact(), 1.5) == Dyadic(3, -1)
    @test lift(HeadExact(), Float128(1.5)) == Dyadic(3, -1)
    @test lift(HeadExact(), BigFloat(1.5)) == Dyadic(3, -1)
    @test !hasmethod(lift, Tuple{HeadF64, Float128})
    @test !hasmethod(lift, Tuple{HeadF64, BigFloat})
    @test !hasmethod(lift, Tuple{HeadF128, BigFloat})
    F8 = Binary(8, 4, SIGNED, EXTENDED); U1 = Binary(8, 1, UNSIGNED, FINITE)
    W = Binary(16, 5, SIGNED, EXTENDED)          # B = 1024: rung 2 alone
    @test rung(Val(:Add), F8, F8) === rung(F8) === HeadF64()
    @test rung(Val(:Multiply), F8, U1) === HeadF64()          # 2·128 ≤ 1024
    @test rung(Val(:Multiply), W, W) === HeadF128()           # 2·1024 ≤ 16384
    @test rung(Val(:Abs), W) === HeadF128()                    # operand bound dominates
    @test rung(Val(:Multiply), W, Binary(16, 1, SIGNED, EXTENDED)) === HeadExact()
    @test rung(Val(:Multiply), F8, Binary(16, 1, SIGNED, EXTENDED)) === HeadExact()
    for (_, F) in AIFloats._NAMED
        # _NAMED holds FORMAT types (improveapi.md §4.1.2); these
        # assertions are about the datum type
        BV = BinaryValue(F)
        F = BinaryFormatOf(BV)
        @test rung(Val(:Multiply), F, F) === rung(F)
        @test AIFloats.carriertype(rung(F)) === AIFloats.datumcarrier(F)
    end
end

@testset "fma128 / faa128 vs libquadmath and an exact reference" begin
    rng = MersenneTwister(11)
    specials = Float128[0, -0.0, 1, -1, Inf, -Inf, NaN, floatmax(Float128), floatmin(Float128),
                        nextfloat(zero(Float128)), Float128(2)^-113, Float128(2)^-226]
    rnd = [Float128(randn(rng)) * Float128(2)^rand(rng, -200:200) for _ in 1:60]
    vals = vcat(specials, rnd)
    # exact reference precision from the operands' exponent span, never a constant
    function refprec(xs...)
        es = [exponent(v) for v in xs if isfinite(v) && !iszero(v)]
        isempty(es) ? 256 : 2 * (maximum(es) - minimum(es)) + 4 * 113 + 64
    end
    n = 0
    for x in vals, y in vals, z in vals[1:20]
        r = fma128(x, y, z)
        if Sys.iswindows()
            (isnan(x) | isnan(y) | isnan(z)) && continue
        else
            @test isequal(r, fma(x, y, z)) || (isnan(r) && isnan(fma(x, y, z)))
        end
        n += 1
    end
    @test n > 0
    # exact reference: one rounding of the exact value (finite, in-range operands)
    for x in rnd, y in rnd[1:20], z in rnd[1:10]
        want = setprecision(() -> Float128(BigFloat(x) * BigFloat(y) + BigFloat(z)), BigFloat, refprec(x, y, z))
        @test isequal(fma128(x, y, z), want)
    end
    for x in vals, y in vals[1:24], z in vals[1:12]
        r = faa128(x, y, z)
        if isfinite(x) && isfinite(y) && isfinite(z)
            want = setprecision(() -> Float128(BigFloat(x) + BigFloat(y) + BigFloat(z)), BigFloat, refprec(x, y, z))
            @test isequal(r, want) || (iszero(r) && iszero(want))
        else
            hasp = any(v -> isinf(v) && v > 0, (x, y, z)); hasn = any(v -> isinf(v) && v < 0, (x, y, z))
            anynan = any(isnan, (x, y, z))
            @test (anynan || (hasp && hasn)) ? isnan(r) : (hasp ? r == Inf : r == -Inf)
        end
    end
    @test faa128(Float128(1), Float128(2)^-113, Float128(2)^-226) == nextfloat(Float128(1))
end

@testset "Float128/BFloat16 from Dyadic take the exact route" begin
    # float128use.md §5: heads.jl built these as `T(BigFloat(x))`, skipping
    # `_dyadic_to`'s exact branch — 196 ns and 13 allocations where the
    # identical Float64 method already managed 3.3 ns. Delegating must not
    # change a single value, including at the rounding boundaries where
    # `_dyadic_to` deliberately falls back through BigFloat.
    D = AIFloats.DyadicNumbers
    wide(d) = setprecision(() -> BigFloat(d), BigFloat, 4096)
    rng = MersenneTwister(3)
    for _ in 1:20000
        d = D.Dyadic(Int128(rand(rng, Int64)), rand(rng, -200:200))
        @test isequal(Float128(d), Float128(wide(d)))
        @test isequal(BFloat16(d), BFloat16(wide(d)))
    end
    for d in (D.DYADIC_ZERO, D.DYADIC_ONE, D.DYADIC_POSINF, D.DYADIC_NEGINF, D.DYADIC_NAN,
              D.Dyadic(Int128(1), Int64(-16500)),   # below Float128's subnormal floor
              D.Dyadic(Int128(1), Int64(16380)),    # near its top
              D.Dyadic(Int128(-1), Int64(-16500)),
              D.Dyadic(typemax(Int128), Int64(0)),  # 127 significant bits: must round once
              D.Dyadic(typemin(Int128), Int64(0)))
        @test isequal(Float128(d), Float128(wide(d)))
        @test isequal(BFloat16(d), BFloat16(wide(d)))
    end
end
