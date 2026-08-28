using AIFloats
using Test
using AIFloats: round_to_precision, _rtp_core, _rtp_f64, _rtp_dyadic, _rtp_zero_sticky,
                Rounded, Dyadic, ρRSA, ρRSB, ρRSC

# The bit path (_rtp_f64), the fixed-point Dyadic path (_rtp_dyadic) and the
# zero-with-sticky row are pinned BIT-IDENTICAL to the generic core (_rtp_core)
# — the semantics — over every (P, B) cell of the grid, every rounding mode
# (stochastic at N ∈ {1, 3, 8, 60}, every R for small N), both stickies, and a
# structured input set that lands on and beside every rounding boundary.

const MODES = (RTE, RTA, RTP, RTN, RTZ, RTO,
               ρRSA(1), ρRSA(3), ρRSA(8), ρRSA(60), ρRSB(3), ρRSB(60), ρRSC(3), ρRSC(60))
rs(μ) = isstochastic(μ) ? (nrandbits(μ) <= 3 ? collect(0:(2^nrandbits(μ) - 1)) : [0, 1, 2^nrandbits(μ) - 1, 12345 & (2^nrandbits(μ) - 1)]) : [0]

# every (P, B) cell of the grid, once
function cells()
    seen = Set{Tuple{Int, Int}}()
    out = Tuple{Int, Int}[]
    for (_, BV) in AIFloats._NAMED
        c = (Int(PrecisionOf(BV)), ExponentBiasOf(BV))
        c in seen || (push!(seen, c); push!(out, c))
    end
    sort!(out)
end

# structured normal Float64 inputs around a grid with precision P and bias B
function inputs(P, B)
    xs = Float64[]
    for e in (-B - P - 2, -B - P, 1 - B - P, 2 - B - P, 1 - B, 2 - B, -3, -1, 0, 1, 3, B - 2, B - 1, B, B + 2)
        -1074 < e < 1023 || continue
        b = 2.0^e
        step = 2.0^(e - P + 1)                    # the target grid step in this binade
        for k in (0, 1, 2, 3), f in (0.0, 0.25, 0.5, 0.75, 0.5 - 2.0^-40, 0.5 + 2.0^-40)
            v = b + k * step + f * step
            isfinite(v) && v > 0 && push!(xs, v, -v)
        end
        push!(xs, nextfloat(b), prevfloat(b), 1.5b, -1.5b, b * (1 + 2.0^-52))
    end
    append!(xs, (1.0, -1.0, 0.1, 1.0e300, -1.0e300, 2.2250738585072014e-308))
    unique!(filter!(x -> isfinite(x) && !iszero(x) && abs(x) >= 2.2250738585072014e-308, xs))
end

@testset "bit path ≡ generic core (Float64)" begin
    ncmp = 0
    for (P, B) in cells(), μ in MODES, R in rs(μ), sticky in (-1, 0, 1), x in inputs(P, B)
        @test _rtp_f64(P, B, μ, x, R, sticky) === _rtp_core(P, B, μ, x, R, sticky)
        ncmp += 1
    end
    @info "bit ≡ generic comparisons" ncmp
    # the entry point routes specials, zero and subnormals to the core
    for (P, B) in cells()[1:8], μ in (RTE, RTP, ρRSA(3)), sticky in (-1, 0, 1), x in (0.0, Inf, -Inf, NaN, 5.0e-324, -2.0e-310)
        @test round_to_precision(P, B, μ, x, 0, sticky) === _rtp_core(P, B, μ, x, 0, sticky)
    end
end

@testset "Dyadic path ≡ generic core" begin
    ncmp = 0
    for (P, B) in cells(), μ in MODES, R in rs(μ), sticky in (-1, 0, 1), x in inputs(P, B)
        d = Dyadic(x)
        @test _rtp_dyadic(P, B, μ, d, R, sticky) === _rtp_core(P, B, μ, x, R, sticky)
        # and against the BigFloat core, on a spelling with un-normalized fields
        d2 = Dyadic(d.S << 5, d.Q - 5)
        @test _rtp_dyadic(P, B, μ, d2, R, sticky) === _rtp_core(P, B, μ, BigFloat(x), R, sticky)
        ncmp += 2
    end
    @info "Dyadic ≡ generic comparisons" ncmp
    # wide Dyadic values beyond Float64 (the rung-3 range) against the BigFloat core
    for (P, B) in ((1, 16384), (2, 8192), (4, 2048)), μ in MODES, R in rs(μ)[1:min(end, 4)], sticky in (-1, 0, 1)
        for (S, Q) in ((3, 20000), (5, -20000), (1, 16382), (7, -16400), (Int128(2)^40 + 1, 8000), (-9, 16000))
            d = Dyadic(S, Q)
            b = setprecision(() -> BigFloat(d), BigFloat, 128)
            @test round_to_precision(P, B, μ, d, R, sticky) === _rtp_core(P, B, μ, b, R, sticky)
        end
    end
    # the zero-with-sticky row
    for (P, B) in cells(), μ in MODES, R in rs(μ), sticky in (-1, 0, 1)
        @test _rtp_zero_sticky(P, B, μ, R, sticky) === _rtp_core(P, B, μ, 0.0, R, sticky)
        @test round_to_precision(P, B, μ, Dyadic(0, 0), R, sticky) === _rtp_core(P, B, μ, 0.0, R, sticky)
    end
    # specials
    for (P, B) in cells()[1:4], sticky in (-1, 0, 1)
        @test round_to_precision(P, B, RTE, AIFloats._cinf(Dyadic), 0, sticky) === _rtp_core(P, B, RTE, Inf, 0, sticky)
        @test round_to_precision(P, B, RTE, AIFloats._cninf(Dyadic), 0, sticky) === _rtp_core(P, B, RTE, -Inf, 0, sticky)
        @test round_to_precision(P, B, RTE, AIFloats._cnan(Dyadic), 0, sticky) === _rtp_core(P, B, RTE, NaN, 0, sticky)
    end
end

@testset "carrier agreement on code points, incl. Dyadic" begin
    for F in (Binary(8, 4, SIGNED, EXTENDED), Binary(5, 2, UNSIGNED, FINITE), Binary(16, 4, SIGNED, EXTENDED))
        for ρ in (RTE_SN, RTP_SF, RTZ_SP, RTO_SN, Projection(ρRSA(4), SN)), x in inputs(Int(PrecisionOf(F)), ExponentBiasOf(F)), R in (0, 5)
            c64 = project(F, ρ, x; R)
            @test project(F, ρ, Dyadic(x); R) === c64
            @test project(F, ρ, BigFloat(x); R) === c64
        end
    end
end
