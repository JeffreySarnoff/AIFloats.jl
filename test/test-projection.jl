using AIFloats
using Test

@isdefined(RefImpl) || include(joinpath(@__DIR__, "support", "refimpl.jl"))
using .RefImpl

# the Phase 2 gate: the projection engine against the independent BigInt
# reference, over every (P, B) cell of the K ≤ 8 grid, every mode, and a value
# set that hits grid points, midpoints, off-midpoints, the subnormal floor,
# the binade carry, and the saturation boundary — as exact dyadic rationals.

const DET_MODES = [(:RTE, RTE), (:RTA, RTA), (:RTP, RTP), (:RTN, RTN),
                   (:RTZ, RTZ), (:RTO, RTO)]
const STO_N = 3
const STO_MODES = [(:RSA, AIFloats.ρRSA(STO_N)), (:RSB, AIFloats.ρRSB(STO_N)),
                   (:RSC, AIFloats.ρRSC(STO_N))]

# dyadic test values for a (P, B) cell: (num, q2) with value = num · 2^q2
function cellvalues(P::Int, B::Int)
    vals = Tuple{BigInt,Int}[]
    Qsub = 2 - B - P                       # the subnormal/lowest-normal grid exponent
    # eighth-step offsets around every grid significand, at the subnormal
    # binade, a mid binade, and the top binade
    for Q in unique([Qsub, min(-P + 1, (B - 1) - P), (B - 1) - P + 1])
        for S in BigInt(0):(BigInt(1) << P) - 1
            base = S << 3                  # value = (8S + o) · 2^(Q-3), o ∈ 0:7
            for o in (0, 1, 2, 3, 4, 5, 6, 7)
                push!(vals, (base + o, Q - 3))
            end
        end
        # the binade-carry midpoint: (2^P − ½)·2^Q
        push!(vals, (((BigInt(1) << P) << 1) - 1, Q - 1))
    end
    # around zero and the saturation boundary
    push!(vals, (BigInt(1), Qsub - 7))     # deep underflow
    push!(vals, (BigInt(1), B + 3))        # far overflow
    vals
end

@testset "Rounding vs the BigInt reference" begin
    cells = Set{Tuple{Int,Int,Bool,Bool}}()
    for K in 3:8, P in 1:K, S in (true, false), E in (true, false)
        S && P >= K && continue
        F = AIFloats.Binary(K, P, S, E)
        push!(cells, (Int(PrecisionOf(F)), ExponentBiasOf(F), S, E))
    end
    ncmp = 0
    for (P, B, S, E) in cells
        for (num, q2) in cellvalues(P, B), sgn in (1, -1)
            n = sgn * num
            v = dyadic_to_bigfloat(n, q2)
            for (msym, μ) in DET_MODES
                ref = refround(P, B, msym, 0, 0, n, q2)
                got = AIFloats._rtp_core(P, B, μ, v, 0, 0)
                if ref.S == 0
                    @test got.kind == AIFloats.KIND_FIN && got.S == 0
                else
                    @test got.kind == AIFloats.KIND_FIN
                    @test (Int(got.sign), BigInt(got.S), Int(got.Q)) ==
                          (ref.sign, ref.S, ref.Q)
                end
                ncmp += 1
            end
            for (msym, μ) in STO_MODES, R in 0:(2^STO_N - 1)
                ref = refround(P, B, msym, STO_N, R, n, q2)
                got = AIFloats._rtp_core(P, B, μ, v, R, 0)
                if ref.S == 0
                    @test got.kind == AIFloats.KIND_FIN && got.S == 0
                else
                    @test (Int(got.sign), BigInt(got.S), Int(got.Q)) ==
                          (ref.sign, ref.S, ref.Q)
                end
                ncmp += 1
            end
        end
    end
    @info "rounding comparisons vs reference" ncmp cells = length(cells)
end

@testset "Projection vs the BigInt reference, end to end" begin
    sats = [(:SF, SF), (:SP, SP), (:SN, SN)]
    ncmp = 0
    for K in 3:8, P in 1:K, S in (true, false), E in (true, false)
        S && P >= K && continue
        F = AIFloats.Binary(K, P, S, E)
        B = ExponentBiasOf(F)
        info = (P = P, B = B, signed = S, extended = E,
                nan = Int(AIFloats.nan_code(F)),
                pinf = Int(AIFloats.posinf_code(F)),
                ninf = Int(AIFloats.neginf_code(F)),
                maxfin = Int(AIFloats._maxfinite_code(F)),
                minfin = Int(AIFloats._minfinite_code(F)), K = K)
        # a leaner value set for the end-to-end sweep
        vals = Tuple{BigInt,Int}[]
        for (num, q2) in cellvalues(P, B)
            push!(vals, (num, q2))
        end
        for (num, q2) in vals, sgn in (1, -1)
            n = sgn * num
            v = dyadic_to_bigfloat(n, q2)
            for (msym, μ) in DET_MODES, (ssym, sm) in sats
                ρ = Projection(μ, sm)
                got = codepoint(project(F, ρ, v))
                ref = refround(P, B, msym, 0, 0, n, q2)
                want = refsaturate_code(ref, msym, ssym; info...)
                @test Int(got) == want
                ncmp += 1
            end
        end
        # specials through the whole pipeline
        for (msym, μ) in DET_MODES, (ssym, sm) in sats
            ρ = Projection(μ, sm)
            @test Int(codepoint(project(F, ρ, BigFloat(NaN)))) == info.nan
            wantp = refsaturate_code(RefImpl.RefRounded(:pinf, 1, big(0), 0),
                                     msym, ssym; info...)
            wantn = refsaturate_code(RefImpl.RefRounded(:ninf, -1, big(0), 0),
                                     msym, ssym; info...)
            @test Int(codepoint(project(F, ρ, BigFloat(Inf)))) == wantp
            @test Int(codepoint(project(F, ρ, BigFloat(-Inf)))) == wantn
            ncmp += 3
        end
    end
    @info "end-to-end projections vs reference" ncmp
end

@testset "Carrier agreement" begin
    # the same value through Float64, Float128, and BigFloat lands on the same
    # code point, for every mode — the generic core is carrier-independent
    F = AIFloats.Binary(8, 4, SIGNED, EXTENDED)
    vals64 = [0.0, 1.0, 1.5625, 1.6, -2.7, 224.0, 240.0, 1e-3, -1e-9, 1e9]
    for v in vals64, (_, μ) in vcat(DET_MODES, STO_MODES), sm in (SF, SP, SN)
        ρ = Projection(μ, sm)
        c64 = codepoint(project(F, ρ, v; R = 5))
        c128 = codepoint(project(F, ρ, binary128(v); R = 5))
        cbig = codepoint(project(F, ρ, BigFloat(v); R = 5))
        @test c64 == c128 == cbig
    end
end

@testset "Idempotence on datums" begin
    # projecting a format's own datum is the identity, for every deterministic
    # mode and saturation — over every datum of representative formats
    for F in (AIFloats.Binary(8, 4, SIGNED, EXTENDED),
              AIFloats.Binary(8, 3, UNSIGNED, FINITE),
              AIFloats.Binary(6, 5, SIGNED, FINITE),
              AIFloats.Binary(5, 1, UNSIGNED, EXTENDED))
        BV = BinaryValue(F)
        for c in 0x00:AIFloats.codemask(F)
            x = BV(c)
            v = decode(x)
            for (_, μ) in DET_MODES, sm in (SF, SP, SN)
                isnan(v) && continue
                # SatFinite clamps a genuine Inf datum; skip that lone row
                (isinf(v) && sm === SF) && continue
                @test codepoint(project(F, Projection(μ, sm), v)) == c
            end
        end
    end
end

@testset "Interval oracle" begin
    F = AIFloats.Binary(8, 4, SIGNED, EXTENDED)
    fpi(prec) = setprecision(BigFloat, prec) do
        (setrounding(() -> BigFloat(π), BigFloat, RoundDown),
         setrounding(() -> BigFloat(π), BigFloat, RoundUp))
    end
    @test decode(AIFloats.project_interval(F, RTE_SF, fpi)) == 3.25
    @test decode(AIFloats.project_interval(F, RTZ_SF, fpi)) == 3.0
    @test decode(AIFloats.project_interval(F, RTP_SF, fpi)) == 3.25
    @test decode(AIFloats.project_interval(F, RTN_SF, fpi)) == 3.0
    # stochastic at fixed R resolves too (monotone at fixed R)
    for R in (0, 3, 7)
        c = AIFloats.project_interval(F, Projection(AIFloats.ρRSA(3), SF), fpi; R)
        @test decode(c) in (3.0, 3.25)
    end
    # an exact enclosure returns the exact projection
    fone(prec) = (BigFloat(1), BigFloat(1))
    @test decode(AIFloats.project_interval(F, RTE_SF, fone)) == 1.0
end

@testset "Stochastic expectation" begin
    # unbiased in expectation over the full draw space, at the sub-grid the
    # budget defines
    F = AIFloats.Binary(4, 2, UNSIGNED, FINITE)
    ρ = Projection(AIFloats.ρRSA(8), SF)
    vals = [decode(project(F, ρ, 1.3; R = r)) for r in 0:255]
    @test all(v -> v in (1.0, 1.5), vals)
    m = sum(vals) / length(vals)
    @test isapprox(m, 1.3; atol = 0.51 / 256 + 1e-9)
end
