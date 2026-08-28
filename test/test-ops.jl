using AIFloats
using Test
using Random

@isdefined(RefImpl) || include(joinpath(@__DIR__, "support", "refimpl.jl"))
using .RefImpl

# exact dyadic arithmetic on canonical (num, q2) pairs — the reference side
_dyadd(n1, q1, n2, q2) = q1 >= q2 ? (n1 << (q1 - q2) + n2, q2) : (n1 + n2 << (q2 - q1), q1)
_dymul(n1, q1, n2, q2) = (n1 * n2, q1 + q2)

function _refbincode(op::Symbol, F, msym, ssym, c1, c2)
    k1, s1, S1, Q1 = AIFloats._canonical(F, c1)
    k2, s2, S2, Q2 = AIFloats._canonical(F, c2)
    P = Int(PrecisionOf(F)); B = ExponentBiasOf(F)
    info = (P = P, B = B, signed = Bool(SignednessOf(F)), extended = Bool(DomainOf(F)),
            nan = Int(AIFloats.nan_code(F)), pinf = Int(AIFloats.posinf_code(F)),
            ninf = Int(AIFloats.neginf_code(F)),
            maxfin = Int(AIFloats._maxfinite_code(F)),
            minfin = Int(AIFloats._minfinite_code(F)), K = Int(BitwidthOf(F)))
    # special operands: mirror the ω rows exactly. _canonical spells the kinds
    # :posinf/:neginf; RefImpl spells them :pinf/:ninf — translate.
    refkind(k) = k === :posinf ? :pinf : k === :neginf ? :ninf : k
    k1, k2 = refkind(k1), refkind(k2)
    if k1 === :nan || k2 === :nan
        return info.nan
    end
    if op === :Add || op === :Subtract
        s2eff, k2eff = op === :Subtract ?
            (-s2, k2 === :pinf ? :ninf : k2 === :ninf ? :pinf : k2) : (s2, k2)
        if k1 !== :finite || k2eff !== :finite
            if k1 !== :finite && k2eff !== :finite
                k1 === k2eff || return info.nan             # ∞ + (−∞)
                return refsaturate_code(RefImpl.RefRounded(k1, 0, big(0), 0),
                                        msym, ssym; info...)
            end
            k = k1 !== :finite ? k1 : k2eff
            return refsaturate_code(RefImpl.RefRounded(k, 0, big(0), 0),
                                    msym, ssym; info...)
        end
        n, q = _dyadd(s1 * big(S1), Int(Q1), s2eff * big(S2), Int(Q2))
        r = refround(P, B, msym, 0, 0, n, q)
        return refsaturate_code(r, msym, ssym; info...)
    elseif op === :Multiply
        if k1 !== :finite || k2 !== :finite
            z1 = k1 === :finite && S1 == 0
            z2 = k2 === :finite && S2 == 0
            (z1 || z2) && return info.nan                   # 0 · ∞
            neg = (k1 === :ninf) ⊻ (k2 === :ninf) ⊻
                  (k1 === :finite && s1 < 0) ⊻ (k2 === :finite && s2 < 0)
            return refsaturate_code(RefImpl.RefRounded(neg ? :ninf : :pinf, 0, big(0), 0),
                                    msym, ssym; info...)
        end
        (S1 == 0 || S2 == 0) && return 0
        n, q = _dymul(s1 * big(S1), Int(Q1), s2 * big(S2), Int(Q2))
        r = refround(P, B, msym, 0, 0, n, q)
        return refsaturate_code(r, msym, ssym; info...)
    end
    error("unhandled $op")
end

@testset "Group A vs the BigInt reference, exhaustive K ≤ 5" begin
    modes = [(:RTE, RTE), (:RTZ, RTZ), (:RTN, RTN), (:RTO, RTO)]
    sats = [(:SN, SN), (:SF, SF), (:SP, SP)]
    ncmp = 0
    for K in 3:5, P in 1:K, Sg in (true, false), E in (true, false)
        Sg && P >= K && continue
        F = AIFloats.Binary(K, P, Sg, E)
        BV = BinaryValue(F)
        n = 2^K
        for c1 in 0:(n - 1), c2 in 0:(n - 1)
            x = BV(UInt8(c1)); y = BV(UInt8(c2))
            for (msym, μ) in modes, (ssym, sm) in sats
                ρ = Projection(μ, sm)
                for (opn, opf) in ((:Add, Add), (:Subtract, Subtract), (:Multiply, Multiply))
                    got = Int(codepoint(opf(F, ρ, x, y)))
                    want = _refbincode(opn, F, msym, ssym, UInt8(c1), UInt8(c2))
                    @test got == want
                    ncmp += 1
                end
            end
        end
    end
    @info "Group A comparisons vs reference" ncmp
end

@testset "Totality at every rung" begin
    # G10-style: every registry op returns a BinaryValue at every carrier rung,
    # on ordinary datums and on specials — a path that throws is the defect
    reps = [AIFloats.Binary(8, 4, SIGNED, EXTENDED),      # rung 1, Float64
            AIFloats.Binary(16, 5, SIGNED, EXTENDED),     # rung 2, Float128
            AIFloats.Binary(16, 1, UNSIGNED, FINITE)]     # rung 3, exact carrier
    for F in reps
        BV = BinaryValue(F)
        U = CodeType(F)
        probe = [BV(zero(U)), MinPositiveOf(F), MinNormalOf(F), MaxFiniteOf(F),
                 BV(AIFloats.nan_code(F))]
        is_extended(F) && push!(probe, BV(AIFloats.posinf_code(F)))
        # a mid-range datum: halfway up the positive codes
        push!(probe, BV(U(AIFloats._maxfinite_code(F) >> 1)))
        for op in AIFloats.OP_REGISTRY
            op.name === :Convert && continue
            f = getfield(AIFloats, op.name)
            for x in probe
                if op.arity == 1
                    @test f(F, RTE_SN, x) isa BinaryValue
                elseif op.arity == 2
                    @test f(F, RTE_SN, x, probe[end]) isa BinaryValue
                else
                    @test f(F, RTE_SN, x, probe[end], probe[1]) isa BinaryValue
                end
            end
        end
        # Convert across the rungs, both directions
        G = AIFloats.Binary(8, 3, UNSIGNED, FINITE)
        for x in probe
            @test Convert(G, RTE_SF, x) isa BinaryValue
        end
        @test Convert(F, RTE_SN, 1.5) isa BinaryValue
    end
end

@testset "Known values" begin
    F = AIFloats.Binary(8, 4, SIGNED, EXTENDED)
    BV = binary8p4se
    @test decode(Add(F, RTE_SN, BV(1.5), BV(0.25))) == 1.75
    @test decode(Divide(F, RTE_SN, BV(1.0), BV(8.0))) == 0.125
    @test isnan(decode(Divide(F, RTE_SN, BV(1.0), BV(0x00))))   # x/0: one zero, no sign
    @test decode(Sqrt(F, RTE_SN, BV(4.0))) == 2.0
    @test decode(Recip(F, RTE_SN, BV(8.0))) == 0.125
    @test decode(RSqrt(F, RTE_SN, BV(4.0))) == 0.5
    # correctly rounded transcendentals: e, ln 2, on the 1/16 grid of [2,4)/[0.5,1)
    @test decode(Exp(F, RTE_SN, BV(1.0))) == 2.75               # e = 2.718… → 2.75
    @test decode(Log(F, RTE_SN, BV(2.0))) == 0.6875             # ln2 = .6931… → 11/16
    @test decode(Exp2(F, RTE_SN, BV(3.0))) == 8.0               # exact peel
    @test decode(Log2(F, RTE_SN, BV(8.0))) == 3.0               # exact peel
    @test decode(Sin(F, RTE_SN, BV(1.0))) == 0.8125             # sin 1 = .8414… → 13/16
    @test decode(SinPi(F, RTE_SN, BV(0.5))) == 1.0
    @test decode(CosPi(F, RTE_SN, BV(1.0))) == -1.0
    @test decode(TanPi(F, RTE_SN, BV(0.25))) == 1.0
    @test isnan(decode(TanPi(F, RTE_SN, BV(0.5))))
    @test decode(ArcTan(F, RTE_SN, BV(1.0))) == 0.8125          # π/4 = .7853… → 13/16
    @test decode(Hypot(F, RTE_SN, BV(3.0), BV(4.0))) == 5.0
    @test decode(Softplus(F, RTE_SN, BV(0x00))) == 0.6875       # ln 2 again
    @test decode(FMA(F, RTE_SN, BV(1.5), BV(0.25), BV(1.0))) == 1.375
    @test decode(FAA(F, RTE_SN, BV(1.5), BV(0.25), BV(1.0))) == 2.75
    @test decode(Clamp(F, RTE_SN, BV(3.0), BV(1.0), BV(2.0))) == 2.0
    # extremum family corner semantics
    nanv = BV(AIFloats.nan_code(F))
    pinf = BV(AIFloats.posinf_code(F))
    @test isnan(decode(Maximum(F, RTE_SN, BV(1.0), nanv)))
    @test decode(MaximumNumber(F, RTE_SN, BV(1.0), nanv)) == 1.0
    @test decode(MaximumMagnitude(F, RTE_SN, BV(-2.0), BV(1.5))) == -2.0
    @test decode(MaximumFinite(F, RTE_SN, pinf, BV(1.0))) == 1.0
    @test decode(MaximumFinite(F, RTE_SN, pinf, nanv)) == Inf        # draft §4.11.3: ∞ beats NaN
    @test decode(Minimum(F, RTE_SN, BV(1.0), BV(-2.0))) == -2.0
end

@testset "Session defaults and value construction" begin
    old = DefaultProjection()
    try
        BV = binary8p4se
        @test DefaultProjection() === RTE_SN
        @test decode(Add(BV(1.5), BV(0.25))) == 1.75            # same-format convenience
        DefaultRoundingMode!(RTZ)
        @test DefaultProjection() === RTZ_SN
        @test DefaultSaturationMode() === SN
        DefaultSaturationMode!(SF)
        @test DefaultProjection() === RTZ_SF
        DefaultProjection!(RTE, SN)
        @test DefaultRoundingMode() === RTE

        @test BV(1.6) === Convert(BV, RTE_SN, 1.6)              # default ρ route
        @test decode(BV(1.6; projection = RTZ_SF)) == 1.5
        @test BV(3) === BV(3.0)
        @test_throws ArgumentError Convert(BV, RTE_SF, 1 // 3)
        @test_throws ArgumentError Convert(BV, RTE_SF, π)
    finally
        DefaultProjection!(old)
    end
end

@testset "rand / randn" begin
    v = rand(Xoshiro(7), binary8p4uf)
    @test v isa binary8p4uf
    @test 0.0 <= decode(v) < 1.0
    @test rand(Xoshiro(7), binary8p4uf) === v                    # reproducible
    A = rand(Xoshiro(9), binary8p4uf, 100)
    @test eltype(A) === binary8p4uf
    @test all(x -> 0.0 <= decode(x) < 1.0, A)
    r = randn(Xoshiro(3), binary8p4se)
    @test isfinite(decode(r))                                    # RTE_SF clamps tails
    @test randn(Xoshiro(3), binary8p4se) === r
    @test_throws ArgumentError randn(binary8p4uf)
    # stochastic conversion draws from the supplied rng: seeded streams agree
    a = Convert(binary8p4se, Projection(AIFloats.ρRSA(8), SF), 1.3; rng = Xoshiro(1))
    b = Convert(binary8p4se, Projection(AIFloats.ρRSA(8), SF), 1.3; rng = Xoshiro(1))
    @test a === b
end
