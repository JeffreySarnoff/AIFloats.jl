using AIFloats
using Test
using Quadmath: Float128
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
            x = fromcode(BV, c1); y = fromcode(BV, c2)
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
        probe = [fromcode(F, 0), MinPositiveOf(F), MinNormalOf(F), MaxFiniteOf(F),
                 fromcode(BV, AIFloats.nan_code(F))]
        is_extended(F) && push!(probe, fromcode(BV, AIFloats.posinf_code(F)))
        # a mid-range datum: halfway up the positive codes
        push!(probe, fromcode(F, AIFloats._maxfinite_code(F) >> 1))
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
    BV = Binary8p4se
    @test decode(Add(F, RTE_SN, BV(1.5), BV(0.25))) == 1.75
    @test decode(Divide(F, RTE_SN, BV(1.0), BV(8.0))) == 0.125
    @test isnan(decode(Divide(F, RTE_SN, BV(1.0), fromcode(BV, 0x00))))   # x/0: one zero, no sign
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
    @test decode(Softplus(F, RTE_SN, fromcode(BV, 0x00))) == 0.6875       # ln 2 again
    @test decode(FMA(F, RTE_SN, BV(1.5), BV(0.25), BV(1.0))) == 1.375
    @test decode(FAA(F, RTE_SN, BV(1.5), BV(0.25), BV(1.0))) == 2.75
    @test decode(Clamp(F, RTE_SN, BV(3.0), BV(1.0), BV(2.0))) == 2.0
    # extremum family corner semantics
    nanv = fromcode(BV, AIFloats.nan_code(F))
    pinf = fromcode(BV, AIFloats.posinf_code(F))
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
        BV = Binary8p4se
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
    v = rand(Xoshiro(7), BinaryValue(Binary8p4uf))
    @test v isa BinaryValue(Binary8p4uf)
    @test 0.0 <= decode(v) < 1.0
    @test rand(Xoshiro(7), BinaryValue(Binary8p4uf)) === v                    # reproducible
    A = rand(Xoshiro(9), BinaryValue(Binary8p4uf), 100)
    @test eltype(A) === BinaryValue(Binary8p4uf)
    @test all(x -> 0.0 <= decode(x) < 1.0, A)
    r = randn(Xoshiro(3), BinaryValue(Binary8p4se))
    @test isfinite(decode(r))                                    # RTE_SF clamps tails
    @test randn(Xoshiro(3), BinaryValue(Binary8p4se)) === r
    @test_throws ArgumentError randn(BinaryValue(Binary8p4uf))
    # stochastic conversion draws from the supplied rng: seeded streams agree
    a = Convert(Binary8p4se, Projection(AIFloats.ρRSA(8), SF), 1.3; rng = Xoshiro(1))
    b = Convert(Binary8p4se, Projection(AIFloats.ρRSA(8), SF), 1.3; rng = Xoshiro(1))
    @test a === b
end

@testset "exact peels are exact, and stay in their carrier" begin
    # float128use.md §3. These peels exist so the enclosure does not chase an
    # interior grid point forever. They were built as BigFloat, which made each
    # SLOWER than the general path it shortcuts (Log2 499 ns against 29 ns).
    # Built in the incoming carrier they are both exact and fast. C is Float64,
    # Float128 or BigFloat here: Dyadic <: Real, not <: AbstractFloat.
    exact(v) = Rational{BigInt}(setprecision(() -> BigFloat(v), BigFloat, 4096))
    for C in (Float64, Float128, BigFloat)
        for k in -40:40
            p = ldexp(one(C), k)
            (isfinite(p) && !iszero(p)) || continue
            @test exact(AIFloats.ωeval(Val(:Log2), p)) == k
        end
        for n in -60:60
            want = n >= 0 ? Rational{BigInt}(big(2)^n) : 1 // Rational{BigInt}(big(2)^(-n))
            @test exact(AIFloats.ωeval(Val(:Exp2), C(n))) == want
        end
        @test exact(AIFloats.ωeval(Val(:ArcSinPi), one(C)))  ==  1//2
        @test exact(AIFloats.ωeval(Val(:ArcSinPi), -one(C))) == -1//2
        @test exact(AIFloats.ωeval(Val(:ArcCosPi), -one(C))) ==  1//1
        @test exact(AIFloats.ωeval(Val(:ArcCosPi), zero(C))) ==  1//2
        @test exact(AIFloats.ωeval(Val(:ArcTanPi), C(Inf)))  ==  1//2
        @test exact(AIFloats.ωeval(Val(:ArcTanPi), C(-Inf))) == -1//2
        @test exact(AIFloats.ωeval(Val(:ArcTanPi), one(C)))  ==  1//4
        @test exact(AIFloats.ωeval(Val(:ArcTanPi), -one(C))) == -1//4
        @test exact(AIFloats.ωeval(Val(:ArcTan2Pi),  one(C),  one(C))) ==  1//4
        @test exact(AIFloats.ωeval(Val(:ArcTan2Pi),  one(C), -one(C))) ==  3//4
        @test exact(AIFloats.ωeval(Val(:ArcTan2Pi), -one(C),  one(C))) == -1//4
        @test exact(AIFloats.ωeval(Val(:ArcTan2Pi), -one(C), -one(C))) == -3//4
    end

    # Exp2's exact answer can leave the input's carrier while still mattering to
    # a wider result format, so its carrier is chosen by round-trip, never
    # inferred from C. Verify the ladder and that every rung is exact.
    @test AIFloats.ωeval(Val(:Exp2), 3.0)      isa Float64
    @test AIFloats.ωeval(Val(:Exp2), 5000.0)   isa Float128
    @test AIFloats.ωeval(Val(:Exp2), 20000.0)  isa BigFloat
    for n in (1023, 1024, 16383, 16384, 20000, -1074, -1075, -16494, -16495, -20000)
        want = n >= 0 ? Rational{BigInt}(big(2)^n) : 1 // Rational{BigInt}(big(2)^(-n))
        @test exact(AIFloats.ωeval(Val(:Exp2), Float64(n))) == want
    end
    # the peels must not widen a Float64 caller to BigFloat
    @test AIFloats.ωeval(Val(:Log2), 8.0)      isa Float64
    @test AIFloats.ωeval(Val(:ArcTanPi), 1.0)  isa Float64
    @test AIFloats.ωeval(Val(:ArcSinPi), 1.0)  isa Float64
end

@testset "Float128 exactness proofs for the quotient family" begin
    # float128use.md §1/P3. `fma128` is correctly rounded by construction, so
    # `fma128(q, y, -x) == 0` is a genuine proof above the magnitude floor —
    # derived at the constant, not copied from the Float64 one. The MPFR ladder
    # stays as the refusal path and as the reference here.
    A = AIFloats
    exq(v) = Rational{BigInt}(setprecision(() -> BigFloat(v), BigFloat, 20000))

    # whenever a helper ACCEPTS, its value must be exactly right as a rational
    pool = Float128[]
    for (K, P) in ((16, 5), (16, 2), (16, 1))
        F = Binary(K, P, SIGNED, EXTENDED)
        A.datumcarrier(F) === Float128 || continue
        T = BinaryValue(F)
        append!(pool, filter(v -> isfinite(v) && !iszero(v),
                             [decode(fromcode(T, c)) for c in 0:409:2^K-1]))
    end
    append!(pool, Float128[Float128(3), Float128(1)/Float128(3),
                           Float128(2)^100, Float128(2)^-100,
                           Float128(2)^4000, Float128(2)^-4000])
    naccept = 0
    for a in pool, b in pool
        q = A._try_div128(a, b)
        q === nothing && continue
        naccept += 1
        @test exq(q) == exq(a) // exq(b)
    end
    for a in pool
        r = A._try_recip128(a)
        if r !== nothing; naccept += 1; @test exq(r) == 1 // exq(a) end
        a > 0 || continue
        s = A._try_sqrt128(a)
        if s !== nothing; naccept += 1; @test exq(s) * exq(s) == exq(a) end
    end
    @test naccept > 0                       # the proofs must actually fire

    # end to end: identical to the ladder, for every projection
    refdiv(F, ρ, a, b) = A._finish(F, ρ, 0, A._mpfr2(/, decode(a), decode(b)))
    refrec(F, ρ, a)    = A._finish(F, ρ, 0, A.Enclosure(A._ladder1(inv, decode(a))))
    refsqrt(F, ρ, a)   = A._finish(F, ρ, 0, A.Enclosure(A._ladder1(sqrt, decode(a))))
    refrsq(F, ρ, a)    = A._finish(F, ρ, 0, A.Enclosure(A._ladder1(b -> inv(sqrt(b)), decode(a))))
    for (K, P) in ((16, 5), (16, 2))
        F = Binary(K, P, SIGNED, EXTENDED)
        A.datumcarrier(F) === Float128 || continue
        T = BinaryValue(F)
        cs = [fromcode(T, c) for c in 0:1021:2^K-1]
        for ρ in (RTE_SN, RTZ_SF, RTP_SN, RTN_SF, RTO_SN, RTA_SP), a in cs
            va = decode(a)
            (isfinite(va) && !iszero(va)) || continue
            @test codepoint(Recip(F, ρ, a)) == codepoint(refrec(F, ρ, a))
            if va > 0
                @test codepoint(Sqrt(F, ρ, a))  == codepoint(refsqrt(F, ρ, a))
                @test codepoint(RSqrt(F, ρ, a)) == codepoint(refrsq(F, ρ, a))
            end
            for b in cs
                vb = decode(b)
                (isfinite(vb) && !iszero(vb)) || continue
                @test codepoint(Divide(F, ρ, a, b)) == codepoint(refdiv(F, ρ, a, b))
            end
        end
    end

    # the special rows of the new Float128 Divide method match rung 1's
    let F = Binary(16, 5, SIGNED, EXTENDED), T = BinaryValue(F), q = Float128
        @test isnan(A.ωeval(Val(:Divide), q(Inf), q(Inf)))
        @test isnan(A.ωeval(Val(:Divide), q(0), q(0)))
        @test isnan(A.ωeval(Val(:Divide), q(1), q(0)))       # one unsigned zero
        @test A.ωeval(Val(:Divide), q(1), q(Inf)) == 0
        @test A.ωeval(Val(:Divide), q(-1), q(Inf)) == 0
        @test isinf(A.ωeval(Val(:Divide), q(Inf), q(2)))
        @test signbit(A.ωeval(Val(:Divide), q(Inf), q(-2)))
        @test A.ωeval(Val(:Divide), q(0), q(2)) == 0
        @test isnan(A.ωeval(Val(:Divide), q(NaN), q(1)))
    end

    # exact rung-2 results are allocation-free
    let F = Binary(16, 5, SIGNED, EXTENDED), T = BinaryValue(F)
        a, b = T(3.0), T(2.0)
        Divide(F, RTE_SN, a, b); Recip(F, RTE_SN, b); Sqrt(F, RTE_SN, T(4.0))
        @test (@allocated Divide(F, RTE_SN, a, b)) == 0
        @test (@allocated Recip(F, RTE_SN, b)) == 0
        @test (@allocated Sqrt(F, RTE_SN, T(4.0))) == 0
    end
end

@testset "correctly-rounded enclosures contain the directed ones" begin
    # `_mpfr1_cr`/`_mpfr2_cr` replace two directed MPFR calls with one
    # round-to-nearest call widened by an ulp each side. That is sound ONLY
    # because MPFR rounds each of its primitives correctly, and only for a
    # SINGLE primitive: a composite closure rounds more than once and its error
    # can exceed half an ulp. `Softplus` keeps the directed pair for that
    # reason, and this testset pins the property the opt-in rests on rather
    # than only its usual consequence.
    A = AIFloats
    unary = ((:Exp, exp), (:Exp2, exp2), (:ExpMinusOne, expm1), (:Log, log),
             (:Log2, log2), (:LogOnePlus, log1p), (:Sin, sin), (:Cos, cos),
             (:Tan, tan), (:ArcSin, asin), (:ArcCos, acos), (:ArcTan, atan),
             (:Sinh, sinh), (:Cosh, cosh), (:Tanh, tanh), (:ArcSinh, asinh),
             (:ArcCosh, acosh), (:ArcTanh, atanh))
    for (_, f) in unary, xv in (0.5, 1.5, 2.0, 0.125, 3.75, 1e-5, 12.0, -0.5, -1.5, 100.0)
        # first rung: the widened enclosure. Above it the cr ladder must hand
        # back the directed pair unchanged, which the equality below asserts.
        dc, uc = try A._ladder1_cr(f, xv)(64) catch; continue end
        dd, ud = try A._ladder1(f, xv)(64)    catch; continue end
        (isfinite(dc) && isfinite(uc) && isfinite(dd) && isfinite(ud)) || continue
        @test dc <= dd && ud <= uc                       # contains the directed pair
        t = setprecision(() -> f(BigFloat(xv)), BigFloat, 4096)
        @test dc <= t <= uc                              # and contains the truth
        @test A._ladder1_cr(f, xv)(256) == A._ladder1(f, xv)(256)   # escalation is rigorous
    end
    for f in (/, hypot, atan), xv in (1.0, 3.0, 0.5, -2.5), yv in (1.0, 3.0, 0.5, -2.5)
        dc, uc = A._ladder2_cr(f, xv, yv)(64); dd, ud = A._ladder2(f, xv, yv)(64)
        (isfinite(dc) && isfinite(uc) && isfinite(dd) && isfinite(ud)) || continue
        @test dc <= dd && ud <= uc
        t = setprecision(() -> f(BigFloat(xv), BigFloat(yv)), BigFloat, 4096)
        @test dc <= t <= uc
        @test A._ladder2_cr(f, xv, yv)(256) == A._ladder2(f, xv, yv)(256)
    end

    # The widened enclosure NEVER collapses to a point, so it cannot report an
    # exactly-representable result; the directed pair can, and a directed mode
    # needs it. Restricting the cheap form to the first rung is what makes this
    # resolve at all -- without it, Exp here escalates to the cap and throws.
    let F = Binary(16, 5, SIGNED, EXTENDED), T = BinaryValue(F)
        for x in (T(1.5), T(1.0), T(2.0), T(0.5)), ρ in (RTP_SF, RTN_SF, RTZ_SN, RTO_SN, RTE_SN)
            @test Exp(F, ρ, x) isa BinaryValue
            @test Log(F, ρ, x) isa BinaryValue
        end
    end
end
