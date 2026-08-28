using AIFloats
using Test
using Random
using AIFloats: FAST_ARITH, FAST_ENCLOSURE, ρRSA, ρRSC, Sticky, Enclosure
using Quadmath: Float128

# The two performance layers over the rigorous path are pinned EQUAL to it:
#   FAST_ARITH     — Float128 exactness proofs + the Sticky wide-spread escape
#                    vs exact-BigFloat escalation, over every operand pair of
#                    formats whose spreads cross the sticky band;
#   FAST_ENCLOSURE — eager Float64/Float128 envelope stages vs the MPFR ladder
#                    alone, over every code point of representative formats.

isdefined(Main, :allcodes) || include(joinpath(@__DIR__, "support", "helpers.jl"))

function both(flag, f)
    old = flag[]
    try
        flag[] = true;  a = f()
        flag[] = false; b = f()
        codepoint.(a) == codepoint.(b)
    finally
        flag[] = old
    end
end

@testset "FAST_ARITH ≡ exact escalation" begin
    U1 = Binary(8, 1, UNSIGNED, FINITE)          # B = 128: spreads reach 256 > 77
    S2 = Binary(8, 2, SIGNED, EXTENDED)          # B = 32, signed: cancellation
    W5 = Binary(16, 5, SIGNED, EXTENDED)         # rung 2, B = 1024
    modes = (RTE_SN, RTZ_SF, RTP_SP, RTN_SN, RTO_SN, Projection(ρRSA(3), SN), Projection(ρRSC(60), SF))
    for F in (U1, S2), ρ in modes
        xs = allcodes(F)
        Rs = isstochastic(ρ) ? (0, 3) : (0,)
        for R in Rs
            @test both(FAST_ARITH, () -> [Add(F, ρ, x, y; R) for x in xs, y in xs])
            @test both(FAST_ARITH, () -> [Subtract(F, ρ, x, y; R) for x in xs, y in xs])
            @test both(FAST_ARITH, () -> [FMA(F, ρ, x, y, x; R) for x in xs, y in xs])
            @test both(FAST_ARITH, () -> [FAA(F, ρ, x, y, y; R) for x in xs, y in xs])
        end
        ts = subcodes(F, 24)
        @test both(FAST_ARITH, () -> [FAA(F, ρ, x, y, z; R = 3) for x in ts, y in ts, z in ts])
        @test both(FAST_ARITH, () -> [FMA(F, ρ, x, y, z; R = 3) for x in ts, y in ts, z in ts])
    end
    # FMA's Float64-first peel (implmentplan.md Step 4): when fma certifies the
    # product exact in Float64, the result is Add's cascade on (x·y, z) rather
    # than a Float128 widening. Exhaustive over whole code cubes, both domains,
    # both signednesses, and a signed cube whose products routinely escalate.
    for F in (Binary(5, 2, SIGNED, EXTENDED), Binary(4, 2, SIGNED, FINITE),
              Binary(6, 3, UNSIGNED, FINITE), Binary(5, 4, SIGNED, EXTENDED))
        cs = allcodes(F)
        @test both(FAST_ARITH, () -> [FMA(F, RTE_SN, x, y, z) for x in cs, y in cs, z in cs])
    end
    # the directed cases the peel has to get right
    @test AIFloats.ωeval(Val(:FMA), 1.5, 0.25, 0.75) isa Float64            # product exact, sum exact
    @test AIFloats.ωeval(Val(:FMA), 1.5, 0.25, -0.375) isa Float64          # exact cancellation
    # below the magnitude floor the peel must NOT fire: p underflows to 0 and
    # the fma residual underflows with it, so exactness cannot be certified
    @test AIFloats.ωeval(Val(:FMA), 2.0^-1060, 2.0^-20, 1.0) isa Sticky
    @test AIFloats.ωeval(Val(:FMA), 2.0^-1060, 2.0^-20, 0.0) ==
          AIFloats.ωeval(Val(:Multiply), 2.0^-1060, 2.0^-20)   # the true tiny product survives
    @test AIFloats.ωeval(Val(:FMA), 1.0 + 2.0^-52, 1.0 + 2.0^-52, 0.0) isa Float128  # product inexact in Float64

    # the sticky escape is actually reached at B = 128
    @test AIFloats.ωeval(Val(:Add), decode(MaxFiniteOf(U1)), decode(MinPositiveOf(U1))) isa Sticky
    @test AIFloats.ωeval(Val(:FMA), 2.0^100, 2.0^100, 1.0) isa Sticky
    @test AIFloats.ωeval(Val(:FAA), 2.0^100, 1.0, -2.0^100) isa Float128     # exact after distillation
    # rung 2 (Float128 operands), a wide subset
    ws = subcodes(W5, 40)
    for ρ in (RTE_SN, RTZ_SF, Projection(ρRSA(3), SN))
        @test both(FAST_ARITH, () -> [Add(W5, ρ, x, y; R = 3) for x in ws, y in ws])
        @test both(FAST_ARITH, () -> [Multiply(W5, ρ, x, y; R = 3) for x in ws, y in ws])
        @test both(FAST_ARITH, () -> [FMA(W5, ρ, x, y, y; R = 3) for x in ws, y in ws])
        @test both(FAST_ARITH, () -> [FAA(W5, ρ, x, y, x; R = 3) for x in ws, y in ws])
    end
    @test AIFloats.ωeval(Val(:Add), decode(MaxFiniteOf(W5)), decode(MinPositiveOf(W5))) isa Sticky
    # mixed 64/128 operands still escalate exactly
    @test AIFloats.ωeval(Val(:Add), 1.5, Float128(0.25)) isa BigFloat
end

@testset "FAST_ENCLOSURE ≡ the ladder alone" begin
    ladder = [o.name for o in AIFloats.OP_REGISTRY
              if o.arity == 1 && o.name in AIFloats._LADDER_OPS || o.name in (:Recip, :Sqrt, :RSqrt)]
    for F in (Binary(8, 4, SIGNED, EXTENDED), Binary(8, 1, UNSIGNED, FINITE),
              Binary(5, 2, SIGNED, EXTENDED), Binary(3, 1, SIGNED, EXTENDED), Binary(7, 3, UNSIGNED, EXTENDED))
        xs = allcodes(F)
        for op in ladder, ρ in (RTE_SN, RTZ_SF, RTP_SP, Projection(ρRSA(4), SN))
            f = getfield(AIFloats, op)
            @test both(FAST_ENCLOSURE, () -> [f(F, ρ, x; R = 3) for x in xs])
        end
        ss = subcodes(F, 16)
        for op in (:Divide, :Hypot, :ArcTan2, :ArcTan2Pi), ρ in (RTE_SN, RTZ_SF, RTP_SP)
            f = getfield(AIFloats, op)
            @test both(FAST_ENCLOSURE, () -> [f(F, ρ, x, y) for x in ss, y in ss])
        end
    end
    # the eager stages are actually built for Float64 operands and dropped for wide ones
    e = AIFloats.ωeval(Val(:Exp), 0.75)
    @test e isa Enclosure && e.fq !== nothing && isfinite(e.yd)
    e2 = AIFloats.ωeval(Val(:Exp), Float128(0.75))
    @test e2 isa Enclosure && e2.fq === nothing && isnan(e2.yd)
    e3 = AIFloats.ωeval(Val(:Exp), AIFloats.Dyadic(3, -2))
    @test e3 isa Enclosure && e3.fq === nothing
    # a Float64 quotient that is not exact carries its CR quotient as the estimate
    q = AIFloats.ωeval(Val(:Divide), 1.0, 3.0)
    @test q isa Enclosure && q.yd == 1 / 3
end

@testset "warm path allocates nothing on the fast layers" begin
    T = binary8p4se
    a, b = T(1.5), T(0.25)
    Add(a, b); Exp(a); FMA(a, b, a)
    T(1.3); T(1.3f0); T(3); convert(T, 1.3); convert(T, 0x03)   # warm the constructors too
    # the value constructors and `convert` carry the same speculation guard as
    # the generated op methods (implmentplan.md Step 2): an eagerly evaluated
    # `projection = DefaultProjection()` default read the abstract Ref on every
    # call and boxed, costing ~98 ns and 2 allocations per construction
    @test (@allocated T(1.3)) == 0
    @test (@allocated T(1.3f0)) == 0
    @test (@allocated convert(T, 1.3)) == 0
    # Step 3: an Integer within ±2^53 widens exactly to Float64 instead of
    # taking Convert's BigFloat route
    @test (@allocated T(3)) == 0
    @test (@allocated convert(T, 0x03)) == 0
    let saved = DefaultProjection()
        try
            DefaultProjection!(RTZ_SF)
            @test T(1.3) === Convert(T, RTZ_SF, 1.3)      # the non-default branch is live
            @test convert(T, 1.3) === Convert(T, RTZ_SF, 1.3)
            @test convert(T, 0x03) === Convert(T, RTZ_SF, 0x03)
        finally
            DefaultProjection!(saved)
        end
    end
    @test T(1.3; projection = RTP_SN) === Convert(T, RTP_SN, 1.3)
    @test T(1.3; projection = RTE_SN) === Convert(T, RTE_SN, 1.3)
    @test T(1.3) === Convert(T, RTE_SN, 1.3)

    @test (@allocated Add(a, b)) == 0
    @test (@allocated FMA(a, b, a)) == 0
    # Group B: the eager Float64 envelope decides for every libm family, and
    # since Step 5 the Enclosure that carries it is not heap-allocated
    for op in (Log, Log2, LogOnePlus, Sin, Cos, Tan, ArcSin, ArcTan, Sinh, Tanh,
               ArcSinh, SinPi, CosPi, Exp, Exp2, ExpMinusOne, Sqrt, RSqrt)
        op(a)                                       # warm
        @test (@allocated op(a)) == 0
    end
    @test (@allocated ArcTan2Pi(a, b)) == 0
    @test (@allocated Hypot(a, b)) == 0
    A = T.(randn(MersenneTwister(1), 4096)); B = T.(randn(MersenneTwister(2), 4096)); D = similar(A)
    AIFloats.empty_tables!()
    old = AIFloats.TABLE_EAGER_BITS[]
    AIFloats.TABLE_EAGER_BITS[] = -1                # force the compute path
    try
        vmap!(D, Val(:Add), RTE_SN, A, B)
        n1 = @allocated vmap!(D, Val(:Add), RTE_SN, A, B)
        vmap!(D, Val(:Multiply), RTE_SN, A, B)
        n2 = @allocated vmap!(D, Val(:Multiply), RTE_SN, A, B)
        @test n1 == 0 && n2 == 0
    finally
        AIFloats.TABLE_EAGER_BITS[] = old
    end
end
