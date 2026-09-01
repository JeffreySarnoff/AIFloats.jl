using AIFloats
using Test

# walk the whole K ≤ 16 grid: 504 formats
function eachformat(f)
    n = 0
    for K in 3:16, P in 1:K, S in (true, false), E in (true, false)
        S && P >= K && continue
        f(AIFloats.Binary(K, P, S, E))
        n += 1
    end
    n
end

@testset "Format grid" begin
    # exactly the P3109 K ≤ 16 lattice
    @test eachformat(_ -> nothing) == 504

    # the ceiling: K = 16 is the top, K = 17 is refused
    @test AIFloats.validformat(16, 16, UNSIGNED, FINITE) === nothing
    @test_throws ArgumentError AIFloats.Binary(17, 4, SIGNED, FINITE)
    @test_throws ArgumentError AIFloats.validformat(17, 4, UNSIGNED, FINITE)
end

@testset "Exponent traits" begin
    eachformat() do F
        K, P = Int(BitwidthOf(F)), Int(PrecisionOf(F))
        S = SignednessOf(F)
        w = ExponentBitwidthOf(F)
        B = ExponentBiasOf(F)

        # every bit is sign, exponent, or stored significand
        @test Int(S) + w + (P - 1) == K
        # the bias is half the exponent field's span
        @test B == 2^(w - 1)
        # the two closed forms
        @test B == (S ? 2^(K - P - 1) : 2^(K - P))
        # at least one exponent bit — the validity rule, restated on the traits
        @test w >= 1

        # trailing significand
        @test TrailingSignificantBitsOf(F) == P - 1

        # every trait answers for the format TYPE; there is no instance form
        for t in (ExponentBiasOf, ExponentBitwidthOf, TrailingSignificantBitsOf,
                  AIFloats.codemask, AIFloats.signmask, AIFloats.orderkeytype)
            @test applicable(t, F)
        end
        @test_throws ArgumentError F()
    end
end

@testset "Masks and key types" begin
    eachformat() do F
        K = Int(BitwidthOf(F))
        U = CodeType(F)
        cm = AIFloats.codemask(F)
        sm = AIFloats.signmask(F)

        @test cm isa U && sm isa U
        # K low bits set, nothing above
        @test count_ones(cm) == K
        @test trailing_ones(cm) == K
        # the sign bit is the top code bit, inside the mask
        @test sm == one(U) << (K - 1)
        @test sm & cm == sm
        # the key type is strictly wider than the code space
        O = AIFloats.orderkeytype(F)
        @test typemax(O) > UInt64(2)^K   # keys run 1:2^K plus key 0 for NaN
    end

    # the structural case: K equals the storage width, mask is all-ones
    @test AIFloats.codemask(AIFloats.Binary(8, 4, SIGNED, FINITE)) === 0xff
    @test AIFloats.codemask(AIFloats.Binary(16, 8, SIGNED, FINITE)) === 0xffff
end

@testset "Stochastic budgets" begin
    # the exported constants are the default-budget instances
    @test RSA === AIFloats.ρRSA{8}()
    @test RSB === AIFloats.ρRSB{8}()
    @test RSC === AIFloats.ρRSC{8}()

    # constructor route to other budgets
    @test nrandbits(AIFloats.ρRSA(1)) == 1
    @test nrandbits(AIFloats.ρRSB(60)) == 60
    @test AIFloats.ρRSC(12) === AIFloats.ρRSC{12}()

    # out-of-range budgets cannot exist as values
    @test_throws ArgumentError AIFloats.ρRSA(0)
    @test_throws ArgumentError AIFloats.ρRSA(61)
    @test_throws ArgumentError AIFloats.ρRSB{0}()
    @test_throws ArgumentError AIFloats.ρRSC{61}()

    # queries on modes
    for r in (RTE, RTA, RTP, RTN, RTZ, RTO)
        @test !isstochastic(r)
        @test nrandbits(r) == 0
    end
    for r in (RSA, RSB, RSC)
        @test isstochastic(r)
        @test nrandbits(r) == 8
    end

    # queries lift to projections, on both value and type
    @test isstochastic(RSA_SF) && isstochastic(typeof(RSB_SP))
    @test !isstochastic(RTE_SN) && !isstochastic(typeof(RTO_SF))
    @test nrandbits(RSC_SN) == 8
    @test nrandbits(RTZ_SP) == 0
    @test nrandbits(Projection(AIFloats.ρRSA(12), SF)) == 12

    # display unchanged by the parameterization
    @test string(RSA) == "RSA"
    @test String(RSA) == "StochasticA"
    @test repr(MIME"text/plain"(), RSA_SF) == "ρ(RSA, SF)"
end

@testset "consolidated queries and formatinfo (improveapi3 §4.1, Phase 4)" begin
    # The Julia-style spellings are BOUND TO THE SAME FUNCTION OBJECT, not
    # written as forwarding methods. That is what makes them permanent
    # vocabulary rather than adapters: the two names cannot drift apart in what
    # they accept, a method added for one is a method for both, and there is
    # provably no run-time cost because there is no second call to elide.
    @test formatof     === BinaryFormatOf
    @test bitwidth     === BitwidthOf
    @test signedness   === SignednessOf
    @test domain       === DomainOf
    @test codetype     === CodeType
    @test valuetype    === ValueType

    eachformat() do F
        T = BinaryValue(F)
        x = fromcode(F, 0)
        # every query answers for the format, the datum type, and a datum
        for f in (formatof, bitwidth, signedness, domain, codetype, valuetype,
                  PrecisionOf, TrailingSignificantBitsOf,
                  ExponentBiasOf, ExponentBitwidthOf)
            @test applicable(f, F) && applicable(f, T) && applicable(f, x)
            @test f(F) === f(T) === f(x)
        end
        # formatof is TOTAL: a format normalizes to itself, so internal code
        # never needs a branch on what it was handed
        @test formatof(F) === F && formatof(T) === F && formatof(x) === F

        # Base.precision covers the format as well as the datum. AIFloats does
        # not export a `precision` of its own: shadowing Base's would change
        # the meaning of a name every Julia program already has.
        @test precision(F) == precision(T) == Int(PrecisionOf(F))
        @test !(:precision in names(AIFloats))

        info = formatinfo(F)
        @test info === formatinfo(T) === formatinfo(x)
        @test info.name         === formatname(F)
        @test info.format       === F
        @test info.datumtype    === T
        @test info.bitwidth     == Int(BitwidthOf(F))
        @test info.precision    == Int(PrecisionOf(F))
        @test info.signed       == is_signed(F)
        @test info.extended     == is_extended(F)
        @test info.exponentbias == ExponentBiasOf(F)
        @test info.exponentbits == ExponentBitwidthOf(F)
        @test info.trailingbits == Int(TrailingSignificantBitsOf(F))
        @test info.codetype     === CodeType(F)
        @test info.valuetype    === ValueType(F)
        @test info.datumcarrier    === AIFloats.datumcarrier(F)
        @test info.promotecarrier  === AIFloats.promotecarrier(F)
    end

    # pure, type-stable, and constant-foldable for a concrete F: the whole
    # named tuple folds to a literal, so the query costs nothing where the
    # format is known at compile time
    let F = Binary8p4se
        f() = formatinfo(F)
        @test @inferred(f()) isa NamedTuple
        f()
        @test (@allocated f()) == 0
        g() = formatinfo(F).bitwidth
        @test length(Base.code_typed(g, Tuple{})[1][1].code) <= 2   # folded
        @test g() == 8
    end
end
