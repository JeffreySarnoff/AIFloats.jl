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
