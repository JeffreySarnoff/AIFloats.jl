using AIFloats
using Test

@testset "Singletons" begin
    @testset "Signedness conversions and predicates" begin
        @test UNSIGNED isa AIFloats.ΣUNSIGNED
        @test SIGNED isa AIFloats.ΣSIGNED

        @test convert(Bool, UNSIGNED) == false
        @test convert(Bool, SIGNED) == true
        @test convert(Bool, AIFloats.ΣUNSIGNED) == false
        @test convert(Bool, AIFloats.ΣSIGNED) == true

        @test convert(AIFloats.Signedness, false) === UNSIGNED
        @test convert(AIFloats.Signedness, true) === SIGNED
        @test AIFloats.Signedness(false) === UNSIGNED
        @test AIFloats.Signedness(true) === SIGNED

        @test is_unsigned(UNSIGNED)
        @test !is_signed(UNSIGNED)
        @test !is_unsigned(SIGNED)
        @test is_signed(SIGNED)

        @test is_unsigned(false)
        @test !is_unsigned(true)
        @test is_signed(true)
        @test !is_signed(false)

        for (value, expected) in [(UNSIGNED, false), (SIGNED, true)]
            @test convert(Bool, value) == expected
            @test is_unsigned(value) == !expected
            @test is_signed(value) == expected
        end
    end

    @testset "Domain conversions and predicates" begin
        @test FINITE isa AIFloats.ΔFINITE
        @test EXTENDED isa AIFloats.ΔEXTENDED

        @test convert(Bool, FINITE) == false
        @test convert(Bool, EXTENDED) == true
        @test convert(Bool, AIFloats.ΔFINITE) == false
        @test convert(Bool, AIFloats.ΔEXTENDED) == true

        @test convert(AIFloats.Domain, false) === FINITE
        @test convert(AIFloats.Domain, true) === EXTENDED
        @test AIFloats.Domain(false) === FINITE
        @test AIFloats.Domain(true) === EXTENDED

        @test is_finite(FINITE)
        @test !is_extended(FINITE)
        @test !is_finite(EXTENDED)
        @test is_extended(EXTENDED)

        @test is_finite(false)
        @test !is_finite(true)
        @test is_extended(true)
        @test !is_extended(false)

        for (value, expected) in [(FINITE, false), (EXTENDED, true)]
            @test convert(Bool, value) == expected
            @test is_finite(value) == !expected
            @test is_extended(value) == expected
        end
    end

    # helpers exercising both show methods defined for each singleton
    showstr(x) = sprint(show, x)
    showplain(x) = sprint(show, MIME"text/plain"(), x)

    @testset "Signedness show functions" begin
        for (value, expected) in [(UNSIGNED, "UNSIGNED"), (SIGNED, "SIGNED")]
            @test string(value) == expected
            @test showplain(value) == expected
            @test showstr(value) == expected
            @test repr(value) == expected
            @test repr(MIME"text/plain"(), value) == expected
        end
    end

    @testset "Domain show functions" begin
        for (value, expected) in [(FINITE, "FINITE"), (EXTENDED, "EXTENDED")]
            @test string(value) == expected
            @test showplain(value) == expected
            @test showstr(value) == expected
            @test repr(value) == expected
            @test repr(MIME"text/plain"(), value) == expected
        end
    end

    @testset "RoundingMode show functions" begin
        rounding = [(RTE, "RTE", "RoundToEven"),
                    (RTA, "RTA", "RoundToAway"),
                    (RUP, "RUP", "RoundUp"),
                    (RDN, "RDN", "RoundDown"),
                    (RTZ, "RTZ", "RoundToZero"),
                    (RTO, "RTO", "RoundToOdd"),
                    (RSA, "RSA", "StochasticA"),
                    (RSB, "RSB", "StochasticB"),
                    (RSC, "RSC", "StochasticC")]

        @test length(rounding) == 9

        for (value, short, long) in rounding
            @test value isa AIFloats.RoundingMode
            @test string(value) == short
            @test String(value) == long
            # both show methods print the short form
            @test showstr(value) == short
            @test showplain(value) == short
            @test repr(value) == short
            @test repr(MIME"text/plain"(), value) == short
        end
    end

    @testset "SaturationMode show functions" begin
        saturation = [(SF, "SF", "SatFinite"),
                      (SP, "SP", "SatPropagate"),
                      (SN, "SN", "SatNone")]

        @test length(saturation) == 3

        for (value, short, long) in saturation
            @test value isa AIFloats.SaturationMode
            @test string(value) == short
            @test String(value) == long
            # both show methods print the short form
            @test showstr(value) == short
            @test showplain(value) == short
            @test repr(value) == short
            @test repr(MIME"text/plain"(), value) == short
        end
    end

    @testset "Projection show functions" begin
        rounding = (RTE, RTA, RUP, RDN, RTZ, RTO, RSA, RSB, RSC)
        saturation = (SF, SP, SN)

        for r in rounding, s in saturation
            p = AIFloats.Projection(r, s)

            @test AIFloats.RoundOf(p) === r
            @test AIFloats.SatOf(p) === s

            # MIME"text/plain" show uses the short (string) names
            @test showplain(p) == "ρ($(string(r)), $(string(s)))"
            @test repr(MIME"text/plain"(), p) == "ρ($(string(r)), $(string(s)))"

            # plain show uses the long (String) names
            @test showstr(p) == "ρ($(String(r)), $(String(s)))"
            @test repr(p) == "ρ($(String(r)), $(String(s)))"
        end

        # the exported Projection constants show the same as freshly built ones
        for (p, r, s) in [(AIFloats.RTE_SF, RTE, SF),
                          (AIFloats.RTA_SP, RTA, SP),
                          (AIFloats.RUP_SN, RUP, SN),
                          (AIFloats.RDN_SF, RDN, SF),
                          (AIFloats.RTZ_SP, RTZ, SP),
                          (AIFloats.RTO_SN, RTO, SN),
                          (AIFloats.RSA_SF, RSA, SF),
                          (AIFloats.RSB_SP, RSB, SP),
                          (AIFloats.RSC_SN, RSC, SN)]
            @test showplain(p) == "ρ($(string(r)), $(string(s)))"
            @test showstr(p) == "ρ($(String(r)), $(String(s)))"
        end
    end
end
