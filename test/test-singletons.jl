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

    @testset "Signedness show functions" begin
        @test string(UNSIGNED) == "UNSIGNED"
        @test string(SIGNED) == "SIGNED"

        # Test MIME"text/plain" show
        io = IOBuffer()
        show(io, MIME"text/plain"(), UNSIGNED)
        @test String(take!(io)) == "UNSIGNED"

        io = IOBuffer()
        show(io, MIME"text/plain"(), SIGNED)
        @test String(take!(io)) == "SIGNED"

        # Test plain show
        io = IOBuffer()
        show(io, UNSIGNED)
        @test String(take!(io)) == "UNSIGNED"

        io = IOBuffer()
        show(io, SIGNED)
        @test String(take!(io)) == "SIGNED"
    end

    @testset "Domain show functions" begin
        @test string(FINITE) == "FINITE"
        @test string(EXTENDED) == "EXTENDED"

        # Test MIME"text/plain" show
        io = IOBuffer()
        show(io, MIME"text/plain"(), FINITE)
        @test String(take!(io)) == "FINITE"

        io = IOBuffer()
        show(io, MIME"text/plain"(), EXTENDED)
        @test String(take!(io)) == "EXTENDED"

        # Test plain show
        io = IOBuffer()
        show(io, FINITE)
        @test String(take!(io)) == "FINITE"

        io = IOBuffer()
        show(io, EXTENDED)
        @test String(take!(io)) == "EXTENDED"
    end

    @testset "Projection singletons" begin
        rounding = (RTE(), RTA(), RUP(), RDN(), RTZ(), RTO(), RSA(), RSB(), RSC())
        saturation = (SF(), SP(), SN())

        @test length(rounding) == 9
        @test length(saturation) == 3

        for x in rounding
            @test x isa AIFloats.RoundingMode
        end
        for x in saturation
            @test x isa AIFloats.SaturationMode
        end
    end
end
