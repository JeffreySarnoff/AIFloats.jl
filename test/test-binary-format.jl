using AIFloats
using Test

@testset "Binary format" begin
    f = AIFloats.Format(16, 10, true, false)
    b = AIFloats.Binary(16, 10, false, true)()

    @testset "resolve_fields" begin
        # singleton arguments and their Bool equivalents canonicalize alike
        @test AIFloats.resolve_fields(16, 10, SIGNED, FINITE) == (Int8(16), Int8(10), true, false)
        @test AIFloats.resolve_fields(16, 10, true, false) == (Int8(16), Int8(10), true, false)
        @test AIFloats.resolve_fields(16, 10, UNSIGNED, EXTENDED) == (Int8(16), Int8(10), false, true)
        @test AIFloats.resolve_fields(16, 10, false, true) == (Int8(16), Int8(10), false, true)

        # bitwidth and precision narrow to Int8 whatever Integer type comes in
        for K in (Int8(8), Int16(8), Int32(8), Int64(8))
            fields = AIFloats.resolve_fields(K, oftype(K, 4), SIGNED, FINITE)
            @test fields == (Int8(8), Int8(4), true, false)
            @test fields[1] isa Int8
            @test fields[2] isa Int8
            @test fields[3] isa Bool
            @test fields[4] isa Bool
        end

        # resolve_fields validates, so bad fields throw rather than resolve
        @test_throws ArgumentError AIFloats.resolve_fields(2, 1, SIGNED, FINITE)
        @test_throws ArgumentError AIFloats.resolve_fields(8, 0, SIGNED, FINITE)
        @test_throws ArgumentError AIFloats.resolve_fields(8, 8, SIGNED, FINITE)
    end

    @testset "Format" begin
        @test f isa AIFloats.Format
        @test f.K == Int8(16)
        @test f.P == Int8(10)
        @test f.S == true
        @test f.D == false

        @test AIFloats.resolve_fields(16, 10, SIGNED, FINITE) == (Int8(16), Int8(10), true, false)
        @test AIFloats.resolve_fields(16, 10, true, false) == (Int8(16), Int8(10), true, false)

        # the outer constructor takes singletons or Bools, and any Integer width
        @test AIFloats.Format(16, 10, SIGNED, FINITE) == f
        @test AIFloats.Format(Int8(16), Int8(10), true, false) == f
        @test AIFloats.Format(Int32(16), Int32(10), SIGNED, FINITE) == f
        @test AIFloats.Format(16, 10, UNSIGNED, EXTENDED) == AIFloats.Format(Int8(16), Int8(10), false, true)

        @test_throws ArgumentError AIFloats.Format(2, 1, SIGNED, FINITE)
        @test_throws ArgumentError AIFloats.Format(8, 8, SIGNED, FINITE)
    end

    @testset "Binary" begin
        @test b isa AIFloats.Binary{Int8(16), Int8(10), false, true}
        @test AIFloats.BitwidthOf(b) == 16
        @test AIFloats.PrecisionOf(b) == 10
        @test AIFloats.SignednessOf(b) == false
        @test AIFloats.DomainOf(b) == true

        # Binary(K,P,S,D) returns the parameterized *type*, with Int8 K and P
        @test AIFloats.Binary(16, 10, UNSIGNED, EXTENDED) === AIFloats.Binary{Int8(16), Int8(10), false, true}
        @test AIFloats.Binary(16, 10, true, false) === AIFloats.Binary{Int8(16), Int8(10), true, false}
        @test AIFloats.Binary(16, 10, SIGNED, FINITE) === AIFloats.Binary(Int32(16), Int32(10), true, false)

        @test_throws ArgumentError AIFloats.Binary(2, 1, SIGNED, FINITE)
        @test_throws ArgumentError AIFloats.Binary(8, 8, SIGNED, FINITE)
    end

    @testset "Field accessors" begin
        @test AIFloats.BitwidthOf(b) == 16
        @test AIFloats.PrecisionOf(b) == 10
        @test AIFloats.SignednessOf(b) == false
        @test AIFloats.DomainOf(b) == true

        @test AIFloats.BitwidthOf(f) == 16
        @test AIFloats.PrecisionOf(f) == 10
        @test AIFloats.SignednessOf(f) == true
        @test AIFloats.DomainOf(f) == false

        # a Format and the Binary built from it report identical fields
        fb = AIFloats.BinaryOf(f)()
        @test AIFloats.BitwidthOf(fb) == AIFloats.BitwidthOf(f)
        @test AIFloats.PrecisionOf(fb) == AIFloats.PrecisionOf(f)
        @test AIFloats.SignednessOf(fb) == AIFloats.SignednessOf(f)
        @test AIFloats.DomainOf(fb) == AIFloats.DomainOf(f)
    end

    @testset "Field accessors on Binary types" begin
        # the accessors read the parameters off the type itself, no instance needed
        B = AIFloats.Binary(16, 10, UNSIGNED, EXTENDED)
        @test B isa Type
        @test AIFloats.BitwidthOf(B) == 16
        @test AIFloats.PrecisionOf(B) == 10
        @test AIFloats.SignednessOf(B) == false
        @test AIFloats.DomainOf(B) == true

        # a type spelled out directly works the same way
        @test AIFloats.BitwidthOf(AIFloats.Binary{8, 4, true, false}) == 8
        @test AIFloats.PrecisionOf(AIFloats.Binary{8, 4, true, false}) == 4
        @test AIFloats.SignednessOf(AIFloats.Binary{8, 4, true, false}) == true
        @test AIFloats.DomainOf(AIFloats.Binary{8, 4, true, false}) == false

        # the type and its instance agree, and BinaryOf feeds the type methods directly
        @test AIFloats.BitwidthOf(B) == AIFloats.BitwidthOf(B())
        @test AIFloats.PrecisionOf(B) == AIFloats.PrecisionOf(B())
        @test AIFloats.SignednessOf(B) == AIFloats.SignednessOf(B())
        @test AIFloats.DomainOf(B) == AIFloats.DomainOf(B())

        @test AIFloats.BitwidthOf(AIFloats.BinaryOf(f)) == AIFloats.BitwidthOf(f)
        @test AIFloats.PrecisionOf(AIFloats.BinaryOf(f)) == AIFloats.PrecisionOf(f)
        @test AIFloats.SignednessOf(AIFloats.BinaryOf(f)) == AIFloats.SignednessOf(f)
        @test AIFloats.DomainOf(AIFloats.BinaryOf(f)) == AIFloats.DomainOf(f)

        for (K, P, S, D) in [(16, 10, SIGNED, FINITE), (8, 4, UNSIGNED, EXTENDED),
                             (3, 1, SIGNED, EXTENDED), (32, 24, UNSIGNED, FINITE)]
            T = AIFloats.Binary(K, P, S, D)
            @test AIFloats.BitwidthOf(T) == K
            @test AIFloats.PrecisionOf(T) == P
            @test AIFloats.SignednessOf(T) == convert(Bool, S)
            @test AIFloats.DomainOf(T) == convert(Bool, D)
        end
    end

    @testset "Binary Format" begin
        @test AIFloats.FormatOf(b) == AIFloats.Format(Int8(16), Int8(10), false, true)
        # BinaryOf yields the type itself, parameterized by the Int8 fields
        @test AIFloats.BinaryOf(f) === AIFloats.Binary{f.K, f.P, f.S, f.D}

        # the two conversions round-trip in both directions
        for (K, P, S, D) in [(16, 10, SIGNED, FINITE), (8, 4, UNSIGNED, EXTENDED),
                             (3, 1, SIGNED, EXTENDED), (32, 24, UNSIGNED, FINITE)]
            fmt = AIFloats.Format(K, P, S, D)
            @test AIFloats.FormatOf(AIFloats.BinaryOf(fmt)()) == fmt

            bin = AIFloats.Binary(K, P, S, D)
            @test AIFloats.BinaryOf(AIFloats.FormatOf(bin())) === bin
        end
    end

    @testset "Predicates" begin
        signed_finite = AIFloats.Format(16, 10, SIGNED, FINITE)
        unsigned_extended = AIFloats.Format(16, 10, UNSIGNED, EXTENDED)

        @test is_signed(signed_finite)
        @test !is_unsigned(signed_finite)
        @test is_finite(signed_finite)
        @test !is_extended(signed_finite)

        @test !is_signed(unsigned_extended)
        @test is_unsigned(unsigned_extended)
        @test !is_finite(unsigned_extended)
        @test is_extended(unsigned_extended)

        # all four corners, checked on both the Format and the Binary
        for (S, D) in [(SIGNED, FINITE), (SIGNED, EXTENDED),
                       (UNSIGNED, FINITE), (UNSIGNED, EXTENDED)]
            fmt = AIFloats.Format(16, 10, S, D)
            bin = AIFloats.Binary(16, 10, S, D)()

            @test is_signed(fmt) == is_signed(S)
            @test is_unsigned(fmt) == is_unsigned(S)
            @test is_finite(fmt) == is_finite(D)
            @test is_extended(fmt) == is_extended(D)

            @test is_signed(bin) == is_signed(S)
            @test is_unsigned(bin) == is_unsigned(S)
            @test is_finite(bin) == is_finite(D)
            @test is_extended(bin) == is_extended(D)
        end
    end

    @testset "validformat" begin
        # accepted formats return nothing
        @test AIFloats.validformat(16, 10, SIGNED, FINITE) === nothing
        @test AIFloats.validformat(16, 10, true, false) === nothing
        @test AIFloats.validformat(f) === nothing
        @test AIFloats.validformat(b) === nothing

        # P may run all the way up to K - S, but no further
        @test AIFloats.validformat(8, 7, SIGNED, FINITE) === nothing
        @test AIFloats.validformat(8, 8, UNSIGNED, FINITE) === nothing
        @test_throws ArgumentError AIFloats.validformat(8, 8, SIGNED, FINITE)
        @test_throws ArgumentError AIFloats.validformat(8, 9, UNSIGNED, FINITE)

        # K must exceed 2 and P must be positive
        @test AIFloats.validformat(3, 1, SIGNED, FINITE) === nothing
        @test_throws ArgumentError AIFloats.validformat(2, 1, SIGNED, FINITE)
        @test_throws ArgumentError AIFloats.validformat(1, 1, UNSIGNED, FINITE)
        @test_throws ArgumentError AIFloats.validformat(8, 0, SIGNED, FINITE)
        @test_throws ArgumentError AIFloats.validformat(8, -1, SIGNED, FINITE)
    end

    @testset "Show Binary" begin
        io = IOBuffer()
        show(io, MIME("text/plain"), b)
        @test String(take!(io)) == "Binary{16, 10, false, true}"

        io = IOBuffer()
        show(io, b)
        @test String(take!(io)) == "Binary{16, 10, false, true}"

        @test repr(b) == "Binary{16, 10, false, true}"
        @test repr(MIME("text/plain"), b) == "Binary{16, 10, false, true}"

        sb = AIFloats.Binary{8, 4, true, false}()
        @test sprint(show, sb) == "Binary{8, 4, true, false}"
        @test sprint(show, MIME("text/plain"), sb) == "Binary{8, 4, true, false}"
    end

    @testset "Show Format" begin
        io = IOBuffer()
        show(io, MIME("text/plain"), f)
        @test String(take!(io)) == "Format(16, 10, true, false)"

        io = IOBuffer()
        show(io, f)
        @test String(take!(io)) == "Format(16, 10, true, false)"

        @test repr(f) == "Format(16, 10, true, false)"
        @test repr(MIME("text/plain"), f) == "Format(16, 10, true, false)"

        uf = AIFloats.Format(8, 4, UNSIGNED, EXTENDED)
        @test sprint(show, uf) == "Format(8, 4, false, true)"
        @test sprint(show, MIME("text/plain"), uf) == "Format(8, 4, false, true)"
    end
end
