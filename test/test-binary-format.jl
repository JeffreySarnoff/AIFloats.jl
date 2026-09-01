using AIFloats
using Test

@testset "Binary format" begin
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

    @testset "Binary" begin
        @test b isa AIFloats.Binary{Int8(16), Int8(10), false, true}

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

        sb = AIFloats.Binary(16, 10, SIGNED, FINITE)()
        @test AIFloats.BitwidthOf(sb) == 16
        @test AIFloats.PrecisionOf(sb) == 10
        @test AIFloats.SignednessOf(sb) == true
        @test AIFloats.DomainOf(sb) == false
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

        # the type and its instance agree
        @test AIFloats.BitwidthOf(B) == AIFloats.BitwidthOf(B())
        @test AIFloats.PrecisionOf(B) == AIFloats.PrecisionOf(B())
        @test AIFloats.SignednessOf(B) == AIFloats.SignednessOf(B())
        @test AIFloats.DomainOf(B) == AIFloats.DomainOf(B())

        for (K, P, S, D) in [(16, 10, SIGNED, FINITE), (8, 4, UNSIGNED, EXTENDED),
                             (3, 1, SIGNED, EXTENDED), (16, 16, UNSIGNED, FINITE)]
            T = AIFloats.Binary(K, P, S, D)
            @test AIFloats.BitwidthOf(T) == K
            @test AIFloats.PrecisionOf(T) == P
            @test AIFloats.SignednessOf(T) == convert(Bool, S)
            @test AIFloats.DomainOf(T) == convert(Bool, D)
        end
    end

    @testset "Predicates" begin
        signed_finite = AIFloats.Binary(16, 10, SIGNED, FINITE)()
        unsigned_extended = AIFloats.Binary(16, 10, UNSIGNED, EXTENDED)()

        @test is_signed(signed_finite)
        @test !is_unsigned(signed_finite)
        @test is_finite(signed_finite)
        @test !is_extended(signed_finite)

        @test !is_signed(unsigned_extended)
        @test is_unsigned(unsigned_extended)
        @test !is_finite(unsigned_extended)
        @test is_extended(unsigned_extended)

        # all four corners
        for (S, D) in [(SIGNED, FINITE), (SIGNED, EXTENDED),
                       (UNSIGNED, FINITE), (UNSIGNED, EXTENDED)]
            bin = AIFloats.Binary(16, 10, S, D)()

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
        # plain show spells the fields out; MIME"text/plain" (what the REPL uses) is glyphic
        io = IOBuffer()
        show(io, MIME("text/plain"), b)
        @test String(take!(io)) == "Binary{16, 10, +, ∞}"

        io = IOBuffer()
        show(io, b)
        @test String(take!(io)) == "Binary{16, 10, UNSIGNED, EXTENDED}"

        @test repr(b) == "Binary{16, 10, UNSIGNED, EXTENDED}"
        @test repr(MIME("text/plain"), b) == "Binary{16, 10, +, ∞}"

        sb = AIFloats.Binary{8, 4, true, false}()
        @test sprint(show, sb) == "Binary{8, 4, SIGNED, FINITE}"
        @test sprint(show, MIME("text/plain"), sb) == "Binary{8, 4, ±, ⏥}"

        # a format and its type display alike
        @test repr(sb) == repr(typeof(sb))
        @test repr(MIME("text/plain"), sb) == repr(MIME("text/plain"), typeof(sb))

        # all four corners of the glyph form: ± / + for signedness, ∞ / ⏥ for domain
        for (S, D, glyphs) in [(SIGNED, FINITE, "±, ⏥"), (SIGNED, EXTENDED, "±, ∞"),
                               (UNSIGNED, FINITE, "+, ⏥"), (UNSIGNED, EXTENDED, "+, ∞")]
            T = AIFloats.Binary(8, 4, S, D)
            @test repr(MIME("text/plain"), T) == "Binary{8, 4, $glyphs}"
            @test repr(T) == "Binary{8, 4, $(string(S)), $(string(D))}"
        end
    end
end

@testset "a format is not a number" begin
    # Binary has NO supertype. It describes a value set; it does not belong to
    # one. Its datums are the AbstractFloats.
    #
    # This is pinned rather than left implicit because the failure it prevents
    # is silent. While `Binary <: BinaryFloat <: AbstractFloat`, Base's numeric
    # fallbacks applied to format instances and `isnan` of a FORMAT returned
    # `false` -- the generic method is `x != x` -- rather than failing. Anyone
    # re-adding a numeric supertype here would reintroduce that with no test
    # failing anywhere else. See docs/structuralplan.md §9.2.
    for F in (Binary(8, 4, SIGNED, EXTENDED), Binary(3, 1, UNSIGNED, FINITE),
              Binary(16, 5, SIGNED, EXTENDED))
        @test supertype(F) === Any
        @test !(F <: AbstractFloat)
        @test !(F <: Real)
        @test !(F <: Number)
        # the datum of that same format IS a number
        T = BinaryValue(F)
        @test T <: AbstractFloat
        @test T <: Real && T <: Number
        @test isconcretetype(T) && isbitstype(T)
        # and the numeric predicates answer about datums, never about formats
        @test isnan(T(AIFloats.nan_code(F))) isa Bool
        @test_throws MethodError isnan(F())
        @test_throws MethodError zero(F())
    end
    @test !(Binary <: AbstractFloat)
    # the name that described the old, inverted hierarchy is gone
    @test !isdefined(AIFloats, :BinaryFloat)
end
