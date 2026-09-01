using AIFloats
using Test

@testset "Construction discipline" begin
    F = AIFloats.Binary(8, 4, SIGNED, FINITE)
    BV = BinaryValue(F)

    # the alias, the normalized spelling, and the full type coincide
    @test BV === Binary8p4sf
    @test BV === BinaryValue{F, UInt8}
    @test BinaryValue{F}(0x45) === BV(0x45)
    @test BinaryValue(F, 0x45) === BV(0x45)
    fmt = F()
    @test BinaryValue(fmt, 0x45) === BV(0x45)
    @test BinaryValue(fmt, 1.625) === BV(0x45)
    @test project(fmt, RTE_SN, 1.625) === BV(0x45)
    @test Convert(fmt, RTE_SN, 1.625) === BV(0x45)

    # Unsigned argument = code point, range-checked against 2^K
    @test codepoint(BV(0xff)) === 0xff
    @test_throws ArgumentError BinaryValue(AIFloats.Binary(4, 2, SIGNED, FINITE), 0x10)
    # wrong storage unit refused
    @test_throws ArgumentError BinaryValue{F, UInt16}(0x0045)

    # wider unsigned code accepted when in range (range first, then narrowed)
    @test BV(UInt16(0x45)) === BV(0x45)
    @test_throws ArgumentError BV(UInt16(0x100))

    # isbits, concrete: a valid array element type
    @test isbitstype(BV)
    @test isconcretetype(BV)
    v = [BV(0x01), BV(0x02)]
    @test eltype(v) === BV

    # format recovery and trait forwarding, on type and instance
    x = BV(0x45)
    @test BinaryFormatOf(BV) === F === BinaryFormatOf(x)
    @test BitwidthOf(x) == 8 && PrecisionOf(x) == 4
    @test is_signed(x) && is_finite(x)
    @test CodeType(x) === UInt8
    @test ExponentBiasOf(x) == 8
end

@testset "Datum predicates" begin
    for (K, P, S, E) in [(8, 4, true, true), (8, 4, false, true),
                         (8, 4, true, false), (8, 4, false, false),
                         (3, 1, true, true), (16, 8, true, true), (16, 1, false, false)]
        F = AIFloats.Binary(K, P, S, E)
        BV = BinaryValue(F)
        U = CodeType(F)

        z = BV(zero(U))
        @test iszero(z) && isfinite(z) && !isnan(z) && !signbit(z) && !issubnormal(z)

        nv = BV(AIFloats.nan_code(F))
        @test isnan(nv) && !isfinite(nv) && !isinf(nv) && !signbit(nv)

        if E
            pinf = BV(AIFloats.posinf_code(F))
            @test isinf(pinf) && !isfinite(pinf) && !signbit(pinf)
            if S
                ninf = BV(AIFloats.neginf_code(F))
                @test isinf(ninf) && signbit(ninf)
            end
        end

        mf = MaxFiniteOf(F)
        @test isfinite(mf) && !signbit(mf) && !issubnormal(mf)
        mp = MinPositiveOf(F)
        @test isfinite(mp) && !signbit(mp)
        @test issubnormal(mp) == (P > 1)
        @test !issubnormal(MinNormalOf(F))
        P > 1 && @test issubnormal(MaxSubnormalOf(F))
    end
end

@testset "Total order and neighbors" begin
    for (K, P, S, E) in [(8, 4, true, true), (8, 3, false, true),
                         (8, 4, true, false), (6, 2, false, false),
                         (16, 8, true, true)]
        F = AIFloats.Binary(K, P, S, E)
        BV = BinaryValue(F)
        U = CodeType(F)
        xs = [BV(U(c)) for c in 0:(2^K - 1)]

        # keys are unique, NaN's is 0 and strictly the smallest
        ks = AIFloats.order_key.(xs)
        @test allunique(ks)
        nv = BV(AIFloats.nan_code(F))
        @test AIFloats.order_key(nv) == 0

        # sorting by key sorts finite datums by value; NaN lands FIRST
        sorted = sort(xs; by = AIFloats.order_key)
        @test isnan(sorted[1])
        vals = [decode(x) for x in sorted[2:end]]
        @test issorted(vals)
        @test allunique(vals)                 # single zero, no duplicate datum

        # NextGreaterThan walks the entire order: NaN → bottom → … → top → NaN
        n = 2^K
        x = nv
        seen = 0
        while true
            seen += 1
            seen > n && break
            y = NextGreaterThan(x)
            isnan(y) && break
            # strictly increasing along the walk
            @test AIFloats.order_key(y) > AIFloats.order_key(x)
            x = y
        end
        @test seen == n                       # visited every datum exactly once

        # NextLessThan inverts NextGreaterThan on every datum
        for c in 0:(2^K - 1)
            a = BV(U(c))
            isnan(a) && continue
            up = NextGreaterThan(a)
            isnan(up) || @test NextLessThan(up) === a
        end
        @test isnan(NextLessThan(nv))
    end
end

@testset "Classification" begin
    F = AIFloats.Binary(8, 4, SIGNED, EXTENDED)
    BV = BinaryValue(F)
    @test Class(BV(AIFloats.nan_code(F))) === ClassNaN
    @test Class(BV(AIFloats.posinf_code(F))) === ClassPosInf
    @test Class(BV(AIFloats.neginf_code(F))) === ClassNegInf
    @test Class(BV(0x00)) === ClassZero
    @test Class(MinPositiveOf(F)) === ClassPosSubnormal
    @test Class(MinNormalOf(F)) === ClassPosNormal
    @test Class(NextGreaterThan(BV(AIFloats.neginf_code(F)))) === ClassNegNormal

    # every datum of every corner format classifies, and class order matches key order
    for (S, E) in ((true, true), (true, false), (false, true), (false, false))
        G = AIFloats.Binary(6, 3, S, E)
        W = BinaryValue(G)
        xs = sort([W(UInt8(c)) for c in 0:63]; by = AIFloats.order_key)
        cs = Class.(xs)
        @test issorted(Int8.(cs))             # FPClass is declared in order position
    end
end

@testset "Show styles" begin
    F = AIFloats.Binary(8, 4, SIGNED, FINITE)
    x = BinaryValue(F)(0x45)
    old = get_show_style()
    try
        set_show_style!(:value)
        @test repr(x) == "1.625"
        set_show_style!(:codepoint)
        @test repr(x) == "0x45"
        set_show_style!(:datum)
        @test repr(x) == "(1.625 ⇆ 0x45)"
        set_show_style!(:typed)
        @test repr(x) == "Binary8p4sf(1.625 ⇆ 0x45)"
        # IOContext overrides the process default
        @test sprint(show, x; context = :binary_show_style => :value) == "1.625"
        # NaN prints as NaN, never throws, in every style
        nv = BinaryValue(F)(AIFloats.nan_code(F))
        for st in VALID_SHOW_STYLES
            set_show_style!(st)
            @test sprint(show, nv) isa String
        end
        @test_throws ArgumentError set_show_style!(:nope)
    finally
        set_show_style!(old)
    end
    # the datum type shows as its alias name
    @test sprint(show, Binary8p4sf) == "Binary8p4sf"
end

@testset "Aliases" begin
    @test Binary8p4se === BinaryValue(AIFloats.Binary(8, 4, SIGNED, EXTENDED))
    @test Binary3p1uf === BinaryValue(AIFloats.Binary(3, 1, UNSIGNED, FINITE))
    @test !isdefined(AIFloats, :binary8p4se)
    # K > 8 aliases are defined but not exported
    @test !isdefined(Main, :Binary16p8se)
    @test AIFloats.Binary16p8se === BinaryValue(AIFloats.Binary(16, 8, SIGNED, EXTENDED))
    @test AIFloats._NAMED[:Binary16p1uf] === AIFloats.Binary16p1uf
    @test length(AIFloats._NAMED) == 504
    @test formatname(Binary8p4se) === :Binary8p4se
    @test formatname(AIFloats.Binary(8, 4, SIGNED, EXTENDED)()) === :Binary8p4se
end

@testset "two-argument value construction" begin
    # BinaryValue(F, code::Unsigned) is a CODE POINT (types/binaryvalue.jl);
    # BinaryValue(F, x::Real) is a VALUE. Unsigned is the more specific
    # signature, so the two meanings cannot collide — that split is the point
    # of this testset, not an incidental property.
    for F in (Binary(8, 4, SIGNED, EXTENDED), Binary(5, 2, SIGNED, EXTENDED),
              Binary(6, 3, UNSIGNED, FINITE), Binary(16, 5, SIGNED, EXTENDED))
        T = BinaryValue(F)
        # the value forms all agree with the fully spelled constructor
        for v in (1.5, 1.3, 0.0, -0.5, 2.0, 1.5f0, Float16(1.5), big(1.25), 3, -7, true)
            @test BinaryValue(F, v) === T(v)
            @test BinaryValue{F}(v) === T(v)
            @test BinaryValue(F, v) isa T
        end
        # and the code-point meaning of an Unsigned survives
        for c in (0x00, 0x01, 0x05)
            u = CodeType(F)(c)
            @test BinaryValue(F, u) === BinaryValue{F}(u)
            @test codepoint(BinaryValue(F, u)) == u
        end
        # a value and a code point that share a numeral must NOT agree
        if Int(BitwidthOf(F)) >= 5
            @test BinaryValue(F, 0x03) !== BinaryValue(F, 3)
        end
        # keywords reach Convert, and the session default is honored
        @test BinaryValue(F, 1.3; projection = RTZ_SF) === Convert(T, RTZ_SF, 1.3)
        @test BinaryValue(F, 1.3; projection = RTP_SN) === Convert(T, RTP_SN, 1.3)
        let saved = DefaultProjection()
            try
                DefaultProjection!(RTZ_SF)
                @test BinaryValue(F, 1.3) === Convert(T, RTZ_SF, 1.3)
            finally
                DefaultProjection!(saved)
            end
        end
        # Rational is refused for this spelling too, with the same message
        @test_throws ArgumentError BinaryValue(F, 1 // 3)
        # inference and allocation, the reason both spellings carry @inline
        @test Base.return_types(BinaryValue, (Type{F}, Float64))[1] === T
        BinaryValue(F, 1.3); BinaryValue{F}(1.3)
        @test (@allocated BinaryValue(F, 1.3)) == 0
        @test (@allocated BinaryValue{F}(1.3)) == 0
    end
end
