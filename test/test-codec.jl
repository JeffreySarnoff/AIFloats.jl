using AIFloats
using Test

# the Phase 1 gate: the codec, exhaustively, over every code point of all 504
# formats (7,602,160 code points).
#
# For each code point:
#   - _canonical (the integer-space field split) and encode invert each other
#   - decode agrees with the canonical form: value == sign · S · 2^Q, exactly
#   - specials land where the layout says they land
# The value comparison runs in Rational{BigInt}: a P3109 datum IS a dyadic
# rational, so every comparison is a decision, not an estimate.

exactrational(x::AbstractFloat) = Rational{BigInt}(BigFloat(x))
exactrational(x::AIFloats.Dyadic) = Rational{BigInt}(x)      # the rung-3 carrier: exact by definition

function sweepformat(F)
    U = CodeType(F)
    BV = BinaryValue(F)
    n = 2^Int(BitwidthOf(F))
    P = Int(PrecisionOf(F))
    B = ExponentBiasOf(F)
    npoints = 0

    for c in 0:(n - 1)
        code = U(c)
        x = BV(code)
        kind, sgn, S, Q = AIFloats._canonical(F, code)
        v = decode(x)

        if kind === :nan
            code == AIFloats.nan_code(F) || return false, npoints
            isnan(v) || return false, npoints
        elseif kind === :posinf
            code == AIFloats.posinf_code(F) || return false, npoints
            (isinf(v) && !signbit(v)) || return false, npoints
        elseif kind === :neginf
            code == AIFloats.neginf_code(F) || return false, npoints
            (isinf(v) && signbit(v)) || return false, npoints
        else
            # canonical bounds: S in 0:2^P - 1 after the split, Q at least the
            # subnormal floor
            (0 <= S < Int64(1) << P) || return false, npoints
            S == 0 || Q >= 2 - B - P || return false, npoints
            # encode inverts the split
            AIFloats.encode(F, sgn, S, Q) == code || return false, npoints
            # decode agrees with the canonical form, exactly
            want = sgn * BigInt(S) * (Rational{BigInt}(2)^Int(Q))
            exactrational(v) == want || return false, npoints
        end
        npoints += 1
    end
    true, npoints
end

@testset "Codec round-trip, exhaustive" begin
    total = 0
    bad = String[]
    for K in 3:16, P in 1:K, S in (true, false), E in (true, false)
        S && P >= K && continue
        F = AIFloats.Binary(K, P, S, E)
        ok, npoints = sweepformat(F)
        ok || push!(bad, string(formatname(F)))
        total += npoints
    end
    @test isempty(bad)
    @test total == 7_602_160
end

@testset "Layout spot checks" begin
    # the worked example: binary8p4se, matching the P3109 slide table
    F = AIFloats.Binary(8, 4, SIGNED, EXTENDED)
    @test AIFloats.nan_code(F) == 0x80          # NaN at the would-be −0
    @test AIFloats.posinf_code(F) == 0x7f
    @test AIFloats.neginf_code(F) == 0xff
    @test codepoint(MaxFiniteOf(F)) == 0x7e
    @test decode(BinaryValue(F)(0x45)) == 1.625

    # unsigned: NaN at the top; the −Inf slot aliases it, so NaN wins
    G = AIFloats.Binary(8, 4, UNSIGNED, EXTENDED)
    @test AIFloats.nan_code(G) == 0xff
    @test AIFloats.posinf_code(G) == 0xfe
    @test codepoint(MaxFiniteOf(G)) == 0xfd
    @test isnan(decode(BinaryValue(G)(0xff)))

    # single zero: code 0 decodes to +0.0 with no sign, everywhere
    for (S, E) in ((true, true), (true, false), (false, true), (false, false))
        H = AIFloats.Binary(5, 2, S, E)
        z = decode(BinaryValue(H)(0x00))
        @test z == 0.0 && !signbit(z)
    end

    # tiny format, full table: binary3p1uf (B = 4) is [0, ⅛, ¼, ½, 1, 2, 4, NaN]
    t = codetable(AIFloats.Binary(3, 1, UNSIGNED, FINITE))
    @test [r.value for r in t[1:7]] == [0.0, 0.125, 0.25, 0.5, 1.0, 2.0, 4.0]
    @test isnan(t[8].value)

    # decode is exact on the wide carriers too
    W = AIFloats.Binary(16, 1, UNSIGNED, FINITE)   # B = 32768: the exact carrier
    @test AIFloats.datumcarrier(W) === AIFloats.Dyadic
    mp = decode(MinPositiveOf(W))
    @test exactrational(mp) == 1 // (big(2)^32767)  # 2^(2 - P - B), exact
    @test exponent(BigFloat(mp)) == 2 - 1 - 32768  # 2^(2 - P - B)

    # table and compute policies agree where both exist (K = 8 boundary)
    F8 = AIFloats.Binary(8, 5, SIGNED, EXTENDED)
    for c in 0x00:0xff
        @test isequal(AIFloats._decode_compute(F8, c),
                      decode(BinaryValue(F8)(c)))
    end
end

@testset "Monotone decode" begin
    # within the non-negative codes, decode is strictly increasing up to the
    # last finite — the property that makes code order and value order agree
    for (K, P, S, E) in [(8, 4, true, true), (8, 8, false, false),
                         (10, 5, true, false), (16, 10, false, true)]
        F = AIFloats.Binary(K, P, S, E)
        BV = BinaryValue(F)
        U = CodeType(F)
        top = Int(AIFloats._maxfinite_code(F))
        prev = decode(BV(zero(U)))
        for c in 1:top
            cur = decode(BV(U(c)))
            @test cur > prev
            prev = cur
        end
    end
end
