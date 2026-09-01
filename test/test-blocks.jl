using AIFloats
using Test
using Random

# Phase 6 gate: block surface enumerated by (FS, FE) shape against an
# independent BigFloat composition; ScaledOp ≡ B=1 BlockOp; reductions vs
# high-precision references; the draft's five ConvertToBlockMaxAbsFinite
# NOTEs; BlockVector layout; packed round-trip exhaustive over lengths.

const T5 = BinaryValue(Binary5p2se)
const T8 = BinaryValue(Binary8p3se)
const U1 = BinaryValue(Binary8p1uf)                      # E8M0: the MX scale format
const T16 = BinaryValue(AIFloats.Binary16p1se)           # rung-3 scale (B = 16384)

rnd(rng, T) = fromcode(T, rand(rng, 0:(1 << Int(BitwidthOf(T))) - 1))
nanof(T) = fromcode(T, AIFloats.nan_code(T)); pinf(T) = fromcode(T, AIFloats.posinf_code(T))

# reference lane: the draft's ωMultiply on decoded values, single zero
function ref_lane(S, x)
    (isnan(S) || isnan(x)) && return BigFloat(NaN)
    ((iszero(S) && isinf(x)) || (isinf(S) && iszero(x))) && return BigFloat(NaN)
    p = setprecision(() -> BigFloat(S) * BigFloat(x), BigFloat, 3000)
    iszero(p) ? BigFloat(0) : p
end
# reference element: S-special rows, then v / S at 3000 bits and one projection
# (v/S is never within 2^-3000 of a rounding boundary unless exactly on it,
# in which case the 3000-bit quotient is exact)
function ref_elem(FR, ρ, v::BigFloat, S)
    (isnan(S) || isnan(v)) && return AIFloats.nan_code(FR)
    iszero(S) && return codepoint(project(FR, ρ, 0.0))
    isinf(S) && return codepoint(project(FR, ρ, Float64(sign(v)) * Float64(sign(S))))
    q = setprecision(() -> v / BigFloat(S), BigFloat, 3000)
    codepoint(project(FR, ρ, q))
end

@testset "blockdecode ≡ lane semantics" begin
    rng = MersenneTwister(1)
    for _ in 1:400
        b = Block(rnd(rng, T5), ntuple(_ -> rnd(rng, T5), 3))
        X = AIFloats.blockdecode(b)
        for i in 1:3
            @test isequal(BigFloat(X[i]), ref_lane(decode(b.s), decode(b.x[i])))
        end
    end
    binf = Block(pinf(T5), (zero(T5), one(T5)))
    @test isnan(AIFloats.blockdecode(binf)[1]) && AIFloats.blockdecode(binf)[2] == Inf
    @test_throws ArgumentError Block(one(T5), ())
    @test blocksize(binf) == 2 && scaleformat(binf) === BinaryFormatOf(T5) && elemformat(binf) === BinaryFormatOf(T5)
    @test Block(one(T5), one(T5), zero(T5)) == Block(one(T5), (one(T5), zero(T5)))
end

@testset "BlockOp ≡ reference composition, by (FS, FE) shape" begin
    rng = MersenneTwister(2)
    for B in (1, 2, 3, 16, 32), ρ in (RTE_SN, RTP_SN, RTZ_SF), FS in (T5, U1), trial in 1:(B <= 3 ? 40 : 6)
        b1 = Block(rnd(rng, FS), ntuple(_ -> rnd(rng, T5), B))
        b2 = Block(rnd(rng, FS), ntuple(_ -> rnd(rng, T5), B))
        sr = rnd(rng, FS)
        got = BlockAdd(T8, ρ, b1, b2, sr)
        @test got.s === sr
        X1 = AIFloats.blockdecode(b1); X2 = AIFloats.blockdecode(b2)
        for i in 1:B
            x, y = BigFloat(X1[i]), BigFloat(X2[i])
            v = if isnan(x) || isnan(y) || (isinf(x) && isinf(y) && x != y); BigFloat(NaN)
                elseif isinf(x) || isinf(y); isinf(x) ? x : y
                else setprecision(() -> x + y, BigFloat, 3000) end
            @test codepoint(got.x[i]) == ref_elem(BinaryFormatOf(T8), ρ, v, decode(sr))
        end
        gexp = BlockExp(T8, ρ, b1, sr)
        for i in 1:B
            x = BigFloat(X1[i])
            v = isnan(x) ? BigFloat(NaN) : x == -Inf ? BigFloat(0) : x == Inf ? BigFloat(Inf) :
                setprecision(() -> exp(x), BigFloat, 3000)
            # MPFR underflows exp(x) to exactly 0 past its exponent floor; the true
            # value is a positive infinitesimal, which directed modes must see
            (iszero(v) && isfinite(x)) && (v = ldexp(BigFloat(1), -100_000))
            @test codepoint(gexp.x[i]) == ref_elem(BinaryFormatOf(T8), ρ, v, decode(sr))
        end
    end
    # rung-3 scale: the general enclosure path with an exact BigFloat divisor
    bw = Block(T16(big(2.0)^8000), (T5(2.0), T5(-0.5)))
    @test decode(bw.s) == big(2.0)^8000
    g = BlockMultiply(T8, RTE_SN, bw, bw, T16(big(2.0)^16000))
    @test decode(g.x[1]) == 4.0 && decode(g.x[2]) == 0.25
    # datum-type-as-format spelling
    @test BlockAdd(BinaryFormatOf(T8), RTE_SN, bw, bw, T16(big(2.0)^8000)) == BlockAdd(T8, RTE_SN, bw, bw, T16(big(2.0)^8000))
end

@testset "S-special rows and ScaledOp ≡ B=1 BlockOp" begin
    xs = (one(T5), -one(T5), zero(T5), nanof(T5))
    bz = ConvertToBlock(T8, RTE_SN, xs, zero(T5))
    @test all(i -> i == 4 ? isnan(bz.x[i]) : iszero(bz.x[i]), 1:4)
    bi = ConvertToBlock(T8, RTE_SN, xs, pinf(T5))
    @test decode(bi.x[1]) == 1.0 && decode(bi.x[2]) == -1.0 && iszero(bi.x[3]) && isnan(bi.x[4])
    bn = ConvertToBlock(T8, RTE_SN, xs, nanof(T5))
    @test all(isnan, bn.x)
    rng = MersenneTwister(3)
    for _ in 1:300
        s1, x1, s2, x2 = rnd(rng, T5), rnd(rng, T5), rnd(rng, T5), rnd(rng, T5)
        @test ScaledAdd(T8, RTE_SN, s1, x1, s2, x2) ===
              BlockAdd(T8, RTE_SN, Block(s1, (x1,)), Block(s2, (x2,)), one(T5)).x[1]
        @test ScaledDivide(T8, RTE_SN, s1, x1, s2, x2) ===
              BlockDivide(T8, RTE_SN, Block(s1, (x1,)), Block(s2, (x2,)), one(T5)).x[1]
        @test ScaledFMA(T8, RTE_SN, s1, x1, s2, x2, s1, x2) ===
              BlockFMA(T8, RTE_SN, Block(s1, (x1,)), Block(s2, (x2,)), Block(s1, (x2,)), one(T5)).x[1]
    end
    @test ScaledExp(T8, RTZ_SF, one(T5), one(T5)) === Exp(T8, RTZ_SF, one(T5))
end

@testset "reductions vs references" begin
    rng = MersenneTwister(4)
    for B in (1, 3, 16, 32), trial in 1:40
        b = Block(rnd(rng, T5), ntuple(_ -> rnd(rng, T5), B))
        X = AIFloats.blockdecode(b)
        want = if any(isnan, X); NaN
        elseif any(==(Inf), X) && any(==(-Inf), X); NaN
        elseif any(isinf, X); Float64(X[findfirst(isinf, X)])
        else setprecision(() -> decode(project(T8, RTE_SN, sum(BigFloat, X; init = BigFloat(0)))), BigFloat, 3000)
        end
        @test isequal(decode(BlockReduceAdd(T8, RTE_SN, b)), want)
        by = Block(rnd(rng, T5), ntuple(_ -> rnd(rng, T5), B))
        Y = AIFloats.blockdecode(by)
        cls = [(isnan(X[i]) || isnan(Y[i]) || (iszero(X[i]) && isinf(Y[i])) || (isinf(X[i]) && iszero(Y[i]))) ? NaN :
               (isinf(X[i]) || isinf(Y[i])) ? Float64(sign(X[i]) * sign(Y[i])) * Inf : 1.0 for i in 1:B]
        wdot = if any(isnan, cls); NaN
        elseif any(isinf, cls); (any(==(Inf), cls) && any(==(-Inf), cls)) ? NaN : cls[findfirst(isinf, cls)]
        else setprecision(BigFloat, 3000) do
                decode(project(T8, RTE_SN, sum(BigFloat(X[i]) * BigFloat(Y[i]) for i in 1:B; init = BigFloat(0))))
             end
        end
        @test isequal(decode(BlockDotProduct(T8, RTE_SN, b, by)), wdot)
        wprod = if any(isnan, X) || (any(iszero, X) && any(isinf, X)); NaN
        elseif any(isinf, X); isodd(count(signbit, X)) ? -Inf : Inf
        elseif any(iszero, X); 0.0
        else setprecision(() -> decode(project(T8, RTE_SN, prod(BigFloat, X; init = BigFloat(1)))), BigFloat, 3000)
        end
        @test isequal(decode(BlockReduceMultiply(T8, RTE_SN, b)), wprod)
    end
    smax = MaxFiniteOf(T5)
    bx = Block(smax, ntuple(_ -> MaxFiniteOf(T5), 4))
    by = Block(MinPositiveOf(T5), ntuple(_ -> MinPositiveOf(T5), 4))
    wexact = setprecision(BigFloat, 3000) do
        decode(project(T8, RTE_SN, 4 * BigFloat(decode(smax))^2 * BigFloat(decode(MinPositiveOf(T5)))^2))
    end
    @test decode(BlockDotProduct(T8, RTE_SN, bx, by)) == wexact
    @test isnan(BlockReduceMultiply(T8, RTE_SN, Block(one(T5), (zero(T5), pinf(T5)))))
    @test decode(BlockReduceMultiply(T8, RTE_SN, Block(one(T5), (-one(T5), pinf(T5))))) == -Inf
    @test decode(BlockReduceMultiply(T8, RTE_SN, Block(T5(2.0), (T5(3.0), T5(2.0))))) == 24.0
    @test BlockDotProduct(T8, RTE_SN, bx, by; R = 0) === BlockDotProduct(BinaryFormatOf(T8), RTE_SN, bx, by)
end

@testset "ConvertToBlockMaxAbsFinite: the draft's NOTEs" begin
    allnan = ntuple(_ -> nanof(T5), 3)
    r = ConvertToBlockMaxAbsFinite(T5, T8, RTE_SN, RTE_SN, allnan)
    @test isnan(r.s) && all(isnan, r.x)                                      # NOTE 1
    allinf = ntuple(_ -> pinf(T5), 3)
    r = ConvertToBlockMaxAbsFinite(T5, T8, RTE_SN, RTE_SN, allinf)
    @test isinf(r.s) && all(v -> decode(v) == 1.0, r.x)                      # NOTE 2 (SN: s = ∞, elems ±1)
    mixed = (pinf(T5), T5(2.0), -pinf(T5))
    r = ConvertToBlockMaxAbsFinite(T5, T8, RTE_SN, RTE_SN, mixed)
    @test decode(r.s) == 2.0                                                 # NOTE 3: ∞ never sets the scale
    @test decode(r.x[1]) == Inf && decode(r.x[3]) == -Inf && decode(r.x[2]) == 1.0
    T3 = BinaryValue(Binary3p1se)
    rz = ConvertToBlockMaxAbsFinite(T3, T8, RTZ_SF, RTE_SN, ntuple(_ -> MinPositiveOf(T5), 3))
    iszero(rz.s) && @test all(iszero, rz.x)                                  # NOTE 4: zero scale ⇒ zeros
    r5 = ConvertToBlockMaxAbsFinite(U1, T8, RTP_SN, RTE_SF, (T5(3.0), T5(0.5), T5(-2.0)))
    @test decode(r5.s) == 4.0                                                # NOTE 5: RTP P=1 scale
    @test decode(r5.x[1]) == 0.75 && decode(r5.x[2]) == 0.125 && decode(r5.x[3]) == -0.5
    # ConvertFromBlock folds the scale in
    @test ConvertFromBlock(T8, RTE_SN, r5) == (T8(3.0), T8(0.5), T8(-2.0))
    # P = 1 scale: division by 2^k is the exact path
    bU = Block(U1(4.0), (T5(3.0), T5(0.5)))
    g = BlockAdd(T8, RTE_SN, bU, Block(U1(1.0), (zero(T5), zero(T5))), U1(2.0))
    @test decode(g.x[1]) == 6.0 && decode(g.x[2]) == 1.0
end

@testset "stochastic block ops reproduce per seed" begin
    σ = Projection(AIFloats.ρRSA(2), SN)
    b1 = Block(T5(2.0), (T5(1.5), T5(3.0))); b2 = Block(one(T5), (T5(0.25), T5(0.25)))
    o1 = BlockAdd(T5, σ, b1, b2, one(T5); rng = Xoshiro(9))
    o2 = BlockAdd(T5, σ, b1, b2, one(T5); rng = Xoshiro(9))
    @test o1 == o2
    @test BlockReduceAdd(T5, σ, b1; rng = Xoshiro(3)) === BlockReduceAdd(T5, σ, b1; rng = Xoshiro(3))
    @test ScaledAdd(T5, σ, one(T5), T5(1.5), one(T5), T5(0.25); rng = Xoshiro(5)) ===
          ScaledAdd(T5, σ, one(T5), T5(1.5), one(T5), T5(0.25); rng = Xoshiro(5))
    r1 = ConvertToBlockMaxAbsFinite(T5, T8, σ, σ, (T5(3.0), T5(0.5)); rng = Xoshiro(7))
    r2 = ConvertToBlockMaxAbsFinite(T5, T8, σ, σ, (T5(3.0), T5(0.5)); rng = Xoshiro(7))
    @test r1 == r2
end

@testset "BlockVector SoA" begin
    rng = MersenneTwister(5)
    blocks = [Block(rnd(rng, T5), ntuple(_ -> rnd(rng, T5), 4)) for _ in 1:10]
    bv = BlockVector(blocks)
    @test length(bv) == 10 && all(isequal(bv[j], blocks[j]) for j in 1:10)
    bv[3] = blocks[7]
    @test isequal(bv[3], blocks[7])
    @test size(bv.elems) == (4, 10) && eltype(bv) === Block{4, T5, T5}
    @test_throws DimensionMismatch BlockVector{4}(bv.scales, bv.elems[1:3, :])
end

@testset "packed round trip, exhaustive over lengths" begin
    rng = MersenneTwister(6)
    for T in BinaryValue.((Binary3p1se, Binary4p2se, Binary5p2se, Binary6p3se, Binary7p3se, Binary8p4se,
              AIFloats.Binary9p4se, AIFloats.Binary13p5uf, AIFloats.Binary16p8se))
        K = Int(BitwidthOf(T))
        for n in 0:70
            A = [rnd(rng, T) for _ in 1:n]
            pv = PackedVector(A)
            @test length(pv) == n && codepoint.(collect(pv)) == codepoint.(A)
            @test length(pv.data) == cld(n * K, 64)
            for i in 1:n
                pv[i] = A[n - i + 1]
            end
            @test codepoint.(collect(pv)) == codepoint.(reverse(A))
        end
        @test packing_saves(T) == (K != 8 && K != 16)
        A = [rnd(rng, T) for _ in 1:1000]
        pv = PackedVector(A)
        @test codepoint.(AIFloats.vmap(:Exp, T, RTE_SN, pv)) == codepoint.(Exp(T, RTE_SN, A))
        @test codepoint.(AIFloats.vmap(:Negate, BinaryFormatOf(T), RTZ_SF, pv)) == codepoint.(Negate(T, RTZ_SF, A))
    end
    σ = Projection(AIFloats.ρRSA(3), SN)
    A = [rnd(rng, T5) for _ in 1:700]
    pv = PackedVector(A)
    @test codepoint.(AIFloats.vmap(:Exp, T5, σ, pv; rng = Xoshiro(1))) == codepoint.(Exp(T5, σ, A; rng = Xoshiro(1)))
    @test isempty(AIFloats.vmap(:Exp, T5, RTE_SN, PackedVector(T5[])))
end

@testset "packed vmap ≡ unpacked vmap" begin
    # implmentplan.md Step 6: the pure-ρ tabled case bypasses the scratch tile
    # and gathers straight out of the packed words. The unpacked `vmap!` is the
    # semantic reference, including for the paths the fast route declines.
    for K in (3, 5, 7, 8, 9, 12), P in (1, 2), (S, D) in ((SIGNED, EXTENDED), (UNSIGNED, FINITE))
        P >= K && continue
        F = Binary(K, P, S, D); T = BinaryValue(F); nc = 2^K
        for N in (0, 1, 63, 64, 65, 1000)          # word boundaries and past them
            A = [fromcode(T, i % nc) for i in 0:N-1]
            pv = PackedVector(A)
            for op in (:Negate, :Exp, :Abs), ρ in (RTE_SN, RTZ_SF)
                @test codepoint.(vmap(op, F, ρ, pv)) == codepoint.(vmap(op, F, ρ, A))
            end
        end
    end
    # The branch-free bulk extractor reads an unaligned 64-bit window, which
    # runs past the last element's own bytes — `_safe_count` bounds it and a
    # scalar tail finishes the job. Lengths here straddle every byte and word
    # boundary precisely because that bound is the failure mode.
    for K in 3:16, (S, D) in ((SIGNED, EXTENDED), (UNSIGNED, FINITE))
        F = Binary(K, min(2, K - 1), S, D); T = BinaryValue(F); U = CodeType(F); nc = 2^K
        for len in vcat(0:70, [126, 127, 128, 129, 130, 255, 256, 257, 1000, 4097])
            xs = [fromcode(F, i % nc) for i in 0:len-1]
            pv = PackedVector(xs)
            @test codepoint.(collect(pv)) == codepoint.(xs)
            @test codepoint.(Vector(pv)) == codepoint.(xs)
            # getindex is the scalar reference the bulk path must match
            @test all(j -> codepoint(pv[j]) == codepoint(xs[j]), 1:len)
        end
    end
    @test AIFloats._safe_count(0, 5, 0) == 0          # empty buffer: no unsafe read
    @test AIFloats._safe_count(100, 5, 4) == 0        # under one window
    @test AIFloats._safe_count(10, 8, 8) <= 10        # never claims past the buffer

    # stochastic keeps the tiled adapter and must stay stream-identical
    let F = Binary(5, 2, SIGNED, EXTENDED), T = BinaryValue(F)
        A = [fromcode(T, i & 0x1f) for i in 0:999]; pv = PackedVector(A)
        for ρ in (RSA_SN, RSB_SF, RSC_SN)
            @test codepoint.(vmap(:Exp, F, ρ, pv; rng = MersenneTwister(7))) ==
                  codepoint.(vmap(:Exp, F, ρ, A;  rng = MersenneTwister(7)))
        end
        # a signature policy declines to tabulate falls back to the tiles
        old = AIFloats.TABLE_EAGER_BITS[]
        try
            AIFloats.TABLE_EAGER_BITS[] = -1
            @test codepoint.(vmap(:Exp, F, RTE_SN, pv)) == codepoint.(vmap(:Exp, F, RTE_SN, A))
        finally
            AIFloats.TABLE_EAGER_BITS[] = old
        end
    end
end

@testset "packed constructor invariants" begin
    A = AIFloats
    T = BinaryValue(Binary8p4se)
    @test_throws ArgumentError A.packedfromwords(T, UInt64[], -1)
    @test_throws DimensionMismatch A.packedfromwords(T, UInt64[], 1)
    @test_throws DimensionMismatch A.packedfromwords(T, UInt64[0, 0], 1)
    pv = PackedVector(fill(T(1.0), 9))
    @test pv.data isa Memory{UInt64}
    @test_throws MethodError resize!(pv.data, 0)
    @test collect(pv) == fill(T(1.0), 9)
    # the ambiguous representation constructor is gone: `PackedVector{T}(words, n)`
    # could not say whether it validated, copied, or took ownership
    @test_throws MethodError PackedVector{T}(UInt64[0], 1)
end

@testset "packed serialization and collections (improveapi3 Phase 6)" begin
    A = AIFloats
    for K in 3:16, (S, D) in ((SIGNED, EXTENDED), (UNSIGNED, FINITE))
        F = Binary(K, min(2, K - 1), S, D); T = BinaryValue(F)
        # exhaustive for small formats, boundary-crossing lengths for the rest
        lens = K <= 6 ? vcat(0:(2^K), [2^K + 1]) :
                        [0, 1, 7, 8, 63, 64, 65, 127, 128, 129, 1000]
        for n in lens
            xs = T[fromcode(F, (i - 1) % (2^K)) for i in 1:n]
            pv = PackedVector(xs)

            # words: cld(n*K, 64) of them, canonical padding, exact round trip
            w = A.packedwords(pv)
            @test length(w) == cld(n * K, 64)
            @test w isa Vector{UInt64}
            @test codepoint.(collect(A.packedfromwords(T, w, n))) == codepoint.(xs)

            # bytes: the MINIMAL cld(n*K, 8), little-endian, exact round trip
            b = A.packedbytes(pv)
            @test length(b) == cld(n * K, 8)
            @test codepoint.(collect(A.packedfrombytes(T, b, n))) == codepoint.(xs)

            # a source held by the caller must not alias the vector built from it
            if !isempty(w)
                w[1] = ~w[1]
                @test codepoint.(collect(A.packedfromwords(T, A.packedwords(pv), n))) ==
                      codepoint.(xs)
            end
        end
    end

    F = Binary(5, 3, SIGNED, FINITE); T = BinaryValue(F)
    xs = [fromcode(F, c) for c in 0:31]
    pv = PackedVector(xs)

    # a byte payload that does not fill its last word is SHORTER as bytes, and
    # that is the point of having a byte form at all
    @test length(A.packedbytes(pv)) == 20 < 8 * length(A.packedwords(pv))

    # nonzero padding is refused, in both forms: a reader cannot tell a corrupt
    # stream from a differently-conventioned writer and must not guess
    let n = 3, G = Binary(5, 3, SIGNED, FINITE), TG = BinaryValue(G)
        good_w = A.packedwords(PackedVector([fromcode(G, c) for c in 0:2]))
        bad_w = copy(good_w); bad_w[end] |= UInt64(1) << 40
        @test_throws ArgumentError A.packedfromwords(TG, bad_w, n)
        good_b = A.packedbytes(PackedVector([fromcode(G, c) for c in 0:2]))
        bad_b = copy(good_b); bad_b[end] |= 0x80
        @test_throws ArgumentError A.packedfrombytes(TG, bad_b, n)
        @test_throws DimensionMismatch A.packedfrombytes(TG, good_b, n + 1)
    end

    # length overflow is an OverflowError from checked arithmetic, not a wrap
    @test_throws OverflowError PackedVector{T}(undef, typemax(Int))

    # `similar` is ZERO-FILLED, not undef-packed. An undef BinaryValue can
    # carry bits above K, and packing one writes them into its neighbour's
    # share of the shared word -- this used to be `PackedVector(Vector{T}(undef, n))`.
    sm = similar(pv)
    @test length(sm) == length(pv) && all(iszero ∘ codepoint, sm)
    @test similar(pv, BinaryValue(Binary8p4se)) isa PackedVector{BinaryValue(Binary8p4se)}
    @test similar(pv, T, (7,)) isa PackedVector{T} && length(similar(pv, T, (7,))) == 7
    @test similar(pv, Float64, (2, 3)) isa Matrix{Float64}     # not packable

    # copy is an independent PACKED copy; mutating one leaves the other alone
    c = copy(pv)
    @test c isa PackedVector{T} && codepoint.(collect(c)) == codepoint.(xs)
    c[1] = fromcode(F, 7)
    @test codepoint(pv[1]) == 0x00 && codepoint(c[1]) == 0x07

    # each copyto! direction, and the shape refusals
    d = Vector{T}(undef, 32); copyto!(d, pv)
    @test codepoint.(d) == codepoint.(xs)
    p2 = similar(pv); copyto!(p2, xs)
    @test codepoint.(collect(p2)) == codepoint.(xs)
    p3 = similar(pv); copyto!(p3, pv)
    @test codepoint.(collect(p3)) == codepoint.(xs)
    @test_throws DimensionMismatch copyto!(Vector{T}(undef, 5), pv)
    @test_throws DimensionMismatch copyto!(similar(pv, T, (5,)), xs)
    @test_throws DimensionMismatch copyto!(similar(pv, T, (5,)), pv)

    # collect/Vector are UNPACKED copies. Compared by CODE POINT: `xs` contains
    # the format's NaN datum, and `==` on a NaN is false by IEEE rule, so an
    # array `==` here would report a difference that is not one.
    @test collect(pv) isa Vector{T}
    @test codepoint.(Vector(pv)) == codepoint.(collect(pv)) == codepoint.(xs)
end

@testset "BlockVector collection contracts (improveapi3 Phase 6.8)" begin
    F = Binary(5, 3, SIGNED, FINITE); T = BinaryValue(F)
    S = Binary(8, 1, UNSIGNED, FINITE); ST = BinaryValue(S)
    bs = [Block(ST(1.0), (T(1.0), T(2.0))), Block(ST(2.0), (T(0.5), T(0.25)))]
    bv = BlockVector(bs)
    @test collect(bv) == bs && Vector(bv) == bs

    # independent copy
    c = copy(bv)
    c[1] = bs[2]
    @test bv[1] == bs[1] && c[1] == bs[2]
    # and the SoA columns are independent too, not merely the outer struct
    c.elems[1, 2] = T(8.0)
    @test bv[2] == bs[2]

    # similar preserves the SoA representation for a Block element type of the
    # same block size, and ZERO-FILLS: an undef BinaryValue can carry bits
    # above K, which every decode and packing step assumes it cannot
    sm = similar(bv)
    @test sm isa BlockVector && length(sm) == length(bv)
    @test all(j -> iszero(codepoint(sm[j].s)) && all(iszero ∘ codepoint, sm[j].x), 1:length(sm))
    @test similar(bv, eltype(bv), (5,)) isa BlockVector
    @test length(similar(bv, eltype(bv), (5,))) == 5
    @test similar(bv, Float64, (2, 2)) isa Matrix{Float64}     # no SoA meaning

    # exact-type copyto!, each direction, with shape refusals
    b2 = similar(bv); copyto!(b2, bv); @test collect(b2) == bs
    b3 = similar(bv); copyto!(b3, bs); @test collect(b3) == bs
    v = Vector{eltype(bv)}(undef, 2); copyto!(v, bv); @test v == bs
    @test_throws DimensionMismatch copyto!(similar(bv, eltype(bv), (1,)), bv)
    @test_throws DimensionMismatch copyto!(similar(bv, eltype(bv), (1,)), bs)
    @test_throws DimensionMismatch copyto!(Vector{eltype(bv)}(undef, 1), bv)

    # the source vector of blocks must not alias the BlockVector built from it
    bs[1] = bs[2]
    @test bv[1] != bv[2]
end


@testset "format-instance block adapters" begin
    F = Binary(5, 2, SIGNED, EXTENDED); T = BinaryValue(F)
    S = Binary(8, 1, UNSIGNED, FINITE); ST = BinaryValue(S)
    b = Block(ST(1.0), (T(1.0), T(2.0)))
    # the datum-type spelling and the format spelling name the same call
    @test BlockReduceAdd(BinaryValue(F), RTE_SN, b) == BlockReduceAdd(F, RTE_SN, b)
    @test ConvertFromBlock(BinaryValue(F), RTE_SN, b) == ConvertFromBlock(F, RTE_SN, b)
    @test packing_saves(BinaryValue(F)) == packing_saves(F)
end

@testset "block reductions: Dyadic accumulation ≡ BigFloat oracle" begin
    # implmentplan.md Step 8. The BigFloat path stays live as both the fallback
    # (wide lane spreads leave Dyadic's exact band) and the reference here.
    A = AIFloats
    refadd(fr, ρ, b::Block{B,Sx,Ex}) where {B,Sx,Ex} =
        A._finish(fr, ρ, 0, A._reduce_add_value(A.blockdecode(b),
                  A._lane_sum_prec(BinaryFormatOf(Sx), BinaryFormatOf(Ex), B)))

    rng = MersenneTwister(20260828)
    scales = BinaryValue.((Binary8p1uf, Binary8p3se, Binary5p2se))
    elems  = BinaryValue.((Binary8p4se, Binary5p2se, Binary6p1uf))
    for Sf in scales, Ef in elems, B in (1, 4, 16, 32)
        KS = Int(BitwidthOf(Sf)); KE = Int(BitwidthOf(Ef))
        US = CodeType(BinaryFormatOf(Sf)); UE = CodeType(BinaryFormatOf(Ef))
        for _ in 1:8
            sd = Sf(US(rand(rng, 0:2^KS - 1)))
            bx = Block(sd, ntuple(i -> Ef(UE(rand(rng, 0:2^KE - 1))), B))
            by = Block(sd, ntuple(i -> Ef(UE(rand(rng, 0:2^KE - 1))), B))
            for ρ in (RTE_SN, RTZ_SF, RTP_SN)
                @test codepoint(BlockReduceAdd(Ef, ρ, bx)) ==
                      codepoint(refadd(BinaryFormatOf(Ef), ρ, bx))
                # the dot product's own oracle is the same sum at BigFloat width
                @test isequal(BlockDotProduct(Ef, ρ, bx, by),
                              BlockDotProduct(Ef, ρ, by, bx))          # symmetry
            end
        end
    end

    # special-value lanes must stay entirely on the generic fold
    let E = BinaryValue(Binary8p4se), S = BinaryValue(Binary8p3se), FE = BinaryFormatOf(E)
        nan  = fromcode(FE, AIFloats.nan_code(FE))
        pinf = fromcode(FE, AIFloats.posinf_code(FE))
        ninf = fromcode(FE, AIFloats.neginf_code(FE))
        mx, mn, mp = MaxFiniteOf(E), MinFiniteOf(E), MinPositiveOf(E)
        pats = (ntuple(_ -> E(0.0), 8),
                ntuple(i -> i == 3 ? nan  : E(1.0), 8),
                ntuple(i -> i == 2 ? pinf : E(1.0), 8),
                ntuple(i -> i == 5 ? ninf : E(1.0), 8),
                ntuple(i -> i == 1 ? pinf : (i == 2 ? ninf : E(1.0)), 8),
                ntuple(_ -> mx, 8),
                ntuple(i -> isodd(i) ? mx : mn, 8),
                ntuple(i -> isodd(i) ? mx : mp, 8),
                ntuple(i -> isodd(i) ? mx : E(-Float64(mx)), 8))
        for sd in (one(S), S(0.0), MaxFiniteOf(S)), xs in pats,
            ρ in (RTE_SN, RTZ_SF, RTP_SN, RTN_SF)
            b = Block(sd, xs)
            @test codepoint(BlockReduceAdd(E, ρ, b)) ==
                  codepoint(refadd(BinaryFormatOf(E), ρ, b))
        end
    end

    # a rung-1 format whose lane spread EXCEEDS Dyadic's exact alignment band:
    # the guard must decline and the BigFloat fallback must still be right
    for (K, P) in ((8, 1), (10, 2), (12, 2))
        F = Binary(K, P, SIGNED, EXTENDED); T = BinaryValue(F)
        b = Block(one(T), (MaxFiniteOf(T), MinPositiveOf(T)))
        X = AIFloats.blockdecode(b)
        @test X isa NTuple{2,Float64}                    # concrete decode …
        @test AIFloats._dyadic_sum(X) === nothing        # … but out of band
        @test codepoint(BlockReduceAdd(F, RTE_SN, b)) ==
              codepoint(refadd(F, RTE_SN, b))
    end

    # and the payoff: no allocation on the common path
    let E = BinaryValue(Binary8p4se), S = BinaryValue(Binary8p3se)
        b = Block(one(S), ntuple(i -> fromcode(E, (7i + 3) & 0x7f), 16))
        BlockReduceAdd(E, RTE_SN, b)
        @test (@allocated BlockReduceAdd(E, RTE_SN, b)) == 0
        @test AIFloats.blockdecode(b) isa NTuple{16,Float64}
        # `blockdecode` itself keeps a union return (NTuple{B,Float64} or the
        # general carrier tuple) — that is its honest general-purpose type, and
        # crossing it costs one box. The reductions above are the hot callers
        # and they bypass it via `_f64_lanes`, which is why THEY are free.
        @test (@allocated AIFloats._f64_lanes(b)) == 0
        bx2 = Block(one(S), ntuple(i -> fromcode(E, (5i + 1) & 0x7f), 16))
        BlockDotProduct(E, RTE_SN, b, bx2)
        @test (@allocated BlockDotProduct(E, RTE_SN, b, bx2)) == 0
    end
end

@testset "max-abs fold runs in the decoded carrier" begin
    # float128use.md §6: `MaximumFinite` SELECTS an operand rather than
    # combining significands, so the fold consumes no precision and needs none
    # added. Lifting every lane through `_exactbig` first cost 1,006 ns and 113
    # allocations for what is a comparison chain; in the lanes' own carrier it
    # is 7.5 ns and none. The reference is that BigFloat fold.
    A = AIFloats
    function reffold(fs, fr, ρs, ρ, xs::NTuple{B,BinaryValue}) where {B}
        X = map(decode, xs)
        M = map(x -> A._exactbig(A.ωeval(Val(:Abs), x)), X)
        S = foldl((a, m) -> A.ωeval(Val(:MaximumFinite), a, m), M; init = A._cnan(BigFloat))
        A.blockproject(fr, ρ, project(fs, ρs, S), X)
    end
    rng = MersenneTwister(77)
    elems = (BinaryValue(Binary8p4se), BinaryValue(Binary5p2se), BinaryValue(Binary6p1uf),
             BinaryValue(Binary(16, 5, SIGNED, EXTENDED)),   # rung 2: Float128 lanes
             BinaryValue(Binary(16, 1, SIGNED, EXTENDED)))   # rung 3: exact carrier
    for Ef in elems, Sf in BinaryValue.((Binary8p1uf, Binary8p3se)), B in (1, 4, 16)
        KE = Int(BitwidthOf(Ef)); UE = CodeType(BinaryFormatOf(Ef))
        for _ in 1:6, ρ in (RTE_SN, RTZ_SF, RTP_SN)
            xs = ntuple(i -> Ef(UE(rand(rng, 0:2^min(KE, 16) - 1))), B)
            got = ConvertToBlockMaxAbsFinite(BinaryFormatOf(Sf), BinaryFormatOf(Ef), ρ, ρ, xs)
            want = reffold(BinaryFormatOf(Sf), BinaryFormatOf(Ef), ρ, ρ, xs)
            @test codepoint(got.s) == codepoint(want.s)
            @test codepoint.(got.x) == codepoint.(want.x)
        end
    end
    # every special-value shape the fold algebra has to preserve
    let E = BinaryValue(Binary8p4se), FE = BinaryFormatOf(E), Sf = BinaryValue(Binary8p3se)
        nan  = fromcode(FE, AIFloats.nan_code(FE))
        pinf = fromcode(FE, AIFloats.posinf_code(FE))
        ninf = fromcode(FE, AIFloats.neginf_code(FE))
        pats = (ntuple(_ -> nan, 8), ntuple(_ -> pinf, 8), ntuple(_ -> ninf, 8),
                ntuple(i -> i == 1 ? nan  : E(1.0), 8),
                ntuple(i -> i == 1 ? pinf : E(1.0), 8),
                ntuple(i -> i == 1 ? ninf : (i == 2 ? nan : E(1.0)), 8),
                ntuple(_ -> E(0.0), 8),
                ntuple(i -> isodd(i) ? MaxFiniteOf(E) : MinFiniteOf(E), 8))
        for xs in pats, ρ in (RTE_SN, RTZ_SF, RTP_SN, RTN_SF)
            got  = ConvertToBlockMaxAbsFinite(BinaryFormatOf(Sf), FE, ρ, ρ, xs)
            want = reffold(BinaryFormatOf(Sf), FE, ρ, ρ, xs)
            @test codepoint(got.s) == codepoint(want.s)
            @test codepoint.(got.x) == codepoint.(want.x)
        end
    end
    # the MX shape (P = 1 power-of-two scale) is exact end to end and allocates nothing
    let E = BinaryValue(Binary8p4se), S1 = BinaryValue(Binary8p1uf)
        xs = ntuple(i -> fromcode(E, (7i + 3) & 0x7f), 16)
        ConvertToBlockMaxAbsFinite(BinaryFormatOf(S1), BinaryFormatOf(E), RTE_SN, RTE_SN, xs)
        @test (@allocated ConvertToBlockMaxAbsFinite(BinaryFormatOf(S1), BinaryFormatOf(E),
                                                     RTE_SN, RTE_SN, xs)) == 0
    end
end

@testset "BlockReduceMultiply: exact Dyadic product" begin
    # float128use.md deferred this on the reasoning that successive products
    # consume the 113-bit significand quickly. Instrumenting it (which the plan
    # required before implementing) showed the reasoning was wrong: Dyadic(v)
    # for a datum carries only that datum's SIGNIFICANT bits, at most P of them,
    # so sixteen P=4 lanes reach 64 bits against mul_dy's 96-bit precondition.
    # Acceptance among blocks that actually reach the accumulator is ~100% at
    # B <= 16. The BigFloat fold stays as fallback and as the reference here.
    A = AIFloats
    function refmul(fr, ρ, b::Block{B,S,E}) where {B,S,E}
        X = A.blockdecode(b)
        res = if any(isnan, X) || (any(iszero, X) && any(isinf, X)); A._cnan(BigFloat)
        elseif any(isinf, X); isodd(count(signbit, X)) ? A._cninf(BigFloat) : A._cinf(BigFloat)
        elseif any(iszero, X); A._czero(BigFloat)
        else
            setprecision(BigFloat, A._lane_prod_prec(BinaryFormatOf(S), BinaryFormatOf(E), B)) do
                acc = BigFloat(1); for v in X; acc *= A._exactbig(v); end; acc
            end
        end
        A._finish(fr, ρ, 0, res)
    end
    rng = MersenneTwister(31)
    for Sf in BinaryValue.((Binary8p1uf, Binary8p3se, Binary5p2se)),
        Ef in (Binary8p4se, Binary5p2se, BinaryValue(Binary(16, 5, SIGNED, EXTENDED))),
        B in (1, 2, 4, 16, 32)
        KS = Int(BitwidthOf(Sf)); KE = Int(BitwidthOf(Ef))
        US = CodeType(BinaryFormatOf(Sf)); UE = CodeType(BinaryFormatOf(Ef))
        for _ in 1:6, ρ in (RTE_SN, RTZ_SF, RTP_SN, RTN_SF)
            b = Block(Sf(US(rand(rng, 0:2^KS - 1))),
                      ntuple(i -> Ef(UE(rand(rng, 0:2^min(KE, 16) - 1))), B))
            @test codepoint(BlockReduceMultiply(BinaryFormatOf(Ef), ρ, b)) ==
                  codepoint(refmul(BinaryFormatOf(Ef), ρ, b))
        end
    end
    # every shape of the fold algebra: NaN, 0·∞, sign parity over infinities,
    # a zero lane, and the extremes
    let E = BinaryValue(Binary8p4se), FE = BinaryFormatOf(E), Sf = BinaryValue(Binary8p3se)
        nan  = fromcode(FE, AIFloats.nan_code(FE))
        pinf = fromcode(FE, AIFloats.posinf_code(FE))
        ninf = fromcode(FE, AIFloats.neginf_code(FE))
        pats = (ntuple(_ -> E(0.0), 8),
                ntuple(i -> i == 1 ? nan  : E(1.5), 8),
                ntuple(i -> i == 1 ? pinf : E(1.5), 8),
                ntuple(i -> i == 1 ? ninf : E(1.5), 8),
                ntuple(i -> i == 1 ? pinf : (i == 2 ? E(0.0) : E(1.5)), 8),   # 0·∞
                ntuple(i -> i <= 2 ? ninf : E(1.5), 8),                       # even # of ∞
                ntuple(i -> isodd(i) ? E(-1.5) : E(1.5), 8),                  # sign parity
                ntuple(_ -> MaxFiniteOf(E), 8), ntuple(_ -> MinPositiveOf(E), 8))
        for xs in pats, sd in (one(Sf), Sf(0.0), MaxFiniteOf(Sf)), ρ in (RTE_SN, RTZ_SF, RTP_SN)
            b = Block(sd, xs)
            @test codepoint(BlockReduceMultiply(FE, ρ, b)) == codepoint(refmul(FE, ρ, b))
        end
    end
    # the accumulator must decline rather than round when the band is exceeded
    @test AIFloats._dyadic_prod(ntuple(_ -> 1.0 + 2.0^-40, 32)) === nothing
    # and the common shape is allocation-free
    let E = BinaryValue(Binary8p4se), S = BinaryValue(Binary8p3se)
        b = Block(one(S), ntuple(i -> fromcode(E, (7i + 3) & 0x7f), 16))
        BlockReduceMultiply(BinaryFormatOf(E), RTE_SN, b)
        @test (@allocated BlockReduceMultiply(BinaryFormatOf(E), RTE_SN, b)) == 0
    end
end
