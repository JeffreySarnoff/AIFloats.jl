using AIFloats
using Test
using Random
using Quadmath: Float128

# Phase 4 gate, kernels side: Shape A ≡ Shape B measured (not assumed);
# threading changes nothing; the stochastic kernel is a reproducible single
# stream; the warm path allocates independently of array length.

# run one op both ways: with tables allowed (Shape A) and with the build band
# closed (Shape B compute), and compare code points
function _both_shapes(op, F, ρ, As...)
    AIFloats.empty_tables!()
    a = getfield(AIFloats, op)(F, ρ, As...)
    old = AIFloats.TABLE_EAGER_BITS[]
    oldt = AIFloats.TERNARY_EAGER_BITS[]
    b = try
        AIFloats.TABLE_EAGER_BITS[] = -1
        AIFloats.TERNARY_EAGER_BITS[] = -1
        getfield(AIFloats, op)(F, ρ, As...)
    finally
        AIFloats.TABLE_EAGER_BITS[] = old
        AIFloats.TERNARY_EAGER_BITS[] = oldt
    end
    codepoint.(a) == codepoint.(b)
end

@testset "Shape A ≡ Shape B, measured" begin
    F = Binary(5, 3, SIGNED, EXTENDED)
    BV = BinaryValue(F)
    all32 = [fromcode(BV, c) for c in 0:31]
    # every operand pair, as two 1024-long arrays: the gather and the compute
    # loop must agree on every code-point combination
    A = repeat(all32, inner = 32)
    B = repeat(all32, outer = 32)
    for ρ in (RTE_SN, RTZ_SF, RTN_SP), op in (:Add, :Multiply, :Divide)
        @test _both_shapes(op, F, ρ, A, B)
    end
    for op in (:Exp, :Log, :Sin, :Softplus, :Negate)
        @test _both_shapes(op, F, RTE_SN, all32)
    end
    @test _both_shapes(:FMA, F, RTE_SN, A, B, reverse(A))
    # mixed formats: results land in a different format than the operands
    G = Binary(4, 2, UNSIGNED, FINITE)
    @test _both_shapes(:Add, G, RTE_SF, A, B)
    AIFloats.empty_tables!()
end

@testset "threading changes nothing" begin
    F = Binary(9, 4, SIGNED, EXTENDED)          # wide: compute path, no table
    BV = BinaryValue(F)
    A = [fromcode(BV, c % 512) for c in 0:2999]
    B = reverse(A)
    oldmin = AIFloats.THREAD_MIN_ELEMS[]
    oldsw = AIFloats.THREADED_KERNELS[]
    try
        AIFloats.THREADED_KERNELS[] = false
        seq = Add(F, RTE_SN, A, B)
        AIFloats.THREADED_KERNELS[] = true
        AIFloats.THREAD_MIN_ELEMS[] = 1         # force the threaded loop
        par = Add(F, RTE_SN, A, B)
        @test codepoint.(seq) == codepoint.(par)
    finally
        AIFloats.THREAD_MIN_ELEMS[] = oldmin
        AIFloats.THREADED_KERNELS[] = oldsw
    end
end

@testset "the stochastic kernel: sequential, single stream, reproducible" begin
    F = Binary(8, 4, SIGNED, EXTENDED)
    BV = BinaryValue(F)
    A = [fromcode(BV, c) for c in 0:255]
    B = reverse(A)
    ρ = RSA_SN
    s1 = Add(F, ρ, A, B; rng = Xoshiro(11))
    s2 = Add(F, ρ, A, B; rng = Xoshiro(11))
    @test codepoint.(s1) == codepoint.(s2)
    # the array kernel consumes the SAME stream the scalar calls would, in
    # index order — the sequential-by-construction property, asserted
    rng = Xoshiro(11)
    s3 = [Add(F, ρ, A[i], B[i]; rng) for i in eachindex(A)]
    @test codepoint.(s1) == codepoint.(s3)
    # stochastic never builds a table
    AIFloats.empty_tables!()
    Add(F, ρ, A, B; rng = Xoshiro(1))
    @test AIFloats.table_count() == 0
end

@testset "vmap / vmap! surface" begin
    F = Binary(5, 3, SIGNED, EXTENDED)
    BV = BinaryValue(F)
    A = [fromcode(BV, c) for c in 0:31]
    r = vmap(:Negate, F, RTE_SN, A)
    @test eltype(r) === BV
    @test codepoint.(r) == codepoint.(Negate(F, RTE_SN, A))
    dest = similar(A)
    @test vmap!(dest, :Negate, RTE_SN, A) === dest
    @test codepoint.(dest) == codepoint.(r)
    # datum-type spelling of the result format
    @test codepoint.(vmap(:Negate, BV, RTE_SN, A)) == codepoint.(r)
    # same-format convenience under the session default ρ
    @test codepoint.(Negate(A)) == codepoint.(Negate(F, DefaultProjection(), A))
    # shape mismatch refuses
    @test_throws DimensionMismatch vmap!(similar(A, 3), :Negate, RTE_SN, A)
    @test_throws DimensionMismatch vmap!(dest, :Add, RTE_SN, A, A[1:3])
end

@testset "Convert array forms" begin
    F = Binary(8, 4, SIGNED, EXTENDED)
    G = Binary(5, 3, SIGNED, EXTENDED)
    BG = BinaryValue(G)
    A = [fromcode(BG, c) for c in 0:31]
    r = Convert(F, RTE_SN, A)
    @test eltype(r) === BinaryValue(F)
    @test all(i -> r[i] === Convert(F, RTE_SN, A[i]), eachindex(A))
    # external float ingestion: exact widening then projection, per element
    x = Float32[0.5, 1.5, -2.25, 100.0]
    c = Convert(F, RTE_SN, x)
    @test decode.(c) == [decode(Convert(F, RTE_SN, Float64(v))) for v in x]
    c64 = Convert(BinaryValue(F), RTZ_SF, [0.1, 0.7])
    @test c64 == [Convert(F, RTZ_SF, 0.1), Convert(F, RTZ_SF, 0.7)]
    # every external scalar input family has the matching array surface and
    # preserves the scalar carrier route rather than narrowing through Float64
    for W in (Float128[Float128(1.1), Float128(-2.3)],
              BigFloat[BigFloat("1.1"), BigFloat("-2.3")],
              BigInt[big(1) << 200, -(big(1) << 200)])
        got = Convert(F, RTE_SN, W)
        @test got == [Convert(F, RTE_SN, v) for v in W]
    end
    # the datum-type spelling is a one-hop adapter over the same
    # type-specialized path; the format-instance spelling no longer exists
    @test Convert(BinaryValue(F), RTE_SN, x) == c
    @test codepoint.(Negate(BinaryValue(F), RTE_SN, r)) == codepoint.(Negate(F, RTE_SN, r))
    @test codepoint.(vmap(:Negate, BinaryValue(F), RTE_SN, r)) ==
          codepoint.(vmap(:Negate, F, RTE_SN, r))
    # stochastic Convert draws per element, reproducibly
    s1 = Convert(F, RSA_SN, A; rng = Xoshiro(5))
    s2 = Convert(F, RSA_SN, A; rng = Xoshiro(5))
    @test codepoint.(s1) == codepoint.(s2)
end

@testset "the warm path allocates independently of length" begin
    F = Binary(5, 3, SIGNED, EXTENDED)
    BV = BinaryValue(F)
    small = [fromcode(BV, c % 32) for c in 0:99]
    big = [fromcode(BV, c % 32) for c in 0:99_999]
    dsmall, dbig = similar(small), similar(big)
    v = Val(:Add)
    vmap!(dsmall, v, RTE_SN, small, small)      # warm: table built, code compiled
    vmap!(dbig, v, RTE_SN, big, big)
    a1 = @allocated vmap!(dsmall, v, RTE_SN, small, small)
    a2 = @allocated vmap!(dbig, v, RTE_SN, big, big)
    # the loop body allocates nothing: whatever constant the call itself costs,
    # a 1000× longer array costs the same
    @test a2 == a1
end

@testset "broadcasting routes through the kernels" begin
    # implmentplan.md Step 7. `vmap!` is the reference; the point of the hook
    # is that the broadcast form now produces IDENTICAL results by taking the
    # same path, and that everything the hook declines still goes to Base.
    T = Binary8p4se; F = BinaryFormatOf(T)
    A = [fromcode(T, (7i + 1) & 0xff) for i in 0:999]
    B = [fromcode(T, (3i + 5) & 0xff) for i in 0:999]
    C = [fromcode(T, (5i + 2) & 0xff) for i in 0:999]

    # every veneer arity the hook serves
    @test codepoint.(A .+ B)       == codepoint.(vmap(:Add, F, RTE_SN, A, B))
    @test codepoint.(A .- B)       == codepoint.(vmap(:Subtract, F, RTE_SN, A, B))
    @test codepoint.(A .* B)       == codepoint.(vmap(:Multiply, F, RTE_SN, A, B))
    @test codepoint.(A ./ B)       == codepoint.(vmap(:Divide, F, RTE_SN, A, B))
    @test codepoint.(.-(A))        == codepoint.(vmap(:Negate, F, RTE_SN, A))
    @test codepoint.(exp.(A))      == codepoint.(vmap(:Exp, F, RTE_SN, A))
    @test codepoint.(sqrt.(A))     == codepoint.(vmap(:Sqrt, F, RTE_SN, A))
    @test codepoint.(max.(A, B))   == codepoint.(vmap(:Maximum, F, RTE_SN, A, B))
    @test codepoint.(atan.(A, B))  == codepoint.(vmap(:ArcTan2, F, RTE_SN, A, B))
    @test codepoint.(fma.(A, B, C)) == codepoint.(vmap(:FMA, F, RTE_SN, A, B, C))
    @test codepoint.(clamp.(A, B, C)) == codepoint.(vmap(:Clamp, F, RTE_SN, A, B, C))

    # the in-place form lands in the same method
    let d = similar(A)
        d .= A .+ B
        @test codepoint.(d) == codepoint.(vmap(:Add, F, RTE_SN, A, B))
    end

    # shapes the hook must NOT intercept, each still matching the scalar veneer
    @test codepoint.((A .+ B) .* C) ==                              # fused chain
          codepoint.(vmap(:Multiply, F, RTE_SN, vmap(:Add, F, RTE_SN, A, B), C))
    @test codepoint.(A .+ B[1]) == codepoint.([a + B[1] for a in A])  # scalar operand
    @test eltype(A .+ 1.0) === Float64                                # mixed types promote
    @test eltype(A .< B) === Bool                                     # predicate
    @test isempty(A[1:0] .+ B[1:0])                                   # empty

    # non-vector shapes and non-Array containers
    let M = reshape(A[1:900], 30, 30)
        @test codepoint.(M .+ M) == codepoint.(vmap(:Add, F, RTE_SN, M, M))
        # a SHAPE broadcast: the operand's axes differ from dest's, so the
        # axes guard has to send it back to Base
        r = reshape(A[1:30], 30, 1)
        @test codepoint.(r .+ M) == codepoint.([A[i] + M[i, j] for i in 1:30, j in 1:30])
    end
    let V = view(A, 1:100)
        @test codepoint.(V .+ V) == codepoint.(vmap(:Add, F, RTE_SN, collect(V), collect(V)))
    end

    # the session default is honored, through the same speculation guard
    with_projection(RTZ_SF) do
        @test codepoint.(A .+ B) == codepoint.(vmap(:Add, F, RTZ_SF, A, B))
        @test codepoint.(exp.(A)) == codepoint.(vmap(:Exp, F, RTZ_SF, A))
    end
end
