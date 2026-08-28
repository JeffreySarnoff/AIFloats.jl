# array suite: table gather vs compute, threading, broadcasting, sorting,
# packed storage, and blocks. Sizes are powers of two so Gelem/s compares
# directly across rows.

section("arrays — vmap! and broadcasting")

const AT8  = binary8p4se
const AT12 = BinaryValue(Binary(12, 6, SIGNED, EXTENDED))
const AF8, AF12 = BinaryFormatOf(AT8), BinaryFormatOf(AT12)

# deterministic code populations; `stride` decorrelates the two operands
codes8(n, stride = 1)  = [AT8(UInt8((stride * i + 1) & 0xff)) for i in 0:n-1]
codes12(n, stride = 1) = [AT12(UInt16((stride * i + 1) & 0xfff)) for i in 0:n-1]

for N in (4096, 65536)
    A8, B8, D8 = codes8(N), codes8(N, 3), similar(codes8(N))
    A12, B12, D12 = codes12(N), codes12(N, 3), similar(codes12(N))
    vmap!(D8, Val(:Add), RTE_SN, A8, B8); vmap!(D12, Val(:Add), RTE_SN, A12, B12)
    vmap!(D8, Val(:Exp), RTE_SN, A8);     vmap!(D12, Val(:Exp), RTE_SN, A12)
    row("vmap! Add K=8  warm table N=$N",   (@b vmap!($D8, Val(:Add), RTE_SN, $A8, $B8)); elems = N)
    row("vmap! Add K=12 compute   N=$N",   (@b vmap!($D12, Val(:Add), RTE_SN, $A12, $B12)); elems = N)
    withflags(threaded = false) do
        vmap!(D12, Val(:Add), RTE_SN, A12, B12)
        row("vmap! Add K=12 compute 1thr N=$N", (@b vmap!($D12, Val(:Add), RTE_SN, $A12, $B12)); elems = N)
    end
    row("vmap! Exp K=8  warm table N=$N",   (@b vmap!($D8, Val(:Exp), RTE_SN, $A8)); elems = N)
    row("vmap! Exp K=12 warm table N=$N",   (@b vmap!($D12, Val(:Exp), RTE_SN, $A12)); elems = N)
    row("A .+ B      K=8  N=$N",            (@b $A8 .+ $B8); elems = N)
    row("A .+ B      K=12 N=$N",            (@b $A12 .+ $B12); elems = N)
    row("exp.(A)     K=8  N=$N",            (@b exp.($A8)); elems = N)
    row("fma.(A,B,A) K=8  N=$N",            (@b fma.($A8, $B8, $A8)); elems = N)
    row("Float64.(A) K=8  N=$N",            (@b Float64.($A8)); elems = N)
    row("sort(A)     K=8  N=$N",            (@b sort($A8)); elems = N)
    row("sort(A)     K=12 N=$N",            (@b sort($A12)); elems = N)
    println()
end

section("arrays — cold table build (evals=1)")

let N = 4096, A8 = codes8(4096), B8 = codes8(4096, 3), D8 = similar(codes8(4096))
    withflags() do
        row("empty_tables! + vmap! Add K=8 N=$N",
            (@b (AIFloats.empty_tables!(); vmap!($D8, Val(:Add), RTE_SN, $A8, $B8)) evals=1); elems = N)
    end
    withflags() do
        row("empty_tables! + vmap! Exp K=8 N=$N",
            (@b (AIFloats.empty_tables!(); vmap!($D8, Val(:Exp), RTE_SN, $A8)) evals=1); elems = N)
    end
end

section("arrays — packed storage")

let N = 65536
    A8 = codes8(N)
    T5 = BinaryValue(Binary(5, 2, SIGNED, EXTENDED))
    A5 = [T5(UInt8((i + 1) & 0x1f)) for i in 0:N-1]
    F5 = BinaryFormatOf(T5)
    P8, P5 = PackedVector(A8), PackedVector(A5)
    vmap(:Negate, AF8, RTE_SN, P8); vmap(:Negate, F5, RTE_SN, P5)
    row("PackedVector(A)   K=8  N=$N",   (@b PackedVector($A8)); elems = N)
    row("PackedVector(A)   K=5  N=$N",   (@b PackedVector($A5)); elems = N)
    row("collect(P)        K=5  N=$N",   (@b collect($P5)); elems = N)
    row("P[i]              K=5",         @b $P5[1000])
    row("vmap Negate packed K=5 N=$N",   (@b vmap(:Negate, $F5, RTE_SN, $P5)); elems = N)
    row("vmap Negate vector K=5 N=$N",   (@b vmap(:Negate, $F5, RTE_SN, $A5)); elems = N)
    row("vmap Exp    packed K=5 N=$N",   (@b vmap(:Exp, $F5, RTE_SN, $P5)); elems = N)
    row("vmap Exp    vector K=5 N=$N",   (@b vmap(:Exp, $F5, RTE_SN, $A5)); elems = N)
end

section("arrays — blocks")

let S = binary8p3se, E = binary8p4se
    for B in (16, 32)
        xs = ntuple(i -> E(UInt8((7i + 3) & 0x7f)), B)
        ys = ntuple(i -> E(UInt8((5i + 1) & 0x7f)), B)
        bx, by = Block(one(S), xs), Block(one(S), ys)
        row("blockdecode        B=$B",    @b AIFloats.blockdecode($bx))
        row("BlockReduceAdd     B=$B",    @b BlockReduceAdd($E, RTE_SN, $bx))
        row("BlockReduceMultiply B=$B",   @b BlockReduceMultiply($E, RTE_SN, $bx))
        row("BlockDotProduct    B=$B",    @b BlockDotProduct($E, RTE_SN, $bx, $by))
        row("BlockAdd           B=$B",    @b BlockAdd($E, RTE_SN, $bx, $by, one($S)))
        println()
    end
    # ScaledAdd is the scalar member of the Scaled* family: one row, no B
    row("ScaledAdd (scalar lanes)",       @b ScaledAdd($E, RTE_SN, one($S), $(E(1.5)), one($S), $(E(0.25))))
end
