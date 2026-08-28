using AIFloats
using Test

# Phase 4 gate, tables side: a table entry IS the scalar result; the budgets
# refuse loudly; policy introspection agrees with the kernels' predicates;
# the ternary bands and LRU behave as stated.

@testset "table entries ≡ the scalar path, exhaustively" begin
    AIFloats.empty_tables!()
    F = Binary(5, 3, SIGNED, EXTENDED)
    G = Binary(4, 2, UNSIGNED, FINITE)
    BVF = BinaryValue(F); BVG = BinaryValue(G)
    for ρ in (RTE_SN, RTZ_SF, RTP_SP)
        # unary, same format
        t = AIFloats.get_table(:Exp, F, F, ρ)
        @test length(t) == 32
        for c in 0:31
            x = BVF(UInt8(c))
            @test t[c + 1] == codepoint(Exp(F, ρ, x))
        end
        # binary, mixed formats (operands G, results F)
        t2 = AIFloats.get_table(:Add, F, G, G, ρ)
        @test length(t2) == 256
        for c1 in 0:15, c2 in 0:15
            want = codepoint(Add(F, ρ, BVG(UInt8(c1)), BVG(UInt8(c2))))
            @test t2[(c1 << 4) + c2 + 1] == want
        end
        # Convert: the one op with no ω-semantics — a bare projection
        t3 = AIFloats.get_table(:Convert, G, F, ρ)
        for c in 0:31
            @test t3[c + 1] == codepoint(Convert(G, ρ, BVF(UInt8(c))))
        end
    end
    # a wide-format table: UInt16 code unit selects the other cache
    W = Binary(9, 4, SIGNED, EXTENDED)
    tw = AIFloats.get_table(:Negate, W, W, RTE_SN)
    @test eltype(tw) === UInt16
    BW = BinaryValue(W)
    for c in (0, 1, 255, 256, 511)
        @test tw[c + 1] == codepoint(Negate(W, RTE_SN, BW(UInt16(c))))
    end
end

@testset "the two budgets refuse, each in its own way" begin
    F16 = Binary(16, 8, SIGNED, EXTENDED)
    F = Binary(5, 3, SIGNED, EXTENDED)
    # byte budget: ternary 16+16+16 = 2^48 entries — get_table throws, naming it
    @test_throws ArgumentError AIFloats.get_table(:Add, F16, F16, F16, F16, RTE_SN)
    # stochastic ρ is never tabulable
    @test_throws ArgumentError AIFloats.get_table(:Add, F, F, F, RSA_SN)
    @test AIFloats.table_for(:Add, F, F, F, RSA_SN) === nothing
    # table_for declines (no throw) over the entry band; get_table still builds
    old = AIFloats.TABLE_EAGER_BITS[]
    try
        AIFloats.TABLE_EAGER_BITS[] = 6
        @test AIFloats.table_for(:Add, F, F, F, RTE_SN) === nothing     # 10 > 6
        @test AIFloats.get_table(:Exp, F, F, RTE_SN) isa Memory         # 5 ≤ 6... entries fine
    finally
        AIFloats.TABLE_EAGER_BITS[] = old
    end
    # binary 16×16 = 2^32 entries of UInt16 = 2^33 bytes: over the byte budget
    @test_throws ArgumentError AIFloats.get_table(:Add, F16, F16, F16, RTE_SN)
    @test AIFloats.table_for(:Add, F16, F16, F16, RTE_SN) === nothing
end

@testset "table_policy reads the kernels' own predicates" begin
    F = Binary(5, 3, SIGNED, EXTENDED)
    F16 = Binary(16, 8, SIGNED, EXTENDED)
    @test AIFloats.table_policy(:Add, F, F, F, RTE_SN).shape === :A
    @test AIFloats.table_policy(:Add, F, F, F, RSA_SN).shape === :B
    @test AIFloats.table_policy(:Add, F16, F16, F16, RTE_SN).shape === :B
    p = AIFloats.table_policy(:Exp, F, F, RTE_SN)
    @test p.shape === :A && p.entries == 32
    # ternary bands: 3×5 = 15 eager; 3×7 = 21 adaptive; 3×8 = 24 beyond
    F7 = Binary(7, 3, SIGNED, EXTENDED); F8 = Binary(8, 4, SIGNED, EXTENDED)
    @test AIFloats.table_policy(:FMA, F, F, F, F, RTE_SN).shape === :A
    @test AIFloats.table_policy(:FMA, F7, F7, F7, F7, RTE_SN).shape === :A   # adaptive band grants
    @test AIFloats.table_policy(:FMA, F8, F8, F8, F8, RTE_SN).shape === :B
end

@testset "ternary bands and LRU eviction" begin
    AIFloats.empty_tables!()
    F = Binary(4, 2, SIGNED, EXTENDED)          # 3×4 = 12 bits: eager band
    BV = BinaryValue(F)
    A = [BV(UInt8(c % 16)) for c in 0:99]
    FMA(F, RTE_SN, A, A, A)
    @test AIFloats.ternary_count() == 1
    # adaptive band: 3×7 = 21 bits — no table until the signature earns it
    F7 = Binary(7, 3, SIGNED, EXTENDED); BV7 = BinaryValue(F7)
    A7 = [BV7(UInt8(c % 128)) for c in 0:999]
    oldE = AIFloats.TERNARY_BUILD_ELEMS[]
    try
        AIFloats.TERNARY_BUILD_ELEMS[] = 2500
        FMA(F7, RTE_SN, A7, A7, A7)             # 1000 elements: not yet
        @test AIFloats.ternary_count() == 1
        FMA(F7, RTE_SN, A7, A7, A7)             # 2000: not yet
        @test AIFloats.ternary_count() == 1
        r = FMA(F7, RTE_SN, A7, A7, A7)         # 3000: earned — builds
        @test AIFloats.ternary_count() == 2
        # the table agrees with the scalar path on every probed element
        @test all(i -> codepoint(r[i]) == codepoint(FMA(F7, RTE_SN, A7[i], A7[i], A7[i])),
                  eachindex(A7))
    finally
        AIFloats.TERNARY_BUILD_ELEMS[] = oldE
    end
    # LRU: shrink the byte budget so inserting a new ternary table evicts the
    # least-recently-used one
    oldB = AIFloats.TERNARY_CACHE_BYTES[]
    try
        AIFloats.TERNARY_CACHE_BYTES[] = 1 << 21   # 2 MiB: holds the 7-bit table alone
        G = Binary(3, 1, UNSIGNED, FINITE); BG = BinaryValue(G)
        Ag = [BG(UInt8(c % 8)) for c in 0:49]
        FMA(G, RTE_SN, Ag, Ag, Ag)                 # eager insert triggers eviction
        @test AIFloats.ternary_count() < 3
    finally
        AIFloats.TERNARY_CACHE_BYTES[] = oldB
    end
    # eviction spans BOTH code-unit caches: an older UInt16-result table must be
    # the victim of a UInt8-result insert, and the budget must hold afterwards
    AIFloats.empty_tables!()
    try
        AIFloats.TERNARY_CACHE_BYTES[] = 6 * 1024
        W = Binary(9, 4, SIGNED, EXTENDED)          # UInt16 result: 2^12 entries × 2 B = 8 KiB
        FMA(W, RTE_SN, A, A, A)                     # inserts alone over budget (earned)
        @test AIFloats.ternary_count() == 1
        FMA(F, RTE_SN, A, A, A)                     # UInt8 result, 4 KiB: must evict W's
        @test AIFloats.ternary_count() == 1
        @test AIFloats.table_bytes() == 4096            # only ternary tables are cached here
        @test isempty(AIFloats.TERNARY_CACHE16) && length(AIFloats.TERNARY_CACHE8) == 1
        # and the other direction
        FMA(W, RTE_SN, A, A, A)
        @test isempty(AIFloats.TERNARY_CACHE8) && length(AIFloats.TERNARY_CACHE16) == 1
    finally
        AIFloats.TERNARY_CACHE_BYTES[] = oldB
    end
    AIFloats.empty_tables!()
    @test AIFloats.table_count() == 0 && AIFloats.ternary_count() == 0
    @test AIFloats.table_bytes() == 0
end

@testset "cache accounting" begin
    AIFloats.empty_tables!()
    F = Binary(5, 3, SIGNED, EXTENDED)
    W = Binary(9, 4, SIGNED, EXTENDED)
    AIFloats.get_table(:Exp, F, F, RTE_SN)         # 32 × UInt8
    AIFloats.get_table(:Negate, W, W, RTE_SN)      # 512 × UInt16
    @test AIFloats.table_count() == 2
    @test AIFloats.table_bytes() == 32 + 1024      # both code units counted
    @test length(AIFloats.table_keys()) == 2
    # a repeat fetch is a cache hit, not a rebuild
    t1 = AIFloats.get_table(:Exp, F, F, RTE_SN)
    t2 = AIFloats.get_table(:Exp, F, F, RTE_SN)
    @test t1 === t2
    AIFloats.empty_tables!()
end

@testset "ternary LRU spans both code widths" begin
    AIFloats.empty_tables!()
    old = AIFloats.TERNARY_CACHE_BYTES[]
    try
        # operands ΣK = 4+4+3 = 11 → 2^11 entries: a UInt16-result table is
        # 4096 B, a UInt8-result one 2048 B. Under a 4096 B budget the second
        # insert must evict the first (the older, other-width) table.
        AIFloats.TERNARY_CACHE_BYTES[] = 4096
        F16 = Binary(9, 4, SIGNED, EXTENDED); F8 = Binary(8, 4, SIGNED, EXTENDED)
        F3 = Binary(4, 2, SIGNED, EXTENDED); F4 = Binary(3, 2, SIGNED, EXTENDED)
        AIFloats.get_table(:FMA, F16, F3, F3, F4, RTE_SN)
        @test AIFloats.table_bytes() == 4096
        AIFloats.get_table(:FMA, F8, F3, F3, F4, RTE_SN)
        @test AIFloats.table_bytes() == 2048
        @test isempty(AIFloats.TERNARY_CACHE16)
        @test AIFloats.table_bytes() <= AIFloats.TERNARY_CACHE_BYTES[]
    finally
        AIFloats.TERNARY_CACHE_BYTES[] = old
        AIFloats.empty_tables!()
    end
end
