# Documentation contracts (docs/refinedocs2.md V-3).
#
# These are the facts the narrative pages assert about themselves. Each one was
# wrong somewhere in the documentation before this file existed, so each is
# pinned here rather than trusted to stay true.

using AIFloats
using Test
using Random

@testset "the default projection is RTE_SN and is task-local" begin
    # P0-3. Three pages and a docstring called RTE_SF "the conventional default".
    @test DefaultProjection() === RTE_SN
    @test DefaultRoundingMode() === RTE
    @test DefaultSaturationMode() === SN

    # bound for a dynamic extent, restored on exit, and never by a setter
    @test with_projection(RTZ_SF) do
        DefaultProjection()
    end === RTZ_SF
    @test DefaultProjection() === RTE_SN
    @test !isdefined(AIFloats, :DefaultProjection!)

    # restored on exception too
    @test_throws ErrorException with_projection(RTZ_SF) do
        error("boom")
    end
    @test DefaultProjection() === RTE_SN

    # a task started inside inherits it
    inner = with_projection(RTP_SN) do
        fetch(Threads.@spawn DefaultProjection())
    end
    @test inner === RTP_SN
end

@testset "the exponent-bit budget closes" begin
    # P0-2. The concepts page rearranged K = S + E + (P-1) as `K - P - S`,
    # dropping the +1, and printed 3 and 4 where the truth is 4 and 5.
    S = Binary(8, 4, SIGNED, FINITE)
    U = Binary(8, 4, UNSIGNED, FINITE)
    @test ExponentBitwidthOf(S) == 4
    @test ExponentBitwidthOf(U) == 5
    @test ExponentBitwidthOf(Binary8p4sf) == 4

    for K in 3:16, P in 1:K, s in (SIGNED, UNSIGNED), d in (FINITE, EXTENDED)
        sgn = s === SIGNED
        P <= K - sgn || continue
        F = Binary(K, P, s, d)
        E = ExponentBitwidthOf(F)
        # every bit is sign, exponent, or stored significand — and nothing else
        @test sgn + E + AIFloats.TrailingSignificantBitsOf(F) == K
        @test E == (K - sgn) - (P - 1)
        # the report derives the bias from the same budget; both are 2^(E-1)
        @test ExponentBiasOf(F) == 1 << (E - 1)
    end
end

@testset "formats, datum types, and datums are three things" begin
    # P0-4. Aliases were described as "datum aliases".
    F = Binary8p4se
    T = BinaryValue(F)
    x = F(1.5)

    @test F === Binary(8, 4, SIGNED, EXTENDED)
    @test F isa Type && !(F <: AbstractFloat)
    @test T === BinaryValue{F, CodeType(F)}
    @test T <: AbstractFloat
    @test x isa T
    @test !(x isa F)
    @test BinaryFormatOf(x) === F
    @test_throws ArgumentError F()

    # every K <= 8 alias names a format, not a datum type and not a datum
    for K in 3:8, P in 1:K, s in ("s", "u"), d in ("f", "e")
        sgn = s == "s"
        P <= K - sgn || continue
        name = Symbol("Binary", K, "p", P, s, d)
        isdefined(AIFloats, name) || continue
        G = getfield(AIFloats, name)
        @test G <: Binary
        @test BinaryValue(G) <: AbstractFloat
    end
end

@testset "numbers and code points are different arguments" begin
    # P1-6. Every Integer, Unsigned included, has VALUE semantics.
    F = Binary8p4se
    @test decode(fromcode(F, 0x45)) == 1.625
    @test decode(F(0x45)) == 72.0            # 0x45 is the number 69
    @test F(0x45) === F(69) === F(69.0)
    @test F(0x45) !== fromcode(F, 0x45)
    @test convert(BinaryValue(F), 0x03) === F(3)
    @test_throws ArgumentError fromcode(Binary5p2se, 0xff)   # out of code range
end

@testset "saturation modes are distinguished by an infinity, not by magnitude" begin
    # P0-6. The example used a finite 1.0e100, which SF and SP clamp alike.
    F = Binary(8, 3, SIGNED, EXTENDED)
    @test Convert(F, RTE_SF, 1.0e100) === Convert(F, RTE_SP, 1.0e100)
    @test Convert(F, RTE_SF, Inf) !== Convert(F, RTE_SP, Inf)
    @test isfinite(Convert(F, RTE_SF, Inf))
    @test isinf(Convert(F, RTE_SP, Inf))

    # SN follows direction, signedness, and domain (report §4.7.5)
    U = Binary(8, 3, UNSIGNED, EXTENDED)
    V = Binary(8, 3, SIGNED, FINITE)
    @test isfinite(Convert(F, RTZ_SN, 1.0e100))       # direction points back in
    @test isinf(Convert(F, RTE_SN, -1.0e100))         # signed extended: -Inf
    @test isnan(Convert(U, RTE_SN, -1.0e100))         # unsigned: no -Inf
    @test isnan(Convert(V, RTE_SN, 1.0e100))          # finite domain: no Inf
end

@testset "the stochastic contract" begin
    # P1-7.
    F = Binary(8, 3, SIGNED, EXTENDED)
    T = BinaryValue(F)
    x, y = T(1.0), T(0.125)

    @test isstochastic(RSA_SN)
    @test !isstochastic(RTE_SN)
    N = nrandbits(RSA_SN)
    @test 1 <= N <= 60

    # an explicit R is reproducible, and out of range is refused
    @test Add(F, RSA_SN, x, y; R = 3) === Add(F, RSA_SN, x, y; R = 3)
    @test_throws ArgumentError Add(F, RSA_SN, x, y; R = 1 << 60)
    @test_throws ArgumentError Add(F, RSA_SN, x, y; R = -1)

    # R takes precedence over rng, so the stream does not advance
    rng = Xoshiro(2026)
    before = copy(rng)
    Add(F, RSA_SN, x, y; R = 3, rng = rng)
    @test rng == before

    # a pure projection touches no RNG state at all
    rng2 = Xoshiro(2026)
    before2 = copy(rng2)
    Add(F, RTE_SN, x, y; rng = rng2)
    @test rng2 == before2

    # arrays consume one sequential stream in eachindex order
    A = T[1.0, 1.0, 1.0, 1.0]
    B = T[0.125, 0.125, 0.125, 0.125]
    @test vmap(:Add, F, RSA_SN, A, B; rng = Xoshiro(7)) ==
          vmap(:Add, F, RSA_SN, A, B; rng = Xoshiro(7))
end

@testset "the public surface is what the documentation says it is" begin
    # P0-7, P1-1, P1-5: names the documentation must NOT recommend, and names
    # it must be able to.
    for n in (:get_table, :table_for, :validformat, :OP_REGISTRY)
        @test isdefined(AIFloats, n)
        @test !Base.ispublic(AIFloats, n)
        @test !Base.isexported(AIFloats, n)
    end
    for n in (:table_policy, :table_stats, :table_entries, :empty_tables!,
              :operations, :operationinfo, :Formats)
        @test Base.ispublic(AIFloats, n)
    end
    for n in (:vmap, :vmap!, :formatinfo, :project, :conformance, :draft_identity)
        @test Base.isexported(AIFloats, n)
    end

    # P1-2: every public binding is documented. The reference pages are
    # generated from this same predicate, so a gap here is a gap there.
    public = filter(names(AIFloats; all = true)) do n
        Base.isexported(AIFloats, n) || Base.ispublic(AIFloats, n)
    end
    undocumented = filter(n -> !Docs.hasdoc(AIFloats, n), public)
    @test isempty(undocumented)
end

@testset "the paired query vocabularies are the same objects" begin
    # P1-4. Not an adapter, not a shim — the identical generic function.
    @test bitwidth === BitwidthOf
    @test signedness === SignednessOf
    @test domain === DomainOf
    @test formatof === BinaryFormatOf
    @test codetype === CodeType
    @test valuetype === ValueType

    info = formatinfo(Binary8p4se)
    @test info.name === :Binary8p4se
    @test info.bitwidth == 8
    @test info.precision == 4
    @test info.exponentbits == ExponentBitwidthOf(Binary8p4se)
    @test info.datumtype === BinaryValue(Binary8p4se)
    @test formatinfo(Binary8p4se(1.5)) === info
end

@testset "the documented operation register matches the registry" begin
    # P1-3. The Operations page states the count and the arity split.
    ops = AIFloats.operations()
    @test length(ops) == 52
    @test all(o -> 1 <= o.arity <= 3, ops)
    @test all(o -> o.group in (:A, :B, :C, :conv), ops)
    @test AIFloats.operationinfo(:Add).arity == 2
    @test AIFloats.operationinfo(:FMA).arity == 3
    @test_throws ArgumentError AIFloats.operationinfo(:NotAnOperation)

    # every register name is a callable binding, and every generated Block*/
    # Scaled* companion exists with it
    for o in ops
        @test isdefined(AIFloats, o.name)
        o.name === :Convert && continue
        @test isdefined(AIFloats, Symbol(:Block, o.name))
        @test isdefined(AIFloats, Symbol(:Scaled, o.name))
    end

    # the Base veneers are one register call, not a second semantics
    F = Binary8p4se
    x, y = F(1.5), F(0.25)
    @test x + y === Add(x, y)
    @test x * y === Multiply(x, y)
    @test exp(y) === Exp(y)
    @test sqrt(x) === Sqrt(x)
end

@testset "table policy reports every documented outcome" begin
    # P0-9. The Status page claimed signatures above the eager band always
    # compute, and described adaptivity only for ternary tables.
    documented = (:eager, :adaptive_cached, :adaptive_earned, :adaptive_pending,
                  :over_adaptive_band, :over_byte_budget, :stochastic)

    F8 = Binary8p4se
    F9 = Binary(9, 4, SIGNED, EXTENDED)
    F16 = Binary(16, 10, SIGNED, EXTENDED)

    @test AIFloats.table_policy(:Add, F8, F8, F8, RTE_SN).state === :eager
    @test AIFloats.table_policy(:Add, F8, F8, F8, RSA_SN).state === :stochastic
    @test AIFloats.table_policy(:Add, F16, F16, F16, RTE_SN).state in
          (:over_byte_budget, :over_adaptive_band)

    # a BINARY adaptive band exists — TABLE_ADAPTIVE_BITS, not only the ternary one
    @test AIFloats.TABLE_ADAPTIVE_BITS[] > AIFloats.TABLE_EAGER_BITS[]
    @test AIFloats.TABLE_BUILD_ELEMS[] > 0
    pending = AIFloats.table_policy(:Add, F9, F9, F9, RTE_SN; nelems = 1)
    earned  = AIFloats.table_policy(:Add, F9, F9, F9, RTE_SN;
                                    nelems = AIFloats.TABLE_BUILD_ELEMS[])
    @test pending.state in (:adaptive_pending, :adaptive_cached)
    @test earned.state in (:adaptive_earned, :adaptive_cached)
    @test pending.threshold == AIFloats.TABLE_BUILD_ELEMS[]

    for p in (AIFloats.table_policy(:Add, F8, F8, F8, RTE_SN),
              AIFloats.table_policy(:Add, F8, F8, F8, RSA_SN),
              pending, earned)
        @test p.state in documented
        @test p.shape in (:A, :B)
    end

    # asking never mutates the cache or a counter
    n_before = AIFloats.table_stats().entries
    AIFloats.table_policy(:Add, F9, F9, F9, RTE_SN; nelems = 10^9)
    @test AIFloats.table_stats().entries == n_before
end

@testset "two cache snapshots are two moments; conformance is one" begin
    # P0-8. Only `conformance()` derives its byte total from the entry vector
    # it captured, so only it can promise a coherent count and size.
    c = conformance()
    @test c.cached_bytes == sum(e -> e.bytes, c.cached_specializations; init = 0)

    s = AIFloats.table_stats()
    @test s.entries >= 0 && s.bytes >= 0
    @test AIFloats.table_entries() isa AbstractVector
end

@testset "the draft identity names the designated report" begin
    # P0-1, P1-12. The identity used to name only a local transliteration.
    id = draft_identity()
    @test id.report_revision == "4.0.3"
    @test id.report_date == "2026-09-01"
    @test occursin("P3109/Public", id.report_url)
    @test occursin("IEEE%20P3109%20Interim%20Report.pdf", id.report_url)
    @test length(id.report_sha256) == 64
    @test all(c -> c in "0123456789abcdef", id.report_sha256)
    @test occursin("unapproved draft", id.report_status)

    # the retained transliteration is provenance, and still recorded
    @test id.retained_source == "docs/other/IEEE_D1.md"
    @test length(id.transliteration_sha256) == 64

    # nothing anywhere may read as a certification
    @test occursin("unapproved draft", draft_revision())
    report = sprint(conformance_report, conformance())
    @test occursin("NOT a certification", report)
    @test occursin("must not be used for conformance", report)

    d = conformance_dict()
    @test d["draft_identity"]["report_revision"] == "4.0.3"
end

@testset "refusals are stated, not silent" begin
    # P1-11 and the Operations page: a refused operation says why.
    F = Binary8p4se
    T = BinaryValue(F)
    x, y = F(1.5), F(0.25)

    @test_throws ArgumentError rem(x, y)
    @test_throws ArgumentError F(1//3)
    @test_throws ArgumentError Binary(8, 8, SIGNED, FINITE)
    @test_throws DimensionMismatch vmap(:Add, F, RTE_SN, T[1.0, 2.0], T[1.0])

    # an out-of-domain VALUE is not a refusal: it has a defined answer
    @test isnan(Binary8p4uf(-1.0))

    # packed wire forms validate rather than guess. K = 5 so the final byte
    # carries padding bits; at K = 8 there are none to corrupt.
    TP = BinaryValue(Binary5p2se)
    A = TP[0.0, 0.5, 1.0, 1.5, 2.0, 3.0]
    bytes = AIFloats.packedbytes(PackedVector(A))
    @test AIFloats.packedfrombytes(TP, bytes, length(A)) == A
    @test_throws DimensionMismatch AIFloats.packedfrombytes(TP, bytes, length(A) + 50)
    corrupt = copy(bytes)
    corrupt[end] |= 0x80
    @test_throws ArgumentError AIFloats.packedfrombytes(TP, corrupt, length(A))
end

@testset "display scope is stated, and separate from projection scope" begin
    # P1-10.
    F = Binary8p4se
    x = F(1.5)
    @test sprint(show, x; context = :binary_show_style => :codepoint) == "0x44"
    @test occursin("Binary8p4se", sprint(show, x; context = :binary_show_style => :typed))

    saved = get_show_style()
    try
        set_show_style!(:codepoint)
        @test get_show_style() === :codepoint
        # the process-wide fallback does not disturb the task-local projection
        @test DefaultProjection() === RTE_SN
    finally
        set_show_style!(saved)
    end
    @test get_show_style() === saved
end
