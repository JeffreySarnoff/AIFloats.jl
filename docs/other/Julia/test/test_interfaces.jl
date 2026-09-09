# Independent API laws and boundary regressions, beyond the Maude fixture set.
using CodecZlib: GzipCompressorStream
using SHA: sha256

@testset "Source format query surface" begin
    f = P.BinaryFormat(4, 2, P.SIGNED, P.FINITE)
    @test P.SpecAPI.IsNormal(f, 4) === true
    @test P.SpecAPI.BitwidthOf(f) == 4
    @test P.SpecAPI.PrecisionOf(f) == 2
    @test P.SpecAPI.ExponentBitwidthOf(f) == 2
    @test P.SpecAPI.TrailingSignificandBitwidthOf(f) == 1
    @test P.SpecAPI.ExponentBiasOf(f) == 2
    @test P.SpecAPI.SignednessOf(f) === P.SIGNED
    @test P.SpecAPI.DomainOf(f) === P.FINITE
    @test P.SpecAPI.MaxFiniteOf(f) == 7
    @test P.SpecAPI.MinFiniteOf(f) == 15
    @test P.SpecAPI.MinPositiveOf(f) == 1
    @test P.SpecAPI.MinNormalOf(f) == 2
end

@testset "Fixture corruption detection" begin
    mktempdir() do root
        function fixture(rows; count = length(rows), hash_override = nothing)
            body = join((JSON.json(row)*"\n" for row in rows))
            open(joinpath(root, "probe.jsonl.gz"), "w") do io
                stream = GzipCompressorStream(io)
                write(stream, body)
                close(stream)
            end
            digest = isnothing(hash_override) ? bytes2hex(sha256(body)) : hash_override
            write(
                joinpath(root, "manifest.json"),
                JSON.json(Dict("probe" => Dict("cases" => count, "sha256" => digest))),
            )
        end
        good = Dict("id" => "one", "expression" => "fin(1) == fin(1)")
        fixture([good])
        @test isempty(SourceCases.run_suite("probe"; root).failures)
        fixture([good]; count = 2)
        @test_throws ErrorException SourceCases.run_suite("probe"; root)
        fixture([good, good])
        @test_throws ErrorException SourceCases.run_suite("probe"; root)
        fixture([good]; hash_override = repeat("0", 64))
        @test_throws ErrorException SourceCases.run_suite("probe"; root)
        for expression in ("fin(1) == fin(2)", "exprExp(fin(1))", "notSupported(fin(1))")
            fixture([Dict("id" => "bad", "expression" => expression)])
            @test length(SourceCases.run_suite("probe"; root).failures) == 1
        end
    end
end
@testset "Exact values and wide formats" begin
    @test_throws DomainError P.finite(big(1)//big(0))
    @test_throws ArgumentError P.BinaryFormat(2, 1, P.SIGNED, P.FINITE)
    @test_throws ArgumentError P.BinaryFormat(4, 4, P.SIGNED, P.FINITE)
    @test !P.valid_format(2, 1, P.SIGNED, P.FINITE)
    for f in (
        P.BinaryFormat(128, 127, P.SIGNED, P.FINITE),
        P.BinaryFormat(128, 128, P.UNSIGNED, P.EXTENDED),
    )
        c=big(1)<<126
        @test P.encode(f, P.decode(f, c)) == c
        @test P.bitwidth(f)==128
        @test !P.valid_code(f, big(1)<<128)
        @test !P.is_datum(f, P.finite(1//3))
    end
    for k = -200:200
        q=P.pow2(k)
        @test P.floor_log2(q)==k
        @test P.floor_log2(q*3//2)==k
    end
    @test P.nearest_even_integer(big(-5)//2)==-2
    @test P.nearest_even_integer(big(-7)//2)==-4
    @test P.mathematical_equal(P.NAN, P.NAN) === false
    @test isequal(P.finite(1), P.finite(big(2)//2))
    @test hash(P.finite(1))==hash(P.finite(big(2)//2))
    @test (@inferred P.ExactValue P.decode(P.F4, 4)) == P.finite(1)
    @test @inferred(P.project(P.F4, P.Projection(P.NEAREST_EVEN), P.finite(3//2))) == 5
end

@testset "Policies and positional blocks" begin
    @test_throws ArgumentError P.RoundPolicy(P.STOCHASTIC_A, -1, 0)
    @test_throws ArgumentError P.RoundPolicy(P.STOCHASTIC_B, 2, 4)
    @test_throws ArgumentError P.RoundPolicy(P.NEAREST_EVEN, 1, 1)
    @test P.random_in_range(200, (big(1)<<200)-1)
    p=P.BlockProjection(P.STOCHASTIC_C, P.SAT_NONE, 2, [0, 3])
    @test P.valid_block_projection(p, 2)
    @test !P.valid_block_projection(p, 1)
    @test P.projection_at(p, 0).rounding.random==0
    @test P.projection_at(p, 1).rounding.random==3
    @test_throws BoundsError P.projection_at(p, 2)
    p.randoms[1]=4
    @test !P.valid_block_projection(p, 2)
    inputs=[0, 4, 5, 6]
    xs=@view inputs[2:3]
    before=copy(inputs)
    b=P.SpecAPI.BlockAdd(
        2,
        P.F4,
        P.F4,
        P.F4,
        P.F4,
        P.F4,
        P.F4,
        P.BlockProjection(P.NEAREST_EVEN),
        4,
        xs,
        4,
        (4, 5),
        4,
    )
    @test b==P.BlockValue(4, [6, 7])
    @test inputs==before
    @test_throws DimensionMismatch P.convert_to_block(
        3,
        P.F4,
        P.F4,
        P.F4,
        P.BlockProjection(P.NEAREST_EVEN),
        (4, 5),
        4,
    )
    @test_throws ArgumentError P.decode_block(0, P.F4, P.F4, 4, ())
end

@testset "Symbolic truth and residuals" begin
    a=P.expression(:Exp, P.finite(1))
    b=P.expression(:Exp, P.finite(2))
    @test a!=b
    @test P.mathematical_equal(a, b) === P.UNKNOWN
    @test P.mathematical_equal(a, a) === true
    @test P.mathematical_less(P.finite(0), a) === true
    @test P.mathematical_equal(a, P.finite(0)) === false
    bad=P.expression(:Log, P.finite(-1))
    @test P.real_domain(bad) === false
    @test P.elementary(:Sqrt, bad) isa P.Residual
    @test P.add(bad, P.finite(1)) isa P.Residual
    @test P.mathematical_equal(bad, bad) === P.UNKNOWN
    root=P.elementary(:Sqrt, P.finite(2))
    @test root isa P.SymbolicExpr
    @test P.project(P.F4, P.Projection(P.NEAREST_EVEN), root).reason==:uncertified_projection
    unknown=P.residual(:unknown, P.finite(1))
    @test P.add(unknown, unknown) isa P.Residual
    @test P.elementary(:Log, unknown) isa P.Residual
    @test P.normalize_element(P.POS_INF, unknown) isa P.Residual
    @test P.elementary(:Sqrt, P.finite(9//16))==P.finite(3//4)
    @test P.atan2_value(P.finite(1), P.finite(-1))==P.pi_multiple(3//4)
end

@testset "External boundaries and evidence" begin
    @test P.decode(P.BINARY32, 0).reason==:missing_backend
    @test P.SpecAPI.IsNaN(P.BINARY32, 0) isa P.Residual
    @test P.SpecAPI.IsFinite(P.BINARY32, 0) isa P.Residual
    @test P.SpecAPI.IsNormal(P.BINARY32, 0) isa P.Residual
    @test P.SpecAPI.IsSubnormal(P.BINARY32, 0) isa P.Residual
    @test P.SpecAPI.Class(P.BINARY32, 0) isa P.Residual
    @test_throws ArgumentError P.SpecAPI.NextGreaterThan(P.BINARY32, 0)
    @test_throws ArgumentError P.SpecAPI.TotalOrder(P.BINARY32, P.F4, 0, 0)
    @test !P.evidence_complete(:sampleEvidence)
    @test P.evidence_complete(:proofEvidence) # A source tag check, not a verified proof.
    @test !P.partition([0, 0], [[0]])
    @test !P.partition([0, 1], [[0], [0, 1]])
end

@testset "Tooling and package boundaries" begin
    @test isempty(Test.detect_ambiguities(P; recursive = true))
    @test_throws ErrorException SourceCases.parse_source("fin(1); run(1)")
    @test_throws ErrorException SourceCases.parse_source("fin(1) trailing")
    @test_throws ErrorException SourceCases.parse_source("fin(")
    @test_throws ErrorException SourceCases.evaluate(
        SourceCases.parse_source("UnknownOperation(1)"),
    )
    @test SourceCases.evaluate(SourceCases.parse_source("fin(1) == fin(2)")) === false
    inventory=JSON.parsefile(joinpath(@__DIR__, "..", "inventory", "operations.json"))["operations"]
    expected=Symbol[]
    for o in inventory
        push!(expected, Symbol(o["name"]))
        o["block"] && push!(expected, Symbol("Block", o["name"]))
        o["scaled"] && push!(expected, Symbol("Scaled", o["name"]))
    end
    @test length(unique(expected))==193
    @test all(n->isdefined(P.SpecAPI, n) && Base.ispublic(P.SpecAPI, n), expected)
    arities=JSON.parsefile(joinpath(@__DIR__, "vectors", "arity-tables.json"))["tables"]
    for (name, actual) in (
        ("numericArityTable", P.NUMERIC_ARITIES),
        ("plainArityTable", P.PLAIN_ARITIES),
        ("blockElementArityTable", P.BLOCK_ARITIES),
    )
        @test Set(actual)==Set((String(x[1]), Int(x[2])) for x in arities[name])
    end
end

# This tiny test double exercises dispatch only; it makes no external-codec claim.
struct BridgeProbe <: P.Contracts.ExternalBackend end
P.Contracts.backend_format(::BridgeProbe) = P.BINARY16
P.Contracts.backend_valid_code(::BridgeProbe, c) = c==0
P.Contracts.backend_decode(::BridgeProbe, c) = P.finite(0)
P.Contracts.backend_datum(::BridgeProbe, x) = x==P.finite(0)
P.Contracts.backend_encode(::BridgeProbe, x) = big(0)
P.Contracts.backend_bound(::BridgeProbe, q) = big(0)
@testset "Explicit backend bridge" begin
    f=P.BoundFormat(P.BINARY16, BridgeProbe())
    @test P.bitwidth(f)==16
    @test_throws ArgumentError P.SpecAPI.NextGreaterThan(f, 0)
    @test P.decode(f, 0)==P.finite(0)
    @test P.encode(f, P.finite(0))==0
    @test P.max_finite_code(f)==0
    @test P.project(f, P.Projection(P.NEAREST_EVEN), P.finite(0))==0
    @test_throws DomainError P.decode(f, 1)
    @test_throws DomainError P.encode(f, P.finite(1))
    @test_throws ArgumentError P.BoundFormat(P.BINARY32, BridgeProbe())
end
