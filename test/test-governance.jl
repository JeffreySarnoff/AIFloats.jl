using AIFloats
using Test
using Random
using SHA

# Phase 7 gate: the conformance report derives from the registry live; κ
# registration rejects understatement; the retained draft's digest matches.

const T8 = BinaryValue(Binary8p4se)
const T5 = BinaryValue(Binary5p2se)

@testset "κ measurement" begin
    exact_exp(x) = Exp(T8, RTE_SN, x)
    @test measure_kappa(exact_exp, :Exp, T8, (T8,), RTE_SN) === (0.0, true)
    exact_add(x, y) = Add(T5, RTE_SN, x, y)
    @test measure_kappa(exact_add, :Add, T5, (T5, T5), RTE_SN) === (0.0, true)
    T4 = BinaryValue(Binary4p2se)
    exact_fma(x, y, z) = FMA(T4, RTE_SN, x, y, z)
    @test measure_kappa(exact_fma, :FMA, T4, (T4, T4, T4), RTE_SN) === (0.0, true)
    @test measure_kappa(x -> Convert(T5, RTE_SN, x), :Convert, T5, (T8,), RTE_SN) === (0.0, true)
    # synthetic known-κ: perturb the defined result by two steps
    step2(x) = (r = Exp(T8, RTE_SN, x); isfinite(r) ? NextGreaterThan(NextGreaterThan(r)) : r)
    κ2, exh = measure_kappa(step2, :Exp, T8, (T8,), RTE_SN)
    @test exh && κ2 >= 2.0
    # NaN mismatch and finite→Inf deviation are κ = NaN
    denan(x) = (r = Log(T8, RTE_SN, x); isnan(r) ? zero(T8) : r)
    @test isnan(measure_kappa(denan, :Log, T8, (T8,), RTE_SN)[1])
    toinf(x) = typemax(T8)
    @test isnan(measure_kappa(toinf, :Abs, T8, (T8,), RTE_SN)[1])
    # sampling above the exhaustive budget says so
    κs, exhs = measure_kappa(exact_add, :Add, T5, (T5, T5), RTE_SN; max_exhaustive = 100, samples = 200)
    @test κs == 0.0 && !exhs
    @test_throws ArgumentError measure_kappa(exact_exp, :Exp, T8, (T8,), Projection(AIFloats.ρRSA(2), SN))
    @test_throws ArgumentError measure_kappa(exact_exp, :Nope, T8, (T8,), RTE_SN)
    @test_throws ArgumentError measure_kappa(exact_exp, :Exp, T8, (T8,), RTE_SN;
                                             max_exhaustive = -1)
    @test_throws ArgumentError measure_kappa(exact_exp, :Exp, T8, (T8,), RTE_SN;
                                             max_exhaustive = 0, samples = -1)
    @test_throws ArgumentError measure_kappa(exact_exp, :Exp, T8, (T8,), RTE_SN;
                                             max_exhaustive = 0, samples = 0)
    @test_throws ArgumentError measure_kappa((x, y) -> x, :Exp, T8, (T8, T8), RTE_SN)
end

@testset "FTZ worked example (draft Annex)" begin
    ρf = RTE_SF
    ftz = ftz_variant(:Exp, T8, T8, ρf)
    P = Int(PrecisionOf(T8)); half = 1 << (P - 2); mn = decode(MinNormalOf(T8))
    for c in 0:255
        x = fromcode(T8, c)
        want = Exp(T8, ρf, x); got = ftz(x)
        if issubnormal(want)
            m = Int(codepoint(want) & ~AIFloats.signmask(T8))
            @test decode(got) == (m <= half ? 0.0 : mn)
        else
            @test got === want
        end
    end
    κf, exhf = measure_kappa(ftz, :Exp, T8, (T8,), ρf)
    @test exhf && κf == 1 << (P - 2)
    U1 = BinaryValue(Binary8p1uf)                                   # no subnormals: FTZ is exact
    @test measure_kappa(ftz_variant(:Convert, U1, T8, ρf), :Convert, U1, (T8,), ρf) === (0.0, true)
    # signed negative subnormal results flush symmetrically
    ftzn = ftz_variant(:Negate, T5, T5, RTE_SN)
    for c in 0:31
        x = fromcode(T5, c); want = Negate(T5, RTE_SN, x); got = ftzn(x)
        issubnormal(want) || @test got === want
        issubnormal(want) && @test iszero(got) || got === (signbit(want) ? Negate(MinNormalOf(T5)) : MinNormalOf(T5))
    end

    foreach(unregister_approx!, list_approx())
    impl = register_approx!(:exp_ftz_8p4, :Exp, T8, (T8,), ρf, ftz)
    @test kappa(:exp_ftz_8p4) == κf && kappa_measured(impl) == κf && impl.exhaustive
    @test :exp_ftz_8p4 in list_approx() && approx(:exp_ftz_8p4).fn === ftz
    @test_throws ArgumentError register_approx!(:exp_ftz_8p4, :Exp, T8, (T8,), ρf, ftz)   # duplicate
    @test_throws ArgumentError register_approx!(:lie, :Exp, T8, (T8,), ρf, ftz; κ = 1)     # understated
    ok = register_approx!(:generous, :Exp, T8, (T8,), ρf, ftz; κ = 10)                      # overstated is honest
    @test kappa(ok) == 10 && kappa_measured(ok) == κf
    denan(x) = (r = Log(T8, RTE_SN, x); isnan(r) ? zero(T8) : r)
    @test_throws ArgumentError register_approx!(:nanimpl, :Log, T8, (T8,), RTE_SN, denan)
    @test isnan(kappa(register_approx!(:nanimpl, :Log, T8, (T8,), RTE_SN, denan; κ = NaN)))
    @test_throws ArgumentError register_approx!(:badop, :Nope, T8, (T8,), ρf, ftz)
    @test_throws ArgumentError register_approx!(:badarity, :Add, T8, (T8,), ρf, ftz)
    unregister_approx!(:generous)
    @test !(:generous in list_approx())
    @test_throws KeyError approx(:generous)
end

@testset "conformance derives live" begin
    AIFloats.empty_tables!()
    AIFloats.get_table(:Exp, BinaryFormatOf(T8), BinaryFormatOf(T8), RTE_SN)
    AIFloats.get_table(:Add, BinaryFormatOf(T5), BinaryFormatOf(T5), BinaryFormatOf(T5), RTE_SN)
    T3 = BinaryValue(Binary3p2sf)
    AIFloats.get_table(:FMA, BinaryFormatOf(T3), BinaryFormatOf(T3),
                       BinaryFormatOf(T3), BinaryFormatOf(T3), RTE_SN)
    c = conformance()
    @test length(c.formats) == sum(4K - 2 for K in Int(AIFloats.KMIN):Int(AIFloats.KMAX)) == 504
    @test :Binary8p4se in c.formats && :Binary16p8se in c.formats
    @test length(c.operations) == length(AIFloats.OP_REGISTRY) == 52
    @test count(o -> o.arity == 3, c.operations) == 3
    @test length(c.cached_specializations) == 3
    # the declaration reports PUBLIC named tuples, not the internal key struct
    @test any(e -> e.arity === :ternary && e.op === :FMA, c.cached_specializations)
    @test all(e -> e.result isa Type && e.result <: Binary, c.cached_specializations)
    @test c.cached_bytes == sum(e -> e.bytes, c.cached_specializations)
    @test :BlockDotProduct in c.block_surface && :ScaledFMA in c.block_surface && :BlockTanh in c.block_surface
    @test length(c.block_surface) == 51 * 2 + 6
    @test any(a -> a.name === :exp_ftz_8p4 && a.exhaustive, c.approximate)
    @test length(c.rounding_modes) == 9 && c.saturation_modes == [:SF, :SP, :SN]
    @test c.package_version == Base.pkgversion(AIFloats)
    d = conformance_dict(c)
    @test d["package"] == "AIFloats.jl $(Base.pkgversion(AIFloats))"
    @test length(d["formats"]) == 504 && d["draft_identity"]["designation"] == "IEEE P3109/D1"
    @test any(s -> s["op"] == "Add" && s["saturation"] == "SN", d["cached_specializations"])
    @test any(s -> s["op"] == "FMA" && length(s["operands"]) == 3, d["cached_specializations"])
    @test d["cached_bytes"] == c.cached_bytes
    buf = IOBuffer(); conformance_report(buf, c); rep = String(take!(buf))
    @test occursin("κ verified exhaustively", rep) && occursin("Exp⟨", rep)
    @test occursin("Scalar operations (52)", rep) && occursin("K ∈ 3:16", rep)
    @test draft_revision() == "IEEE P3109/D1, uploaded 2026-07-17"
    # the retained transliteration matches its declared digest
    src = joinpath(pkgdir(AIFloats), draft_identity().retained_source)
    @test isfile(src)
    @test bytes2hex(open(sha256, src)) == draft_identity().transliteration_sha256
    foreach(unregister_approx!, list_approx())
    AIFloats.empty_tables!()
    @test isempty(conformance().cached_specializations) && isempty(conformance().approximate)
end

@testset "runtime-symbol validation and error taxonomy (improveapi3 Phase 7)" begin
    A = AIFloats
    F = Binary8p4se; T = BinaryValue(F)
    x, y = F(1.5), F(0.25)
    Av = [x, y, x]; Bv = [y, x, y]

    # registry metadata is frozen and looked up by name, not scanned
    @test A.operationinfo(:Add) == (name = :Add, arity = 2, group = :A, factors = 1)
    @test A.operationinfo(:FAA).arity == 3 && A.operationinfo(:FAA).factors == 1
    @test length(A.operations()) == length(A.OP_REGISTRY)
    # listings are deterministic: sorted on a semantic field, never insertion
    # order or type-object identity
    @test issorted([String(o.name) for o in A.operations()])
    @test A.operations() == A.operations()

    # ---- unknown operation: ArgumentError naming the alternative -------------
    for f in (() -> A.operationinfo(:NotAnOp),
              () -> vmap(:NotAnOp, F, RTE_SN, Av),
              () -> vmap!(similar(Av), :NotAnOp, RTE_SN, Av),
              () -> A.table_policy(:NotAnOp, F, F, RTE_SN),
              () -> A.measure_kappa(identity, :NotAnOp, F, (F,), RTE_SN),
              () -> A.register_approx!(:z, :NotAnOp, F, (F,), RTE_SN, identity))
        err = try (f(); nothing) catch e; e end
        @test err isa ArgumentError
        @test occursin("NotAnOp", err.msg)
    end

    # ---- known operation, wrong operand count: expected AND actual named -----
    for (f, want) in ((() -> vmap(:Add, F, RTE_SN, Av), ("2", "1")),
                      (() -> vmap(:Add, F, RTE_SN, Av, Bv, Av), ("2", "3")),
                      (() -> vmap(:Negate, F, RTE_SN, Av, Bv), ("1", "2")),
                      (() -> A.table_policy(:Add, F, F, RTE_SN), ("2", "1")))
        err = try (f(); nothing) catch e; e end
        @test err isa ArgumentError
        @test occursin(want[1], err.msg) && occursin(want[2], err.msg)
    end

    # ---- shape mismatches are DimensionMismatch, not ArgumentError -----------
    @test_throws DimensionMismatch vmap!(similar(Av), :Add, RTE_SN, Av, [y, x])
    @test_throws DimensionMismatch vmap!(Vector{T}(undef, 2), :Add, RTE_SN, Av, Bv)

    # ---- an invalid index is a BoundsError, through Base bounds checking -----
    pv = PackedVector(Av)
    @test_throws BoundsError pv[0]
    @test_throws BoundsError pv[4]
    @test_throws BoundsError Av[9]

    # ---- checked size arithmetic overflows, never wraps ----------------------
    @test_throws OverflowError PackedVector{T}(undef, typemax(Int))

    # ---- a refused conversion explains the correctness risk ------------------
    for f in (() -> Convert(F, RTE_SN, 1 // 3), () -> Convert(F, RTE_SN, π))
        err = try (f(); nothing) catch e; e end
        @test err isa ArgumentError
        @test occursin("Convert", err.msg)
    end

    # ---- IEEE invalid arithmetic RETURNS the prescribed NaN, never throws ----
    @test isnan(decode(Sqrt(F, RTE_SN, F(-1.0))))
    @test isnan(decode(Log(F, RTE_SN, F(-1.0))))
    @test isnan(decode(Divide(F, RTE_SN, F(0.0), F(0.0))))
    @test codepoint(Sqrt(F, RTE_SN, F(-1.0))) == A.nan_code(F)

    # ---- a type with no promised API is a MethodError, not a fabricated one --
    @test_throws MethodError Convert(F, RTE_SN, "1.5")
    @test_throws MethodError F(nothing)

    # validation happens ONCE at the boundary, not per element: a 100k-element
    # call costs the same one lookup a 3-element call does
    big = fill(x, 100_000)
    @test length(vmap(:Negate, F, RTE_SN, big)) == 100_000
end
