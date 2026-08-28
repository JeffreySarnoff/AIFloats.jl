using AIFloats
using Test
using Random
using SHA

# Phase 7 gate: the conformance report derives from the registry live; κ
# registration rejects understatement; the retained draft's digest matches.

const T8 = binary8p4se
const T5 = binary5p2se

@testset "κ measurement" begin
    exact_exp(x) = Exp(T8, RTE_SN, x)
    @test measure_kappa(exact_exp, :Exp, T8, (T8,), RTE_SN) === (0.0, true)
    exact_add(x, y) = Add(T5, RTE_SN, x, y)
    @test measure_kappa(exact_add, :Add, T5, (T5, T5), RTE_SN) === (0.0, true)
    T4 = binary4p2se
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
end

@testset "FTZ worked example (draft Annex)" begin
    ρf = RTE_SF
    ftz = ftz_variant(:Exp, T8, T8, ρf)
    P = Int(PrecisionOf(T8)); half = 1 << (P - 2); mn = decode(MinNormalOf(T8))
    for c in 0:255
        x = T8(UInt8(c))
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
    U1 = binary8p1uf                                   # no subnormals: FTZ is exact
    @test measure_kappa(ftz_variant(:Convert, U1, T8, ρf), :Convert, U1, (T8,), ρf) === (0.0, true)
    # signed negative subnormal results flush symmetrically
    ftzn = ftz_variant(:Negate, T5, T5, RTE_SN)
    for c in 0:31
        x = T5(UInt8(c)); want = Negate(T5, RTE_SN, x); got = ftzn(x)
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
    c = conformance()
    @test length(c.formats) == sum(4K - 2 for K in Int(AIFloats.KMIN):Int(AIFloats.KMAX)) == 504
    @test :binary8p4se in c.formats && :binary16p8se in c.formats
    @test length(c.operations) == length(AIFloats.OP_REGISTRY) == 52
    @test count(o -> o.arity == 3, c.operations) == 3
    @test length(c.cached_specializations) == 2
    @test :BlockDotProduct in c.block_surface && :ScaledFMA in c.block_surface && :BlockTanh in c.block_surface
    @test length(c.block_surface) == 51 * 2 + 6
    @test any(a -> a.name === :exp_ftz_8p4 && a.exhaustive, c.approximate)
    @test length(c.rounding_modes) == 9 && c.saturation_modes == [:SF, :SP, :SN]
    @test c.package_version == Base.pkgversion(AIFloats)
    d = conformance_dict(c)
    @test d["package"] == "AIFloats.jl $(Base.pkgversion(AIFloats))"
    @test length(d["formats"]) == 504 && d["draft_identity"]["designation"] == "IEEE P3109/D1"
    @test any(s -> s["op"] == "Add" && s["saturation"] == "ρSN", d["cached_specializations"])
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
