using AIFloats
using Test
using Random
using Aqua
using JET

# Phase 5 gate, hygiene side. Aqua: ambiguities, undefined exports, piracy,
# unbound parameters, compat. JET: whole-package abstract interpretation, then
# the concrete entry points users call with the format statically known.

@testset "Aqua" begin
    # Aqua and JET are direct project dependencies so `using` works in an
    # ordinary --project=. session; PrecompileTools/SHA are declared ahead of
    # the phases that use them (plan Phase 7).
    # persistent_tasks loads the package in a fresh process and times the
    # exit; the precompile workload plus a busy machine (the suite and the docs
    # build run side by side in CI) exceeded Aqua's 5 s default once — the
    # bound is about the process exiting at all, not about load time
    Aqua.test_all(AIFloats;
        stale_deps = (ignore = [:Aqua, :JET, :PrecompileTools, :SHA],),
        persistent_tasks = (tmax = 60,))
end

# `_vmap_packed` builds `Vector{OUT}` from its `::Type{OUT}` argument and views
# it per tile. Analyzed as a generic method JET widens the correlation between
# the type parameter and the container's element type and reports a method
# error the concrete-call gate below shows does not exist. Nothing else may
# report.
const _JET_KNOWN_GENERIC_WIDENING = (:_vmap_packed,)
_report_method(r) = let li = r.vst[end].linfo
    li isa Core.MethodInstance && li.def isa Method ? li.def.name : nothing
end

@testset "JET (whole package)" begin
    result = JET.report_package(AIFloats; target_modules = (AIFloats,),
                                toplevel_logger = nothing)
    reports = filter(r -> _report_method(r) ∉ _JET_KNOWN_GENERIC_WIDENING,
                     JET.get_reports(result))
    @test isempty(reports)
    isempty(reports) || foreach(display, reports)
end

@testset "JET (concrete entry points)" begin
    T = Binary8p4se
    S = Binary8p3se
    a, b = T(1.5), T(0.25)
    A = T.(randn(MersenneTwister(1), 64)); B = T.(randn(MersenneTwister(2), 64))
    D = similar(A)
    JET.@test_call Add(T, RTE_SN, a, b)
    JET.@test_call FMA(T, RTE_SN, a, b, a)
    JET.@test_call Exp(T, RTE_SN, a)
    JET.@test_call Convert(S, RTE_SN, a)
    JET.@test_call a + b
    JET.@test_call a < b
    JET.@test_call round(a)
    JET.@test_call eps(a)
    JET.@test_call a + 1.0
    JET.@test_call project(T, RTE_SN, 1.6)
    JET.@test_call vmap!(D, Val(:Exp), RTE_SN, A)
    JET.@test_call vmap!(D, Val(:Add), RTE_SN, A, B)
    JET.@test_call vmap!(D, Val(:FMA), RTE_SN, A, B, A)
    JET.@test_call Float32(a)
    JET.@test_call sort!(copy(A))
    JET.@test_call rand(T)
    # the method the package-wide pass cannot verify, verified where it is called
    pv = PackedVector(A)
    JET.@test_call AIFloats.vmap(:Exp, T, RTE_SN, pv)
    JET.@test_call AIFloats.vmap(:Exp, T, Projection(AIFloats.ρRSA(3), SN), pv; rng = MersenneTwister(1))
    # rung 2 and 3 entry points, the fast layers, and the block surface
    W2 = AIFloats.Binary16p5se; W3 = AIFloats.Binary16p1se
    JET.@test_call Add(W2, RTE_SN, W2(1.5), W2(0.25))
    JET.@test_call Add(W3, RTE_SN, W3(2.0), W3(0.25))
    JET.@test_call Exp(W3, RTE_SN, W3(2.0))
    JET.@test_call FAA(T, RTE_SN, a, b, a)
    JET.@test_call BlockDotProduct(T, RTE_SN, Block(one(S), (a, b)), Block(one(S), (b, a)))
end
