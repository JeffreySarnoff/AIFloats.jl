# the conformance declaration — derived LIVE from the registry, the table
# cache, and the κ registry. Nothing here is spelled by hand that the package
# already knows: a declaration that can go stale is worse than none.

"""The retained P3109 draft this package implements, with the digest of its
transliteration (`docs/other/IEEE_D1.md`)."""
const DRAFT_IDENTITY = (
    designation = "IEEE P3109/D1",
    uploaded = "2026-07-17",
    retained_source = "docs/other/IEEE_D1.md",
    transliteration_sha256 = "820cb5009cd6fe9032f5bdfb661bc639e33296f716a552eafc81f899411bb5f2",
)
const DRAFT_REVISION = "$(DRAFT_IDENTITY.designation), uploaded $(DRAFT_IDENTITY.uploaded)"
"""Human-readable designation of the retained P3109 draft implemented by this release."""
draft_revision() = DRAFT_REVISION
"""Structured identity and SHA-256 digest of the retained P3109 draft transliteration."""
draft_identity() = DRAFT_IDENTITY

# the supported vocabulary, declared once. The type hierarchy owns
# classification; this list owns stable external names. Never discovered with
# `subtypes`: a third-party subtype is not a supported mode.
const _ROUNDING_MODE_DECLARATIONS = (
    "RTE (RoundToEven)", "RTA (RoundToAway)",
    "RTP (RoundTowardPositive)", "RTN (RoundTowardNegative)", "RTZ (RoundTowardZero)",
    "RTO (RoundToOdd)",
    "RSA{N} (StochasticA, 1 ≤ N ≤ 60)", "RSB{N} (StochasticB)", "RSC{N} (StochasticC)",
)
const _SATURATION_MODE_DECLARATIONS = (:SF, :SP, :SN)

"""
    ConformanceDeclaration

The package's draft-§4.6-style conformance declaration. Fields: `package`,
`package_version`, `draft`, `draft_identity`, `interpretations`, `formats`,
`operations`, `rounding_modes`, `saturation_modes`, `block_surface`,
`cached_specializations`, `approximate`. Build with [`conformance`](@ref).
"""
struct ConformanceDeclaration
    package::String
    package_version::VersionNumber
    draft::String
    draft_identity::typeof(DRAFT_IDENTITY)
    interpretations::Vector{String}
    formats::Vector{Symbol}
    operations::Vector{NamedTuple{(:name, :arity, :group), Tuple{Symbol, Int, Symbol}}}
    rounding_modes::Vector{String}
    saturation_modes::Vector{Symbol}
    block_surface::Vector{Symbol}
    cached_specializations::Vector{TableKey}
    approximate::Vector{NamedTuple{(:name, :op, :kappa, :exhaustive), Tuple{Symbol, Symbol, Float64, Bool}}}
end

# interpretations the implementation records where the draft leaves a choice
# (the [interp] marks in ops/oracle.jl)
const _INTERPRETATIONS = (
    "extremum operations follow IEEE 754-2019 maximum/minimum/maximumNumber/minimumNumber semantics",
)

"""
    conformance() -> ConformanceDeclaration

The live conformance declaration: formats from the alias grid, operations
from `OP_REGISTRY`, the block surface generated from it, the pure-ρ table
specializations actually instantiated (`table_keys()` — both code-unit caches),
and the κ registry. Serialize with [`conformance_dict`](@ref) or render with
[`conformance_report`](@ref).
"""
function conformance()
    ops = [(name = o.name, arity = o.arity, group = o.group) for o in OP_REGISTRY]
    blocknames = Symbol[]
    for o in OP_REGISTRY
        o.name === :Convert && continue
        push!(blocknames, Symbol(:Block, o.name), Symbol(:Scaled, o.name))
    end
    append!(blocknames, (:BlockReduceAdd, :BlockReduceMultiply, :BlockDotProduct,
                         :ConvertFromBlock, :ConvertToBlock, :ConvertToBlockMaxAbsFinite))
    cached = table_keys()
    apx = lock(() -> [(name = a.name, op = a.op, kappa = a.kappa_declared, exhaustive = a.exhaustive)
                      for a in values(APPROX_REGISTRY)], APPROX_LOCK)
    version = something(Base.pkgversion(@__MODULE__), v"0.0.0-DEV")
    ConformanceDeclaration(
        "AIFloats.jl $version", version, DRAFT_REVISION, DRAFT_IDENTITY,
        collect(String, _INTERPRETATIONS),
        sort!(collect(keys(_NAMED))),
        ops,
        collect(String, _ROUNDING_MODE_DECLARATIONS),
        collect(Symbol, _SATURATION_MODE_DECLARATIONS),
        sort!(blocknames),
        cached, sort!(apx; by = a -> a.name))
end

"""
    conformance_dict(c = conformance()) -> Dict{String,Any}

Nested `Dict` form of the declaration — serializable by any JSON/TOML writer.
"""
function conformance_dict(c::ConformanceDeclaration = conformance())
    Dict{String, Any}(
        "package" => c.package,
        "package_version" => string(c.package_version),
        "draft" => c.draft,
        "draft_identity" => Dict(
            "designation" => c.draft_identity.designation,
            "uploaded" => c.draft_identity.uploaded,
            "retained_source" => c.draft_identity.retained_source,
            "transliteration_sha256" => c.draft_identity.transliteration_sha256),
        "interpretations" => copy(c.interpretations),
        "formats" => String.(c.formats),
        "operations" => [Dict("name" => String(o.name), "arity" => o.arity,
                              "group" => String(o.group)) for o in c.operations],
        "rounding_modes" => copy(c.rounding_modes),
        "saturation_modes" => String.(c.saturation_modes),
        "block_surface" => String.(c.block_surface),
        "cached_specializations" => [Dict("op" => String(k.op), "fr" => collect(k.fr),
                                          "f1" => collect(k.f1), "f2" => collect(k.f2),
                                          "rounding" => String(k.rm), "saturation" => String(k.sm))
                                     for k in c.cached_specializations],
        "approximate" => [Dict("name" => String(a.name), "op" => String(a.op),
                               "kappa" => a.kappa, "exhaustive" => a.exhaustive)
                          for a in c.approximate])
end

"""
    conformance_report([io], c = conformance())

Human-readable rendering of the conformance declaration.
"""
function conformance_report(io::IO = stdout, c::ConformanceDeclaration = conformance())
    println(io, "Conformance declaration — ", c.package)
    println(io, "Implements: ", c.draft)
    println(io, "Retained source: ", c.draft_identity.retained_source,
            " (sha256 ", c.draft_identity.transliteration_sha256, ")")
    println(io, "Interpretations: ", isempty(c.interpretations) ? "none" : "")
    for s in c.interpretations
        println(io, "  - ", s)
    end
    # the range is READ FROM THE CONSTANTS, never spelled
    println(io, "\nFormats (", length(c.formats), "): all Binary{K,P,Σ,Δ}, K ∈ $(Int(KMIN)):$(Int(KMAX)), ",
            "Σ ∈ {SIGNED, UNSIGNED}, Δ ∈ {FINITE, EXTENDED}")
    println(io, "\nScalar operations (", length(c.operations), "):")
    for a in 1:3
        println(io, "  arity ", a, ": ", join((String(o.name) for o in c.operations if o.arity == a), ", "))
    end
    println(io, "\nRounding modes: ", join(c.rounding_modes, ", "))
    println(io, "Saturation modes: ", join(String.(c.saturation_modes), ", "))
    println(io, "\nBlock/scaled surface (", length(c.block_surface), " operations), any B ≥ 1")
    println(io, "\nInstantiated pure-ρ table specializations: ", length(c.cached_specializations),
            " (", table_bytes(), " bytes)")
    for k in c.cached_specializations
        println(io, "  ", k.op, "⟨", k.f1, k.f2 == (0, 0, 0, 0) ? "" : string(" × ", k.f2),
                " → ", k.fr, ", (", k.rm, ", ", k.sm, ")⟩")
    end
    if isempty(c.approximate)
        println(io, "\nApproximate implementations: none (all default paths are bit-exact)")
    else
        println(io, "\nDeclared κ-approximate implementations:")
        for a in c.approximate
            println(io, "  :", a.name, "  op=", a.op, "  κ=", a.kappa,
                    a.exhaustive ? "  (κ verified exhaustively)" : "  (κ sampled — not exhaustive)")
        end
    end
    nothing
end
