# the conformance declaration — derived LIVE from the registry, the table
# cache, and the κ registry. Nothing here is spelled by hand that the package
# already knows: a declaration that can go stale is worse than none.

"""
    DRAFT_IDENTITY

The normative source this release is measured against, and the transliteration it
retains as provenance.

`report_*` names the **designated document**: the IEEE Working Group P3109 Interim
Report on Arithmetic Formats for Machine Learning, at the stable P3109 Public URL,
identified by its cover revision, cover date, and the SHA-256 of the PDF that was
compared. That comparison is recorded in `docs/other/p3109-delta.md`.

`retained_*` names the local Markdown transliteration the implementation was
originally written against. It is provenance, not authority: where the two differ,
the PDF governs.

The report is an **unapproved draft**. Its cover states that it must not be used for
conformance or compliance purposes, and neither this identity nor
[`conformance`](@ref) asserts otherwise.
"""
const DRAFT_IDENTITY = (
    designation = "IEEE P3109 Interim Report on Arithmetic Formats for Machine Learning",
    report_revision = "4.0.3",
    report_date = "2026-09-01",
    report_url = "https://github.com/P3109/Public/blob/main/IEEE%20P3109%20Interim%20Report.pdf",
    report_sha256 = "7de115ed6882b7550b8fa61e81e5173857b340c3bfe30db8d4ad74b472229b9e",
    report_status = "unapproved draft; not for conformance/compliance use",
    retained_designation = "IEEE P3109/D1",
    retained_uploaded = "2026-07-17",
    retained_source = "docs/other/IEEE_D1.md",
    transliteration_sha256 = "820cb5009cd6fe9032f5bdfb661bc639e33296f716a552eafc81f899411bb5f2",
)
const DRAFT_REVISION =
    "$(DRAFT_IDENTITY.designation), version $(DRAFT_IDENTITY.report_revision) " *
    "($(DRAFT_IDENTITY.report_date)) — $(DRAFT_IDENTITY.report_status)"
"""
    draft_revision() -> String

Human-readable designation of the normative P3109 report this release is measured
against, including its unapproved-draft status. See [`draft_identity`](@ref) for the
structured form.
"""
draft_revision() = DRAFT_REVISION
"""
    draft_identity() -> NamedTuple

Structured identity of the designated P3109 Interim Report — revision, date, URL, and
PDF SHA-256 — together with the retained transliteration and its digest. See
`AIFloats.DRAFT_IDENTITY` for what each field means and which one is authoritative.
"""
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
`cached_specializations`, `cached_bytes`, `approximate`. Build with
[`conformance`](@ref).
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
    cached_specializations::Vector{TableEntry}
    cached_bytes::Int
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
specializations actually instantiated (`AIFloats.table_entries()` — both
code-unit caches, in one locked snapshot alongside their total bytes),
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
    # ONE snapshot: the entries and their byte total must describe the same
    # moment. Reading them through two separately locked queries let another
    # task's build land between them, and the report then printed a count and a
    # size that did not correspond (improveapi3.md §6 Phase 5.7).
    cached = table_entries()
    cached_bytes = sum(e -> e.bytes, cached; init = 0)
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
        cached, cached_bytes, sort!(apx; by = a -> a.name))
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
        "draft_identity" => Dict(String(k) => v for (k, v) in pairs(c.draft_identity)),
        "interpretations" => copy(c.interpretations),
        "formats" => String.(c.formats),
        "operations" => [Dict("name" => String(o.name), "arity" => o.arity,
                              "group" => String(o.group)) for o in c.operations],
        "rounding_modes" => copy(c.rounding_modes),
        "saturation_modes" => String.(c.saturation_modes),
        "block_surface" => String.(c.block_surface),
        "cached_specializations" => [Dict("op" => String(e.op),
                                          "arity" => String(e.arity),
                                          "result" => string(e.result),
                                          "operands" => [string(f) for f in e.operands],
                                          "rounding" => String(e.rounding),
                                          "saturation" => String(e.saturation),
                                          "bytes" => e.bytes)
                                     for e in c.cached_specializations],
        "cached_bytes" => c.cached_bytes,
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
    println(io, "Measured against: ", c.draft)
    println(io, "  ", c.draft_identity.report_url)
    println(io, "  pdf sha256 ", c.draft_identity.report_sha256)
    println(io, "Retained transliteration: ", c.draft_identity.retained_source,
            " (", c.draft_identity.retained_designation,
            ", sha256 ", c.draft_identity.transliteration_sha256, ")")
    # The cover of the designated report says so in as many words. A declaration
    # that omitted it would read as a certification, which this is not.
    println(io, "NOT a certification: the designated report is an unapproved draft and")
    println(io, "must not be used for conformance or compliance purposes. This is a query")
    println(io, "of what this package implements, in the shape §4.6 describes.")
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
    # `c.cached_bytes`, not a fresh `table_stats()` call: the count and the
    # size printed here must describe the same moment the declaration captured
    println(io, "\nInstantiated pure-ρ table specializations: ", length(c.cached_specializations),
            " (", c.cached_bytes, " bytes)")
    for e in c.cached_specializations
        println(io, "  ", e.op, "⟨", join(string.(e.operands), " × "),
                " → ", e.result, ", (", e.rounding, ", ", e.saturation, ")⟩")
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
