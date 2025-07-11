using Documenter
using DocumenterMermaid
using AIFloats

makedocs(;
    modules=[AIFloats],
    authors="Jeffrey Sarnoff <jeffrey.sarnoff@gmail.com>",
    repo="https://github.com/JeffreySarnoff/AIFloats.jl/blob/{commit}{path}#{line}",
    sitename="AIFloats.jl",
    format=Documenter.HTML(;
        prettyurls=get(ENV, "CI", "false") == "true",
        canonical="https://jeffreysarnoff.github.io/AIFloats.jl",
        edit_link="main",
        assets=String[],
        mathengine=MathJax3(Dict(
            :loader => Dict("load" => ["[tex]/physics"]),
            :tex => Dict(
                "inlineMath" => [["\$", "\$"], ["\\(", "\\)"]],
                "tags" => "ams",
                "packages" => ["base", "ams", "autoload", "physics"]
            )
        ))
    ),
    pages=[
        "Home" => "index.md",
        "Manual" => [
            "Overview" => "manual/overview.md",
            "Type Hierarchy" => "manual/hierarchy.md",
            "Construction" => "manual/construction.md",
            "Operations" => "manual/operations.md",
            "Value Sequences" => "manual/sequences.md",
            "Encoding & Indexing" => "manual/encoding.md",
        ],
        "Tutorials" => [
            "Getting Started" => "tutorials/getting_started.md",
            "Custom Formats" => "tutorials/custom_formats.md",
            "Performance Optimization" => "tutorials/performance.md",
        ],
        "Reference" => [
            "Type System" => "reference/types.md",
            "Constructors" => "reference/constructors.md",
            "Predicates" => "reference/predicates.md",
            "Counts & Metrics" => "reference/counts.md",
            "Exponents" => "reference/exponents.md",
            "Extrema" => "reference/extrema.md",
            "Encoding Functions" => "reference/encoding.md",
            "Index Functions" => "reference/indices.md",
            "Julia Integration" => "reference/julia.md",
        ],
        "Examples" => "examples.md",
        "Implementation Notes" => "implementation.md",
        "Glossary" => "glossary.md",
    ],
)

deploydocs(;
    repo="github.com/JeffreySarnoff/AIFloats.jl",
    devbranch="main",
)