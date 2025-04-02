using FloatsForML
using Documenter

DocMeta.setdocmeta!(FloatsForML, :DocTestSetup, :(using FloatsForML); recursive = true)

const page_rename = Dict("developer.md" => "Developer docs") # Without the numbers
const numbered_pages = [
    file for file in readdir(joinpath(@__DIR__, "src")) if
    file != "index.md" && splitext(file)[2] == ".md"
]

makedocs(;
    modules = [FloatsForML],
    authors = "Jeffrey Sarnoff <jeffrey.sarnoff@gmail.com>",
    repo = "https://github.com/JeffreySarnoff/FloatsForML.jl/blob/{commit}{path}#{line}",
    sitename = "FloatsForML.jl",
    format = Documenter.HTML(; canonical = "https://JeffreySarnoff.github.io/FloatsForML.jl"),
    pages = ["index.md"; numbered_pages],
)

deploydocs(; repo = "github.com/JeffreySarnoff/FloatsForML.jl")
