using FloatsForML
using Documenter, DocumenterMermaid

push!(LOAD_PATH,"../src/")

DocMeta.setdocmeta!(FloatsForML, :DocTestSetup, :(using FloatsForML); recursive = true)

#const page_rename = Dict("developer.md" => "Developer docs") # Without the numbers
#const numbered_pages = [
#    file for file in readdir(joinpath(@__DIR__, "src")) if
#    file != "index.md" && splitext(file)[2] == ".md"
# ]

makedocs(;
    modules = [FloatsForML],
    sitename = "FloatsForML",
    authors = "Jeffrey Sarnoff <jeffrey.sarnoff@gmail.com>",
    format = Documenter.HTML(),
    repo = "https://github.com/DiademSpecialProjects/FloatsForML.jl/blob/{commit}{path}#{line}",
    pages = Any[
                "Home" => "index.md",
                "Overview" => "overview.md",
                "Float Families" => "families.md",
                "Type Specifics" => "specifics.md",
                "Computing over Type abstractions" => "abstractions.md",
                "The foundational sequence" => "sequence.md",
                "Operations" => "operations.md",
                "Mathematical Functions" => "mathfunctions.md",
                "Acknowledgements" => "acknowledgements.md",
               ])

deploydocs(; 
    repo = "github.com/DiademSpecialProjects/FloatsForML.jl",
    target = "build")
