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
    repo = "https://github.com/DiademSpecialProjects/FloatsForML.jl/blob/{commit}{path}#{line}",
    sitename = "FloatsForML.jl",
    format = Documenter.HTML(; 
                 repolink="https://github.com/DiademSpecialProjects/FloatsForML.jl/",
                 prettyurls=get(ENV, "CI", "false") == "true",
                 canonical = "https://DiademSpecialProjects.github.io/FloatsForML.jl",
                 edit_link  = "main",
                 assets=String[],
            ),
    pages = [
                 "Home" => "index.md",
                 "Reference" => "reference.md";
                 numbered_pages
            ],
   )
 
deploydocs(; repo = "github.com/DiademSpecialProjects/FloatsForML.jl",
             target = "FloatsForML.jl",
             push_preview = true,
             devbranch = "main",
             force = true,
             commit_message = "Update documentation",
             branch = "gh-pages",
          )
