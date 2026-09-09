include(joinpath(@__DIR__, "..", "test", "support", "source_cases.jl"))
using .SourceCases: run_suite
using JSON: JSON
using SHA: sha256

function main(args)
    args=copy(args)
    report=nothing
    if "--report" in args
        i=findfirst(==("--report"), args)
        i<length(args) || error("--report requires an output path")
        report=args[i+1]
        deleteat!(args, i:(i+1))
    end
    suites=isempty(args) ?
           [
        "smoke",
        "domains",
        "codec",
        "projection",
        "scalar",
        "order-next",
        "blocks",
        "conformance",
        "symbolic",
        "order-full",
        "standalone",
    ] : args
    failed=0
    results=Any[]
    for suite in suites
        elapsed=@elapsed result=run_suite(suite)
        failed+=length(result.failures)
        push!(
            results,
            Dict(
                "suite"=>suite,
                "expected_executed"=>result.count,
                "failures"=>length(result.failures),
                "seconds"=>elapsed,
            ),
        )
        println(
            "$suite: $(result.count-length(result.failures))/$(result.count) passed ($(round(elapsed;digits=2))s)",
        )
        if !isempty(result.failures)
            path=joinpath(tempdir(), "p3109-julia-$suite-failures.txt")
            write(path, join(result.failures, "\n\n"))
            println(join(first(result.failures, min(5, length(result.failures))), "\n\n"))
            println("All failures: $path")
        end
    end
    if report !== nothing
        root=normpath(joinpath(@__DIR__, ".."))
        hashes=Dict{String,String}()
        for directory in ("src", "test", "tools")
            for (folder, _, files) in walkdir(joinpath(root, directory))
                for file in files
                    endswith(file, ".jl") || continue
                    path=joinpath(folder, file)
                    hashes[relpath(path, root)]=bytes2hex(sha256(read(path)))
                end
            end
        end
        data=Dict(
            "julia_version"=>string(VERSION),
            "prerelease"=>!isempty(VERSION.prerelease),
            "command"=>"julia --startup-file=no --project=tools tools/run-cases.jl --report PATH "*join(
                args,
                " ",
            ),
            "working_directory"=>root,
            "suites"=>results,
            "exit_code"=>Int(failed!=0),
            "implementation_hashes"=>hashes,
            "input_manifest_sha256"=>bytes2hex(
                sha256(read(joinpath(root, "inventory", "inputs.toml"))),
            ),
            "dependency_manifest_sha256"=>bytes2hex(sha256(read(joinpath(root, "Manifest.toml")))),
        )
        write(report, JSON.json(data)*"\n")
    end
    failed==0 || error("$failed source cases failed")
end
main(ARGS)
