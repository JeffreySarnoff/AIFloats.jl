using BenchmarkTools: @benchmark, median
using TOML: print as print_toml
import P3109Reference as P

function benchmark_suite(first_projection_seconds)
    f=P.F8
    p=P.Projection(P.NEAREST_EVEN)
    x=P.finite(7//3)
    projection=@benchmark P.project($f, $p, $x) samples=1000 seconds=1
    codec=@benchmark P.decode($f, 72) samples=1000 seconds=1
    scalar=@benchmark P.SpecAPI.FMA($f, $f, $f, $f, $p, 72, 68, 192) samples=1000 seconds=1
    xs=fill(big(64), 32)
    reduction=@benchmark P.SpecAPI.BlockReduceAdd(32, $f, $f, $f, $p, 64, $xs) samples=1000 seconds=1
    rows=Dict{String,Any}(
        "julia_version"=>string(VERSION),
        "cpu"=>Sys.CPU_NAME,
        "first_projection_seconds"=>first_projection_seconds,
        "note"=>"first invocation timed outside the benchmark function; may reuse precompiled code; warmed medians are workload-specific",
    )
    for (name, trial) in (
        ("decode", codec),
        ("project", projection),
        ("fma", scalar),
        ("block_reduce_32", reduction),
    )
        estimate=median(trial)
        rows[name]=Dict(
            "median_ns"=>estimate.time,
            "bytes"=>estimate.memory,
            "allocations"=>estimate.allocs,
        )
    end
    return rows
end
first_projection_seconds =
    @elapsed Base.invokelatest(P.project, P.F8, P.Projection(P.NEAREST_EVEN), P.finite(7//3))
print_toml(stdout, benchmark_suite(first_projection_seconds); sorted = true)
