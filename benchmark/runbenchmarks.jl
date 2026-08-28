# AIFloats benchmark driver — Chairmarks lives here, never in the package's
# runtime dependencies. Run:
#
#     julia --project=benchmark -t 4 benchmark/runbenchmarks.jl            # all suites
#     julia --project=benchmark -t 4 benchmark/runbenchmarks.jl scalar     # one suite
#
# Every row is one `@b` sample with interpolated operands. Rows that need a
# non-default global (a cold cache, one thread, a disabled fast path) run
# inside `withflags`, which restores every Ref in a `finally`.

using Chairmarks, AIFloats

const NSCOL = 46

"""One benchmark row: label, time in ns, allocations, bytes."""
function row(label, s::Chairmarks.Sample; elems::Union{Nothing,Int} = nothing)
    print(rpad(label, NSCOL), lpad(round(s.time * 1e9; digits = 1), 11), " ns")
    s.allocs > 0 && print("  allocs=", Int(s.allocs), " bytes=", Int(s.bytes))
    elems === nothing || print("  ", round(elems / s.time / 1e9; digits = 3), " Gelem/s")
    println()
end

"""Run `f` with the package's mutable policy Refs set, restoring all of them."""
function withflags(f; fast_arith = true, fast_enclosure = true, threaded = true,
                   eager_bits = 16, thread_min = 1 << 15)
    saved = (AIFloats.FAST_ARITH[], AIFloats.FAST_ENCLOSURE[],
             AIFloats.THREADED_KERNELS[], AIFloats.TABLE_EAGER_BITS[],
             AIFloats.THREAD_MIN_ELEMS[], DefaultProjection())
    try
        AIFloats.FAST_ARITH[] = fast_arith
        AIFloats.FAST_ENCLOSURE[] = fast_enclosure
        AIFloats.THREADED_KERNELS[] = threaded
        AIFloats.TABLE_EAGER_BITS[] = eager_bits
        AIFloats.THREAD_MIN_ELEMS[] = thread_min
        f()
    finally
        AIFloats.FAST_ARITH[], AIFloats.FAST_ENCLOSURE[],
        AIFloats.THREADED_KERNELS[], AIFloats.TABLE_EAGER_BITS[],
        AIFloats.THREAD_MIN_ELEMS[] = saved[1:5]
        DefaultProjection!(saved[6])
        AIFloats.empty_tables!()
    end
end

function header()
    pkgroot = pkgdir(AIFloats)
    commit = try
        c = readchomp(`git -C $pkgroot rev-parse --short HEAD`)
        isempty(readchomp(`git -C $pkgroot status --porcelain`)) ? c : c * " (dirty)"
    catch
        "unknown"
    end
    println("AIFloats benchmarks")
    println("  julia    ", VERSION, "   threads=", Threads.nthreads())
    println("  cpu      ", Sys.cpu_info()[1].model)
    println("  commit   ", commit)
    println("  defaults ρ=", DefaultProjection(),
            "  TABLE_EAGER_BITS=", AIFloats.TABLE_EAGER_BITS[],
            "  THREAD_MIN_ELEMS=", AIFloats.THREAD_MIN_ELEMS[])
    println()
end

section(name) = println("\n── ", name, " ", "─"^max(0, 60 - length(name)))

const SUITES = ("scalar", "arrays")

function main(args)
    header()
    suites = isempty(args) ? SUITES : args
    for s in suites
        s in SUITES || error("unknown suite $s; choose from $(SUITES)")
        include(joinpath(@__DIR__, s * ".jl"))
    end
    AIFloats.empty_tables!()
    return nothing
end

main(ARGS)
