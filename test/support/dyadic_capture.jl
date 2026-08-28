# capture the Dyadic golden digests from SmallFloats' ORIGINAL DyadicNumbers
#
#     julia --project=$HOME/github/SmallFloats.jl test/support/dyadic_capture.jl
#
# Run on a machine that has SmallFloats. Re-running against the adaptation
# would prove only that the code agrees with itself; the file refuses to be
# overwritten unless AIFLOATS_DYADIC_OVERWRITE=1.
using SmallFloats
include(joinpath(@__DIR__, "dyadic_digest.jl"))
const GOLDEN = joinpath(@__DIR__, "dyadic_golden.sha256")
if isfile(GOLDEN) && get(ENV, "AIFLOATS_DYADIC_OVERWRITE", "") != "1"
    println("REFUSING to overwrite $GOLDEN (set AIFLOATS_DYADIC_OVERWRITE=1)")
    exit(1)
end
ds = dyadic_digests(SmallFloats.DyadicNumbers)
open(GOLDEN, "w") do io
    println(io, "# AIFloats.jl — Dyadic differential golden digests (plan §9.9)")
    println(io, "# captured from SmallFloats.jl DyadicNumbers, git ",
            strip(read(`git -C $(homedir())/github/SmallFloats.jl rev-parse HEAD`, String)),
            " on Julia ", VERSION)
    println(io, "# Each line: <sha256> <section>. See test/support/dyadic_digest.jl.")
    for (name, d) in ds
        println(io, d, "  ", name)
    end
end
println("wrote ", GOLDEN); foreach(p -> println(p[2], "  ", p[1]), ds)
