# latency suite: package load and first-call compilation, measured in FRESH
# processes. These cannot be Chairmarks samples — the quantity of interest
# happens exactly once per process — so the suite shells out and parses.

section("latency — load and first call (fresh process each)")

const _LAT_PROBE = raw"""
t0 = time_ns(); using AIFloats; t1 = time_ns()
println("load\t", (t1 - t0) / 1e6)
const T = Binary8p4se
const S = Binary8p3se
const F = BinaryFormatOf(T)
macro first(label, ex)
    quote
        local t = time_ns(); $(esc(ex)); local d = (time_ns() - t) / 1e6
        println($label, "\t", d)
    end
end
const x = T(1.5); const y = T(0.25)
@first "T(1.3)"          T(1.3)
@first "Add(x,y)"        Add(x, y)
@first "Exp(x)"          Exp(x)
@first "Log(x)"          Log(x)
@first "sort"            sort([x, y, x])
const A = [T(UInt8(i & 0xff)) for i in 0:4095]
const B = [T(UInt8((3i + 1) & 0xff)) for i in 0:4095]
const D = similar(A)
@first "vmap! Add"       vmap!(D, Val(:Add), RTE_SN, A, B)
@first "A .+ B"          A .+ B
@first "exp.(A)"         exp.(A)
@first "PackedVector"    PackedVector(A)
const bx = Block(one(S), ntuple(i -> T(UInt8((7i + 3) & 0x7f)), 16))
@first "BlockReduceAdd"  BlockReduceAdd(T, RTE_SN, bx)
"""

let probe = joinpath(mktempdir(), "probe.jl")
    write(probe, _LAT_PROBE)
    proj = dirname(@__DIR__)
    # two processes; report the second (the first can pay for a stale cache)
    local out = ""
    for _ in 1:2
        out = read(`$(Base.julia_cmd()) --project=$proj --startup-file=no $probe`, String)
    end
    for line in split(strip(out), '\n')
        label, ms = split(line, '\t')
        println(rpad(label == "load" ? "using AIFloats" : "first " * label, 44),
                lpad(round(parse(Float64, ms); digits = 2), 11), " ms")
    end
end
