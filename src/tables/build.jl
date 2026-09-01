# builders: Val(op) function barrier, threaded fill
#
# One table entry = one trip through the scalar path — the same path Shape B
# runs per element, so a table can never disagree with the compute kernel.
# Convert is the sole op with no ω-semantics (registry group :conv): a bare
# projection of the decoded operand. R = 0 is safe everywhere here: stochastic
# ρ never reaches a builder.

@inline _scalar_code(op::Val, fr::Type{<:Binary}, ρ::Projection, xs...) =
    codepoint(_kernel_result(op, fr, ρ, 0, xs...))

# Every datum of an operand format, indexable by `code + 1`. The TableDecode
# row is the constant tuple UInt8-coded formats already carry; the
# ComputeDecode row materializes the same values for a wide operand, which has
# no such tuple but can still appear inside an affordable table — a 7×9
# binary signature is 2^16 entries and perfectly buildable.
@inline _operand_datums(::Type{F}) where {F<:Binary} = _opdat(decodepolicy(F), F)
@inline _opdat(::TableDecode, ::Type{F}) where {F<:Binary} = _decode_table(F)
@inline _opdat(::ComputeDecode, ::Type{F}) where {F<:Binary} =
    [decode(_rawvalue(F, CodeType(F)(c))) for c in 0:(1 << Int(BitwidthOf(F))) - 1]

# ---- parallel builds ---------------------------------------------------------
# A build is embarrassingly parallel: every entry is one independent trip
# through `_scalar_code`, written to a disjoint index of a preallocated
# `Memory`. Sound for stated reasons, not "threads are usually fine":
#   1. only pure ρ is ever tabulated (_check_tabulable throws first), so an
#      entry is a pure function of its operand code points;
#   2. the scalar path reaches MPFR through the FUNCTION forms of
#      setprecision/setrounding exclusively, which on Julia ≥ 1.12 are
#      ScopedValue-backed and hence task-local — this is why Project.toml
#      floors at 1.12 as a correctness bound;
#   3. builds already run outside the cache lock (the double-checked pattern),
#      so parallelizing needs no lock changes.

"""Minimum entry count before a table build parallelizes. Its own threshold
rather than `THREAD_MIN_ELEMS`: a table entry costs a full scalar-engine trip
including any MPFR escalation, while an array element costs a decode plus one
operation — different costs, different numbers."""
const TABLE_BUILD_MIN_ENTRIES = Ref(1 << 12)
"""Master switch for parallel table builds."""
const THREADED_TABLE_BUILDS = Ref(true)

@inline _should_thread_build(n::Int) =
    THREADED_TABLE_BUILDS[] && Threads.nthreads() > 1 && n >= TABLE_BUILD_MIN_ENTRIES[]

# ---- the function barrier ----------------------------------------------------
# `_build_*` receives `op` as a runtime Symbol, so `Val(op)` inside it is a
# value of unknown type: every `_scalar_code(V, …)` there would be a DYNAMIC
# DISPATCH, once per entry. Passing `Val(op)` as an ARGUMENT makes `op` a type
# parameter of the callee and the whole scalar path specializes — measured in
# SmallFloats at 13× serial (13.4 ms → 1.0 ms on a 65,536-entry Multiply
# table), independent of threading.

@inline function _fill_unary!(tbl, ::Val{op}, ::Type{fr}, ::Type{f1}, ρ::Projection,
                              n::Int, threaded::Bool) where {op,fr<:Binary,f1<:Binary}
    U1 = CodeType(f1)
    V = Val(op)
    if threaded
        Threads.@threads for c in 0:n - 1
            @inbounds tbl[c + 1] = _scalar_code(V, fr, ρ, decode(_rawvalue(f1, U1(c))))
        end
    else
        @inbounds for c in 0:n - 1
            tbl[c + 1] = _scalar_code(V, fr, ρ, decode(_rawvalue(f1, U1(c))))
        end
    end
    tbl
end

# partitioned over the OUTER code loop rather than the flat index: each task
# decodes its own `x1` once and writes a contiguous 2^K2-entry span — the
# cache-friendly shape and the one whose disjointness is obvious by inspection
@inline function _fill_binary!(tbl, ::Val{op}, ::Type{fr}, ::Type{f1}, ::Type{f2},
                               ρ::Projection, threaded::Bool) where {op,fr<:Binary,f1<:Binary,f2<:Binary}
    K1, K2 = Int(BitwidthOf(f1)), Int(BitwidthOf(f2))
    U1 = CodeType(f1)
    V = Val(op)
    X2 = _operand_datums(f2)                 # shared, read-only
    if threaded
        Threads.@threads for c1 in 0:(1 << K1) - 1
            x1 = decode(_rawvalue(f1, U1(c1)))
            base = c1 << K2
            @inbounds for c2 in 0:(1 << K2) - 1
                tbl[base + c2 + 1] = _scalar_code(V, fr, ρ, x1, X2[c2 + 1])
            end
        end
    else
        @inbounds for c1 in 0:(1 << K1) - 1
            x1 = decode(_rawvalue(f1, U1(c1)))
            base = c1 << K2
            for c2 in 0:(1 << K2) - 1
                tbl[base + c2 + 1] = _scalar_code(V, fr, ρ, x1, X2[c2 + 1])
            end
        end
    end
    tbl
end

@inline function _fill_ternary!(tbl, ::Val{op}, ::Type{fr}, ::Type{f1}, ::Type{f2},
                                ::Type{f3}, ρ::Projection, threaded::Bool) where
        {op,fr<:Binary,f1<:Binary,f2<:Binary,f3<:Binary}
    K2, K3 = Int(BitwidthOf(f2)), Int(BitwidthOf(f3))
    K1 = Int(BitwidthOf(f1))
    U1 = CodeType(f1)
    V = Val(op)
    X2, X3 = _operand_datums(f2), _operand_datums(f3)
    if threaded
        Threads.@threads for c1 in 0:(1 << K1) - 1
            x1 = decode(_rawvalue(f1, U1(c1)))
            for c2 in 0:(1 << K2) - 1
                x2 = @inbounds X2[c2 + 1]
                base = ((c1 << K2) | c2) << K3
                @inbounds for c3 in 0:(1 << K3) - 1
                    tbl[base + c3 + 1] = _scalar_code(V, fr, ρ, x1, x2, X3[c3 + 1])
                end
            end
        end
    else
        @inbounds for c1 in 0:(1 << K1) - 1
            x1 = decode(_rawvalue(f1, U1(c1)))
            for c2 in 0:(1 << K2) - 1
                x2 = X2[c2 + 1]
                base = ((c1 << K2) | c2) << K3
                for c3 in 0:(1 << K3) - 1
                    tbl[base + c3 + 1] = _scalar_code(V, fr, ρ, x1, x2, X3[c3 + 1])
                end
            end
        end
    end
    tbl
end

function _build_unary(op::Symbol, ::Type{fr}, ::Type{f1},
                      ρ::Projection) where {fr<:Binary,f1<:Binary}
    n = 1 << Int(BitwidthOf(f1))
    tbl = Memory{CodeType(fr)}(undef, n)
    _fill_unary!(tbl, Val(op), fr, f1, ρ, n, _should_thread_build(n))
end

function _build_binary(op::Symbol, ::Type{fr}, ::Type{f1}, ::Type{f2},
                       ρ::Projection) where {fr<:Binary,f1<:Binary,f2<:Binary}
    n = 1 << (Int(BitwidthOf(f1)) + Int(BitwidthOf(f2)))
    tbl = Memory{CodeType(fr)}(undef, n)
    _fill_binary!(tbl, Val(op), fr, f1, f2, ρ, _should_thread_build(n))
end

function _build_ternary(op::Symbol, ::Type{fr}, ::Type{f1}, ::Type{f2}, ::Type{f3},
                        ρ::Projection) where {fr<:Binary,f1<:Binary,f2<:Binary,f3<:Binary}
    n = 1 << (Int(BitwidthOf(f1)) + Int(BitwidthOf(f2)) + Int(BitwidthOf(f3)))
    tbl = Memory{CodeType(fr)}(undef, n)
    _fill_ternary!(tbl, Val(op), fr, f1, f2, f3, ρ, _should_thread_build(n))
end

# tables/build.jl
