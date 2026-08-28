function codetable(::Type{B}; by::Symbol = :code) where {B<:Binary}
    by in (:code, :value) || throw(ArgumentError("by must be :code or :value"))
    CT = CodeType(B)
    VT = ValueType(B)
    codes =  [CT(c) for c in (0:(1 << BitwidthOf(B)) - 1)]
    vals = [valueof(B, c) for c in codes]   # TODO: Binary has no code-point constructor yet
    if by === :value
        sp = sortperm(vals)
        # NaN is last, unlike total order
        vals  = vals[sp]
        codes = codes[sp]
    end 
    [(code = codepoint(v), value = decode(v)) for v in vals]   # TODO: no codepoint/decode in current API
end

function printcodetable(io::IO, ::Type{F}; by::Symbol = :code) where {F<:Binary}
    w = 2 * sizeof(codeunit_type(F))            # TODO: no codeunit_type in current API
    for r in codetable(F; by)
        println(io, "  0x", string(r.code; base = 16, pad = w), "  ", r.value)
    endc in 0:(1 << BitwidthOf(B)) - 1
end