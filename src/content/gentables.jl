# human-readable enumeration of a format's contents

"""
    codetable(F; by = :code)

Every `(code, value)` pair of format `F` (a `Binary`, or a datum type/alias),
as a vector of named tuples — ordered by code point, or by value
(`by = :value`, total order: NaN first).

# Examples

```jldoctest
julia> codetable(Binary(3, 1, UNSIGNED, FINITE))
8-element Vector{@NamedTuple{code::UInt8, value::Float64}}:
 (code = 0x00, value = 0.0)
 (code = 0x01, value = 0.125)
 (code = 0x02, value = 0.25)
 (code = 0x03, value = 0.5)
 (code = 0x04, value = 1.0)
 (code = 0x05, value = 2.0)
 (code = 0x06, value = 4.0)
 (code = 0x07, value = NaN)
```
"""
function codetable(::Type{F}; by::Symbol = :code) where {F<:Binary}
    by in (:code, :value) || throw(ArgumentError("by must be :code or :value, got :$by"))
    U = CodeType(F)
    xs = [rawvalue(F, U(c)) for c in 0:(1 << Int(BitwidthOf(F))) - 1]
    by === :value && sort!(xs; by = order_key)      # total order: NaN first
    [(code = codepoint(x), value = decode(x)) for x in xs]
end
codetable(::Type{BV}; kw...) where {BV<:BinaryValue} = codetable(BinaryFormatOf(BV); kw...)
codetable(F::Binary; kw...) = codetable(typeof(F); kw...)

"""
    printcodetable([io,] F; by = :code)

Print [`codetable`](@ref) one row per line: the code point in hex, then the
value.
"""
function printcodetable(io::IO, ::Type{F}; by::Symbol = :code) where {F<:Binary}
    pad = 2 * sizeof(CodeType(F))
    for r in codetable(F; by)
        println(io, "  0x", string(r.code; base = 16, pad), "  ", r.value)
    end
    nothing
end
printcodetable(::Type{F}; kw...) where {F<:Binary} = printcodetable(stdout, F; kw...)
printcodetable(io::IO, F::Binary; kw...) = printcodetable(io, typeof(F); kw...)
printcodetable(F::Binary; kw...) = printcodetable(stdout, typeof(F); kw...)
printcodetable(io::IO, ::Type{BV}; kw...) where {BV<:BinaryValue} =
    printcodetable(io, BinaryFormatOf(BV); kw...)
printcodetable(::Type{BV}; kw...) where {BV<:BinaryValue} =
    printcodetable(stdout, BinaryFormatOf(BV); kw...)
