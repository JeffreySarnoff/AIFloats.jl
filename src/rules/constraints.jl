# the format grid: names for every K ≤ 16 format
#
# Validity itself lives in validformat (types/binaryformats.jl) — one
# validator, one place. This file WALKS the grid validformat implies and gives
# each cell its P3109 name.
#
# The name is spelled in exactly one place: Binary⟨K⟩p⟨P⟩⟨u|s⟩⟨f|e⟩. All 504
# aliases are DEFINED; only the 120 at K ≤ 8 are EXPORTED — exporting more later
# is non-breaking, un-exporting is not. The rest are reachable qualified
# (AIFloats.Binary16p6se) or via `using AIFloats.Formats`.
#
# Each alias names the FORMAT type, not the datum type (improveapi.md §4.1.2).
# The two readings cannot coexist: `Binary(K,P,S,D)` already returns a format, so
# letting the standard names return datum types would give "format" two meanings
# in one vocabulary. The convenient constructor role survives — `Binary8p4se(x)`
# still builds a datum, because `(::Type{F})(x::Real)` does — but an ARRAY
# ELEMENT TYPE must now be written `BinaryValue(Binary8p4se)`.

_formatname(K::Integer, P::Integer, S::Bool, D::Bool) =
    Symbol("Binary", Int(K), "p", Int(P), S ? "s" : "u", D ? "e" : "f")

"""
    formatname(F)

The P3109 name of a format (or of its datum type / a datum), as a `Symbol`:
`Binary⟨K⟩p⟨P⟩⟨u|s⟩⟨f|e⟩`.

# Examples

```jldoctest
julia> formatname(Binary(8, 4, SIGNED, EXTENDED))
:Binary8p4se
```
"""
formatname(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = _formatname(K, P, S, D)
formatname(::Type{BV}) where {BV<:BinaryValue} = formatname(BinaryFormatOf(BV))
formatname(x::BinaryValue) = formatname(BinaryFormatOf(x))

# the registry of named formats: Symbol → format type
const _NAMED = Dict{Symbol, DataType}()

for K in Int(KMIN):Int(KMAX), P in 1:K, S in (true, false), E in (true, false)
    S && P >= K && continue
    name = _formatname(K, P, S, E)
    F = Binary(K, P, S, E)                     # canonical Int8-parameter type
    @eval const $name = $F
    _NAMED[name] = F
end

"""
    Formats

Opt-in namespace re-exporting **all 504** format aliases. `using AIFloats`
exports the 120 names at `K <= 8`; `using AIFloats.Formats` adds the rest.
Every alias is defined in `AIFloats` either way (`AIFloats.Binary16p6se`).
"""
module Formats
import ..AIFloats
for n in sort!(collect(keys(AIFloats._NAMED)))
    @eval using ..AIFloats: $n
    @eval export $n
end
end # module Formats
