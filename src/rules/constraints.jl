# the format grid: names for every K ≤ 16 format
#
# Validity itself lives in validformat (types/binaryformats.jl) — one
# validator, one place. This file WALKS the grid validformat implies and gives
# each cell its P3109 name.
#
# The name is spelled in exactly one place: binary⟨K⟩p⟨P⟩⟨u|s⟩⟨f|e⟩. All 504
# aliases are DEFINED (each names the concrete datum type, so it serves as an
# array element type and a constructor); only the 120 at K ≤ 8 are EXPORTED —
# exporting more later is non-breaking, un-exporting is not. The rest are
# reachable qualified (AIFloats.binary16p6se) or via `using AIFloats.Formats`.

_formatname(K::Integer, P::Integer, S::Bool, D::Bool) =
    Symbol("binary", Int(K), "p", Int(P), S ? "s" : "u", D ? "e" : "f")

"""
    formatname(F)

The P3109 name of a format (or of its datum type / a datum), as a `Symbol`:
`binary⟨K⟩p⟨P⟩⟨u|s⟩⟨f|e⟩`.

# Examples

```jldoctest
julia> formatname(Binary(8, 4, SIGNED, EXTENDED))
:binary8p4se
```
"""
formatname(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = _formatname(K, P, S, D)
formatname(b::Binary) = formatname(typeof(b))
formatname(::Type{BV}) where {BV<:BinaryValue} = formatname(BinaryFormatOf(BV))
formatname(x::BinaryValue) = formatname(BinaryFormatOf(x))

# the registry of named formats: Symbol → datum type
const _NAMED = Dict{Symbol, DataType}()

for K in Int(KMIN):Int(KMAX), P in 1:K, S in (true, false), E in (true, false)
    S && P >= K && continue
    name = _formatname(K, P, S, E)
    F = Binary(K, P, S, E)                     # canonical Int8-parameter type
    BV = BinaryValue(F)
    @eval const $name = $BV
    _NAMED[name] = BV
end

"""
    Formats

Opt-in namespace re-exporting **all 504** format aliases. `using AIFloats`
exports the 120 names at `K <= 8`; `using AIFloats.Formats` adds the rest.
Every alias is defined in `AIFloats` either way (`AIFloats.binary16p6se`).
"""
module Formats
import ..AIFloats
for n in sort!(collect(keys(AIFloats._NAMED)))
    @eval using ..AIFloats: $n
    @eval export $n
end
end # module Formats