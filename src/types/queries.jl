# the consolidated query surface (improveapi3.md §4.1, §6 Phase 4)
#
# Loaded LATE on purpose: it binds names defined across types/binaryvalue.jl,
# carriers/heads.jl and rules/constraints.jl, so it cannot live in
# types/traits.jl, which the format machinery needs before any of those exist.

# ---- Julia-style spellings of the P3109 queries -------------------------------
#
# improveapi3.md §4.1/§4.4: these are PERMANENT vocabulary bindings, not
# transitional adapters. Each is bound to the very same generic function object
# as its P3109 spelling — `const bitwidth = BitwidthOf` — rather than written as
# a forwarding method. That matters for three reasons: the two names can never
# drift apart in what they accept, a method added for one is a method for both,
# and there is provably zero run-time cost because there is no second call to
# elide. `formatof === BinaryFormatOf` answers `true`.
"""
    formatof(x)

Julia-style spelling of [`BinaryFormatOf`](@ref) — the same function.

`formatof(F) === F` for a format type, so internal code has one total
normalization query, whatever it is handed.

# Examples

```jldoctest
julia> formatof === BinaryFormatOf
true

julia> formatof(Binary8p4sf(1.5)) === Binary8p4sf
true

julia> formatof(Binary8p4sf) === Binary8p4sf
true
```
"""
const formatof = BinaryFormatOf

"""
    bitwidth(x)

Julia-style spelling of [`BitwidthOf`](@ref) — the same function.
"""
const bitwidth = BitwidthOf

"""
    signedness(x)

Julia-style spelling of [`SignednessOf`](@ref) — the same function.
"""
const signedness = SignednessOf

"""
    domain(x)

Julia-style spelling of [`DomainOf`](@ref) — the same function.
"""
const domain = DomainOf

"""
    codetype(x)

Julia-style spelling of [`CodeType`](@ref) — the same function.
"""
const codetype = CodeType

"""
    valuetype(x)

Julia-style spelling of [`ValueType`](@ref) — the same function.
"""
const valuetype = ValueType

# `:foldable` is a promise, and it is an honest one here: the body is pure,
# terminates, and every component of the result is interned or immortal — Ints,
# Bools, a Symbol, and types. Without it the call does not fold, because
# `formatname` builds its Symbol through a String and inference will not prove
# that consistent on its own; the tuple then costs ~900 bytes on every call
# instead of vanishing into a literal.
Base.@assume_effects :foldable @inline function _formatinfo(::Type{F}) where {F<:Binary}
    (name          = formatname(F),
     format        = F,
     datumtype     = BinaryValue{F, CodeType(F)},
     bitwidth      = Int(BitwidthOf(F)),
     precision     = Int(PrecisionOf(F)),
     signed        = is_signed(F),
     extended      = is_extended(F),
     exponentbias  = ExponentBiasOf(F),
     exponentbits  = ExponentBitwidthOf(F),
     trailingbits  = Int(TrailingSignificantBitsOf(F)),
     codetype      = CodeType(F),
     valuetype     = ValueType(F),
     datumcarrier  = datumcarrier(F),
     promotecarrier = promotecarrier(F))
end
# `Base.@assume_effects` on the worker used to sit between this docstring and
# the definition, so Documenter attached it to nothing (refinedocs2 P1-2). The
# effects annotation stays where it is load-bearing; the docstring now sits on
# `formatinfo`, the public name.
"""
    formatinfo(F) -> NamedTuple

Everything statically known about a format, in one stable named tuple.

Pure, type-stable, and constant-foldable for a concrete `F` — the whole result
folds to a literal, so this is a documentation and introspection convenience
that costs nothing when the format is known at compile time.

Accepts a format, a datum type, or a datum.

Deliberately excludes decoded extrema and any allocated table: those have
focused APIs ([`MaxFiniteOf`](@ref), [`MinPositiveOf`](@ref),
`AIFloats.table_stats`) and putting them here would make a cheap query
expensive.

# Examples

```jldoctest
julia> info = formatinfo(Binary8p4se);

julia> info.name, info.bitwidth, info.precision
(:Binary8p4se, 8, 4)

julia> info.signed, info.extended
(true, true)

julia> info.datumtype
BinaryValue(Binary8p4se)

julia> formatinfo(Binary8p4se(1.5)) === info
true
```
"""
@inline formatinfo(::Type{F}) where {F<:Binary} = _formatinfo(F)
@inline formatinfo(::Type{BV}) where {BV<:BinaryValue} = formatinfo(BinaryFormatOf(BV))
@inline formatinfo(x::BinaryValue) = formatinfo(BinaryFormatOf(x))
