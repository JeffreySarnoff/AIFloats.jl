# the datum type: a member of a format's value set
#
# AIFloats separates the format (Binary{K,P,S,D}, a type-level token) from the
# datum. BinaryValue completes that separation: the format is a Binary, a member
# of its value set is a BinaryValue.

"""
    BinaryValue{F,U}

A datum of format `F` — one member of `F`'s value set, stored as its code point.

- `F` is the [`Binary`](@ref) format
- `U` is `CodeType(F)` — `UInt8` for `K <= 8`, `UInt16` above

The representation invariant: the code point occupies the low `K` bits of the
storage unit and the high bits are zero. Constructors enforce it.

An `Unsigned` constructor argument means **code point** (range-checked against
`2^K`); construction *from a value* goes through the projection engine and
arrives with `Convert` (plan Phase 3).

```julia
BinaryValue{F}(0x45)      # code point 0x45 of format F
codepoint(x)              # the code point back
decode(x)                 # the value the datum denotes
```
"""
struct BinaryValue{F<:Binary, U<:Unsigned} <: AbstractFloat
    code::U
    # the one checked gateway; rawvalue (below) is the unchecked kernel route
    function BinaryValue{F,U}(code::Unsigned) where {F<:Binary, U<:Unsigned}
        U === CodeType(F) ||
            throw(ArgumentError("BinaryValue storage unit must be $(CodeType(F)) for $(string(F)), got $U"))
        (code <= codemask(F)) ||
            throw(ArgumentError("code point $code exceeds $(2^Int(BitwidthOf(F)) - 1) for $(string(F))"))
        new{F,U}(code % U)
    end

    # unchecked construction — kernel-internal. Assumes the representation
    # invariant (high bits zero); every checked path goes through the
    # constructor above. Defined inside the struct so it is the only door
    # around the checks.
    global @inline rawvalue(::Type{F}, code::Unsigned) where {F<:Binary} =
        new{F, CodeType(F)}(code % CodeType(F))
end

# normalize the one-parameter spellings to the full type
BinaryValue{F}(code::Unsigned) where {F<:Binary} = BinaryValue{F, CodeType(F)}(code)
BinaryValue(::Type{F}) where {F<:Binary} = BinaryValue{F, CodeType(F)}
BinaryValue(::Type{F}, code::Unsigned) where {F<:Binary} = BinaryValue{F, CodeType(F)}(code)

"""
    codepoint(x::BinaryValue)

The datum's code point, as the format's storage unit (`CodeType`).

Extends `Base.codepoint` (which Base defines for `Char`).

# Examples

```jldoctest
julia> codepoint(BinaryValue(Binary(8, 4, SIGNED, FINITE), 0x45))
0x45
```
"""
Base.codepoint(x::BinaryValue) = x.code

# format recovery and trait forwarding: every format trait answers on the datum
# type and the datum, so user code never needs to reach for F explicitly
"""
    BinaryFormatOf(x)

The [`Binary`](@ref) format of a `BinaryValue` datum or datum type.

# Examples

```jldoctest
julia> BinaryFormatOf(BinaryValue(Binary(8, 4, SIGNED, FINITE), 0x00))
Binary{8, 4, ±, ⏥}
```
"""
BinaryFormatOf(::Type{BinaryValue{F,U}}) where {F,U} = F
BinaryFormatOf(::Type{BinaryValue{F}}) where {F} = F
BinaryFormatOf(x::BinaryValue) = BinaryFormatOf(typeof(x))
# the bottom type satisfies `<: BinaryValue` and has no format; a stated
# refusal keeps the trait-forwarding methods below total under analysis
BinaryFormatOf(::Type{Union{}}) = throw(ArgumentError("Union{} has no Binary format"))

for t in (:BitwidthOf, :PrecisionOf, :SignednessOf, :DomainOf,
          :ExponentBiasOf, :ExponentBitwidthOf, :TrailingSignificantBitsOf,
          :CodeType, :ValueType, :codemask, :signmask, :orderkeytype,
          :is_signed, :is_unsigned, :is_finite, :is_extended,
          :rung, :datumcarrier, :promotecarrier)
    @eval $t(::Type{BV}) where {BV<:BinaryValue} = $t(BinaryFormatOf(BV))
    @eval $t(x::BinaryValue) = $t(BinaryFormatOf(x))
end