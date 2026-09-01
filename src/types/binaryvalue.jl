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
`2^K`); every other `Real` means a **value**, and goes through the projection
engine under a [`Projection`](@ref) — the session default unless a `projection`
keyword says otherwise.

The format may be given as a type or as an instance, and either may be spelled
as a parameter or passed as an argument. All four spellings agree.

# Examples

```jldoctest
julia> F = Binary(8, 4, SIGNED, EXTENDED)
Binary{8, 4, ±, ∞}

julia> x = BinaryValue(F, 0x45)          # an Unsigned is a CODE POINT
1.625

julia> codepoint(x), decode(x)
(0x45, 1.625)

julia> BinaryValue(F, 1.625) === x       # any other Real is a VALUE
true

julia> BinaryValue{F}(1.625) === x       # the parameter spelling
true

julia> BinaryValue(F(), 0x45) === x      # a format instance also works
true

julia> BinaryValue(F, 1.7)               # a value off the lattice is projected
1.75

julia> BinaryValue(F, 1.7; projection = RTZ_SN)
1.625
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

    # improveapi3.md §4.2.5: the internal fast path. Precondition: the code is
    # already canonical for F (high bits zero). No range check.
    #
    # The plan spells the contract `code::CodeType(F)`, which Julia cannot
    # express -- a signature is evaluated at definition time, where F is still
    # a TypeVar. It is enforced by CONVERSION instead: `new` converts into the
    # field type, so a value that does not fit raises InexactError. That is
    # strictly better than `rawvalue`'s `%`, which truncates silently, and it
    # checks the representation invariant rather than merely the storage width.
    # Never exported, never `public`. `rawvalue` is its lenient predecessor and
    # is deleted once every internal caller has moved (Phase 1c.6).
    global @inline _rawvalue(::Type{F}, code::Unsigned) where {F<:Binary} =
        new{F, CodeType(F)}(code)
end

# normalize the one-parameter spellings to the full type
BinaryValue{F}(code::Unsigned) where {F<:Binary} = BinaryValue{F, CodeType(F)}(code)
BinaryValue(::Type{F}) where {F<:Binary} = BinaryValue{F, CodeType(F)}
BinaryValue(::Type{F}, code::Unsigned) where {F<:Binary} = BinaryValue{F, CodeType(F)}(code)

# ---- accepting a format INSTANCE ---------------------------------------------
# A format is canonically a TYPE here — `Binary(K,P,S,D)` returns one, and it has
# to, because it is `BinaryValue{F,U}`'s first parameter. Instances are still
# constructible (`Binary(5,3,SIGNED,FINITE)()`) and every format accessor
# already accepts one, so these two were the last hole in that surface. A hole
# is worse than either extreme: it is what invites the fix below to be written
# wrongly.
#
# THE RULE, and the reason these are one-liners: an instance-form method must
# change its argument's KIND, never merely its value. `typeof` does that, so the
# forwarded call provably lands on the `::Type{F}` method above and cannot
# re-enter this one. Delegating through anything that hands back a `Binary`
# value instead — including an identity-like helper — is an infinite recursion
# that Julia cannot warn about, because the signature legitimately matches
# itself. It is a StackOverflowError, not an ambiguity.
BinaryValue(fmt::Binary) = BinaryValue(typeof(fmt))
BinaryValue(fmt::Binary, code::Unsigned) = BinaryValue(typeof(fmt), code)

"""
    fromcode(F, code) -> BinaryValue
    fromcode(T, code) -> BinaryValue

The datum of format `F` (or datum type `T`) whose code point is `code`,
checked.

This is the ONLY public way to say "the datum at this code point". Ordinary
construction means a numeric VALUE: `F(3)` is the number three projected into
`F`, while `fromcode(F, 3)` is the datum stored as code point three. Keeping
those apart in the spelling is the point — they used to be told apart by the
argument's type, which made `T(codepoint(y))` a silent reinterpretation.

`code` may be any `Integer`, of any width, independent of `CodeType(F)`: the
range is checked first and narrowed only after, so `fromcode(F, UInt16(3))` is
safe for an eight-bit format rather than silently truncating. Negative values
and values above `codemask(F)` throw `ArgumentError`.

The guaranteed round trip is `fromcode(typeof(x), codepoint(x)) === x`.

# Examples

```jldoctest
julia> F = Binary(8, 4, SIGNED, EXTENDED);

julia> x = fromcode(F, 0x45)
1.625

julia> codepoint(x)
0x45

julia> fromcode(typeof(x), codepoint(x)) === x
true

julia> fromcode(F, 3) === fromcode(BinaryValue(F), UInt16(3))
true
```
"""
function fromcode(::Type{F}, code::Integer) where {F<:Binary}
    (code >= 0) & (code <= codemask(F)) ||
        throw(ArgumentError("code point $code is outside 0:$(codemask(F)) for " *
                            "$(string(F)); for the numeric VALUE $code write " *
                            "$(formatname(F))($code)"))
    _rawvalue(F, CodeType(F)(code))          # narrowed only after the check
end
fromcode(::Type{BV}, code::Integer) where {BV<:BinaryValue} =
    fromcode(BinaryFormatOf(BV), code)

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
# A format normalizes to itself, so internal code has ONE total query for "what
# format is this?" whatever it is handed (improveapi.md §4.3.3). Without it,
# every such call site needs a branch, and the branch is what eventually gets
# written wrongly. Placed AFTER the documented method on purpose: a docstring
# attaches to the next method defined, so leading with these would silently
# retarget it and the `@ref` in docs/src/50-status.md would stop resolving.
BinaryFormatOf(::Type{F}) where {F<:Binary} = F
BinaryFormatOf(f::Binary) = typeof(f)
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
