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
storage unit and the high bits are zero. Every construction path enforces it.

**Construction has one semantic axis.** Every constructor argument is a
`Real` **value**, projected into `F` under a [`Projection`](@ref) — the session
default unless a `projection` keyword says otherwise. `Unsigned` is not special:
`BinaryValue(F, 0x03)` is the number three, exactly as `BinaryValue(F, 3.0)` is.

To name a **code point**, use [`fromcode`](@ref). It is a different question and
it gets a different spelling, because the two used to be told apart by the
argument's type — which silently made `T(codepoint(y))` a reinterpretation.

`BinaryValue(F)` is the datum TYPE of `F`; `F` itself is the format.

# Examples

```jldoctest
julia> F = Binary(8, 4, SIGNED, EXTENDED)
Binary{8, 4, ±, ∞}

julia> x = BinaryValue(F, 1.625)         # every Real argument is a VALUE
1.625

julia> BinaryValue{F}(1.625) === x       # the parameter spelling
true

julia> F(1.625) === x                    # calling the format is the short one
true

julia> fromcode(F, 0x45) === x           # and 0x45 is where that value lives
true

julia> BinaryValue(F, 0x45)              # but as a NUMBER, 0x45 is 69
64.0

julia> BinaryValue(F, 1.7)               # a value off the lattice is projected
1.75

julia> BinaryValue(F, 1.7; projection = RTZ_SN)
1.625
```
"""
# PHASE 1b DIAGNOSTIC -- TEMPORARY, NEVER TO BE THE COMMITTED INTERFACE.
#
# Deleting the code-point constructor outright would NOT give a MethodError:
# the value-taking `Real` constructor accepts the very same argument, so every
# missed `T(0x45)` would silently become the number 69. That is the plan's
# top-ranked risk (improveapi3.md §6 Phase 1b) and a loud diagnostic is the
# only way to expose the call sites a grep and the test inventory missed.
#
struct BinaryValue{F<:Binary, U<:Unsigned} <: AbstractFloat
    code::U

    # improveapi3.md §4.2.5: the ONE internal door. Precondition: the code is
    # already canonical for F (high bits zero). No range check.
    #
    # The plan spells the contract `code::CodeType(F)`, which Julia cannot
    # express -- a signature is evaluated at definition time, where F is still
    # a TypeVar. Enforced by CONVERSION instead: `new` converts into the field
    # type, so a value that does not fit raises InexactError. That checks the
    # representation invariant, not merely the storage width.
    #
    # There is deliberately no public `Unsigned` inner constructor. One would
    # out-specialize the `Real` value constructor in ops/scalar.jl, and
    # `BinaryValue{F,U}(0x03)` would silently mean code point three rather than
    # the number three. Code points are reached only through `fromcode`.
    global @inline _rawvalue(::Type{F}, code::Unsigned) where {F<:Binary} =
        new{F, CodeType(F)}(code)
end

"""
    BinaryValue(F) -> Type

The concrete `AbstractFloat` datum type of format `F`: `BinaryValue{F,CodeType(F)}`.

This is the spelling to use for an array element type or a type annotation. `F`
itself is the FORMAT — `x isa F` is false for every datum `x`, because a format
describes a value set rather than belonging to one. Calling a format,
`F(x)`, is a convenience that constructs a datum; it is not the ordinary Julia
relationship between a type and its instances, so the two spellings answer
different questions and both are needed.

# Examples

```jldoctest
julia> F = Binary(8, 4, SIGNED, FINITE);

julia> T = BinaryValue(F)
BinaryValue(Binary8p4sf)

julia> F(1.5) isa T
true

julia> F(1.5) isa F
false
```
"""
BinaryValue(::Type{F}) where {F<:Binary} = BinaryValue{F, CodeType(F)}

# improveapi3.md §4.1.3: the internal spelling of the same query. Public code
# writes `BinaryValue(F)`; kernels that need a concrete element type write this,
# so the intent reads as "the datum type of F" rather than as a constructor call.
@inline _datumtype(::Type{F}) where {F<:Binary} = BinaryValue{F, CodeType(F)}

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
julia> codepoint(fromcode(Binary(8, 4, SIGNED, FINITE), 0x45))
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
julia> BinaryFormatOf(fromcode(Binary(8, 4, SIGNED, FINITE), 0x00))
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
