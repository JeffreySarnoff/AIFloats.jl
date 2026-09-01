"""
    Binary{K,P,S,D}

A 3109 complete binary format specifier.

- K is BitwidthOf(format)
- P is PrecisionOf(format)
- S is SignednessOf(format)
- D is DomainOf(format)

The four parameters fully determine a format, so `Binary{K,P,S,D}` carries no fields.
`K` and `P` are `Int8`, `S` and `D` are `Bool`. Build one with [`Binary(K, P, S, D)`](@ref
Binary(::Integer, ::Integer, ::AIFloats.ΣBool, ::AIFloats.ΔBool)) rather than writing the
parameters out, so that they are canonicalized and validated.

A format has NO supertype, and in particular is not an `AbstractFloat`: it
describes a value set rather than belonging to one. Its datums are
[`BinaryValue`](@ref), and those are the `AbstractFloat`s. The distinction is
not cosmetic — while `Binary` was an `AbstractFloat`, Base's fallbacks applied
to format instances and `isnan` of a *format* returned `false` instead of
failing. `test-binary-format.jl` pins this.

See also [`BitwidthOf`](@ref), [`PrecisionOf`](@ref), [`SignednessOf`](@ref),
[`DomainOf`](@ref).
"""
struct Binary{K,P,S,D} end

# The one normalization seam for public methods that accept either canonical
# format types or their zero-field instances. Type-based methods remain the hot
# implementation; instance methods are one-hop adapters into them.
const BinarySpecifier = Union{Type{<:Binary},Binary}
@inline _formattype(::Type{F}) where {F<:Binary} = F
@inline _formattype(f::Binary) = typeof(f)

"""
    Binary(K, P, S, D)

Construct the binary format specifier with bitwidth `K`, precision `P`, signedness `S`, and
domain `D`.

- `K`, `P` are `Integer`s **of the same type**; they are narrowed to `Int8`
- `S` is [`SIGNED`](@ref) or [`UNSIGNED`](@ref), or the equivalent `Bool`
- `D` is [`EXTENDED`](@ref) or [`FINITE`](@ref), or the equivalent `Bool`

This returns the parameterized **type**, not an instance. Append `()` when you need a value.
Invalid combinations throw an `ArgumentError` — see [`validformat`](@ref) for the rules.

The type is the canonical spelling: it is what [`BinaryValue`](@ref) takes as its first
parameter. An instance is accepted everywhere a format is, and every accessor and
constructor answers identically for both — see `docs/structuralplan.md` §9.2a for why that
surface must stay total, and for the rule any new instance-form method has to follow.

# Examples

```jldoctest
julia> B = Binary(8, 4, SIGNED, FINITE)
Binary{8, 4, ±, ⏥}

julia> B isa Type
true

julia> B()
Binary{8, 4, ±, ⏥}

julia> Binary(8, 4, true, false) === B
true
```
"""
function Binary(K::I, P::I, S::ΣBool, D::ΔBool) where {I<:Integer}
    fields = resolve_fields(K, P, S, D)
    Binary{fields...}
end

"""
    CodeType(K)
    CodeType(format)

The unsigned integer type that holds one code point of a `K`-bit format.

`UInt8` for `K <= 8`, `UInt16` above. Accepts a bitwidth, a [`Binary`](@ref) type, or a
`Binary` instance.

# Examples

```jldoctest
julia> CodeType(8), CodeType(9)
(UInt8, UInt16)

julia> CodeType(Binary(16, 10, SIGNED, EXTENDED))
UInt16
```
"""
function CodeType(K::Integer)
    KMIN <= K <= KMAX || throw(ArgumentError("bitwidth K must be in $(Int(KMIN)):$(Int(KMAX)), got $K"))
    K <= 8 ? UInt8 : UInt16
end
CodeType(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = CodeType(K)
CodeType(B::Binary) = CodeType(typeof(B))

"""
    ValueType(K)
    ValueType(format)

A Julia float type wide enough to hold every value of a `K`-bit format exactly.

`Float32` for `K <= 8`, `Float64` for `K <= 10`, `Float128` above. Accepts a bitwidth, a
[`Binary`](@ref) type, or a `Binary` instance.

# Examples

```jldoctest
julia> ValueType(8), ValueType(10), ValueType(16)
(Float32, Float64, Quadmath.Float128)

julia> ValueType(Binary(8, 4, SIGNED, FINITE))
Float32
```
"""
function ValueType(K::Integer)
    KMIN <= K <= KMAX || throw(ArgumentError("bitwidth K must be in $(Int(KMIN)):$(Int(KMAX)), got $K"))
    K <= 8 ? Float32 : K <= 10 ? Float64 : Float128
end
ValueType(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = ValueType(K)
ValueType(B::Binary) = ValueType(typeof(B))

"""
    resolve_fields(K, P, S, D)

provide internal canonical forms for the field values

Returns the 4-tuple `(Int8(K), Int8(P), Bool(S), Bool(D))` that becomes the parameters of
[`Binary`](@ref), throwing an `ArgumentError` if the combination is invalid. This is how the
singleton spellings ([`SIGNED`](@ref), [`FINITE`](@ref)) and the raw `Bool`s collapse onto one
representation.

Not exported; call it as `AIFloats.resolve_fields`.

```jldoctest
julia> AIFloats.resolve_fields(16, 10, SIGNED, FINITE)
(16, 10, true, false)

julia> AIFloats.resolve_fields(16, 10, true, false)
(16, 10, true, false)
```
"""
function resolve_fields(K::I, P::I, S::ΣBool, D::ΔBool) where {I<:Integer}
    # Validate in the caller's integer domain. Narrowing first turned an
    # ordinary invalid format such as K=128 into an unrelated InexactError.
    validformat(K, P, S, D)
    bitwidth = Int8(K)
    bitprecision = Int8(P)
    signedness = convert(Bool, S)
    domain = convert(Bool, D)
    (bitwidth, bitprecision, signedness, domain)
end

"""
    is_unsigned(x)

Whether `x` describes an unsigned format — one that represents magnitudes only.

`x` may be a [`Binary`](@ref) type or instance, a [`Signedness`](@ref) singleton, or a `Bool`.
Opposite of [`is_signed`](@ref).

# Examples

```jldoctest
julia> is_unsigned(Binary(8, 4, UNSIGNED, FINITE))
true

julia> is_unsigned(SIGNED)
false
```
"""
is_unsigned(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = S === false

"""
    is_signed(x)

Whether `x` describes a signed format — one in which negative values are representable.

`x` may be a [`Binary`](@ref) type or instance, a [`Signedness`](@ref) singleton, or a `Bool`.
Opposite of [`is_unsigned`](@ref).

# Examples

```jldoctest
julia> is_signed(Binary(8, 4, SIGNED, FINITE))
true

julia> is_signed(Binary(8, 4, UNSIGNED, FINITE)())
false
```
"""
is_signed(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = S === true

is_unsigned(b::Binary{K,P,S,D}) where {K,P,S,D} = S === false
is_signed(b::Binary{K,P,S,D}) where {K,P,S,D} = S === true

"""
    is_finite(x)

Whether `x` describes a finite format — reals and NaN, but no infinities.

`x` may be a [`Binary`](@ref) type or instance, a [`Domain`](@ref) singleton, or a `Bool`.
Opposite of [`is_extended`](@ref).

This asks about a *format*, not about a number, so it is unrelated to `Base.isfinite`.

# Examples

```jldoctest
julia> is_finite(Binary(8, 4, SIGNED, FINITE))
true

julia> is_finite(EXTENDED)
false
```
"""
is_finite(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = D === false

"""
    is_extended(x)

Whether `x` describes an extended format — one that includes the infinities.

`x` may be a [`Binary`](@ref) type or instance, a [`Domain`](@ref) singleton, or a `Bool`.
Opposite of [`is_finite`](@ref).

"Extended" means the value domain is extended with ±Inf. It says nothing about bitwidth or
about how many exponent bits the format has.

# Examples

```jldoctest
julia> is_extended(Binary(8, 4, SIGNED, EXTENDED))
true

julia> is_extended(FINITE)
false
```
"""
is_extended(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = D === true

is_finite(b::Binary{K,P,S,D}) where {K,P,S,D} = D === false
is_extended(b::Binary{K,P,S,D}) where {K,P,S,D} = D === true

"""
    validformat(K, P, S, D)
    validformat(format)

Return `nothing` if the format is representable, otherwise throw an `ArgumentError`.

A format is valid when

- `K > 2` — at least three bits
- `K <= 16` — the largest code point must fit a `UInt16`
- `P > 0` — at least one significand bit
- `P <= K - S` — after the sign bit, if any, at least one bit is left for the exponent

Not exported; call it as `AIFloats.validformat`.

# Examples

```jldoctest
julia> AIFloats.validformat(8, 7, SIGNED, FINITE)   # 1 sign, 7 significand, 1 exponent

julia> AIFloats.validformat(8, 8, UNSIGNED, FINITE) # no sign bit, so P may reach K

julia> AIFloats.validformat(8, 8, SIGNED, FINITE)   # no bit left for the exponent
ERROR: ArgumentError: Invalid format: K=8, P=8, S=SIGNED, D=FINITE
[...]
```
"""
validformat(K::I, P::I, S::Union{Signedness,Bool}, D::Union{Domain,Bool}) where {I<:Integer} =
     ((KMIN <= K <= KMAX) && (P > 0) && (P <= K - convert(Bool, S)) && (S isa Signedness || S isa Bool) && (D isa Domain || D isa Bool)) ? nothing : throw(ArgumentError("Invalid format: K=$K, P=$P, S=$S, D=$D"))

validformat(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = validformat(K, P, S, D)
validformat(b::Binary{K,P,S,D}) where {K,P,S,D} = validformat(K, P, S, D)  

# format-level accessors
"""
    BitwidthOf(format)

The total number of bits in the format, `K`.

# Examples

```jldoctest
julia> BitwidthOf(Binary(8, 4, SIGNED, FINITE))
8
```
"""
BitwidthOf(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = K

"""
    PrecisionOf(format)

The number of significand bits, `P`, **counting the implicit leading bit**.

The bits actually stored are [`TrailingSignificantBitsOf`](@ref) = `P - 1`; the rest of the
format, `K - P - is_signed(format)`, is exponent.

# Examples

```jldoctest
julia> PrecisionOf(Binary(8, 4, SIGNED, FINITE))
4
```
"""
PrecisionOf(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = P

"""
    SignednessOf(format)

The signedness parameter `S`, as a `Bool`: `true` for signed, `false` for unsigned.

For a predicate that also accepts singletons, use [`is_signed`](@ref) / [`is_unsigned`](@ref).

# Examples

```jldoctest
julia> SignednessOf(Binary(8, 4, SIGNED, FINITE))
true
```
"""
SignednessOf(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = S

"""
    DomainOf(format)

The domain parameter `D`, as a `Bool`: `true` for extended, `false` for finite.

For a predicate that also accepts singletons, use [`is_extended`](@ref) / [`is_finite`](@ref).

# Examples

```jldoctest
julia> DomainOf(Binary(8, 4, SIGNED, EXTENDED))
true
```
"""
DomainOf(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = D

BitwidthOf(::Binary{K,P,S,D}) where {K,P,S,D} = K
PrecisionOf(::Binary{K,P,S,D}) where {K,P,S,D} = P
SignednessOf(::Binary{K,P,S,D}) where {K,P,S,D} = S
DomainOf(::Binary{K,P,S,D}) where {K,P,S,D} = D

"""
    TrailingSignificantBitsOf(format)

The number of significand bits actually stored, `P - 1`.

[`PrecisionOf`](@ref) counts the implicit leading bit; this does not.

# Examples

```jldoctest
julia> TrailingSignificantBitsOf(Binary(8, 4, SIGNED, FINITE))
3
```
"""
TrailingSignificantBitsOf(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = P - one(IntParam)
TrailingSignificantBitsOf(b::Binary) = TrailingSignificantBitsOf(typeof(b))

# `Binary` itself, a partial form such as `Binary{8,4}`, and the `Binary{K,P,S,D}` Julia
# builds to print a method signature all carry TypeVars where values belong. So the
# parameters are read off the type at runtime rather than bound as static parameters, and a
# TypeVar prints as its own name.
fieldsof(T::Type{<:Binary}) = Base.unwrap_unionall(T).parameters

signstr(S, signed, unsigned) = S isa Bool ? (S ? signed : unsigned) : string(S)
domainstr(D, extended, finite) = D isa Bool ? (D ? extended : finite) : string(D)

# the spelled-out form: Binary{8, 4, SIGNED, FINITE}
function Base.string(T::Type{<:Binary})
    K, P, S, D = fieldsof(T)
    string("Binary{", K, ", ", P, ", ",
           signstr(S, "SIGNED", "UNSIGNED"), ", ",
           domainstr(D, "EXTENDED", "FINITE"), "}")
end

Base.string(x::Binary) = string(typeof(x))

# the glyphic form: Binary{8, 4, ±, ⏥}
function Base.String(T::Type{<:Binary})
    K, P, S, D = fieldsof(T)
    string("Binary{", K, ", ", P, ", ",
           signstr(S, "±", "+"), ", ",
           domainstr(D, "∞", "⏥"), "}")
end

Base.String(x::Binary) = String(typeof(x))

Base.show(io::IO, ::MIME"text/plain", T::Type{<:Binary}) = print(io, String(T))
Base.show(io::IO, T::Type{<:Binary}) = print(io, string(T))

Base.show(io::IO, ::MIME"text/plain", b::Binary) = print(io, String(b))
Base.show(io::IO, b::Binary) = print(io, string(b))
