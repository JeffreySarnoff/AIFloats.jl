# Abstractions

----

```mermaid
graph TD
    A[AbstractAIFloat]
    A--> S[AbstractSigned]
    A--> U[AbstractUnsigned]
    S--> SF[AbstractSignedFinite]
    S--> SE[AbstractSignedExtended]
    U--> UF[AbstractUnsignedFinite]
    U--> UE[AbstractUnsignedExtended]
```

----

```mermaid
graph LR
    A[AbstractAIFloat]
    A--> S[Signed]
    A--> U[Unsigned]
    S--> SF[Finite ⊕ NaN]
    S--> SE[Finite ⊕ Inf ⊕ NaN]
    U--> UF[Finite ⊕ NaN]
    U--> UE[Finite ⊕ Inf ⊕ NaN]
```

----

### Computing over these abstractions

Every predicate, count, and extremal value available in [Type Specifics] is defined over these abstract types. We do not require instantiations to know characterizations.  The way that we stage our abstract parameterizations allows the freedom to use declarations like this:

```julia
abstract type AbstractAIFloat{Bits, Precision} <: AbstractFloat end
#                        B is Bits, P is Precision == SigBits
bitsize(::Type{<:AbstractAIFloat{B,P}}) where {B,P} = B
sigbits(::Type{<:AbstractAIFloat{B,P}}) where {B,P} = P
# the fractional bits (or trailing significand bits) are explicitly stored
fracbits(::Type{<:AbstractAIFloat{B,P}}) where {B,P} = P - 1

signbits(T::Type{<:AbstractAIFloat{Bits,Precision}}) where {Bits,Precision} =
     0 + is_signed(T)

expbits(T::Type{<:AbstractAIFloat{Bits,Precision}}) where {Bits,Precision} =
   Bits - Precision + is_unsigned(T)

nvalues(T::Type{<:AbstractAIFloat}) = 2^nbits(T)
nNumericValues(T::Type{<:AbstractAIFloat}) = nvalues(T) - 1 # remove NaN
nFiniteValues(T::Type{<:AbstractAIFloat}) = nNumericValues(T) - nInfs(T) # remove Infs

nInfs(T::Type{<:AbstractAIFloat}) = is_extended(T) * (is_signed(T) + is_extended(T))
```
and then
```
for F in (:bitsize, :sigbits, :fracbits, :expbits, :signbits,
          :nvalues, :nNumericValues, :nFiniteValues, :nInfs)
    @eval $(F)(x::AbstractAIFloat) = $(F)(typeof(x))
end
```

====

In essence, this code provides a framework for creating custom floating-point numeric types in Julia by defining essential properties and methods that describe their bit structure. It allows the user to query information about bits, significance, and the count of representable values including handling special cases like NaN and infinity. This abstraction enables more straightforward implementation and manipulation of different floating-point representations in a systematic way.
