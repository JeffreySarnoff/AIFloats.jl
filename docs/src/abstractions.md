# Abstractions

----

```mermaid
graph TD
    A[AbstracFloatML] 
    A--> S[AbsSignedFloatML]
    A--> U[AbsUnsignedFloatML]
    S--> SF[AbsSFiniteFloatML]
    S--> SE[AbsSExtendedFloatML]
    U--> UF[AbsUFiniteFloatML]
    U--> UE[AbsUExtendedFloatML]
```

----

```mermaid
graph LR
    A[AbstractFloatML] 
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
abstract type AbstractFloatML{Bits, Precision} <: AbstractFloat end
#                        B is Bits, P is Precision == SigBits
bitsize(::Type{<:AbstractFloatML{B,P}}) where {B,P} = B
sigbits(::Type{<:AbstractFloatML{B,P}}) where {B,P} = P
# the fractional bits (or trailing significand bits) are explicitly stored
fracbits(::Type{<:AbstractFloatML{B,P}}) where {B,P} = P - 1

signbits(T::Type{<:AbstractFloatML{Bits,Precision}}) where {Bits,Precision} =
     0 + is_signed(T)

expbits(T::Type{<:AbstractFloatML{Bits,Precision}}) where {Bits,Precision} =
   Bits - Precision + is_unsigned(T)

nValues(T::Type{<:AbstractFloatML}) = 2^nBits(T)
nNumericValues(T::Type{<:AbstractFloatML}) = nValues(T) - 1 # remove NaN
nFiniteValues(T::Type{<:AbstractFloatML}) = nNumericValues(T) - nInfs(T) # remove Infs

nInfs(T::Type{<:AbstractFloatML}) = is_extended(T) * (is_signed(T) + is_extended(T))
```
and then
```
for F in (:bitsize, :sigbits, :fracbits, :expbits, :signbits,
          :nValues, :nNumericValues, :nFiniteValues, :nInfs)
    @eval $(F)(x::AbstractFloatML) = $(F)(typeof(x))
end
```

====

In essence, this code provides a framework for creating custom floating-point numeric types in Julia by defining essential properties and methods that describe their bit structure. It allows the user to query information about bits, significance, and the count of representable values including handling special cases like NaN and infinity. This abstraction enables more straightforward implementation and manipulation of different floating-point representations in a systematic way.
