# Type Hierarchy

## Abstract Type Foundation

The AIFloats type system employs a three-parameter abstract hierarchy that captures both structural and semantic properties:

```julia
abstract type AbstractAIFloat{Bits, SigBits, IsSigned} <: AbstractFloat end
```

This parametric design enables compile-time specialization while maintaining runtime polymorphism across the format family.

### Primary Abstractions

```julia
abstract type AbstractSigned{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits, true} end
abstract type AbstractUnsigned{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits, false} end
```

The `IsSigned` parameter is embedded as a type-level boolean, eliminating runtime dispatch overhead for signedness-dependent operations.

### Domain-Specific Abstractions

The hierarchy further stratifies by representable value domains:

```julia
# Finite formats: Real numbers ∪ {NaN}
abstract type AkoSignedFinite{Bits, SigBits} <: AbstractSigned{Bits, SigBits} end
abstract type AkoUnsignedFinite{Bits, SigBits} <: AbstractUnsigned{Bits, SigBits} end

# Extended formats: Real numbers ∪ {±∞, NaN} or {+∞, NaN}
abstract type AkoSignedExtended{Bits, SigBits} <: AbstractSigned{Bits, SigBits} end
abstract type AkoUnsignedExtended{Bits, SigBits} <: AbstractUnsigned{Bits, SigBits} end
```

The `Ako` prefix (from "A kind of") distinguishes domain abstractions from structural ones, enabling precise dispatch without naming conflicts.

## Type Parameter Constraints

The type system enforces mathematical consistency through compile-time parameter validation:

### Signed Format Constraints
```julia
# Require: 3 ≤ Bits ≤ 15, 1 ≤ SigBits < Bits
# Minimum configuration: 1 sign + 1 exponent + 1 significand bit
```

### Unsigned Format Constraints  
```julia
# Require: 3 ≤ Bits ≤ 15, 1 ≤ SigBits ≤ Bits
# Additional exponent bit available: nbits_exp = Bits - SigBits + 1
```

These constraints prevent degenerate configurations while maximizing the useful parameter space.

## Concrete Type Structure

Concrete implementations store both floating-point values and their integer encodings:

```julia
struct SignedFinite{bits, sigbits, T<:AbstractFloat, S<:Unsigned} <: AkoSignedFinite{bits, sigbits}
    floats::Vector{T}  # Canonical value sequence
    codes::Vector{S}   # Corresponding bit encodings
end
```

### Storage Type Selection

The `T` and `S` parameters are automatically determined by bitwidth:

```julia
typeforfloat(bits) = bits ≤ 8 ? Float64 : (bits ≤ 11 ? Float64 : Float128)
typeforcode(bits) = bits ≤ 8 ? UInt8 : UInt16
```

This selection balances precision requirements against memory efficiency.

## Method Dispatch Patterns

The hierarchy enables sophisticated dispatch strategies that minimize runtime overhead:

### Abstract-Concrete Duality

Every method supports both type-level and instance-level invocation:

```julia
# Type-level dispatch (compile-time resolution)
nbits(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = Bits

# Instance-level dispatch (automatic forwarding)
nbits(x::T) where {T<:AbstractAIFloat} = nbits(T)
```

This pattern eliminates redundant implementations while preserving both programming paradigms.

### Signedness-Aware Dispatch

The type system naturally partitions methods by signedness requirements:

```julia
# Signed-only operations
code_negone(::Type{T}) where {T<:AbstractSigned} = ...
code_negone(::Type{T}) where {T<:AbstractUnsigned} = nothing

# Universal operations with signedness-dependent implementation
nmagnitudes(T::Type{<:AbstractUnsigned}) = 2^nbits(T) - 1
nmagnitudes(T::Type{<:AbstractSigned}) = 2^(nbits(T) - 1)
```

### Domain-Specific Specialization

Extended vs. finite domain differences require specialized handling:

```julia
nInfs(::Type{<:AkoSignedFinite}) = 0
nInfs(::Type{<:AkoSignedExtended}) = 2
nInfs(::Type{<:AkoUnsignedFinite}) = 0  
nInfs(::Type{<:AkoUnsignedExtended}) = 1
```

This approach ensures that domain-specific properties compile to optimal code without runtime conditionals.

## Type-Level Computation Benefits

The parametric design enables extensive compile-time precomputation:

### Bit Field Calculations
```julia
# Exponent field width computed at compile time
nbits_exp(::Type{<:AbstractSigned{Bits, SigBits}}) where {Bits, SigBits} = Bits - SigBits
nbits_exp(::Type{<:AbstractUnsigned{Bits, SigBits}}) where {Bits, SigBits} = Bits - SigBits + 1
```

### Count Computations
```julia
# Value counts resolved during compilation
nvalues(::Type{<:AbstractAIFloat{Bits}}) where {Bits} = 2^Bits
nmagnitudes_prenormal(::Type{<:AbstractAIFloat{Bits, SigBits}}) where {Bits, SigBits} = 2^(SigBits - 1)
```

This compile-time resolution eliminates computational overhead for format introspection operations.

## Hierarchy Traversal Utilities

The package provides predicates for runtime type classification:

```julia
is_aifloat(::Type{<:AbstractAIFloat}) = true
is_signed(::Type{<:AbstractSigned}) = true
is_finite(::Type{<:AkoSignedFinite}) = true
is_extended(::Type{<:AkoSignedExtended}) = true
```

These predicates enable generic programming while maintaining type safety and performance characteristics.