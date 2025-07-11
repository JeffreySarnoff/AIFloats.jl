# Type System Reference

## Abstract Types

### Core Hierarchy

The abstract type hierarchy provides the foundation for the AIFloat format family, enabling both compile-time specialization and runtime polymorphism.

### Domain-Specific Abstractions


Domain abstractions distinguish between finite-only formats and those including infinities, enabling precise dispatch for domain-specific operations.

## Concrete Types

### Primary Implementations


Each concrete type stores both the canonical floating-point value sequence and corresponding integer encodings in cache-aligned arrays.

### Type Parameters

All concrete types are parameterized by:

- **`bits`**: Total bitwidth (3 ≤ bits ≤ 15)
- **`sigbits`**: Significand precision including implicit bit
- **`T<:AbstractFloat`**: Storage type for floating-point values
- **`S<:Unsigned`**: Storage type for integer encodings

The storage types are automatically selected based on bitwidth:

| Bitwidth Range | Float Type | Code Type |
|----------------|------------|-----------|
| 3-8 bits | `Float64` | `UInt8` |
| 9-11 bits | `Float64` | `UInt16` |
| 12-15 bits | `Float128` | `UInt16` |

## Type Parameter Relationships

### Bit Allocation Constraints

The type system enforces these mathematical relationships:

```julia
# Signed formats require space for sign bit
nbits_exp(::Type{<:AbstractSigned{Bits, SigBits}}) = Bits - SigBits

# Unsigned formats gain an extra exponent bit
nbits_exp(::Type{<:AbstractUnsigned{Bits, SigBits}}) = Bits - SigBits + 1

# Fractional bits exclude implicit leading bit
nbits_frac(::Type{<:AbstractAIFloat{Bits, SigBits}}) = SigBits - 1
```

### Value Count Relationships

Total representable values follow these patterns:

```julia
# All formats use full bit space
nvalues(::Type{<:AbstractAIFloat{Bits}}) = 2^Bits

# Magnitude counts differ by signedness
nmagnitudes(::Type{<:AbstractUnsigned{Bits}}) = 2^Bits - 1  # Exclude NaN
nmagnitudes(::Type{<:AbstractSigned{Bits}}) = 2^(Bits-1)    # Half-space
```

## Type Predicates

### Basic Classification


These predicates enable runtime type classification and generic programming patterns.

### Specialized Properties


Format-specific properties that affect numerical behavior and algorithm selection.

## Type Construction Utilities

### Storage Type Selection


These functions automatically select appropriate storage types based on bitwidth requirements.

### Format Validation

The type system validates parameter combinations during construction:

```julia
function validate_parameters(bits::Int, sigbits::Int, signed::Bool)
    # Basic range checks
    3 ≤ bits ≤ 15 || error("Bitwidth out of range: $bits ∉ [3,15]")
    1 ≤ sigbits ≤ bits || error("Invalid precision: $sigbits ∉ [1,$bits]")
    
    # Signedness-specific constraints
    if signed
        sigbits < bits || error("Signed formats require sigbits < bits")
    end
    
    return true
end
```

## Method Dispatch Patterns

### Abstract-Concrete Duality

The type system supports both compile-time and runtime method resolution:

```julia
# Type-level methods (compile-time resolution)
nbits(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = Bits

# Instance-level methods (automatic forwarding)  
nbits(x::T) where {T<:AbstractAIFloat} = nbits(T)

# Bulk forwarding via metaprogramming
for F in (:nbits, :nbits_sig, :nvalues, :nmagnitudes)
    @eval $F(x::T) where {T<:AbstractAIFloat} = $F(T)
end
```

### Signedness-Aware Dispatch

Operations naturally partition by signedness requirements:

```julia
# Signed-specific operations
code_negone(::Type{T}) where {T<:AbstractSigned} = # implementation
code_negone(::Type{T}) where {T<:AbstractUnsigned} = nothing

# Universal operations with signedness-dependent behavior
exp_bias(::Type{T}) where {T<:AbstractSigned{Bits, SigBits}} = 2^(Bits - SigBits - 1)
exp_bias(::Type{T}) where {T<:AbstractUnsigned{Bits, SigBits}} = 2^(Bits - SigBits)
```

### Domain-Specific Specialization

Extended vs. finite domain differences require specialized handling:

```julia
# Infinity counts by domain
nInfs(::Type{<:AkoSignedFinite}) = 0
nInfs(::Type{<:AkoSignedExtended}) = 2
nInfs(::Type{<:AkoUnsignedFinite}) = 0
nInfs(::Type{<:AkoUnsignedExtended}) = 1
```

## Compile-Time Optimization

The parametric type system enables extensive compile-time precomputation, eliminating runtime overhead for format introspection:

### Static Bit Computations
```julia
# These resolve to constants during compilation
const SF4P2_BITS = nbits(SignedFinite{4,2,Float64,UInt8})     # 4
const SF4P2_EXP_BITS = nbits_exp(SignedFinite{4,2,Float64,UInt8}) # 2
const SF4P2_VALUES = nvalues(SignedFinite{4,2,Float64,UInt8})   # 16
```

### Loop Unrolling Opportunities
```julia
# Enables aggressive loop optimization
function process_all_codes(::Type{T}) where {T<:AbstractAIFloat}
    # Loop bound known at compile time
    for code in 0:(nvalues(T)-1)
        # Process each encoding...
    end
end
```

This design philosophy maximizes both performance and programmer ergonomics through careful exploitation of Julia's type system capabilities.
