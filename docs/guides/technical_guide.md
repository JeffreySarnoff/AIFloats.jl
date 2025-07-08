# AIFloats.jl Technical Documentation

## Architecture Overview

AIFloats.jl implements a comprehensive family of microfloat formats based on the IEEE P3109 standard for arithmetic interchange formats. The design emphasizes mathematical rigor, computational efficiency, and deep learning optimization.

## Type System Architecture

### Abstract Type Hierarchy

```julia
                                 abstract type AbstractAIFloat{Bits, SigBits} <: AbstractFloat end

abstract type AbstractSigned{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits} end

    abstract type AbstractSignedFinite{Bits, SigBits} <: AbstractSigned{Bits, SigBits} end
    abstract type AbstractSignedExtended{Bits, SigBits} <: AbstractSigned{Bits, SigBits} end

abstract type AbstractUnsigned{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits} end

    abstract type AbstractUnsignedFinite{Bits, SigBits} <: AbstractUnsigned{Bits, SigBits} end
    abstract type AbstractUnsignedExtended{Bits, SigBits} <: AbstractUnsigned{Bits, SigBits} end
```

### Concrete Implementation Types

```julia
struct SignedFinite{bits, sigbits, T, U} <: AbstractSignedFinite{bits, sigbits}
    floats::Vector{T}  # Aligned memory for float values
    codes::Vector{U}   # Aligned memory for encodings
end

struct SignedExtended{bits, sigbits, T, U} <: AbstractSignedExtended{bits, sigbits}
    floats::Vector{T}
    codes::Vector{U}
end

struct UnsignedFinite{bits, sigbits, T, U} <: AbstractUnsignedFinite{bits, sigbits}
    floats::Vector{T}
    codes::Vector{U}
end

struct UnsignedExtended{bits, sigbits, T, U} <: AbstractUnsignedExtended{bits, sigbits}
    floats::Vector{T}
    codes::Vector{U}
end
```

## Mathematical Foundation

### Binary Rational Number Systems

AIFloats represent **augmented binary rational numbers** (ℚ₂◊):

- **ℚ₂**: Binary rational numbers with numerator 0..2ᴷ-1, implicit denominator 2ᴷ
- **ℚ₂***: Extended binary rationals = ℚ₂ ∪ {-∞, +∞}  
- **ℚ₂◊**: Augmented binary rationals = ℚ₂* ∪ {NaN}

This provides a mathematically rigorous foundation distinct from extended real numbers (ℝ*), since NaN has no real number expression.

### Precision-Limited Binary Rationals

The format uses **prenormal** magnitudes (a generalization of subnormal):

```julia
n_prenormals(precision) = 2^(precision - 1)
n_subnormals(precision) = n_prenormals(precision) - 1
fractional_step(precision) = 1 / n_prenormals(precision)
prenormal_sequence(precision) = (0:1:(n_prenormals-1)) * fractional_step * exponent_min
normal_sequence(precision) = 1.0 .+ prenormal_sequence(precision)

prenormal_values(bits, precision) = prenormal_sequence(precision) * exponent_min(bits, precision)

```

### Exponent System

Exponents are **sign-symmetric** with bias calculations:

**Signed formats:**
```julia
n_exponent_bits(signed_bits, precision) = bits - precision
bias(signed_bits, precision) = 2^(n_exponent_bits - 1) - 1
```

**Unsigned formats:**
```julia
n_exponent_bits(unsigned_bits, precision) = bits - precision + 1  
bias(unsigned_bits, precision) = 2^(n_exponent_bits - 1)
```

**Unbiased exponent ranges:**
```julia
exponent_extrema = (-bias, bias)  # Always symmetric
```

## Value Sequence Generation

### Foundation Magnitude Algorithm

The core algorithm generates magnitude sequences by combining significand patterns with exponent scaling:

```julia
function foundation_magnitudes(T::Type{<:AbstractAIFloat})
    # Generate significand magnitude patterns
    significands = significand_magnitudes(T)
    
    # Generate exponent values as powers of 2
    exp_values = map(two_pow, exp_unbiased_magnitude_strides(T))
    
    # Scale significands by exponents
    magnitudes = significands .* exp_values
    
    # Convert to appropriate float type and align memory
    typ = typeforfloat(nBits(T))
    aligned_magnitudes = memalign_clear(typ, length(significands))
    aligned_magnitudes[:] = map(typ, magnitudes)
    
    return aligned_magnitudes
end
```

### Significand Generation

```julia
function significand_magnitudes(T::Type{<:AbstractAIFloat})
    # Prenormal (subnormal-like) step pattern
    prenormal_steps = (0:nPrenormalMagnitudes(T)-1) ./ nPrenormalMagnitudes(T)
    
    # Normal step pattern  
    normal_steps = (nPrenormalMagnitudes(T):(2*nPrenormalMagnitudes(T)-1)) ./ nPrenormalMagnitudes(T)
    
    # Combine and replicate for all exponent values
    significands = collect(prenormal_steps)
    nmagnitudes = nMagnitudes(T) - (is_signed(T) * nPrenormalMagnitudes(T))
    normal_cycles = fld(nmagnitudes, nPrenormalMagnitudes(T))
    
    for _ in 1:normal_cycles
        append!(significands, normal_steps)
    end
    
    return significands
end
```

## Special Value Placement

### Unsigned Types

**Finite unsigned:**
- Position 1: `0.0` (always first)
- Positions 2 to n-1: Increasing positive magnitudes
- Position n: `NaN` (always last)

**Extended unsigned:**
- Position 1: `0.0`
- Positions 2 to n-2: Increasing positive magnitudes  
- Position n-1: `+Inf`
- Position n: `NaN`

### Signed Types

**Finite signed:**
- First half: Non-negative magnitudes (0, positive values)
- Second half: Negative magnitudes with NaN transformation

**Extended signed:**
- Similar to finite, but with `+Inf` at end of first half, `-Inf` at end

### Internal Architecture Invariants

```julia
# Universal invariants across all types
length(T) = 2^n_bits(T)
code(T, 0) == 0x00                    # Zero always at position 0
code(T, NaN) == n_values(T) - 1      # NaN position varies by type

# Signed vs unsigned magnitude counts  
n_magnitudes(Signed) = length(T) >> 1     # Half values are magnitudes
n_magnitudes(Unsigned) = length(T) - 1    # All except NaN

# Special value positions
code(T, +1) == n_values(Signed) >> 2      # Quarter position for signed
code(T, +1) == n_values(Unsigned) >> 1    # Half position for unsigned
```

## Memory Management and Performance

### Aligned Memory Allocation

All arrays use cache-aligned allocation via AlignedAllocs.jl:

```julia
function encoding_sequence(T::Type{<:AbstractAIFloat})
    nbits = nBits(T)
    n = 1 << nbits
    typ = typeforcode(nbits)  # UInt8 for ≤8 bits, UInt16 for 9-15 bits
    codes = memalign_clear(typ, n)  # Cache-line aligned
    codes[:] = map(typ, 0:(n-1))
    return codes
end
```

### Type Selection Strategy

**Encoding types:**
- `UInt8` for bitwidths ≤ 8
- `UInt16` for bitwidths 9-15

**Float types:**
- `Float64` for bitwidths ≤ 8  
- `Float64` for bitwidths 9-10 (transition region)
- `Float128` for bitwidths ≥ 11

This balances precision requirements with computational efficiency.

### Lookup Table Optimization

For small formats (3-8 bits), complete function lookup tables are feasible:

```julia
# Example: 8-bit format has only 256 values
# Unary function table: 256 entries
# Binary function table: 256×256 = 64K entries (cacheable)

function create_function_table(T::Type{<:AbstractAIFloat}, f::Function)
    values = floats(T)
    table = similar(values)
    for i in eachindex(values)
        table[i] = f(values[i])
    end
    return table
end
```

## Rounding and Projection

### Rounding Modes

AIFloats.jl implements comprehensive rounding support:

```julia
const RoundToOdd = RoundingMode{:Odd}
const RoundStochastic = RoundingMode{:Stochastic}

# Standard IEEE rounding modes plus extensions
round_up(xs, x)              # Round toward +∞
round_down(xs, x)            # Round toward -∞  
round_tozero(xs, x)          # Round toward 0
round_fromzero(xs, x)        # Round away from 0
round_nearesteven(xs, x)     # Round to nearest, ties to even
round_nearestodd(xs, x)      # Round to nearest, ties to odd
round_nearesttozero(xs, x)   # Round to nearest, ties toward zero
round_nearestfromzero(xs, x) # Round to nearest, ties away from zero
```

### Projection Algorithm

High-precision values are projected into AIFloat formats using binary search:

```julia
function round_nearesteven(xs::T, x::F) where {T<:AbstractAIFloat, F<:AbstractFloat}
    isnan(x) && return x
    
    # Binary search for bracketing values
    idx1 = searchsortedfirst(floats(xs), x)
    val1 = floats(xs)[idx1]
    
    # Handle exact matches and boundaries
    (x == val1 || idx1 === 1) && return val1
    idx1 >= length(floats(xs)) && return floats(xs)[end-1]
    
    # Find nearest with tie-breaking
    idx0 = idx1 - 1
    val0 = floats(xs)[idx0]
    
    distance0 = x - val0
    distance1 = val1 - x
    
    if distance0 != distance1
        return distance0 < distance1 ? val0 : val1
    else
        # Tie-breaking: choose value with even encoding
        even_bits_0 = trailing_zeros(codes(xs)[idx0])
        even_bits_1 = trailing_zeros(codes(xs)[idx1])
        return even_bits_0 > even_bits_1 ? val0 : val1
    end
end
```

## Index and Encoding System

### Conversion Functions

```julia
# Julia uses 1-based indexing, encodings are 0-based
offset_to_index(offset::Integer) = offset + 1
index_to_offset(index::Integer) = index - 1

# Convert index to encoding value  
index_to_code(bits::Integer, index::Integer) = 
    (index - 1) % (bits <= 8 ? UInt8 : UInt16)

# Special value indices (computed, not stored)
idxone(T::Type{<:AbstractUnsigned}) = (nValues(T) >> 1) + 1
idxone(T::Type{<:AbstractSigned}) = (nValues(T) >> 2) + 1  
idxnan(T::Type{<:AbstractUnsigned}) = nValues(T)
idxnan(T::Type{<:AbstractSigned}) = (nValues(T) >> 1) + 1
```

### Value-Index Mapping

```julia
function valuetoindex(xs::T, x::F) where {T<:AbstractAIFloat, F<:AbstractFloat}
    # Direct search in aligned array
    findfirst(isequal(x), floats(xs))
end

function indextovalue(xs::T, index::Integer) where {T<:AbstractAIFloat}
    # Bounds checking with NaN fallback
    if 1 <= index <= nValues(typeof(xs))
        return floats(xs)[index]
    else
        return eltype(floats(xs))(NaN)
    end
end
```

## Bit Field Computations

### Mask Generation

```julia
# Sign mask (0 for unsigned, MSB for signed)
sign_mask(::Type{T}) where {T<:AbstractUnsigned} = zero(typeforcode(nBits(T)))
sign_mask(::Type{T}) where {T<:AbstractSigned} = 
    one(typeforcode(nBits(T))) << (nBits(T) - 1)

# Exponent mask
function exponent_mask(::Type{T}) where {T<:AbstractAIFloat}
    unit = one(typeforcode(nBits(T)))
    mask = (unit << nExpBits(T)) - unit
    return mask << nFracBits(T)
end

# Significand mask (trailing bits only)
function trailing_significand_mask(::Type{T}) where {T<:AbstractAIFloat}
    unit = one(typeforcode(nBits(T)))
    return (unit << nFracBits(T)) - unit
end
```

## Counting Functions

### Comprehensive Bit and Value Counts

```julia
# Basic bit allocation
nBits(T::Type{<:AbstractAIFloat}) = Bits
nSigBits(T::Type{<:AbstractAIFloat}) = SigBits
nFracBits(::Type{T}) where {T<:AbstractAIFloat} = nSigBits(T) - 1

# Sign and exponent bits
nSignBits(::Type{T}) where {T<:AbstractSigned} = 1
nSignBits(::Type{T}) where {T<:AbstractUnsigned} = 0
nExpBits(::Type{T}) where {T<:AbstractSigned} = nBits(T) - nSigBits(T)
nExpBits(::Type{T}) where {T<:AbstractUnsigned} = nBits(T) - nSigBits(T) + 1

# Value counts
nValues(::Type{T}) where {T<:AbstractAIFloat} = 1 << nBits(T)
nMagnitudes(::Type{T}) where {T<:AbstractSigned} = nValues(T) >> 1
nMagnitudes(::Type{T}) where {T<:AbstractUnsigned} = nValues(T) - 1

# Special value counts
nInfs(::Type{T}) where {T<:AbstractSignedExtended} = 2    # ±Inf
nInfs(::Type{T}) where {T<:AbstractUnsignedExtended} = 1  # +Inf only
nInfs(::Type{T}) where {T<:AbsFiniteFloat} = 0            # No infinities

# Prenormal/subnormal counts
nPrenormalMagnitudes(::Type{T}) where {T<:AbstractAIFloat} = 1 << (nSigBits(T) - 1)
nSubnormalMagnitudes(::Type{T}) where {T<:AbstractAIFloat} = nPrenormalMagnitudes(T) - 1
```

## IEEE P3109 Compliance

### Verified Properties

AIFloats.jl implements the first formally verified floating-point standard (IEEE P3109):

1. **NaN Isolation**: NaNs cannot arise except where specified
2. **Infinity Control**: Infinities only appear in extended formats where specified  
3. **Operation Compliance**: All arithmetic operations follow verified specifications
4. **No Exceptional States**: Designed to never interrupt computation flow

### Format Interconversion Specification

```julia
# Generic conversion between P3109 formats
function convert_p3109(source_format, target_format, projection_spec, value)
    if isnan(value)
        return target_format(NaN)
    else
        decoded_value = decode(source_format, value)
        return project(target_format, projection_spec, decoded_value)
    end
end
```

### Arithmetic Operation Specification

```julia
# Addition with mixed formats (P3109 compliant)
function add_p3109(fx, fy, fz, π, x, y)
    # Handle special cases
    isnan(x) || isnan(y) && return convert(fz, NaN)
    
    # Decode operands
    X = decode(fx, x)
    Y = decode(fy, y)
    
    # Compute in extended precision, then project
    result = X + Y
    return project(fz, π, result)
end
```

This architecture ensures mathematical rigor while providing the performance characteristics needed for deep learning applications.