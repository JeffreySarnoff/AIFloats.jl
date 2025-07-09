# AIFloats.jl User Guide

## Introduction

AIFloats.jl provides a comprehensive family of microfloat formats designed specifically for deep learning applications. These formats range from 2 to 15 bits and offer precise control over precision, signedness, and special value handling.

## Key Features

- **Comprehensive Format Family**: Support for 2-15 bit floating-point formats
- **Flexible Precision**: Each format supports precisions from 1 to bits-1 (signed) or 1 to bits (unsigned)
- **Four Variants**: Signed/Unsigned × Finite/Extended combinations
- **Deep Learning Optimized**: No exceptional states that interfere with training flow
- **IEEE P3109 Compliant**: Based on the first formally verified floating-point standard
- **High Performance**: Cache-aligned memory allocation and lookup table support

## Quick Start

### Installation

```julia
using Pkg
Pkg.add("AIFloats")
```

### Basic Usage

```julia
using AIFloats

# Create a 3-bit unsigned finite float with 1-bit precision
uf31 = AIFloat(3, 1; UnsignedFloat=true, FiniteFloat=true)

# Access the float values and their encodings
floats(uf31)  # Float32[0.0, 0.125, 0.25, 0.5, 1.0, 2.0, 4.0, NaN]
codes(uf31)   # UInt8[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]

# Create a 3-bit signed extended float with 2-bit precision
se32 = AIFloat(3, 2; SignedFloat=true, ExtendedFloat=true)

floats(se32)  # Float32[0.0, 0.5, 1.0, Inf, NaN, -0.5, -1.0, -Inf]
codes(se32)   # UInt8[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]
```

### Working with Abstract Types

You can also work directly with abstract types:

```julia
# Using abstract type constructors
uf31_abstract = AIFloat(AkoUnsignedFinite{3, 1})
se32_abstract = AIFloat(AkoSignedExtended{3, 2})

# Results are identical to parameter-based construction
floats(uf31_abstract) == floats(uf31)  # true
```

## Understanding the Format Family

### Signedness

- **Signed**: Support both positive and negative values, plus signed infinities
- **Unsigned**: Only non-negative values, single positive infinity

### Finiteness

- **Finite**: Include NaN but no infinities - safer for training
- **Extended**: Include infinities (±Inf for signed, +Inf for unsigned)

### Four Main Types

1. **Signed Finite (sf)**: Bipolar, finite values + NaN
2. **Signed Extended (se)**: Bipolar, finite values + ±Inf + NaN  
3. **Unsigned Finite (uf)**: Unipolar, finite values + NaN
4. **Unsigned Extended (ue)**: Unipolar, finite values + +Inf + NaN

## Format Characteristics

### Value Layout

All formats follow consistent patterns:

- **Zero**: Always encoded as `0b0...0` (first value)
- **NaN**: Consistent placement (last for unsigned, specific position for signed)
- **Infinities**: Predictable locations in extended formats

### Special Properties

- **No Exceptional States**: Designed to never interrupt deep learning workflows
- **Monotonic Ordering**: Values increase monotonically (except special values)
- **Symmetric Exponents**: Sign-symmetric exponent ranges

## Advanced Usage

### Querying Format Properties

```julia
uf = AIFloat(8, 4; UnsignedFloat=true, FiniteFloat=true)

# Basic properties
nBits(uf)      # 8
nSigBits(uf)   # 4
nValues(uf)    # 256
nMagnitudes(uf) # 255

# Type predicates
is_unsigned(uf)  # true
is_finite(uf)    # true
has_subnormals(uf) # true

# Exponent properties
expBias(uf)      # Exponent bias
expMin(uf)       # Minimum exponent
expMax(uf)       # Maximum exponent
```

### Working with Sequences

```julia
# Get encoding sequence (all possible bit patterns)
codes_seq = encoding_sequence(uf)

# Get foundation magnitudes (base magnitude progression)
foundation_mags = foundation_magnitudes(uf)

# Get complete value sequence
values_seq = value_sequence(typeof(uf))
```

### Index and Offset Conversion

```julia
# Convert between Julia indices (1-based) and encoding offsets (0-based)
offset_to_index(5)  # 6 (Julia index)
index_to_offset(6)  # 5 (encoding offset)

# Convert indices to encoding values
index_to_code(8, 256)  # UInt8(255) for 8-bit format
```

## Integration with Julia Ecosystem

AIFloats.jl integrates seamlessly with Julia's number system:

```julia
sf = AIFloat(8, 4; SignedFloat=true, FiniteFloat=true)

# Standard Julia functions work
zero(sf)      # Get zero value
one(sf)       # Get one value  
eps(sf)       # Get epsilon (ULP at 1.0)
nextfloat(sf, 1.0)  # Next representable value
prevfloat(sf, 1.0)  # Previous representable value
```

## Performance Considerations

### Memory Alignment

AIFloats.jl uses cache-aligned memory allocation via AlignedAllocs.jl for optimal performance:

```julia
# All internal arrays are cache-line aligned for best performance
uf = AIFloat(8, 4; UnsignedFloat=true, FiniteFloat=true)
# floats(uf) and codes(uf) are automatically aligned
```

### Lookup Tables

For small bit widths (3-8 bits), lookup tables provide extremely fast operations:

```julia
# For 3-8 bit formats, all unary functions can use direct lookup
# Binary operations on small formats can also use precomputed tables
```

## Common Use Cases

### Deep Learning Training

```julia
# Create formats optimized for different training phases
weights_format = AIFloat(8, 4; SignedFloat=true, FiniteFloat=true)
activations_format = AIFloat(6, 3; UnsignedFloat=true, FiniteFloat=true) 
gradients_format = AIFloat(8, 5; SignedFloat=true, ExtendedFloat=true)
```

### Inference Optimization

```julia
# Ultra-low precision for inference
inference_format = AIFloat(4, 2; UnsignedFloat=true, FiniteFloat=true)

# Check value ranges
min_val = minimum(filter(isfinite, floats(inference_format)))
max_val = maximum(filter(isfinite, floats(inference_format)))
```

### Custom Precision Experiments

```julia
# Explore different precision trade-offs
for bits in 4:8, precision in 2:(bits-1)
    sf = AIFloat(bits, precision; SignedFloat=true, FiniteFloat=true)
    println("$bits-bit, $precision-precision: $(nMagnitudes(sf)) magnitudes")
end
```

## Best Practices

1. **Choose Finite for Training**: Finite formats avoid infinity-related numerical issues
2. **Use Unsigned for Non-negative Data**: More efficient representation for activations, weights
3. **Match Precision to Data**: Higher precision for gradients, lower for activations
4. **Leverage Lookup Tables**: For 3-8 bit formats, precompute function tables
5. **Monitor Value Ranges**: Ensure your data fits within the format's representable range

## Error Handling

AIFloats.jl provides clear error messages for invalid configurations:

```julia
# This will error - must specify exactly one signedness
try
    AIFloat(8, 4; FiniteFloat=true)  # Missing signedness
catch e
    println(e)  # Clear error about missing SignedFloat/UnsignedFloat
end

# This will error - precision constraints
try  
    AIFloat(4, 4; SignedFloat=true, FiniteFloat=true)  # precision >= bitwidth for signed
catch e
    println(e)  # Clear error about parameter constraints
end
```

## Next Steps

- Explore the [Technical Documentation](technical_guide.md) for implementation details
- See [Examples](examples.md) for complete usage examples
- Check [API Reference](api_reference.md) for detailed function documentation
- Learn about [IEEE P3109 Standard](p3109_overview.md) compliance