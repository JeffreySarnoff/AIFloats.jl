# Getting Started

This tutorial provides a hands-on introduction to AIFloats.jl, demonstrating core concepts through practical examples that illustrate the unique characteristics of reduced-precision arithmetic designed for machine learning applications.

## Installation and Basic Setup

```julia
using Pkg
Pkg.add("AIFloats")
using AIFloats
```

## Creating Your First AIFloat Format

### Understanding Format Specification

AIFloat formats are specified by four parameters that completely determine their arithmetic properties:

```julia
# Create a 4-bit unsigned finite format with 2-bit significand precision
uf4p2 = AIFloat(4, 2, :unsigned, :finite)

# Examine the complete value domain
println("Values: ", floats(uf4p2))
println("Codes:  ", codes(uf4p2))
```

Output:
```
Values: [0.0, 0.25, 0.5, 0.75, 1.0, 1.25, 1.5, NaN]
Codes:  [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]
```

### Analyzing the Bit Layout

The 4-bit unsigned format allocates bits as follows:
- **Significand**: 2 bits (1 implicit + 1 fractional)
- **Exponent**: 3 bits (4 - 2 + 1 for unsigned)
- **Sign**: 0 bits (unsigned format)

```julia
# Verify bit allocation
println("Total bits: ", n_bits(uf4p2))           # 4
println("Significand bits: ", n_sig_bits(uf4p2)) # 2  
println("Exponent bits: ", n_exp_bits(uf4p2))    # 3
println("Sign bits: ", n_sign_bits(uf4p2))       # 0
```

## Exploring Format Variants

### Signed vs. Unsigned Formats

Compare equivalent signed and unsigned formats to understand the trade-offs:

```julia
# 4-bit signed finite format
sf4p2 = AIFloat(4, 2, :signed, :finite)
println("Signed values: ", floats(sf4p2))

# 4-bit unsigned finite format  
uf4p2 = AIFloat(4, 2, :unsigned, :finite)
println("Unsigned values: ", floats(uf4p2))
```

Output:
```
Signed values:   [0.0, 0.5, 1.0, 1.5, NaN, -0.5, -1.0, -1.5]
Unsigned values: [0.0, 0.25, 0.5, 0.75, 1.0, 1.25, 1.5, NaN]
```

**Key Observations**:
- Signed format sacrifices one exponent bit for sign representation
- Unsigned format provides finer granularity in the positive domain
- Both maintain symmetric NaN placement

### Finite vs. Extended Domains

Extended formats incorporate infinities for overflow handling:

```julia
# Compare finite and extended variants
uf4_finite = AIFloat(4, 2, :unsigned, :finite)
uf4_extended = AIFloat(4, 2, :unsigned, :extended)

println("Finite values:   ", floats(uf4_finite))
println("Extended values: ", floats(uf4_extended))
```

Output:
```
Finite values:   [0.0, 0.25, 0.5, 0.75, 1.0, 1.25, 1.5, NaN]
Extended values: [0.0, 0.25, 0.5, 0.75, 1.0, 1.25, Inf, NaN]
```

The extended format replaces the largest finite mag with positive infinity, providing overflow handling at the cost of reduced finite precision.

## Understanding Value Organization

### Prenormal and Normal Regimes

AIFloat formats partition values into distinct mathematical regimes:

```julia
# Create a format with observable subnormal structure
se6p3 = AIFloat(6, 3, :signed, :extended)

# Examine regime boundaries
println("Prenormal count: ", nmags_prenormal(se6p3))
println("Subnormal count: ", nmags_subnormal(se6p3))  
println("Normal count: ", nmags_normal(se6p3))

# Extract subnormal and normal value ranges
values = floats(se6p3)
prenormal_end = nmags_prenormal(se6p3)

println("Prenormal values: ", values[1:prenormal_end])
println("First few normals: ", values[prenormal_end+1:prenormal_end+4])
```

This reveals the transition from fractional scaling (subnormals) to exponential scaling (normals), demonstrating how precision is allocated across the dynamic range.

## Format Introspection and Analysis

### Querying Format Properties

AIFloats provides comprehensive introspection capabilities:

```julia
# Create a representative format for analysis
se8p4 = AIFloat(8, 4, :signed, :extended)

# Basic format characterization
println("Format family: ", is_signed(se8p4) ? "Signed" : "Unsigned", 
        ", ", is_extended(se8p4) ? "Extended" : "Finite")

# Count various value categories
println("Total values: ", n_values(se8p4))
println("Finite values: ", n_finite_nums(se8p4))
println("Positive values: ", n_pos_nums(se8p4))
println("Normal values: ", n_normal_nums(se8p4))
println("Infinity count: ", n_inf(se8p4))
```

### Examining Exponent Structure

Understanding the exponent system is crucial for effective format utilization:

```julia
# Analyze exponent characteristics
println("Exponent bias: ", exp_bias(se8p4))
println("Min unbiased exponent: ", exp_unbiased_min(se8p4))
println("Max unbiased exponent: ", exp_unbiased_max(se8p4))
println("Subnormal exponent: ", exp_unbiased_subnormal(se8p4))

# Examine exponent value scaling
println("Min exponent value: ", exp_value_min(se8p4))
println("Max exponent value: ", exp_value_max(se8p4))
println("Subnormal scale: ", exp_subnormal_value(se8p4))
```

## Working with Encodings and Indices

### Code-Value Correspondence

Every AIFloat maintains perfect correspondence between bit patterns and floating-point values:

```julia
sf4p2 = AIFloat(4, 2, :signed, :finite)

# Demonstrate encoding lookup
for i in 1:length(codes(sf4p2))
    code = codes(sf4p2)[i]
    value = floats(sf4p2)[i]
    println("Code 0x$(string(code, base=16, pad=2)) ↔ Value $value")
end
```

Output:
```
Code 0x00 ↔ Value 0.0
Code 0x01 ↔ Value 0.5
Code 0x02 ↔ Value 1.0
Code 0x03 ↔ Value 1.5
Code 0x04 ↔ Value NaN
Code 0x05 ↔ Value -0.5
Code 0x06 ↔ Value -1.0
Code 0x07 ↔ Value -1.5
```

### Special Value Locations

AIFloats use deterministic placement for special values:

```julia
# Locate special value encodings
println("Zero code: 0x$(string(code_zero(sf4p2), base=16, pad=2))")
println("One code: 0x$(string(code_one(sf4p2), base=16, pad=2))")
println("NaN code: 0x$(string(code_nan(sf4p2), base=16, pad=2))")

# For signed formats, negative one is also available
println("Negative one code: 0x$(string(code_negone(sf4p2), base=16, pad=2))")
```

### Index-Based Access

Julia's 1-based indexing provides natural access to the value sequences:

```julia
# Convert between 0-based codes and 1-based indices
code = 0x03
index = code_to_index(length(floats(sf4p2)), code)
value = floats(sf4p2)[index]

println("Code $code → Index $index → Value $value")

# Reverse lookup: find code for a specific value
target_value = 1.0
found_index = findfirst(==(target_value), floats(sf4p2))
found_code = codes(sf4p2)[found_index]
println("Value $target_value → Index $found_index → Code 0x$(string(found_code, base=16, pad=2))")
```

## Practical Applications

### Neural Network Weight Quantization

Demonstrate AIFloat usage for weight quantization scenarios:

```julia
# Simulate weight matrix quantization
using Random
Random.seed!(42)

# Generate synthetic weight matrix
weights_fp32 = randn(Float32, 4, 4) * 0.5

# Choose quantization format based on weight distribution
weight_format = AIFloat(6, 3, :signed, :finite)  # 6-bit signed for weights

println("Original weights (Float32):")
display(weights_fp32)

# Quantize by finding nearest representable values
quantized_weights = similar(weights_fp32)
for i in eachindex(weights_fp32)
    # Find closest AIFloat representation
    distances = abs.(floats(weight_format) .- weights_fp32[i])
    closest_idx = argmin(distances)
    quantized_weights[i] = floats(weight_format)[closest_idx]
end

println("\nQuantized weights (6-bit AIFloat):")
display(quantized_weights)

# Analyze quantization error
mse = mean((weights_fp32 .- quantized_weights).^2)
println("\nQuantization MSE: $mse")
```

### Activation Function Table Generation

Create lookup tables for fast activation function evaluation:

```julia
# Generate ReLU lookup table for small format
relu_format = AIFloat(4, 2, :signed, :finite)
relu_table = max.(0.0, floats(relu_format))

println("ReLU lookup table:")
for (code, input, output) in zip(codes(relu_format), floats(relu_format), relu_table)
    println("Code 0x$(string(code, base=16, pad=2)): ReLU($input) = $output")
end

# Demonstrate table-based computation
input_code = 0x01  # Corresponds to 0.5
output_value = relu_table[input_code + 1]  # +1 for Julia indexing
println("\nTable lookup: ReLU($(floats(relu_format)[input_code + 1])) = $output_value")
```

## Performance Considerations

### Memory Layout Inspection

Examine the memory-efficient dual-array structure:

```julia
# Create format and inspect memory layout
format = AIFloat(6, 3, :unsigned, :finite)

println("Memory usage analysis:")
println("Values array: $(sizeof(floats(format))) bytes")
println("Codes array: $(sizeof(codes(format))) bytes")
println("Total overhead: $(sizeof(floats(format)) + sizeof(codes(format))) bytes")
println("Entries: $(length(floats(format)))")

#= Verify cache alignment (requires AlignedAllocs.jl)
using AlignedAllocs
println("Values alignment: $(alignment(floats(format))) bytes")
println("Codes alignment: $(alignment(codes(format))) bytes")
=@
```

## Next Steps

This tutorial covered the fundamental concepts of AIFloat format creation, introspection, and basic manipulation. To continue learning:

1. **[Custom Formats Tutorial](custom_formats.md)**: Learn to design application-specific formats
2. **[Performance Optimization](performance.md)**: Explore advanced optimization techniques
3. **[Reference Documentation](../reference/types.md)**: Detailed API coverage

### Key Takeaways

- AIFloat formats provide deterministic, exception-free arithmetic
- Bit allocation trades off precision against dynamic range
- Dual-array storage enables both direct computation and table lookup
- Format introspection supports algorithmic format selection
- Cache-aligned memory layout optimizes computational performance

The next tutorial will demonstrate how to design custom formats optimized for specific neural network architectures and training regimes.