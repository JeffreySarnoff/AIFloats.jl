# AIFloats.jl Examples

## Basic Usage Examples

### Creating Different Format Types

```julia
using AIFloats

# Create all four basic variants with 8 bits, 4-bit precision
sf = AIFloat(8, 4; SignedFloat=true, FiniteFloat=true)      # Signed Finite
se = AIFloat(8, 4; SignedFloat=true, ExtendedFloat=true)    # Signed Extended  
uf = AIFloat(8, 4; UnsignedFloat=true, FiniteFloat=true)    # Unsigned Finite
ue = AIFloat(8, 4; UnsignedFloat=true, ExtendedFloat=true)  # Unsigned Extended

println("Signed Finite: $(length(floats(sf))) values")
println("Signed Extended: $(length(floats(se))) values") 
println("Unsigned Finite: $(length(floats(uf))) values")
println("Unsigned Extended: $(length(floats(ue))) values")
```

### Exploring Format Properties

```julia
# Examine a 6-bit unsigned finite format with 3-bit precision
uf = AIFloat(6, 3; UnsignedFloat=true, FiniteFloat=true)

println("Format Properties:")
println("  Total bits: $(nBits(uf))")
println("  Significand bits: $(nSigBits(uf))")
println("  Exponent bits: $(nExpBits(uf))")
println("  Total values: $(nValues(uf))")
println("  Magnitudes: $(nMagnitudes(uf))")
println("  Has subnormals: $(has_subnormals(uf))")

# Look at the actual values
values = floats(uf)
println("\nFirst 10 values: $(values[1:10])")
println("Last 5 values: $(values[end-4:end])")
```

### Working with Value Sequences

```julia
# Create a small format for detailed inspection
uf = AIFloat(4, 2; UnsignedFloat=true, FiniteFloat=true)

println("All values and their codes:")
for (i, (code, value)) in enumerate(zip(codes(uf), floats(uf)))
    println("  Index $i: Code 0x$(string(code, base=16, pad=2)) → $value")
end

# Find specific values
one_idx = valuetoindex(uf, 1.0)
zero_idx = valuetoindex(uf, 0.0)
nan_idx = findfirst(isnan, floats(uf))

println("\nSpecial value indices:")
println("  Zero at index: $zero_idx")
println("  One at index: $one_idx") 
println("  NaN at index: $nan_idx")
```

## Format Comparison Examples

### Signed vs Unsigned Comparison

```julia
# Compare signed and unsigned formats of same size
sf = AIFloat(6, 3; SignedFloat=true, FiniteFloat=true)
uf = AIFloat(6, 3; UnsignedFloat=true, FiniteFloat=true)

println("Signed Format (6-bit, 3-bit precision):")
println("  Values: $(nValues(sf)), Magnitudes: $(nMagnitudes(sf))")
signed_finite = filter(isfinite, floats(sf))
println("  Range: $(minimum(signed_finite)) to $(maximum(signed_finite))")

println("\nUnsigned Format (6-bit, 3-bit precision):")  
println("  Values: $(nValues(uf)), Magnitudes: $(nMagnitudes(uf))")
unsigned_finite = filter(isfinite, floats(uf))
println("  Range: $(minimum(unsigned_finite)) to $(maximum(unsigned_finite))")

# Compare positive value density
sf_positive = filter(x -> x > 0 && isfinite(x), floats(sf))
uf_positive = filter(x -> x > 0 && isfinite(x), floats(uf))
println("\nPositive value count:")
println("  Signed: $(length(sf_positive))")
println("  Unsigned: $(length(uf_positive))")
```

### Finite vs Extended Comparison

```julia
# Compare finite and extended versions
uf_finite = AIFloat(6, 3; UnsignedFloat=true, FiniteFloat=true)
uf_extended = AIFloat(6, 3; UnsignedFloat=true, ExtendedFloat=true)

println("Finite vs Extended (6-bit unsigned, 3-bit precision):")

finite_vals = floats(uf_finite)
extended_vals = floats(uf_extended)

println("Finite format:")
println("  Has infinity: $(any(isinf, finite_vals))")
println("  NaN count: $(count(isnan, finite_vals))")
println("  Finite value count: $(count(isfinite, finite_vals))")

println("Extended format:")  
println("  Has infinity: $(any(isinf, extended_vals))")
println("  Infinity count: $(count(isinf, extended_vals))")
println("  NaN count: $(count(isnan, extended_vals))")
println("  Finite value count: $(count(isfinite, extended_vals))")

# Show where infinity appears
inf_idx = findfirst(isinf, extended_vals)
println("  Infinity at index: $inf_idx (value: $(extended_vals[inf_idx]))")
```

## Precision Analysis Examples

### Precision vs Range Trade-offs

```julia
# Analyze different precision choices for 8-bit formats
println("8-bit Unsigned Finite Formats - Precision Analysis:")
println("Precision | Exp Bits | Magnitudes | Min Positive | Max Finite")
println("----------|----------|------------|--------------|----------")

for precision in 2:7
    uf = AIFloat(8, precision; UnsignedFloat=true, FiniteFloat=true)
    finite_vals = filter(isfinite, floats(uf))
    positive_vals = filter(x -> x > 0, finite_vals)
    
    min_pos = minimum(positive_vals)
    max_finite = maximum(finite_vals)
    
    println("    $precision     |    $(nExpBits(uf))     |    $(nMagnitudes(uf))      | $(round(min_pos, sigdigits=3))      | $(round(max_finite, sigdigits=3))")
end
```

### Subnormal Analysis

```julia
# Examine subnormal behavior across different formats
println("Subnormal Analysis:")
println("Format | Has Subnormals | Subnormal Count | Subnormal Range")
println("-------|----------------|-----------------|----------------")

for (bits, precision) in [(4, 2), (6, 3), (8, 4), (8, 1)]
    uf = AIFloat(bits, precision; UnsignedFloat=true, FiniteFloat=true)
    
    has_sub = has_subnormals(uf)
    sub_count = has_sub ? nSubnormalMagnitudes(uf) : 0
    
    if has_sub
        sub_min = subnormalMagnitudeMin(uf)
        sub_max = subnormalMagnitudeMax(uf)
        sub_range = "$sub_min to $sub_max"
    else
        sub_range = "None"
    end
    
    println("$bits-bit p$precision | $has_sub        | $sub_count               | $sub_range")
end
```

## Rounding and Projection Examples

### Basic Rounding

```julia
# Demonstrate different rounding modes
uf = AIFloat(5, 2; UnsignedFloat=true, FiniteFloat=true)
test_value = 1.7  # A value not exactly representable

println("Rounding $test_value in 5-bit unsigned format:")
println("  Round up: $(round_up(uf, test_value))")
println("  Round down: $(round_down(uf, test_value))")
println("  Round to zero: $(round_tozero(uf, test_value))")
println("  Round from zero: $(round_fromzero(uf, test_value))")
println("  Round nearest even: $(round_nearesteven(uf, test_value))")
println("  Round nearest odd: $(round_nearestodd(uf, test_value))")

# Show the bracketing values
values = floats(uf)
lower_idx = searchsortedlast(values, test_value)
upper_idx = searchsortedfirst(values, test_value)

if lower_idx > 0 && upper_idx <= length(values)
    println("\nBracketing values:")
    println("  Below: $(values[lower_idx]) (index $lower_idx)")
    println("  Above: $(values[upper_idx]) (index $upper_idx)")
end
```

### High-Precision to Low-Precision Projection

```julia
# Project Float64 values into different AIFloat formats
high_precision_values = [0.1, 0.333, 1.0, 2.718, 3.14159, 10.5]

formats = [
    (AIFloat(4, 2; UnsignedFloat=true, FiniteFloat=true), "4-bit p2"),
    (AIFloat(6, 3; UnsignedFloat=true, FiniteFloat=true), "6-bit p3"), 
    (AIFloat(8, 4; UnsignedFloat=true, FiniteFloat=true), "8-bit p4")
]

println("High-precision to low-precision projection:")
println("Original    | 4-bit p2  | 6-bit p3  | 8-bit p4")
println("------------|-----------|-----------|----------")

for value in high_precision_values
    row = @sprintf("%-10.5f |", value)
    
    for (fmt, name) in formats
        projected = round_nearesteven(fmt, value)
        row *= @sprintf(" %-8.4f |", projected)
    end
    
    println(row)
end
```

## Index and Encoding Examples

### Index Conversion

```julia
# Demonstrate index/offset/code conversions
uf = AIFloat(4, 2; UnsignedFloat=true, FiniteFloat=true)

println("Index/Offset/Code Conversion for 4-bit format:")
println("Julia Index | Offset | Code | Value")
println("------------|--------|------|------")

for julia_idx in 1:length(floats(uf))
    offset = index_to_offset(julia_idx)
    code = index_to_code(4, julia_idx)
    value = floats(uf)[julia_idx]
    
    println(@sprintf("    %2d      |   %2d   | 0x%02X | %s", 
             julia_idx, offset, code, 
             isnan(value) ? "NaN" : string(value)))
end
```

### Special Value Indices

```julia
# Find indices of special values
sf = AIFloat(6, 3; SignedFloat=true, ExtendedFloat=true)

println("Special value indices for 6-bit signed extended format:")
println("  Zero index: $(idxone(sf) - div(nValues(sf), 4))  # Approximate, zero is typically at index 1")
println("  One index: $(idxone(sf))")
println("  Negative one index: $(idxnegone(sf))")
println("  NaN index: $(idxnan(sf))")
println("  +Inf index: $(idxinf(sf))")
println("  -Inf index: $(idxneginf(sf))")

# Verify by looking up actual values
println("\nVerification:")
println("  Value at one index: $(indextovalue(sf, idxone(sf)))")
println("  Value at -one index: $(indextovalue(sf, idxnegone(sf)))")
println("  Value at NaN index: $(indextovalue(sf, idxnan(sf)))")
println("  Value at +Inf index: $(indextovalue(sf, idxinf(sf)))")
println("  Value at -Inf index: $(indextovalue(sf, idxneginf(sf)))")
```

## Deep Learning Application Examples

### Quantization Simulation

```julia
using AIFloats, Printf
using AIFloats: round_nearesteven
# Simulate quantizing neural network weights
original_weights = abs.(randn(10))  # Some random weights

# Different quantization schemes
quantization_formats = [
    (AIFloat(8, 4; UnsignedFloat=true, FiniteFloat=true), "8-bit weights"),
    (AIFloat(6, 3; UnsignedFloat=true, FiniteFloat=true), "6-bit weights"),
    (AIFloat(4, 2; UnsignedFloat=true, FiniteFloat=true), "4-bit weights")
]

println("Weight Quantization Simulation:")
println("Original     | 8-bit      | 6-bit      | 4-bit")
println("-------------|------------|------------|------------")

for weight in original_weights[1:6]  # Show first 6 weights
    row = @sprintf("% 10.6f |", weight)
    
    for (fmt, name) in quantization_formats
        # Clamp to representable range first
        finite_vals = filter(isfinite, floats(fmt))
        min_val, max_val = extrema(finite_vals)
        clamped = clamp(weight, min_val, max_val)
        
        quantized = round_nearesteven(fmt, clamped)
        row *= @sprintf(" % 9.6f |", quantized)
    end
    
    println(row)
end
```

### Activation Range Analysis

```julia
# Analyze representable ranges for different activation quantization
activation_formats = [
    (AIFloat(6, 3; UnsignedFloat=true, FiniteFloat=true), "ReLU 6-bit"),
    (AIFloat(8, 4; UnsignedFloat=true, FiniteFloat=true), "ReLU 8-bit"),
    (AIFloat(6, 3; SignedFloat=true, FiniteFloat=true), "Tanh 6-bit"),
    (AIFloat(8, 4; SignedFloat=true, FiniteFloat=true), "Tanh 8-bit")
]

println("Activation Quantization Range Analysis:")
println("Format      | Min Value  | Max Value  | Resolution near 0")
println("------------|------------|------------|------------------")

for (fmt, name) in activation_formats
    finite_vals = filter(isfinite, floats(fmt))
    min_val = minimum(finite_vals)
    max_val = maximum(finite_vals)
    
    # Find resolution near zero (smallest positive value)
    positive_vals = filter(x -> x > 0, finite_vals)
    resolution = length(positive_vals) > 0 ? minimum(positive_vals) : NaN
    
    println(@sprintf("%-11s | %9.5f | %9.5f | %9.7f", 
             name, min_val, max_val, resolution))
end
```

### Gradient Scaling Example

```julia
# Demonstrate gradient scaling for low-precision training
gradient_format = AIFloat(8, 5; SignedFloat=true, ExtendedFloat=true)

# Simulate some gradients (typically very small)
raw_gradients = [1e-4, -3e-5, 2e-6, -8e-4, 5e-7]
scale_factors = [1, 16, 256, 1024]

println("Gradient Scaling for Low-Precision Training:")
println("Raw Gradient | Scale=1   | Scale=16  | Scale=256 | Scale=1024")
println("-------------|-----------|-----------|-----------|------------")

for grad in raw_gradients
    row = @sprintf("% 9.2e |", grad)
    
    for scale in scale_factors
        scaled_grad = grad * scale
        
        # Quantize the scaled gradient
        finite_vals = filter(isfinite, floats(gradient_format))
        min_val, max_val = extrema(finite_vals)
        
        if abs(scaled_grad) > max_val
            quantized = sign(scaled_grad) * max_val
        else
            quantized = round_nearesteven(gradient_format, scaled_grad)
        end
        
        # Unscale for comparison
        final_grad = quantized / scale
        row *= @sprintf(" % 8.2e |", final_grad)
    end
    
    println(row)
end
```

## Performance Examples

### Lookup Table Generation

```julia
# Generate lookup tables for small formats (useful for hardware implementation)
uf = AIFloat(6, 3; UnsignedFloat=true, FiniteFloat=true)  # 64 values

# Create a ReLU lookup table
relu_table = similar(floats(uf))
for i in eachindex(floats(uf))
    val = floats(uf)[i]
    relu_table[i] = isfinite(val) ? max(0.0f0, val) : val
end

println("ReLU lookup table for 6-bit unsigned format:")
println("Index | Input   | ReLU")
println("------|---------|--------")
for i in 1:min(10, length(floats(uf)))
    println(@sprintf("  %2d  | %7.4f | %7.4f", 
             i, floats(uf)[i], relu_table[i]))
end

# Create a sigmoid approximation table
sigmoid_table = similar(floats(uf))
for i in eachindex(floats(uf))
    val = floats(uf)[i]
    if isfinite(val)
        sigmoid_table[i] = 1.0f0 / (1.0f0 + exp(-val))
    else
        sigmoid_table[i] = isnan(val) ? NaN32 : (val > 0 ? 1.0f0 : 0.0f0)
    end
end

println("\nSigmoid lookup table (first 10 entries):")
println("Index | Input   | Sigmoid")
println("------|---------|--------")
for i in 1:min(10, length(floats(uf)))
    println(@sprintf("  %2d  | %7.4f | %7.4f", 
             i, floats(uf)[i], sigmoid_table[i]))
end
```

### Format Selection Analysis

```julia
# Analyze format choices for different bit budgets
println("Format Selection Analysis:")
println("Bits | Best Unsigned Config | Range          | Best Signed Config   | Range")
println("-----|---------------------|----------------|---------------------|----------------")

for bits in 4:8
    best_unsigned_range = 0.0
    best_unsigned_config = (0, 0)
    best_signed_range = 0.0  
    best_signed_config = (0, 0)
    
    # Try all valid precision values
    for precision in 2:(bits-1)
        # Unsigned format
        try
            uf = AIFloat(bits, precision; UnsignedFloat=true, FiniteFloat=true)
            finite_vals = filter(isfinite, floats(uf))
            range_u = maximum(finite_vals) - minimum(finite_vals)
            if range_u > best_unsigned_range
                best_unsigned_range = range_u
                best_unsigned_config = (bits, precision)
            end
        catch
        end
        
        # Signed format
        try
            sf = AIFloat(bits, precision; SignedFloat=true, FiniteFloat=true)
            finite_vals = filter(isfinite, floats(sf))
            range_s = maximum(finite_vals) - minimum(finite_vals)
            if range_s > best_signed_range
                best_signed_range = range_s
                best_signed_config = (bits, precision)
            end
        catch
        end
    end
    
    println(@sprintf("  %d  | %d-bit p%d          | %13.6f | %d-bit p%d           | %13.6f",
             bits, 
             best_unsigned_config[1], best_unsigned_config[2], best_unsigned_range,
             best_signed_config[1], best_signed_config[2], best_signed_range))
end
```

These examples demonstrate the key capabilities and use cases of AIFloats.jl, from basic format exploration to advanced deep learning applications.