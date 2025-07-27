# Construction Methods

AIFloats provides dual construction pathways that accommodate both abstract type specifications and direct parameter-based instantiation, enabling flexible integration into diverse computational workflows.

## Primary Constructor Interface

### Parametric Construction

The canonical construction method accepts bitwidth, precision, and domain qualifiers:

```julia
AIFloat(bitwidth::Int, precision::Int, signedness::Symbol, domain::Symbol)
```

**Parameter Validation**: The constructor enforces strict mathematical constraints during instantiation:

```julia
# Signed format constraints: sign bit reduces available width
signedness == :signed && bitwidth > precision  # Minimum: 3 bits
# Unsigned format constraints: full width available for mag
signedness == :unsigned && bitwidth >= precision  # Minimum: 2 bits
```

**Domain Specification**: The domain qualifier controls special value semantics:
- `:finite` → Finite reals ∪ {NaN}
- `:extended` → Finite reals ∪ {NaN, ±∞} or {NaN, +∞}

### Construction Examples

```julia
# 4-bit signed finite: [-1.5, +1.5] ∪ {NaN}
sf4p2 = AIFloat(4, 2, :signed, :finite)

# 6-bit unsigned extended: [0, 7.875] ∪ {+∞, NaN}  
ue6p3 = AIFloat(6, 3, :unsigned, :extended)

# 8-bit signed extended: maximum dynamic range with infinities
se8p4 = AIFloat(8, 4, :signed, :extended)
```

## Abstract Type-Based Construction

### Type-Driven Instantiation

For generic programming scenarios, construction from abstract types enables parametric algorithms:

```julia
# Construct from parameterized abstract type
T = AkoSignedFinite{5, 3}
sf5p3 = AIFloat(T)

# Extract parameters for algorithmic construction
bits, precision = n_bits(T), n_sig_bits(T)
family_member = AIFloat(bits, precision, :signed, :finite)
```

This approach facilitates type-stable generic functions that operate across format families.

## Internal Construction Pipeline

### Memory Allocation Strategy

The construction process employs cache-aligned allocation for optimal memory access patterns:

```julia
function ConstructAIFloat(bitwidth::Int, sigbits::Int; plusminus::Bool, extended::Bool)
    F = typeforfloat(bitwidth)  # Float64 or Float128 based on precision requirements
    S = typeforcode(bitwidth)   # UInt8 or UInt16 based on encoding width
    
    # Generate canonical sequences with aligned allocation
    codes = encoding_seq(S, bitwidth)           # 0x00, 0x01, ..., 0xFF
    floats = value_seq(concrete_type, ...)      # Corresponding FP values
    
    return ConcreteType{bitwidth, sigbits, F, S}(floats, codes)
end
```

### Value Sequence Generation

The constructor synthesizes mathematically precise value sequences through multi-stage computation:

#### Stage 1: Magnitude Foundation
```julia
function mag_foundation_seq(::Type{T}) where {T<:AbstractAIFloat}
    # Generate normalized significand sequence
    significands = significand_mags(T)
    
    # Compute scaled exponent values with extended precision
    exp_values = map(x -> Float128(2)^x, exp_unbiased_mag_strides(T))
    
    # Element-wise scaling: significand × 2^exponent
    scaled_mags = significands .* exp_values
    
    return convert_to_working_precision(scaled_mags, T)
end
```

#### Stage 2: Sign and Special Value Integration
```julia
function value_seq(::Type{T}) where {T<:AkoSignedFinite}
    nonneg_mags = mag_foundation_seq(T)
    
    # Generate negative counterparts with sign symmetry
    neg_mags = -nonneg_mags
    neg_mags[1] = convert(working_type, NaN)  # NaN at symmetric position
    
    return vcat(nonneg_mags, neg_mags)
end
```

This approach ensures bit-exact reproducibility across platforms while maintaining numerical accuracy.

## Format-Specific Construction Details

### Exponent Bias Computation

The bias calculation establishes symmetric exponent ranges:

```julia
# Signed formats: traditional IEEE-style bias
exp_bias(::Type{<:AbstractSigned{Bits, SigBits}}) = 2^(Bits - SigBits - 1)

# Unsigned formats: enhanced bias due to additional exponent bit  
exp_bias(::Type{<:AbstractUnsigned{Bits, SigBits}}) = 2^(Bits - SigBits)
```

This asymmetric bias allocation maximizes dynamic range utilization within bit budget constraints.

### Subnormal Threshold Determination

The prenormal/normal boundary is established through precision-dependent scaling:

```julia
# Smallest normal mag: 2^(exp_min) where implicit bit = 1
mag_normal_min(T) = exp_value_min(T)

# Largest subnormal mag: (1 - ε) × 2^(exp_min) where ε = ULP
mag_subnormal_max(T) = (1 - 1/n_prenormal_mags(T)) * exp_subnormal_value(T)
```

This boundary placement ensures maximal precision utilization in the critical near-zero region.

## Construction Validation and Error Handling

### Parameter Range Validation

The constructor performs comprehensive parameter validation with informative error messages:

```julia
function validate_construction_parameters(bitwidth, precision, signedness)
    # Bit budget validation
    min_bitwidth = (signedness == :signed) ? precision + 2 : precision + 1
    bitwidth >= min_bitwidth || throw(ArgumentError(
        "Insufficient bit budget: $bitwidth < $min_bitwidth for $signedness format"))
    
    # Precision constraints
    1 ≤ precision ≤ 15 || throw(ArgumentError(
        "Precision out of range: $precision ∉ [1, 15]"))
    
    # Implementation limits
    bitwidth ≤ 15 || throw(ArgumentError(
        "Bitwidth exceeds maximum: $bitwidth > 15"))
end
```

### Type Consistency Verification

Post-construction verification ensures mathematical consistency:

```julia
function verify_construction_invariants(aifloat::AbstractAIFloat)
    @assert length(floats(aifloat)) == n_values(typeof(aifloat))
    @assert length(codes(aifloat)) == n_values(typeof(aifloat))
    @assert issorted(floats(aifloat)[1:n_mags(typeof(aifloat))])  # Magnitude ordering
    @assert codes(aifloat)[1] == 0x00  # Zero encoding
    @assert isnan(floats(aifloat)[end])  # NaN placement
end
```

This validation layer prevents subtle construction errors that could compromise numerical correctness.

## Performance Characteristics

### Construction Complexity

- **Time Complexity**: O(2^bitwidth) for value sequence generation
- **Space Complexity**: O(2^bitwidth) for dual array storage  
- **Cache Efficiency**: Aligned allocation enables optimal memory access patterns

### Optimization Strategies

For performance-critical applications, consider:

1. **Pre-constructed formats**: Cache frequently used format instances
2. **Type-stable construction**: Use abstract type parameters when possible
3. **Batch construction**: Amortize validation overhead across multiple instances

The construction system balances mathematical precision, computational efficiency, and programmer ergonomics to support diverse floating-point arithmetic applications.