# Overview

## Computational Paradigm

AIFloats implements a family of reduced-precision floating-point formats specifically engineered for machine learning workloads. Unlike traditional IEEE 754 formats, these representations prioritize **computational continuity** over numerical precision, eliminating exception states that disrupt gradient flow during training.

## Bit Allocation Strategy

The fundamental design principle allocates bits according to the inequality:

$$\text{bitwidth} \geq \text{precision} + \text{signbit} + \text{minimum\_exponent\_bits}$$

Where:
- **Signed formats**: `1 ≤ precision < bitwidth ≤ 15`  
- **Unsigned formats**: `1 ≤ precision ≤ bitwidth ≤ 15`

This constraint ensures sufficient exponent range while maximizing significand precision within the bit budget.

### Exponent Field Sizing

The exponent field width follows the relation:

```julia
nbits_exp(T::Type{<:AbstractSigned}) = nbits(T) - nbits_sig(T)
nbits_exp(T::Type{<:AbstractUnsigned}) = nbits(T) - nbits_sig(T) + 1
```

Unsigned formats gain an additional exponent bit by eliminating the sign bit, providing extended dynamic range for magnitude-only representations.

## Value Domain Partitioning

Each format partitions its $2^{\text{bitwidth}}$ encodings into distinct regions:

### Prenormal Region
Contains zero plus subnormal magnitudes where the implicit leading bit is 0:
- **Zero**: Always encoded as `0b0...0`
- **Subnormal values**: $\text{significand} \times 2^{\text{exp\_min}}$ where significand $\in (0, 1)$

### Normal Region  
Standard IEEE-style representation with implicit leading 1:
- **Normal values**: $(1 + \text{fraction}) \times 2^{\text{unbiased\_exponent}}$
- **Biased exponents**: Raw exponent field offset by format-specific bias

### Special Values
- **NaN**: Deterministically placed opposite zero encoding
- **Infinities** (Extended formats only): Maximum exponent with specific significand patterns

## Exception-Free Arithmetic

The critical design innovation eliminates computational exceptions through:

1. **Deterministic NaN placement**: No runtime NaN generation from valid operands
2. **Saturation semantics**: Overflow clamps to finite maximum rather than infinity
3. **Continuous gradient flow**: No exceptional states interrupt backpropagation

This approach ensures that training dynamics remain stable even with aggressive precision reduction.

## Memory Layout Optimization

AIFloats employs cache-aligned allocation patterns to maximize throughput:

```julia
# Values and codes use aligned allocation for L1 cache efficiency
floats = memalign_clear(Float64, nvalues)  # Cache-line aligned
codes = memalign_clear(UInt8, nvalues)     # Corresponding encodings
```

The dual-array structure (values, encodings) enables both:
- **Direct computation**: Operating on decoded floating-point values
- **Table lookup**: Ultra-fast encoding/decoding via array indexing

## Precision vs. Range Trade-offs

Format selection involves balancing numerical precision against dynamic range:

| Format | Bitwidth | Precision | Range | Use Case |
|--------|----------|-----------|-------|----------|
| `sf4p2` | 4 | 2 | ±1.5 | Activation gradients |
| `uf6p3` | 6 | 3 | [0, 7.5] | Attention weights |
| `se8p4` | 8 | 4 | ±240 | Feature maps |

The format taxonomy enables fine-grained optimization for specific tensor roles within neural network architectures.

## Performance Characteristics

AIFloats achieve computational efficiency through multiple pathways:

- **Small formats (≤6 bits)**: Complete lookup tables for all unary/binary operations
- **Medium formats (7-8 bits)**: Hybrid approach with selective table acceleration  
- **Large formats (≥9 bits)**: Direct computation with efficient projection

This tiered strategy minimizes memory footprint while maximizing computational throughput across the precision spectrum.