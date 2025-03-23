"""
    subnormals

P3109 value sets shall include subnormals.

IEEE Std 754 value sets include subnormals. 
- A value with trailing significand field T and exponent field E is interpreted as `1.T × 2^(E−bias)` except when all bits of the exponent bitfield are 0, in which case the value is subnormal (or zero), interpreted as `0.T × 2^exponent_min`.

- Subnormal numbers extend the dynamic range of floating-point values and induce equal quantization steps close to zero. They can be useful when training models, where it is common to represent near-zero values for gradients. 

- Subnormals can also be useful to represent random values drawn from certain distributions. For example, model weights are initialized to small random values at training.

- Subnormals are uniformly spaced around zero, and values near zero are more probable values drawn from Gaussian-like distributions. 

- Finally, formats with narrow exponent widths necessarily have a limited range; subnormals extend this range by a power of 2 for every bit in the trailing significand.

    - from the P3109 Interim Report (v3)

see [subnormal](@ref)
""" subnormals


"""
    subnormal

`Zero` is a special value, it is neither normal nor subnormal. [^1](The other special values are `±∞` and `NaN`.)

Including zero (which is neither normal nor subnormal) and the positive subnormals only, there are P-1 positive subnormals occuring in a BinaryryKpP float (of bitwidth **K** and precision **P**). 

A value is subnormal (as defined) where the value
1) is coded with its exponent bitfield cleared to zero
2) is not zero [(1) also holds for zero values]

The implicit bit of any subnormal value is 0b0; it does not alter the numeric value imputed.
- all subnormals are formed of fractional bits and scaled by exponent_min, the least unbiased exponent value.
- all subnormals are formed over the available combinations of fractional bits, scaled by exponnent_min.
- there are  `2^(precision - 1) - 1 == 2^fraction_bits - 1` positive subnormals in a BinaryKpP float

The initial subnormal value (`== nextafter(zero(T))`) is assigned (`(1 / 2^(fraction_bits)) * exponent_min`).
- successive subnormals are successive integer multiples of the initial subnormal value.
One may compute all of the positive subnormals with `[i * initial_subnormal_value for i in 1:2^prec ]` (or   `ith * initial_subnormal_value`)

```

subnormal_min(bitwidth, precision) = (1 / 2^(precision - 1)) * 2.0^(-(2.0^(bitwidth + (-1-precision )) - 1))
# maple
subnormal_min(bitwidth, precision) = 4 * 2.0^(-precision - 2.0^(bitwidth - 1 - precision))
subnormal_min(bitwidth, fracbits) =  2.0^(1-fracbits - ((2.0^(bitwidth - fracbits)) / 4))
subnormal_min(bitwidth, fracbits) =  2.0^(1-fracbits - (2.0^(bitwidth - fracbits - 2)))

```

```
julia> intial_subnormal_value = (1 / 2^(fraction_bits)) * 2.0^(-15)
7.62939453125e-6

julia> [i * intial_subnormal_value for i in 0:(2^(prec-1)-1) ]
4-element Vector{Float64}:
 0.0
 7.62939453125e-6
 1.52587890625e-5
 2.288818359375e-5
 ```
see  [subnormals](@ref)

""" subnormal
