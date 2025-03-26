"""
    prenormal

A magnitude is prenormal (before all normal magnitudes) if it is a subnormal magnitude or it is zero.

A value is prenormal if abs(value) is a prenormal magnitude.

There are 
- `2^(precision - 1)` prenormal *magnitudes* in a BinaryKpP.
    - n_prenormal_magnitudes(precision) = 2^(precision - 1) * (precision > 1)
- `2^(precision - 1)` prenormal *values* in with Unsigned BinaryKpP.
- `2^precision - 1`   prenormal *values* in with Signed BinaryKpP.

The smallest nonzero prenormal magnitude is the smallest subnormal magnitude.
- subnormal_min(bitwidth, precision) = 4 * 2.0^(-precision - 2.0^(bitwidth - 1 - precision))
- subnormal_min(bitwidth, fracbits) =  2.0^(1- fracbits - (2.0^(bitwidth - fracbits - 2)))

One may compute all of the prenormal magnitudes
```
prenormal_magnitudes(bitwidth, precision) =
           [i * subnormal_min(bitwidth, precision) for i in 0:(n_prenormal_magnitudes(precision) - 1)]
```
see  [subnormals](@ref) [subnormal](@ref)
""" prenormal

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

see [subnormal](@ref) [prenormal](@ref)
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

There are 
- `2^(precision - 1) - 1` subnormal *magnitudes* in a BinaryKpP.
   - n_subnormal_magnitudes(precision) = (2^(precision - 1) - 1) * (precision > 1)
- `2^(precision - 1) - 1` subnormal *values* in with Unsigned BinaryKpP.
- `2^precision - 2`       subnormal *values* in with Signed BinaryKpP.

The smallest subnormal magnitude (precision > 1, fracbits > 0, otherwise no subnormals)
- subnormal_min(bitwidth, precision) = 4 * 2.0^(-precision - 2.0^(bitwidth - 1 - precision))
- subnormal_min(bitwidth, fracbits) =  2.0^(1- fracbits - (2.0^(bitwidth - fracbits - 2)))

The initial subnormal value (`== nextafter(zero(T))`) is assigned
(`(1 / 2^(fraction_bits)) * exponent_min`).
```
subnormal_min(bitwidth, precision) = 4 * 2.0^(-precision - 2.0^(bitwidth - 1 - precision))
subnormal_min(bitwidth, fracbits) =  2.0^(1-fracbits - (2.0^(bitwidth - fracbits - 2)))
```
- successive subnormals are successive integer multiples of the initial subnormal magnitude.
One may compute all of the positive subnormals
```
subnormal_magnitudes(bitwidth, precision) = 
    [i * subnormal_min(bitwidth, precision) for i in 1:n_subnormal_magnitudes(precision)]
```
see  [subnormals](@ref) [prenormal](@ref) [fractionals](@ref)

""" subnormal

"""
    fractionals

The fractionals are the significands of prenormal values. They are the prenormals unscaled by exponent_min. 

```
fractionals(precision) =
    [i * (1 / 2^(precision - 1)) for i in 0:(n_prenormal_magnitudes(precision) - 1)]
```
see  [prenormal](@ref) [significands](@ref) [subnormals](@ref) 
""" fractionals

"""
    significands

The significands are normalized fractionals; the implicit bit is 0b1 and used.

```
significands(precision) = fractionals(precision) .+ 1
```
see  [significand](@ref) [prenormal](@ref) [fractionals](@ref) [subnormals](@ref) 
""" significands

"""
    exponent

The exponent is the interpretation of the exponent bitfield of a BinaryKpP float.
Where the exponent bitfield is zero, one has a subnormal value and the exponent == exponent_min (`-(2^(ebits-1)-1)`; the exponent conveys a subnormal value which is scaled as if the exponent bit field were 1.

An exponent field of zero is a subnormal value; it is valued as if the implicit bit were shifted into the exponent field (and out of the significand).

It is valued as `2^(resolved_ebitfield  - bias)` where the `bias = 2^(ebits - 1) - 1` and 
`resolved_ebitfield = iszero(ebitfield) ? 1 : ebitfield`

```math
exponent_value = 2^(ebits - bias)
```
``exponent_value = 2^(ebits - 2^((ebits - 1) - 1))``
""" exponent

"""
    significand

The significand is the interpretation of the significand bitfield of a BinaryKpP float.
The significand includes an implicit leading integer bit, all explicit bits of the significand are fractional bits. For normal values, the implicit leading integer bit is 0b1; for subnormal values, the implicit leading integer bit is 0b0. Special values {0, NaN, ±∞} are neither normal nor subnormal, they are interpreted directly.

see [specials](@ref) [exponent](@ref) [significands](@ref)
""" significand

"""
    specials

All P3109 conformant value sets include the special values {0, NaN}. There is one 0 encoding and one NaN encoding (note this is unlike IEEE 754). All P3109 conformant value sets encode 0 with all zero bits. All P3109 conformant signed value sets encode NaN with the sign bit 0b1 and all other bits zero. Unsigned value sets encode NaN with all one bits.

For signed value sets, +Infinity is encoded to as the largest positive encoding, it precedes NaN; and -Infinity is encoded setting the sign bit of the positive Infinity encoding to 0b1; it is the largest negative encoding, and the largest absolute encoding. Unsigned value sets encode +Infinity as the penultimate value, preceding NaN.
""" specials

"""
    UnsignedFloat

An Unsigned, Finite microfloat value set has the special values {Zero, NaN} and positive finite values (subnormal and normal; unless precision == 1 then all values are normal). An Unsigned BinaryKpP (1<K<16, 0<P<K) [ufBinaryKpP] has no sign bit; that available position is assigned to the the exponent, giving greater dynamic range to the format. This benefits training without causing difficulty with inference. If two unsigned modalities were supported, with one assigning the available bit to the significand, that modality would be more suitable for inference where extra precision is of import. Nonetheless, on balance, the extension of dynamic range has greater benefit.

The exponent bitfield in an Unsigned BinaryKpP has K-P+1 bits.
""" UnsignedFloat

"""
    SignedFloat

""" SignedFloat

"""
    Magnitude Sequence Construction

The magnitude sequence is constructed from the significand and exponent bitfields of a BinaryKpP float. The significand is interpreted the value of its implicit integral bit plus its explicit fractional bits, the exponent is interpreted as a power of two. The magnitude is the product of the significand and the exponent.

There are `2^(precision - 1) - 1` subnormal magnitudes, and `2^(precision - 1)` prenormal magnitudes.

This leaves `2^bits - nzeros - ninfs` normal values, and `(2^bits - nzeros - ninfs) >> 1` normal_magnitudes.

There are `2^expbits` exponent values (`== 2^(bits - sigbits)`).
How many elements are there assigned to a single exponent value?
`div( (2^bits- 3) >> 1, 2^(bits - sigbits)))` for Signed Extended formats

each binade has div(cfg.n_values >> 1, cfg.n_exponent_values) entries
after the prenormals, 
there are cfg.unbiased_exponent_max - cfg.unbiased_exponent_min + 1 magnitude binades


each binade runs through n_fraction_magnitudes + 1 significands
there are div(cfg.n_values >> 1, cfg.n_fraction_magnitudes+1) magnitudebinades

""" MagnitudeSequenceConstruction

"""
    Magnitude Sequence Construction

""" MagnitudeSequenceConstruction
