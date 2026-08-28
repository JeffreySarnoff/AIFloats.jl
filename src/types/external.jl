"""
    binary16

`Float16` under its IEEE 754 name.

Provided so that established formats can be named the same way P3109 formats are.
"""
const binary16 = Float16

"""
    binary32

`Float32` under its IEEE 754 name. See [`binary16`](@ref).
"""
const binary32 = Float32

"""
    binary64

`Float64` under its IEEE 754 name. See [`binary16`](@ref).
"""
const binary64 = Float64

"""
    binary128

`Quadmath.Float128` under its IEEE 754 name. See [`binary16`](@ref).

This is also the type [`ValueType`](@ref) selects for formats wider than 10 bits.
"""
const binary128 = Float128

"""
    bfloat16

`BFloat16s.BFloat16`, the 16-bit brain float.

Not an IEEE 754 format: it keeps `Float32`'s 8 exponent bits and cuts the significand to 8,
trading precision for range.
"""
const bfloat16 = BFloat16
