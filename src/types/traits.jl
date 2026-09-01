# format traits derived from the four parameters
#
# Everything here is a pure function of (K, P, S, D) and must constant-fold.
# Trait values are computed in Int, not IntParam: shifts like 1 << (K - P)
# reach 2^13 at K = 16, past Int8.

"""
    ExponentBiasOf(format)

The exponent bias `B`: `2^(K-P-1)` for a signed format, `2^(K-P)` for unsigned.

Dropping the sign bit hands its bit to the exponent, doubling the bias — that is
the unsigned formats' extra dynamic range. The biased exponent field `Eb` maps to
the unbiased binade exponent `Eb - B`, so the normal exponent range is symmetric.

# Examples

```jldoctest
julia> ExponentBiasOf(Binary(8, 4, SIGNED, FINITE))
8

julia> ExponentBiasOf(Binary(8, 4, UNSIGNED, FINITE))
16
```
"""
ExponentBiasOf(::Type{Binary{K,P,S,D}}) where {K,P,S,D} =
    S ? 1 << (Int(K) - Int(P) - 1) : 1 << (Int(K) - Int(P))

"""
    ExponentBitwidthOf(format)

The number of exponent bits: `(K - S) - (P - 1)` — what remains after the sign
bit (if any) and the stored significand bits.

# Examples

```jldoctest
julia> ExponentBitwidthOf(Binary(8, 4, SIGNED, FINITE))
4

julia> ExponentBitwidthOf(Binary(8, 4, UNSIGNED, FINITE))
5
```
"""
ExponentBitwidthOf(::Type{Binary{K,P,S,D}}) where {K,P,S,D} =
    (Int(K) - Int(S)) - (Int(P) - 1)

# the mask primitive, built BY COMPLEMENT — shift down from typemax, never up
# from one. UInt8(1) << 8 == 0 in Julia, and the grid always contains a format
# whose K equals its storage width (K = 8 on UInt8, K = 16 on UInt16), so that
# is structural, not an edge. Here the shift amount is width - K in
# [0, width - 1]: the pathological amount is unreachable by construction.
_unitmask(::Type{U}, K::Integer) where {U<:Unsigned} =
    typemax(U) >> (8 * sizeof(U) - Int(K))

"""
    codemask(format)

The mask of the format's `K` code bits in its storage unit ([`CodeType`](@ref)):
`0xff` for `K = 8`, `0x03ff` for `K = 10`.

Not exported; call it as `AIFloats.codemask`.
"""
codemask(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = _unitmask(CodeType(K), K)

"""
    signmask(format)

The sign bit's mask in the storage unit: `one(CodeType) << (K - 1)`.

For a signed format this isolates the sign; for an unsigned format the same bit
position is ordinary magnitude. Not exported; call it as `AIFloats.signmask`.
"""
signmask(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = one(CodeType(K)) << (Int(K) - 1)

"""
    orderkeytype(format)

The unsigned type that holds a total-order key for the format's datums.

One key wider than the code: a format has `2^K` code points mapping to keys
`1:2^K` (key `0` is reserved for NaN, which sorts first), so the key type must
not wrap at `2^K` — `UInt16` for `UInt8`-coded formats, `UInt32` for
`UInt16`-coded ones. Not exported.
"""
orderkeytype(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = _orderkeytype(CodeType(K))
_orderkeytype(::Type{UInt8}) = UInt16
_orderkeytype(::Type{UInt16}) = UInt32