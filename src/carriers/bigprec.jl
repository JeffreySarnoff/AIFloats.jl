# derived MPFR working precision — never a flat constant
#
# An exact sum of dyadic terms needs (exponent spread) + (max significand
# width) + margin bits. A format's spread reaches 2B + P. Every flat "wide
# enough" constant in SmallFloats' history was ample at K ≤ 8 and silently
# wrong later, in the one direction no test can see: a truncated "exact"
# BigFloat is the worst failure mode available.

"""
    bigprec(F)

Working MPFR precision sufficient for exact arithmetic on `F`'s datums:
`2(B + P) + 64`. Not exported.
"""
bigprec(::Type{F}) where {F<:Binary} =
    2 * (ExponentBiasOf(F) + Int(PrecisionOf(F))) + 64
bigprec(::Type{BV}) where {BV<:BinaryValue} = bigprec(BinaryFormatOf(BV))