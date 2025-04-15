*this development immediately pertains to binaryKpP, where P ∈ {2..K-1}.[^a]*

each finite value in the [nonnegative portion of a] value sequence is a arithmetic composition of three components:
1. a trailing significand (a nonnegative integer in the range [0, 2^P-1])
   - this is a fractional binary value
2. an implicit leading bit {0b0, 0b1}
   - the *finite* value is **subnormal** when the implicit bit is 0b0 and the trailing significand is non-zero
   - the *finite* value is **normal** when the implicit bit is 1b1, whatever the trailing significand may be.

3. an exponent (stored as a nonnegative integer in the range [0, 2^(K-P)-1])
   - the exponent is biased (all values >= 0)
   -  to recover its constructive value, subtract the bias (2^(K-P-1)-1) from the biased value.
   -  the exponent acts multiplicatively as `2^exponent`

each finite value in the [nonnegative portion of a] value sequence is determined with:
    `value = (2^unbiased_exponent) * (implicit_bit + (trailing_significand_bits / 2^P))`

 


[^a]: Floating-point value sequences that have no subnormal values are eccentric.
