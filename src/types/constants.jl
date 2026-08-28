const FiniteChar = Char(0x29DE)
const FiniteString = string(FiniteChar)
const InfinityChar = Char(0x221E)
const InfinityString = string(InfinityChar)

const PositiveInfinityString = "+" * InfinityString
const NegativeInfinityString = "-" * InfinityString
const PositiveFiniteString = "+" * FiniteString
const NonNegativeFiniteString = "₀" * "+" * FiniteString
const NegativeFiniteString = "-" * FiniteString

const UnsignedExtendedString = InfinityString
const SignedExtendedString = "±" * InfinityString
const UnsignedFiniteString = FiniteString
const SignedFiniteString = "±" * FiniteString

const ΣUnsigned = false
const ΣSigned = true

const ΔFinite = false
const ΔExtended = true

"""
    IntParam

`Int8` — the integer type in which a format's bitwidth `K` and precision `P` are stored.

[`Binary`](@ref) narrows both to this type, so `Binary(16, 10, SIGNED, FINITE)` and
`Binary(Int32(16), Int32(10), SIGNED, FINITE)` are the same type.
"""
const IntParam = Int8

const ByteCode = UInt8
const WordCode = UInt16
const CodePoint = Union{ByteCode, WordCode}
const ByteValue = Float32
const WordValue = Float64
const TwoWordValue = Float128
const FloatValue = Union{ByteValue, WordValue, BFloat16}

# the supported bitwidth range: K == KMAX is the largest code point that fits
# a WordCode, and every ported algorithm is verified on this range
const KMIN = IntParam(3)
const KMAX = IntParam(16)

# default random-bit budget N for the stochastic rounding modes
const DEFAULT_RBITS = 8
