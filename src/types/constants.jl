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

const IntParam = Int8

const ByteCode = UInt8
const WordCode = UInt16
const CodePoint = Union{ByteCode, WordCode
}
const ByteValue = Float32
const WordValue = Float64
const TwoWordValue = Float128
const FloatValue = Union{ByteValue, WordValue, BFloat16}
