"""Qualified source-compatible names; parameters precede integer-code operands."""
module SpecAPI
import ..P3109Reference as P
include("generated_operations.jl")

public CompareLess,
    CompareLessEqual,
    CompareEqual,
    CompareGreater,
    CompareGreaterEqual,
    TotalOrder,
    IsZero,
    IsOne,
    IsNaN,
    IsInfinite,
    IsFinite,
    IsSignMinus,
    IsNormal,
    IsSubnormal,
    Class,
    BitwidthOf,
    PrecisionOf,
    ExponentBitwidthOf,
    TrailingSignificandBitwidthOf,
    ExponentBiasOf,
    SignednessOf,
    DomainOf,
    MaxFiniteOf,
    MinFiniteOf,
    MinPositiveOf,
    MaxSubnormalOf,
    MinNormalOf,
    RoundOf,
    SatOf,
    NextGreaterThan,
    NextLessThan,
    ConvertFromBlock,
    ConvertToBlock,
    ConvertToBlockMaxAbsFinite,
    BlockReduceAdd,
    BlockReduceMultiply,
    BlockDotProduct

CompareLess(f, g, c, d) = P.mathematical_less(P.decode(f, c), P.decode(g, d))
CompareLessEqual(f, g, c, d) = P.mathematical_le(P.decode(f, c), P.decode(g, d))
CompareEqual(f, g, c, d) = P.mathematical_equal(P.decode(f, c), P.decode(g, d))
CompareGreater(f, g, c, d) = CompareLess(g, f, d, c)
CompareGreaterEqual(f, g, c, d) = CompareLessEqual(g, f, d, c)
TotalOrder(f, g, c, d) = P.total_order(f, g, c, d)
IsZero(f, c) = P.mathematical_equal(P.decode(f, c), P.finite(0))
IsOne(f, c) = P.mathematical_equal(P.decode(f, c), P.finite(1))
IsNaN(f, c) = P.decoded_predicate(P.is_nan, :xNaN, f, c)
IsInfinite(f, c) = P.decoded_predicate(P.is_infinite, :xInfinite, f, c)
IsFinite(f, c) = P.decoded_predicate(P.is_finite, :xFinite, f, c)
IsSignMinus(f, c) = P.decoded_predicate(P.is_negative, :xMinus, f, c)
IsNormal(f, c) = P.is_normal(f, c)
IsSubnormal(f, c) = P.is_subnormal(f, c)
Class(f, c) = P.classify(f, c)
BitwidthOf(f) = P.bitwidth(f)
PrecisionOf(f) = P.precision_bits(f)
ExponentBitwidthOf(f) = P.exponent_bits(f)
TrailingSignificandBitwidthOf(f) = P.trailing_bits(f)
ExponentBiasOf(f) = P.exponent_bias(f)
SignednessOf(f) = P.signedness(f)
DomainOf(f) = P.domain(f)
MaxFiniteOf(f) = P.max_finite_code(f)
MinFiniteOf(f) = P.min_finite_code(f)
MinPositiveOf(f) = P.min_positive_code(f)
MaxSubnormalOf(f) = P.max_subnormal_code(f)
MinNormalOf(f) = P.min_normal_code(f)
RoundOf(p) = p.rounding
SatOf(p) = p.saturation
NextGreaterThan(f, c) = P.next_code(f, c, true)
NextLessThan(f, c) = P.next_code(f, c, false)
ConvertFromBlock(n, fs, fx, fr, p, s, cs) = P.convert_from_block(n, fs, fx, fr, p, s, cs)
ConvertToBlock(n, fx, fs, fr, p, cs, s) = P.convert_to_block(n, fx, fs, fr, p, cs, s)
ConvertToBlockMaxAbsFinite(n, fx, fs, fr, sp, p, cs) =
    P.convert_to_block_max_abs(n, fx, fs, fr, sp, p, cs)
BlockReduceAdd(n, fs, fx, fr, p, s, cs) =
    P.block_reduce(P.add, P.finite(0), n, fs, fx, fr, p, s, cs)
BlockReduceMultiply(n, fs, fx, fr, p, s, cs) =
    P.block_reduce(P.multiply, P.finite(1), n, fs, fx, fr, p, s, cs)
BlockDotProduct(n, fsx, fx, fsy, fy, fr, p, sx, xs, sy, ys) =
    P.block_dot(n, fsx, fx, fsy, fy, fr, p, sx, xs, sy, ys)
end
