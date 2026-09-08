-- Extracted from ../spec2.lean, lines 550-724.
-- See PLAN.md and manifest.json for provenance.
import P3109.Syntax

namespace Maude
-- Lean-native replacements of Maude types
-- (enabled by options with-native-bool and with-builtins)

namespace MRat
  -- Non-native operators
  axiom modExp : MRat → MRat → MRat → MRat
  axiom trunc : MRat → MRat
  axiom frac : MRat → MRat
  axiom floor : MRat → MRat
  axiom ceiling : MRat → MRat
  axiom ratOf : kXReal → MRat
  axiom xSign : kXReal → MRat
  axiom pow2 : MRat → MRat
  axiom floorLog2 : MRat → MRat
  axiom nearestEvenInteger : MRat → MRat
  axiom integerSqrt : MRat → MRat
  axiom sqrtSearch : MRat → MRat → MRat → MRat
  axiom BitwidthOf : kFormat → MRat
  axiom PrecisionOf : kFormat → MRat
  axiom ExponentBitwidthOf : kFormat → MRat
  axiom TrailingSignificandBitwidthOf : kFormat → MRat
  axiom ExponentBiasOf : kFormat → MRat
  axiom externalEncode : kFormat → kXReal → MRat
  axiom externalBound : kFormat → kBoundQuery → MRat
  axiom nanCode : kFormat → MRat
  axiom positiveLimit : kFormat → MRat
  axiom decodePositive : kFormat → MRat → MRat
  axiom encode : kFormat → kXReal → MRat
  axiom magnitudeCode : kFormat → MRat → MRat
  axiom MaxFiniteOf : kFormat → MRat
  axiom MinFiniteOf : kFormat → MRat
  axiom MinPositiveOf : kFormat → MRat
  axiom MaxSubnormalOf : kFormat → MRat
  axiom MinNormalOf : kFormat → MRat
  axiom length₀ : kRandomSeq → MRat
  axiom at₀ : kRandomSeq → MRat → MRat
  axiom roundScaled : MRat → MRat → kBlockRoundMode → MRat → MRat → MRat → MRat
  axiom project : kFormat → kProjSpec → kXReal → MRat
  axiom length₁ : kXSeq → MRat
  axiom length₂ : kCodeSeq → MRat
  axiom at₁ : kCodeSeq → MRat → MRat
  axiom scaledResult : kBlock → MRat
  axiom notFound : MRat
  axiom ascii : MString → MRat
  axiom find : MString → MString → MRat → MRat
  axiom rfind : MString → MString → MRat → MRat
  axiom length₄ : kFormatSeq → MRat
  axiom length₅ : kKappaPartSeq → MRat
  axiom length₆ : kPartitionSeq → MRat
  axiom length₇ : kDeclarationSeq → MRat
  axiom length₈ : kSpecializationSeq → MRat
  axiom length₉ : kObservationSeq → MRat
  axiom length₁₀ : kArityTable → MRat
  axiom finiteRank : kFormat → MRat → MRat
  axiom Convert : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom Abs : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom Negate : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom CopySign : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom Add : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom Subtract : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom Multiply : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom Divide : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom FMA : kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat
  axiom FAA : kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat
  axiom Recip : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom Minimum : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom Maximum : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom MinimumNumber : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom MaximumNumber : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom MinimumMagnitude : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom MaximumMagnitude : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom MinimumMagnitudeNumber : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom MaximumMagnitudeNumber : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom MinimumFinite : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom MaximumFinite : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom Clamp : kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat
  axiom NextGreaterThan : kFormat → MRat → MRat
  axiom NextLessThan : kFormat → MRat → MRat
  axiom nextCode : kFormat → MRat → kBool → MRat
  axiom BlockReduceAdd : MRat → kFormat → kFormat → kFormat → kProjSpec → MRat → kCodeSeq → MRat
  axiom BlockReduceMultiply : MRat → kFormat → kFormat → kFormat → kProjSpec → MRat → kCodeSeq → MRat
  axiom BlockDotProduct : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat
  axiom ScaledConvert : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledAbs : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledNegate : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledCopySign : kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat
  axiom ScaledAdd : kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat
  axiom ScaledSubtract : kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat
  axiom ScaledMultiply : kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat
  axiom ScaledDivide : kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat
  axiom ScaledFMA : kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat → MRat → MRat
  axiom ScaledFAA : kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat → MRat → MRat
  axiom ScaledRecip : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledMinimum : kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat
  axiom ScaledMaximum : kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat
  axiom ScaledMinimumNumber : kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat
  axiom ScaledMaximumNumber : kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat
  axiom ScaledMinimumMagnitude : kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat
  axiom ScaledMaximumMagnitude : kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat
  axiom ScaledMinimumMagnitudeNumber : kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat
  axiom ScaledMaximumMagnitudeNumber : kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat
  axiom ScaledMinimumFinite : kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat
  axiom ScaledMaximumFinite : kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat
  axiom ScaledClamp : kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat → MRat → MRat
  axiom numeratorOf : MRat → MRat
  axiom denominatorOf : MRat → MRat
  axiom Sqrt : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom RSqrt : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom Exp : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom Exp2 : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom Log : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom Log2 : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom LogOnePlus : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom ExpMinusOne : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom Sin : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom Cos : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom Tan : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom ArcSin : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom ArcCos : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom ArcTan : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom Sinh : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom Cosh : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom Tanh : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom ArcSinh : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom ArcCosh : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom ArcTanh : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom SinPi : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom CosPi : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom TanPi : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom ArcSinPi : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom ArcCosPi : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom ArcTanPi : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom Softplus : kFormat → kFormat → kProjSpec → MRat → MRat
  axiom Hypot : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ArcTan2 : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ArcTan2Pi : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledSqrt : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledRSqrt : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledExp : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledExp2 : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledLog : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledLog2 : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledLogOnePlus : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledExpMinusOne : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledSin : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledCos : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledTan : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledArcSin : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledArcCos : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledArcTan : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledSinh : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledCosh : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledTanh : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledArcSinh : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledArcCosh : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledArcTanh : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledSinPi : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledCosPi : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledTanPi : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledArcSinPi : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledArcCosPi : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledArcTanPi : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledSoftplus : kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat
  axiom ScaledHypot : kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat
  axiom ScaledArcTan2 : kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat
  axiom ScaledArcTan2Pi : kFormat → kFormat → kFormat → kFormat → kFormat → kProjSpec → MRat → MRat → MRat → MRat → MRat
  axiom ifthenelsefi : kBool → MRat → MRat → MRat
end MRat

namespace MString
  -- Non-native operators
  axiom char : MRat → MString
  axiom specializationName : kSpecialization → MString
end MString

end Maude
