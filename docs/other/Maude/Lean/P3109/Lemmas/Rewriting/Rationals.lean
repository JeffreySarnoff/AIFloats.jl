-- Extracted from ../spec2.lean, lines 16528-20395.
-- See PLAN.md and manifest.json for provenance.
import P3109.Lemmas.Rewriting.Conformance

namespace Maude
namespace MRat

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_modExp₀ {a b a₁ a₂ : MRat} : MRat.rw_star a b →
      MRat.rw_star (modExp a a₁ a₂) (modExp b a₁ a₂)
    | .step h => .step (rw_one.sub_modExp₀ h)
    | .refl h => .refl (eqe_modExp h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_modExp₀ h₀) (rw_star_sub_modExp₀ h₁)
  theorem rw_star_sub_modExp₁ {a₀ a b a₂ : MRat} : MRat.rw_star a b →
      MRat.rw_star (modExp a₀ a a₂) (modExp a₀ b a₂)
    | .step h => .step (rw_one.sub_modExp₁ h)
    | .refl h => .refl (eqe_modExp rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_modExp₁ h₀) (rw_star_sub_modExp₁ h₁)
  theorem rw_star_sub_modExp₂ {a₀ a₁ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (modExp a₀ a₁ a) (modExp a₀ a₁ b)
    | .step h => .step (rw_one.sub_modExp₂ h)
    | .refl h => .refl (eqe_modExp rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_modExp₂ h₀) (rw_star_sub_modExp₂ h₁)
  theorem rw_star_sub_trunc {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (trunc a) (trunc b)
    | .step h => .step (rw_one.sub_trunc h)
    | .refl h => .refl (eqe_trunc h)
    | .trans h₀ h₁ => .trans (rw_star_sub_trunc h₀) (rw_star_sub_trunc h₁)
  theorem rw_star_sub_frac {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (frac a) (frac b)
    | .step h => .step (rw_one.sub_frac h)
    | .refl h => .refl (eqe_frac h)
    | .trans h₀ h₁ => .trans (rw_star_sub_frac h₀) (rw_star_sub_frac h₁)
  theorem rw_star_sub_floor {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (floor a) (floor b)
    | .step h => .step (rw_one.sub_floor h)
    | .refl h => .refl (eqe_floor h)
    | .trans h₀ h₁ => .trans (rw_star_sub_floor h₀) (rw_star_sub_floor h₁)
  theorem rw_star_sub_ceiling {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ceiling a) (ceiling b)
    | .step h => .step (rw_one.sub_ceiling h)
    | .refl h => .refl (eqe_ceiling h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ceiling h₀) (rw_star_sub_ceiling h₁)
  theorem rw_star_sub_ratOf {a b : kXReal} : a.rw_star b →
      MRat.rw_star (ratOf a) (ratOf b)
    | .step h => .step (rw_one.sub_ratOf h)
    | .refl h => .refl (eqe_ratOf h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ratOf h₀) (rw_star_sub_ratOf h₁)
  theorem rw_star_sub_xSign {a b : kXReal} : a.rw_star b →
      MRat.rw_star (xSign a) (xSign b)
    | .step h => .step (rw_one.sub_xSign h)
    | .refl h => .refl (eqe_xSign h)
    | .trans h₀ h₁ => .trans (rw_star_sub_xSign h₀) (rw_star_sub_xSign h₁)
  theorem rw_star_sub_pow2 {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (pow2 a) (pow2 b)
    | .step h => .step (rw_one.sub_pow2 h)
    | .refl h => .refl (eqe_pow2 h)
    | .trans h₀ h₁ => .trans (rw_star_sub_pow2 h₀) (rw_star_sub_pow2 h₁)
  theorem rw_star_sub_floorLog2 {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (floorLog2 a) (floorLog2 b)
    | .step h => .step (rw_one.sub_floorLog2 h)
    | .refl h => .refl (eqe_floorLog2 h)
    | .trans h₀ h₁ => .trans (rw_star_sub_floorLog2 h₀) (rw_star_sub_floorLog2 h₁)
  theorem rw_star_sub_nearestEvenInteger {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (nearestEvenInteger a) (nearestEvenInteger b)
    | .step h => .step (rw_one.sub_nearestEvenInteger h)
    | .refl h => .refl (eqe_nearestEvenInteger h)
    | .trans h₀ h₁ => .trans (rw_star_sub_nearestEvenInteger h₀) (rw_star_sub_nearestEvenInteger h₁)
  theorem rw_star_sub_integerSqrt {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (integerSqrt a) (integerSqrt b)
    | .step h => .step (rw_one.sub_integerSqrt h)
    | .refl h => .refl (eqe_integerSqrt h)
    | .trans h₀ h₁ => .trans (rw_star_sub_integerSqrt h₀) (rw_star_sub_integerSqrt h₁)
  theorem rw_star_sub_sqrtSearch₀ {a b a₁ a₂ : MRat} : MRat.rw_star a b →
      MRat.rw_star (sqrtSearch a a₁ a₂) (sqrtSearch b a₁ a₂)
    | .step h => .step (rw_one.sub_sqrtSearch₀ h)
    | .refl h => .refl (eqe_sqrtSearch h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_sqrtSearch₀ h₀) (rw_star_sub_sqrtSearch₀ h₁)
  theorem rw_star_sub_sqrtSearch₁ {a₀ a b a₂ : MRat} : MRat.rw_star a b →
      MRat.rw_star (sqrtSearch a₀ a a₂) (sqrtSearch a₀ b a₂)
    | .step h => .step (rw_one.sub_sqrtSearch₁ h)
    | .refl h => .refl (eqe_sqrtSearch rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_sqrtSearch₁ h₀) (rw_star_sub_sqrtSearch₁ h₁)
  theorem rw_star_sub_sqrtSearch₂ {a₀ a₁ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (sqrtSearch a₀ a₁ a) (sqrtSearch a₀ a₁ b)
    | .step h => .step (rw_one.sub_sqrtSearch₂ h)
    | .refl h => .refl (eqe_sqrtSearch rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_sqrtSearch₂ h₀) (rw_star_sub_sqrtSearch₂ h₁)
  theorem rw_star_sub_BitwidthOf {a b : kFormat} : a.rw_star b →
      MRat.rw_star (BitwidthOf a) (BitwidthOf b)
    | .step h => .step (rw_one.sub_BitwidthOf h)
    | .refl h => .refl (eqe_BitwidthOf h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BitwidthOf h₀) (rw_star_sub_BitwidthOf h₁)
  theorem rw_star_sub_PrecisionOf {a b : kFormat} : a.rw_star b →
      MRat.rw_star (PrecisionOf a) (PrecisionOf b)
    | .step h => .step (rw_one.sub_PrecisionOf h)
    | .refl h => .refl (eqe_PrecisionOf h)
    | .trans h₀ h₁ => .trans (rw_star_sub_PrecisionOf h₀) (rw_star_sub_PrecisionOf h₁)
  theorem rw_star_sub_ExponentBitwidthOf {a b : kFormat} : a.rw_star b →
      MRat.rw_star (ExponentBitwidthOf a) (ExponentBitwidthOf b)
    | .step h => .step (rw_one.sub_ExponentBitwidthOf h)
    | .refl h => .refl (eqe_ExponentBitwidthOf h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ExponentBitwidthOf h₀) (rw_star_sub_ExponentBitwidthOf h₁)
  theorem rw_star_sub_TrailingSignificandBitwidthOf {a b : kFormat} : a.rw_star b →
      MRat.rw_star (TrailingSignificandBitwidthOf a) (TrailingSignificandBitwidthOf b)
    | .step h => .step (rw_one.sub_TrailingSignificandBitwidthOf h)
    | .refl h => .refl (eqe_TrailingSignificandBitwidthOf h)
    | .trans h₀ h₁ => .trans (rw_star_sub_TrailingSignificandBitwidthOf h₀) (rw_star_sub_TrailingSignificandBitwidthOf h₁)
  theorem rw_star_sub_ExponentBiasOf {a b : kFormat} : a.rw_star b →
      MRat.rw_star (ExponentBiasOf a) (ExponentBiasOf b)
    | .step h => .step (rw_one.sub_ExponentBiasOf h)
    | .refl h => .refl (eqe_ExponentBiasOf h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ExponentBiasOf h₀) (rw_star_sub_ExponentBiasOf h₁)
  theorem rw_star_sub_externalEncode₀ {a b : kFormat} {a₁ : kXReal} : a.rw_star b →
      MRat.rw_star (externalEncode a a₁) (externalEncode b a₁)
    | .step h => .step (rw_one.sub_externalEncode₀ h)
    | .refl h => .refl (eqe_externalEncode h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_externalEncode₀ h₀) (rw_star_sub_externalEncode₀ h₁)
  theorem rw_star_sub_externalEncode₁ {a₀ : kFormat} {a b : kXReal} : a.rw_star b →
      MRat.rw_star (externalEncode a₀ a) (externalEncode a₀ b)
    | .step h => .step (rw_one.sub_externalEncode₁ h)
    | .refl h => .refl (eqe_externalEncode (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_externalEncode₁ h₀) (rw_star_sub_externalEncode₁ h₁)
  theorem rw_star_sub_externalBound₀ {a b : kFormat} {a₁ : kBoundQuery} : a.rw_star b →
      MRat.rw_star (externalBound a a₁) (externalBound b a₁)
    | .step h => .step (rw_one.sub_externalBound₀ h)
    | .refl h => .refl (eqe_externalBound h (kBoundQuery.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_externalBound₀ h₀) (rw_star_sub_externalBound₀ h₁)
  theorem rw_star_sub_externalBound₁ {a₀ : kFormat} {a b : kBoundQuery} : a.rw_star b →
      MRat.rw_star (externalBound a₀ a) (externalBound a₀ b)
    | .step h => .step (rw_one.sub_externalBound₁ h)
    | .refl h => .refl (eqe_externalBound (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_externalBound₁ h₀) (rw_star_sub_externalBound₁ h₁)
  theorem rw_star_sub_nanCode {a b : kFormat} : a.rw_star b →
      MRat.rw_star (nanCode a) (nanCode b)
    | .step h => .step (rw_one.sub_nanCode h)
    | .refl h => .refl (eqe_nanCode h)
    | .trans h₀ h₁ => .trans (rw_star_sub_nanCode h₀) (rw_star_sub_nanCode h₁)
  theorem rw_star_sub_positiveLimit {a b : kFormat} : a.rw_star b →
      MRat.rw_star (positiveLimit a) (positiveLimit b)
    | .step h => .step (rw_one.sub_positiveLimit h)
    | .refl h => .refl (eqe_positiveLimit h)
    | .trans h₀ h₁ => .trans (rw_star_sub_positiveLimit h₀) (rw_star_sub_positiveLimit h₁)
  theorem rw_star_sub_decodePositive₀ {a b : kFormat} {a₁ : MRat} : a.rw_star b →
      MRat.rw_star (decodePositive a a₁) (decodePositive b a₁)
    | .step h => .step (rw_one.sub_decodePositive₀ h)
    | .refl h => .refl (eqe_decodePositive h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_decodePositive₀ h₀) (rw_star_sub_decodePositive₀ h₁)
  theorem rw_star_sub_decodePositive₁ {a₀ : kFormat} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (decodePositive a₀ a) (decodePositive a₀ b)
    | .step h => .step (rw_one.sub_decodePositive₁ h)
    | .refl h => .refl (eqe_decodePositive (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_decodePositive₁ h₀) (rw_star_sub_decodePositive₁ h₁)
  theorem rw_star_sub_encode₀ {a b : kFormat} {a₁ : kXReal} : a.rw_star b →
      MRat.rw_star (encode a a₁) (encode b a₁)
    | .step h => .step (rw_one.sub_encode₀ h)
    | .refl h => .refl (eqe_encode h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_encode₀ h₀) (rw_star_sub_encode₀ h₁)
  theorem rw_star_sub_encode₁ {a₀ : kFormat} {a b : kXReal} : a.rw_star b →
      MRat.rw_star (encode a₀ a) (encode a₀ b)
    | .step h => .step (rw_one.sub_encode₁ h)
    | .refl h => .refl (eqe_encode (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_encode₁ h₀) (rw_star_sub_encode₁ h₁)
  theorem rw_star_sub_magnitudeCode₀ {a b : kFormat} {a₁ : MRat} : a.rw_star b →
      MRat.rw_star (magnitudeCode a a₁) (magnitudeCode b a₁)
    | .step h => .step (rw_one.sub_magnitudeCode₀ h)
    | .refl h => .refl (eqe_magnitudeCode h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_magnitudeCode₀ h₀) (rw_star_sub_magnitudeCode₀ h₁)
  theorem rw_star_sub_magnitudeCode₁ {a₀ : kFormat} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (magnitudeCode a₀ a) (magnitudeCode a₀ b)
    | .step h => .step (rw_one.sub_magnitudeCode₁ h)
    | .refl h => .refl (eqe_magnitudeCode (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_magnitudeCode₁ h₀) (rw_star_sub_magnitudeCode₁ h₁)
  theorem rw_star_sub_MaxFiniteOf {a b : kFormat} : a.rw_star b →
      MRat.rw_star (MaxFiniteOf a) (MaxFiniteOf b)
    | .step h => .step (rw_one.sub_MaxFiniteOf h)
    | .refl h => .refl (eqe_MaxFiniteOf h)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaxFiniteOf h₀) (rw_star_sub_MaxFiniteOf h₁)
  theorem rw_star_sub_MinFiniteOf {a b : kFormat} : a.rw_star b →
      MRat.rw_star (MinFiniteOf a) (MinFiniteOf b)
    | .step h => .step (rw_one.sub_MinFiniteOf h)
    | .refl h => .refl (eqe_MinFiniteOf h)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinFiniteOf h₀) (rw_star_sub_MinFiniteOf h₁)
  theorem rw_star_sub_MinPositiveOf {a b : kFormat} : a.rw_star b →
      MRat.rw_star (MinPositiveOf a) (MinPositiveOf b)
    | .step h => .step (rw_one.sub_MinPositiveOf h)
    | .refl h => .refl (eqe_MinPositiveOf h)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinPositiveOf h₀) (rw_star_sub_MinPositiveOf h₁)
  theorem rw_star_sub_MaxSubnormalOf {a b : kFormat} : a.rw_star b →
      MRat.rw_star (MaxSubnormalOf a) (MaxSubnormalOf b)
    | .step h => .step (rw_one.sub_MaxSubnormalOf h)
    | .refl h => .refl (eqe_MaxSubnormalOf h)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaxSubnormalOf h₀) (rw_star_sub_MaxSubnormalOf h₁)
  theorem rw_star_sub_MinNormalOf {a b : kFormat} : a.rw_star b →
      MRat.rw_star (MinNormalOf a) (MinNormalOf b)
    | .step h => .step (rw_one.sub_MinNormalOf h)
    | .refl h => .refl (eqe_MinNormalOf h)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinNormalOf h₀) (rw_star_sub_MinNormalOf h₁)
  theorem rw_star_sub_length₀ {a b : kRandomSeq} : a.rw_star b →
      MRat.rw_star (length₀ a) (length₀ b)
    | .step h => .step (rw_one.sub_length₀ h)
    | .refl h => .refl (eqe_length₀ h)
    | .trans h₀ h₁ => .trans (rw_star_sub_length₀ h₀) (rw_star_sub_length₀ h₁)
  theorem rw_star_sub_at₀₀ {a b : kRandomSeq} {a₁ : MRat} : a.rw_star b →
      MRat.rw_star (at₀ a a₁) (at₀ b a₁)
    | .step h => .step (rw_one.sub_at₀₀ h)
    | .refl h => .refl (eqe_at₀ h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₀₀ h₀) (rw_star_sub_at₀₀ h₁)
  theorem rw_star_sub_at₀₁ {a₀ : kRandomSeq} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (at₀ a₀ a) (at₀ a₀ b)
    | .step h => .step (rw_one.sub_at₀₁ h)
    | .refl h => .refl (eqe_at₀ (kRandomSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₀₁ h₀) (rw_star_sub_at₀₁ h₁)
  theorem rw_star_sub_roundScaled₀ {a b a₁ : MRat} {a₂ : kBlockRoundMode} {a₃ a₄ a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (roundScaled a a₁ a₂ a₃ a₄ a₅) (roundScaled b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_roundScaled₀ h)
    | .refl h => .refl (eqe_roundScaled h rfl (kBlockRoundMode.eqe_refl a₂) rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_roundScaled₀ h₀) (rw_star_sub_roundScaled₀ h₁)
  theorem rw_star_sub_roundScaled₁ {a₀ a b : MRat} {a₂ : kBlockRoundMode} {a₃ a₄ a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (roundScaled a₀ a a₂ a₃ a₄ a₅) (roundScaled a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_roundScaled₁ h)
    | .refl h => .refl (eqe_roundScaled rfl h (kBlockRoundMode.eqe_refl a₂) rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_roundScaled₁ h₀) (rw_star_sub_roundScaled₁ h₁)
  theorem rw_star_sub_roundScaled₂ {a₀ a₁ : MRat} {a b : kBlockRoundMode} {a₃ a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (roundScaled a₀ a₁ a a₃ a₄ a₅) (roundScaled a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_roundScaled₂ h)
    | .refl h => .refl (eqe_roundScaled rfl rfl h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_roundScaled₂ h₀) (rw_star_sub_roundScaled₂ h₁)
  theorem rw_star_sub_roundScaled₃ {a₀ a₁ : MRat} {a₂ : kBlockRoundMode} {a b a₄ a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (roundScaled a₀ a₁ a₂ a a₄ a₅) (roundScaled a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_roundScaled₃ h)
    | .refl h => .refl (eqe_roundScaled rfl rfl (kBlockRoundMode.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_roundScaled₃ h₀) (rw_star_sub_roundScaled₃ h₁)
  theorem rw_star_sub_roundScaled₄ {a₀ a₁ : MRat} {a₂ : kBlockRoundMode} {a₃ a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (roundScaled a₀ a₁ a₂ a₃ a a₅) (roundScaled a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_roundScaled₄ h)
    | .refl h => .refl (eqe_roundScaled rfl rfl (kBlockRoundMode.eqe_refl a₂) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_roundScaled₄ h₀) (rw_star_sub_roundScaled₄ h₁)
  theorem rw_star_sub_roundScaled₅ {a₀ a₁ : MRat} {a₂ : kBlockRoundMode} {a₃ a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (roundScaled a₀ a₁ a₂ a₃ a₄ a) (roundScaled a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_roundScaled₅ h)
    | .refl h => .refl (eqe_roundScaled rfl rfl (kBlockRoundMode.eqe_refl a₂) rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_roundScaled₅ h₀) (rw_star_sub_roundScaled₅ h₁)
  theorem rw_star_sub_project₀ {a b : kFormat} {a₁ : kProjSpec} {a₂ : kXReal} : a.rw_star b →
      MRat.rw_star (project a a₁ a₂) (project b a₁ a₂)
    | .step h => .step (rw_one.sub_project₀ h)
    | .refl h => .refl (eqe_project h (kProjSpec.eqe_refl a₁) (kXReal.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_project₀ h₀) (rw_star_sub_project₀ h₁)
  theorem rw_star_sub_project₁ {a₀ : kFormat} {a b : kProjSpec} {a₂ : kXReal} : a.rw_star b →
      MRat.rw_star (project a₀ a a₂) (project a₀ b a₂)
    | .step h => .step (rw_one.sub_project₁ h)
    | .refl h => .refl (eqe_project (kFormat.eqe_refl a₀) h (kXReal.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_project₁ h₀) (rw_star_sub_project₁ h₁)
  theorem rw_star_sub_project₂ {a₀ : kFormat} {a₁ : kProjSpec} {a b : kXReal} : a.rw_star b →
      MRat.rw_star (project a₀ a₁ a) (project a₀ a₁ b)
    | .step h => .step (rw_one.sub_project₂ h)
    | .refl h => .refl (eqe_project (kFormat.eqe_refl a₀) (kProjSpec.eqe_refl a₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_project₂ h₀) (rw_star_sub_project₂ h₁)
  theorem rw_star_sub_length₁ {a b : kXSeq} : a.rw_star b →
      MRat.rw_star (length₁ a) (length₁ b)
    | .step h => .step (rw_one.sub_length₁ h)
    | .refl h => .refl (eqe_length₁ h)
    | .trans h₀ h₁ => .trans (rw_star_sub_length₁ h₀) (rw_star_sub_length₁ h₁)
  theorem rw_star_sub_length₂ {a b : kCodeSeq} : a.rw_star b →
      MRat.rw_star (length₂ a) (length₂ b)
    | .step h => .step (rw_one.sub_length₂ h)
    | .refl h => .refl (eqe_length₂ h)
    | .trans h₀ h₁ => .trans (rw_star_sub_length₂ h₀) (rw_star_sub_length₂ h₁)
  theorem rw_star_sub_at₁₀ {a b : kCodeSeq} {a₁ : MRat} : a.rw_star b →
      MRat.rw_star (at₁ a a₁) (at₁ b a₁)
    | .step h => .step (rw_one.sub_at₁₀ h)
    | .refl h => .refl (eqe_at₁ h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₁₀ h₀) (rw_star_sub_at₁₀ h₁)
  theorem rw_star_sub_at₁₁ {a₀ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (at₁ a₀ a) (at₁ a₀ b)
    | .step h => .step (rw_one.sub_at₁₁ h)
    | .refl h => .refl (eqe_at₁ (kCodeSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₁₁ h₀) (rw_star_sub_at₁₁ h₁)
  theorem rw_star_sub_scaledResult {a b : kBlock} : a.rw_star b →
      MRat.rw_star (scaledResult a) (scaledResult b)
    | .step h => .step (rw_one.sub_scaledResult h)
    | .refl h => .refl (eqe_scaledResult h)
    | .trans h₀ h₁ => .trans (rw_star_sub_scaledResult h₀) (rw_star_sub_scaledResult h₁)
  theorem rw_star_sub_ascii {a b : MString} : MString.rw_star a b →
      MRat.rw_star (ascii a) (ascii b)
    | .step h => .step (rw_one.sub_ascii h)
    | .refl h => .refl (eqe_ascii h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ascii h₀) (rw_star_sub_ascii h₁)
  theorem rw_star_sub_find₀ {a b a₁ : MString} {a₂ : MRat} : MString.rw_star a b →
      MRat.rw_star (find a a₁ a₂) (find b a₁ a₂)
    | .step h => .step (rw_one.sub_find₀ h)
    | .refl h => .refl (eqe_find h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_find₀ h₀) (rw_star_sub_find₀ h₁)
  theorem rw_star_sub_find₁ {a₀ a b : MString} {a₂ : MRat} : MString.rw_star a b →
      MRat.rw_star (find a₀ a a₂) (find a₀ b a₂)
    | .step h => .step (rw_one.sub_find₁ h)
    | .refl h => .refl (eqe_find rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_find₁ h₀) (rw_star_sub_find₁ h₁)
  theorem rw_star_sub_find₂ {a₀ a₁ : MString} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (find a₀ a₁ a) (find a₀ a₁ b)
    | .step h => .step (rw_one.sub_find₂ h)
    | .refl h => .refl (eqe_find rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_find₂ h₀) (rw_star_sub_find₂ h₁)
  theorem rw_star_sub_rfind₀ {a b a₁ : MString} {a₂ : MRat} : MString.rw_star a b →
      MRat.rw_star (rfind a a₁ a₂) (rfind b a₁ a₂)
    | .step h => .step (rw_one.sub_rfind₀ h)
    | .refl h => .refl (eqe_rfind h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_rfind₀ h₀) (rw_star_sub_rfind₀ h₁)
  theorem rw_star_sub_rfind₁ {a₀ a b : MString} {a₂ : MRat} : MString.rw_star a b →
      MRat.rw_star (rfind a₀ a a₂) (rfind a₀ b a₂)
    | .step h => .step (rw_one.sub_rfind₁ h)
    | .refl h => .refl (eqe_rfind rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_rfind₁ h₀) (rw_star_sub_rfind₁ h₁)
  theorem rw_star_sub_rfind₂ {a₀ a₁ : MString} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (rfind a₀ a₁ a) (rfind a₀ a₁ b)
    | .step h => .step (rw_one.sub_rfind₂ h)
    | .refl h => .refl (eqe_rfind rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_rfind₂ h₀) (rw_star_sub_rfind₂ h₁)
  theorem rw_star_sub_length₄ {a b : kFormatSeq} : a.rw_star b →
      MRat.rw_star (length₄ a) (length₄ b)
    | .step h => .step (rw_one.sub_length₄ h)
    | .refl h => .refl (eqe_length₄ h)
    | .trans h₀ h₁ => .trans (rw_star_sub_length₄ h₀) (rw_star_sub_length₄ h₁)
  theorem rw_star_sub_length₅ {a b : kKappaPartSeq} : a.rw_star b →
      MRat.rw_star (length₅ a) (length₅ b)
    | .step h => .step (rw_one.sub_length₅ h)
    | .refl h => .refl (eqe_length₅ h)
    | .trans h₀ h₁ => .trans (rw_star_sub_length₅ h₀) (rw_star_sub_length₅ h₁)
  theorem rw_star_sub_length₆ {a b : kPartitionSeq} : a.rw_star b →
      MRat.rw_star (length₆ a) (length₆ b)
    | .step h => .step (rw_one.sub_length₆ h)
    | .refl h => .refl (eqe_length₆ h)
    | .trans h₀ h₁ => .trans (rw_star_sub_length₆ h₀) (rw_star_sub_length₆ h₁)
  theorem rw_star_sub_length₇ {a b : kDeclarationSeq} : a.rw_star b →
      MRat.rw_star (length₇ a) (length₇ b)
    | .step h => .step (rw_one.sub_length₇ h)
    | .refl h => .refl (eqe_length₇ h)
    | .trans h₀ h₁ => .trans (rw_star_sub_length₇ h₀) (rw_star_sub_length₇ h₁)
  theorem rw_star_sub_length₈ {a b : kSpecializationSeq} : a.rw_star b →
      MRat.rw_star (length₈ a) (length₈ b)
    | .step h => .step (rw_one.sub_length₈ h)
    | .refl h => .refl (eqe_length₈ h)
    | .trans h₀ h₁ => .trans (rw_star_sub_length₈ h₀) (rw_star_sub_length₈ h₁)
  theorem rw_star_sub_length₉ {a b : kObservationSeq} : a.rw_star b →
      MRat.rw_star (length₉ a) (length₉ b)
    | .step h => .step (rw_one.sub_length₉ h)
    | .refl h => .refl (eqe_length₉ h)
    | .trans h₀ h₁ => .trans (rw_star_sub_length₉ h₀) (rw_star_sub_length₉ h₁)
  theorem rw_star_sub_length₁₀ {a b : kArityTable} : a.rw_star b →
      MRat.rw_star (length₁₀ a) (length₁₀ b)
    | .step h => .step (rw_one.sub_length₁₀ h)
    | .refl h => .refl (eqe_length₁₀ h)
    | .trans h₀ h₁ => .trans (rw_star_sub_length₁₀ h₀) (rw_star_sub_length₁₀ h₁)
  theorem rw_star_sub_finiteRank₀ {a b : kFormat} {a₁ : MRat} : a.rw_star b →
      MRat.rw_star (finiteRank a a₁) (finiteRank b a₁)
    | .step h => .step (rw_one.sub_finiteRank₀ h)
    | .refl h => .refl (eqe_finiteRank h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_finiteRank₀ h₀) (rw_star_sub_finiteRank₀ h₁)
  theorem rw_star_sub_finiteRank₁ {a₀ : kFormat} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (finiteRank a₀ a) (finiteRank a₀ b)
    | .step h => .step (rw_one.sub_finiteRank₁ h)
    | .refl h => .refl (eqe_finiteRank (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_finiteRank₁ h₀) (rw_star_sub_finiteRank₁ h₁)
  theorem rw_star_sub_Convert₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Convert a a₁ a₂ a₃) (Convert b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_Convert₀ h)
    | .refl h => .refl (eqe_Convert h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Convert₀ h₀) (rw_star_sub_Convert₀ h₁)
  theorem rw_star_sub_Convert₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Convert a₀ a a₂ a₃) (Convert a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_Convert₁ h)
    | .refl h => .refl (eqe_Convert (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Convert₁ h₀) (rw_star_sub_Convert₁ h₁)
  theorem rw_star_sub_Convert₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Convert a₀ a₁ a a₃) (Convert a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_Convert₂ h)
    | .refl h => .refl (eqe_Convert (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Convert₂ h₀) (rw_star_sub_Convert₂ h₁)
  theorem rw_star_sub_Convert₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Convert a₀ a₁ a₂ a) (Convert a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_Convert₃ h)
    | .refl h => .refl (eqe_Convert (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Convert₃ h₀) (rw_star_sub_Convert₃ h₁)
  theorem rw_star_sub_Abs₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Abs a a₁ a₂ a₃) (Abs b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_Abs₀ h)
    | .refl h => .refl (eqe_Abs h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Abs₀ h₀) (rw_star_sub_Abs₀ h₁)
  theorem rw_star_sub_Abs₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Abs a₀ a a₂ a₃) (Abs a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_Abs₁ h)
    | .refl h => .refl (eqe_Abs (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Abs₁ h₀) (rw_star_sub_Abs₁ h₁)
  theorem rw_star_sub_Abs₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Abs a₀ a₁ a a₃) (Abs a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_Abs₂ h)
    | .refl h => .refl (eqe_Abs (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Abs₂ h₀) (rw_star_sub_Abs₂ h₁)
  theorem rw_star_sub_Abs₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Abs a₀ a₁ a₂ a) (Abs a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_Abs₃ h)
    | .refl h => .refl (eqe_Abs (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Abs₃ h₀) (rw_star_sub_Abs₃ h₁)
  theorem rw_star_sub_Negate₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Negate a a₁ a₂ a₃) (Negate b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_Negate₀ h)
    | .refl h => .refl (eqe_Negate h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Negate₀ h₀) (rw_star_sub_Negate₀ h₁)
  theorem rw_star_sub_Negate₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Negate a₀ a a₂ a₃) (Negate a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_Negate₁ h)
    | .refl h => .refl (eqe_Negate (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Negate₁ h₀) (rw_star_sub_Negate₁ h₁)
  theorem rw_star_sub_Negate₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Negate a₀ a₁ a a₃) (Negate a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_Negate₂ h)
    | .refl h => .refl (eqe_Negate (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Negate₂ h₀) (rw_star_sub_Negate₂ h₁)
  theorem rw_star_sub_Negate₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Negate a₀ a₁ a₂ a) (Negate a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_Negate₃ h)
    | .refl h => .refl (eqe_Negate (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Negate₃ h₀) (rw_star_sub_Negate₃ h₁)
  theorem rw_star_sub_CopySign₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (CopySign a a₁ a₂ a₃ a₄ a₅) (CopySign b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_CopySign₀ h)
    | .refl h => .refl (eqe_CopySign h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CopySign₀ h₀) (rw_star_sub_CopySign₀ h₁)
  theorem rw_star_sub_CopySign₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (CopySign a₀ a a₂ a₃ a₄ a₅) (CopySign a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_CopySign₁ h)
    | .refl h => .refl (eqe_CopySign (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CopySign₁ h₀) (rw_star_sub_CopySign₁ h₁)
  theorem rw_star_sub_CopySign₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (CopySign a₀ a₁ a a₃ a₄ a₅) (CopySign a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_CopySign₂ h)
    | .refl h => .refl (eqe_CopySign (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CopySign₂ h₀) (rw_star_sub_CopySign₂ h₁)
  theorem rw_star_sub_CopySign₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (CopySign a₀ a₁ a₂ a a₄ a₅) (CopySign a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_CopySign₃ h)
    | .refl h => .refl (eqe_CopySign (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CopySign₃ h₀) (rw_star_sub_CopySign₃ h₁)
  theorem rw_star_sub_CopySign₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (CopySign a₀ a₁ a₂ a₃ a a₅) (CopySign a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_CopySign₄ h)
    | .refl h => .refl (eqe_CopySign (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CopySign₄ h₀) (rw_star_sub_CopySign₄ h₁)
  theorem rw_star_sub_CopySign₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (CopySign a₀ a₁ a₂ a₃ a₄ a) (CopySign a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_CopySign₅ h)
    | .refl h => .refl (eqe_CopySign (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_CopySign₅ h₀) (rw_star_sub_CopySign₅ h₁)
  theorem rw_star_sub_Add₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Add a a₁ a₂ a₃ a₄ a₅) (Add b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Add₀ h)
    | .refl h => .refl (eqe_Add h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Add₀ h₀) (rw_star_sub_Add₀ h₁)
  theorem rw_star_sub_Add₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Add a₀ a a₂ a₃ a₄ a₅) (Add a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Add₁ h)
    | .refl h => .refl (eqe_Add (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Add₁ h₀) (rw_star_sub_Add₁ h₁)
  theorem rw_star_sub_Add₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Add a₀ a₁ a a₃ a₄ a₅) (Add a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Add₂ h)
    | .refl h => .refl (eqe_Add (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Add₂ h₀) (rw_star_sub_Add₂ h₁)
  theorem rw_star_sub_Add₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Add a₀ a₁ a₂ a a₄ a₅) (Add a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_Add₃ h)
    | .refl h => .refl (eqe_Add (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Add₃ h₀) (rw_star_sub_Add₃ h₁)
  theorem rw_star_sub_Add₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (Add a₀ a₁ a₂ a₃ a a₅) (Add a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_Add₄ h)
    | .refl h => .refl (eqe_Add (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Add₄ h₀) (rw_star_sub_Add₄ h₁)
  theorem rw_star_sub_Add₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Add a₀ a₁ a₂ a₃ a₄ a) (Add a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_Add₅ h)
    | .refl h => .refl (eqe_Add (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Add₅ h₀) (rw_star_sub_Add₅ h₁)
  theorem rw_star_sub_Subtract₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Subtract a a₁ a₂ a₃ a₄ a₅) (Subtract b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Subtract₀ h)
    | .refl h => .refl (eqe_Subtract h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Subtract₀ h₀) (rw_star_sub_Subtract₀ h₁)
  theorem rw_star_sub_Subtract₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Subtract a₀ a a₂ a₃ a₄ a₅) (Subtract a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Subtract₁ h)
    | .refl h => .refl (eqe_Subtract (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Subtract₁ h₀) (rw_star_sub_Subtract₁ h₁)
  theorem rw_star_sub_Subtract₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Subtract a₀ a₁ a a₃ a₄ a₅) (Subtract a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Subtract₂ h)
    | .refl h => .refl (eqe_Subtract (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Subtract₂ h₀) (rw_star_sub_Subtract₂ h₁)
  theorem rw_star_sub_Subtract₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Subtract a₀ a₁ a₂ a a₄ a₅) (Subtract a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_Subtract₃ h)
    | .refl h => .refl (eqe_Subtract (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Subtract₃ h₀) (rw_star_sub_Subtract₃ h₁)
  theorem rw_star_sub_Subtract₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (Subtract a₀ a₁ a₂ a₃ a a₅) (Subtract a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_Subtract₄ h)
    | .refl h => .refl (eqe_Subtract (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Subtract₄ h₀) (rw_star_sub_Subtract₄ h₁)
  theorem rw_star_sub_Subtract₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Subtract a₀ a₁ a₂ a₃ a₄ a) (Subtract a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_Subtract₅ h)
    | .refl h => .refl (eqe_Subtract (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Subtract₅ h₀) (rw_star_sub_Subtract₅ h₁)
  theorem rw_star_sub_Multiply₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Multiply a a₁ a₂ a₃ a₄ a₅) (Multiply b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Multiply₀ h)
    | .refl h => .refl (eqe_Multiply h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Multiply₀ h₀) (rw_star_sub_Multiply₀ h₁)
  theorem rw_star_sub_Multiply₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Multiply a₀ a a₂ a₃ a₄ a₅) (Multiply a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Multiply₁ h)
    | .refl h => .refl (eqe_Multiply (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Multiply₁ h₀) (rw_star_sub_Multiply₁ h₁)
  theorem rw_star_sub_Multiply₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Multiply a₀ a₁ a a₃ a₄ a₅) (Multiply a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Multiply₂ h)
    | .refl h => .refl (eqe_Multiply (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Multiply₂ h₀) (rw_star_sub_Multiply₂ h₁)
  theorem rw_star_sub_Multiply₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Multiply a₀ a₁ a₂ a a₄ a₅) (Multiply a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_Multiply₃ h)
    | .refl h => .refl (eqe_Multiply (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Multiply₃ h₀) (rw_star_sub_Multiply₃ h₁)
  theorem rw_star_sub_Multiply₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (Multiply a₀ a₁ a₂ a₃ a a₅) (Multiply a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_Multiply₄ h)
    | .refl h => .refl (eqe_Multiply (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Multiply₄ h₀) (rw_star_sub_Multiply₄ h₁)
  theorem rw_star_sub_Multiply₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Multiply a₀ a₁ a₂ a₃ a₄ a) (Multiply a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_Multiply₅ h)
    | .refl h => .refl (eqe_Multiply (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Multiply₅ h₀) (rw_star_sub_Multiply₅ h₁)
  theorem rw_star_sub_Divide₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Divide a a₁ a₂ a₃ a₄ a₅) (Divide b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Divide₀ h)
    | .refl h => .refl (eqe_Divide h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Divide₀ h₀) (rw_star_sub_Divide₀ h₁)
  theorem rw_star_sub_Divide₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Divide a₀ a a₂ a₃ a₄ a₅) (Divide a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Divide₁ h)
    | .refl h => .refl (eqe_Divide (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Divide₁ h₀) (rw_star_sub_Divide₁ h₁)
  theorem rw_star_sub_Divide₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Divide a₀ a₁ a a₃ a₄ a₅) (Divide a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Divide₂ h)
    | .refl h => .refl (eqe_Divide (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Divide₂ h₀) (rw_star_sub_Divide₂ h₁)
  theorem rw_star_sub_Divide₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Divide a₀ a₁ a₂ a a₄ a₅) (Divide a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_Divide₃ h)
    | .refl h => .refl (eqe_Divide (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Divide₃ h₀) (rw_star_sub_Divide₃ h₁)
  theorem rw_star_sub_Divide₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (Divide a₀ a₁ a₂ a₃ a a₅) (Divide a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_Divide₄ h)
    | .refl h => .refl (eqe_Divide (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Divide₄ h₀) (rw_star_sub_Divide₄ h₁)
  theorem rw_star_sub_Divide₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Divide a₀ a₁ a₂ a₃ a₄ a) (Divide a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_Divide₅ h)
    | .refl h => .refl (eqe_Divide (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Divide₅ h₀) (rw_star_sub_Divide₅ h₁)
  theorem rw_star_sub_FMA₀ {a b a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ a₆ a₇ : MRat} : a.rw_star b →
      MRat.rw_star (FMA a a₁ a₂ a₃ a₄ a₅ a₆ a₇) (FMA b a₁ a₂ a₃ a₄ a₅ a₆ a₇)
    | .step h => .step (rw_one.sub_FMA₀ h)
    | .refl h => .refl (eqe_FMA h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_FMA₀ h₀) (rw_star_sub_FMA₀ h₁)
  theorem rw_star_sub_FMA₁ {a₀ a b a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ a₆ a₇ : MRat} : a.rw_star b →
      MRat.rw_star (FMA a₀ a a₂ a₃ a₄ a₅ a₆ a₇) (FMA a₀ b a₂ a₃ a₄ a₅ a₆ a₇)
    | .step h => .step (rw_one.sub_FMA₁ h)
    | .refl h => .refl (eqe_FMA (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_FMA₁ h₀) (rw_star_sub_FMA₁ h₁)
  theorem rw_star_sub_FMA₂ {a₀ a₁ a b a₃ : kFormat} {a₄ : kProjSpec} {a₅ a₆ a₇ : MRat} : a.rw_star b →
      MRat.rw_star (FMA a₀ a₁ a a₃ a₄ a₅ a₆ a₇) (FMA a₀ a₁ b a₃ a₄ a₅ a₆ a₇)
    | .step h => .step (rw_one.sub_FMA₂ h)
    | .refl h => .refl (eqe_FMA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_FMA₂ h₀) (rw_star_sub_FMA₂ h₁)
  theorem rw_star_sub_FMA₃ {a₀ a₁ a₂ a b : kFormat} {a₄ : kProjSpec} {a₅ a₆ a₇ : MRat} : a.rw_star b →
      MRat.rw_star (FMA a₀ a₁ a₂ a a₄ a₅ a₆ a₇) (FMA a₀ a₁ a₂ b a₄ a₅ a₆ a₇)
    | .step h => .step (rw_one.sub_FMA₃ h)
    | .refl h => .refl (eqe_FMA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kProjSpec.eqe_refl a₄) rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_FMA₃ h₀) (rw_star_sub_FMA₃ h₁)
  theorem rw_star_sub_FMA₄ {a₀ a₁ a₂ a₃ : kFormat} {a b : kProjSpec} {a₅ a₆ a₇ : MRat} : a.rw_star b →
      MRat.rw_star (FMA a₀ a₁ a₂ a₃ a a₅ a₆ a₇) (FMA a₀ a₁ a₂ a₃ b a₅ a₆ a₇)
    | .step h => .step (rw_one.sub_FMA₄ h)
    | .refl h => .refl (eqe_FMA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_FMA₄ h₀) (rw_star_sub_FMA₄ h₁)
  theorem rw_star_sub_FMA₅ {a₀ a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a b a₆ a₇ : MRat} : MRat.rw_star a b →
      MRat.rw_star (FMA a₀ a₁ a₂ a₃ a₄ a a₆ a₇) (FMA a₀ a₁ a₂ a₃ a₄ b a₆ a₇)
    | .step h => .step (rw_one.sub_FMA₅ h)
    | .refl h => .refl (eqe_FMA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_FMA₅ h₀) (rw_star_sub_FMA₅ h₁)
  theorem rw_star_sub_FMA₆ {a₀ a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ a b a₇ : MRat} : MRat.rw_star a b →
      MRat.rw_star (FMA a₀ a₁ a₂ a₃ a₄ a₅ a a₇) (FMA a₀ a₁ a₂ a₃ a₄ a₅ b a₇)
    | .step h => .step (rw_one.sub_FMA₆ h)
    | .refl h => .refl (eqe_FMA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_FMA₆ h₀) (rw_star_sub_FMA₆ h₁)
  theorem rw_star_sub_FMA₇ {a₀ a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ a₆ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (FMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a) (FMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ b)
    | .step h => .step (rw_one.sub_FMA₇ h)
    | .refl h => .refl (eqe_FMA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_FMA₇ h₀) (rw_star_sub_FMA₇ h₁)
  theorem rw_star_sub_FAA₀ {a b a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ a₆ a₇ : MRat} : a.rw_star b →
      MRat.rw_star (FAA a a₁ a₂ a₃ a₄ a₅ a₆ a₇) (FAA b a₁ a₂ a₃ a₄ a₅ a₆ a₇)
    | .step h => .step (rw_one.sub_FAA₀ h)
    | .refl h => .refl (eqe_FAA h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_FAA₀ h₀) (rw_star_sub_FAA₀ h₁)
  theorem rw_star_sub_FAA₁ {a₀ a b a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ a₆ a₇ : MRat} : a.rw_star b →
      MRat.rw_star (FAA a₀ a a₂ a₃ a₄ a₅ a₆ a₇) (FAA a₀ b a₂ a₃ a₄ a₅ a₆ a₇)
    | .step h => .step (rw_one.sub_FAA₁ h)
    | .refl h => .refl (eqe_FAA (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_FAA₁ h₀) (rw_star_sub_FAA₁ h₁)
  theorem rw_star_sub_FAA₂ {a₀ a₁ a b a₃ : kFormat} {a₄ : kProjSpec} {a₅ a₆ a₇ : MRat} : a.rw_star b →
      MRat.rw_star (FAA a₀ a₁ a a₃ a₄ a₅ a₆ a₇) (FAA a₀ a₁ b a₃ a₄ a₅ a₆ a₇)
    | .step h => .step (rw_one.sub_FAA₂ h)
    | .refl h => .refl (eqe_FAA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_FAA₂ h₀) (rw_star_sub_FAA₂ h₁)
  theorem rw_star_sub_FAA₃ {a₀ a₁ a₂ a b : kFormat} {a₄ : kProjSpec} {a₅ a₆ a₇ : MRat} : a.rw_star b →
      MRat.rw_star (FAA a₀ a₁ a₂ a a₄ a₅ a₆ a₇) (FAA a₀ a₁ a₂ b a₄ a₅ a₆ a₇)
    | .step h => .step (rw_one.sub_FAA₃ h)
    | .refl h => .refl (eqe_FAA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kProjSpec.eqe_refl a₄) rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_FAA₃ h₀) (rw_star_sub_FAA₃ h₁)
  theorem rw_star_sub_FAA₄ {a₀ a₁ a₂ a₃ : kFormat} {a b : kProjSpec} {a₅ a₆ a₇ : MRat} : a.rw_star b →
      MRat.rw_star (FAA a₀ a₁ a₂ a₃ a a₅ a₆ a₇) (FAA a₀ a₁ a₂ a₃ b a₅ a₆ a₇)
    | .step h => .step (rw_one.sub_FAA₄ h)
    | .refl h => .refl (eqe_FAA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_FAA₄ h₀) (rw_star_sub_FAA₄ h₁)
  theorem rw_star_sub_FAA₅ {a₀ a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a b a₆ a₇ : MRat} : MRat.rw_star a b →
      MRat.rw_star (FAA a₀ a₁ a₂ a₃ a₄ a a₆ a₇) (FAA a₀ a₁ a₂ a₃ a₄ b a₆ a₇)
    | .step h => .step (rw_one.sub_FAA₅ h)
    | .refl h => .refl (eqe_FAA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_FAA₅ h₀) (rw_star_sub_FAA₅ h₁)
  theorem rw_star_sub_FAA₆ {a₀ a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ a b a₇ : MRat} : MRat.rw_star a b →
      MRat.rw_star (FAA a₀ a₁ a₂ a₃ a₄ a₅ a a₇) (FAA a₀ a₁ a₂ a₃ a₄ a₅ b a₇)
    | .step h => .step (rw_one.sub_FAA₆ h)
    | .refl h => .refl (eqe_FAA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_FAA₆ h₀) (rw_star_sub_FAA₆ h₁)
  theorem rw_star_sub_FAA₇ {a₀ a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ a₆ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (FAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a) (FAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ b)
    | .step h => .step (rw_one.sub_FAA₇ h)
    | .refl h => .refl (eqe_FAA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_FAA₇ h₀) (rw_star_sub_FAA₇ h₁)
  theorem rw_star_sub_Recip₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Recip a a₁ a₂ a₃) (Recip b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_Recip₀ h)
    | .refl h => .refl (eqe_Recip h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Recip₀ h₀) (rw_star_sub_Recip₀ h₁)
  theorem rw_star_sub_Recip₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Recip a₀ a a₂ a₃) (Recip a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_Recip₁ h)
    | .refl h => .refl (eqe_Recip (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Recip₁ h₀) (rw_star_sub_Recip₁ h₁)
  theorem rw_star_sub_Recip₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Recip a₀ a₁ a a₃) (Recip a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_Recip₂ h)
    | .refl h => .refl (eqe_Recip (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Recip₂ h₀) (rw_star_sub_Recip₂ h₁)
  theorem rw_star_sub_Recip₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Recip a₀ a₁ a₂ a) (Recip a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_Recip₃ h)
    | .refl h => .refl (eqe_Recip (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Recip₃ h₀) (rw_star_sub_Recip₃ h₁)
  theorem rw_star_sub_Minimum₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Minimum a a₁ a₂ a₃ a₄ a₅) (Minimum b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Minimum₀ h)
    | .refl h => .refl (eqe_Minimum h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Minimum₀ h₀) (rw_star_sub_Minimum₀ h₁)
  theorem rw_star_sub_Minimum₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Minimum a₀ a a₂ a₃ a₄ a₅) (Minimum a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Minimum₁ h)
    | .refl h => .refl (eqe_Minimum (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Minimum₁ h₀) (rw_star_sub_Minimum₁ h₁)
  theorem rw_star_sub_Minimum₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Minimum a₀ a₁ a a₃ a₄ a₅) (Minimum a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Minimum₂ h)
    | .refl h => .refl (eqe_Minimum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Minimum₂ h₀) (rw_star_sub_Minimum₂ h₁)
  theorem rw_star_sub_Minimum₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Minimum a₀ a₁ a₂ a a₄ a₅) (Minimum a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_Minimum₃ h)
    | .refl h => .refl (eqe_Minimum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Minimum₃ h₀) (rw_star_sub_Minimum₃ h₁)
  theorem rw_star_sub_Minimum₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (Minimum a₀ a₁ a₂ a₃ a a₅) (Minimum a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_Minimum₄ h)
    | .refl h => .refl (eqe_Minimum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Minimum₄ h₀) (rw_star_sub_Minimum₄ h₁)
  theorem rw_star_sub_Minimum₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Minimum a₀ a₁ a₂ a₃ a₄ a) (Minimum a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_Minimum₅ h)
    | .refl h => .refl (eqe_Minimum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Minimum₅ h₀) (rw_star_sub_Minimum₅ h₁)
  theorem rw_star_sub_Maximum₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Maximum a a₁ a₂ a₃ a₄ a₅) (Maximum b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Maximum₀ h)
    | .refl h => .refl (eqe_Maximum h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Maximum₀ h₀) (rw_star_sub_Maximum₀ h₁)
  theorem rw_star_sub_Maximum₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Maximum a₀ a a₂ a₃ a₄ a₅) (Maximum a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Maximum₁ h)
    | .refl h => .refl (eqe_Maximum (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Maximum₁ h₀) (rw_star_sub_Maximum₁ h₁)
  theorem rw_star_sub_Maximum₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Maximum a₀ a₁ a a₃ a₄ a₅) (Maximum a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Maximum₂ h)
    | .refl h => .refl (eqe_Maximum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Maximum₂ h₀) (rw_star_sub_Maximum₂ h₁)
  theorem rw_star_sub_Maximum₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Maximum a₀ a₁ a₂ a a₄ a₅) (Maximum a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_Maximum₃ h)
    | .refl h => .refl (eqe_Maximum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Maximum₃ h₀) (rw_star_sub_Maximum₃ h₁)
  theorem rw_star_sub_Maximum₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (Maximum a₀ a₁ a₂ a₃ a a₅) (Maximum a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_Maximum₄ h)
    | .refl h => .refl (eqe_Maximum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Maximum₄ h₀) (rw_star_sub_Maximum₄ h₁)
  theorem rw_star_sub_Maximum₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Maximum a₀ a₁ a₂ a₃ a₄ a) (Maximum a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_Maximum₅ h)
    | .refl h => .refl (eqe_Maximum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Maximum₅ h₀) (rw_star_sub_Maximum₅ h₁)
  theorem rw_star_sub_MinimumNumber₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MinimumNumber a a₁ a₂ a₃ a₄ a₅) (MinimumNumber b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MinimumNumber₀ h)
    | .refl h => .refl (eqe_MinimumNumber h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumNumber₀ h₀) (rw_star_sub_MinimumNumber₀ h₁)
  theorem rw_star_sub_MinimumNumber₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MinimumNumber a₀ a a₂ a₃ a₄ a₅) (MinimumNumber a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MinimumNumber₁ h)
    | .refl h => .refl (eqe_MinimumNumber (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumNumber₁ h₀) (rw_star_sub_MinimumNumber₁ h₁)
  theorem rw_star_sub_MinimumNumber₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MinimumNumber a₀ a₁ a a₃ a₄ a₅) (MinimumNumber a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MinimumNumber₂ h)
    | .refl h => .refl (eqe_MinimumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumNumber₂ h₀) (rw_star_sub_MinimumNumber₂ h₁)
  theorem rw_star_sub_MinimumNumber₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MinimumNumber a₀ a₁ a₂ a a₄ a₅) (MinimumNumber a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_MinimumNumber₃ h)
    | .refl h => .refl (eqe_MinimumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumNumber₃ h₀) (rw_star_sub_MinimumNumber₃ h₁)
  theorem rw_star_sub_MinimumNumber₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (MinimumNumber a₀ a₁ a₂ a₃ a a₅) (MinimumNumber a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_MinimumNumber₄ h)
    | .refl h => .refl (eqe_MinimumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumNumber₄ h₀) (rw_star_sub_MinimumNumber₄ h₁)
  theorem rw_star_sub_MinimumNumber₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (MinimumNumber a₀ a₁ a₂ a₃ a₄ a) (MinimumNumber a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_MinimumNumber₅ h)
    | .refl h => .refl (eqe_MinimumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumNumber₅ h₀) (rw_star_sub_MinimumNumber₅ h₁)
  theorem rw_star_sub_MaximumNumber₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MaximumNumber a a₁ a₂ a₃ a₄ a₅) (MaximumNumber b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MaximumNumber₀ h)
    | .refl h => .refl (eqe_MaximumNumber h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumNumber₀ h₀) (rw_star_sub_MaximumNumber₀ h₁)
  theorem rw_star_sub_MaximumNumber₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MaximumNumber a₀ a a₂ a₃ a₄ a₅) (MaximumNumber a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MaximumNumber₁ h)
    | .refl h => .refl (eqe_MaximumNumber (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumNumber₁ h₀) (rw_star_sub_MaximumNumber₁ h₁)
  theorem rw_star_sub_MaximumNumber₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MaximumNumber a₀ a₁ a a₃ a₄ a₅) (MaximumNumber a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MaximumNumber₂ h)
    | .refl h => .refl (eqe_MaximumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumNumber₂ h₀) (rw_star_sub_MaximumNumber₂ h₁)
  theorem rw_star_sub_MaximumNumber₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MaximumNumber a₀ a₁ a₂ a a₄ a₅) (MaximumNumber a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_MaximumNumber₃ h)
    | .refl h => .refl (eqe_MaximumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumNumber₃ h₀) (rw_star_sub_MaximumNumber₃ h₁)
  theorem rw_star_sub_MaximumNumber₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (MaximumNumber a₀ a₁ a₂ a₃ a a₅) (MaximumNumber a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_MaximumNumber₄ h)
    | .refl h => .refl (eqe_MaximumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumNumber₄ h₀) (rw_star_sub_MaximumNumber₄ h₁)
  theorem rw_star_sub_MaximumNumber₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (MaximumNumber a₀ a₁ a₂ a₃ a₄ a) (MaximumNumber a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_MaximumNumber₅ h)
    | .refl h => .refl (eqe_MaximumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumNumber₅ h₀) (rw_star_sub_MaximumNumber₅ h₁)
  theorem rw_star_sub_MinimumMagnitude₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MinimumMagnitude a a₁ a₂ a₃ a₄ a₅) (MinimumMagnitude b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MinimumMagnitude₀ h)
    | .refl h => .refl (eqe_MinimumMagnitude h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumMagnitude₀ h₀) (rw_star_sub_MinimumMagnitude₀ h₁)
  theorem rw_star_sub_MinimumMagnitude₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MinimumMagnitude a₀ a a₂ a₃ a₄ a₅) (MinimumMagnitude a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MinimumMagnitude₁ h)
    | .refl h => .refl (eqe_MinimumMagnitude (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumMagnitude₁ h₀) (rw_star_sub_MinimumMagnitude₁ h₁)
  theorem rw_star_sub_MinimumMagnitude₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MinimumMagnitude a₀ a₁ a a₃ a₄ a₅) (MinimumMagnitude a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MinimumMagnitude₂ h)
    | .refl h => .refl (eqe_MinimumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumMagnitude₂ h₀) (rw_star_sub_MinimumMagnitude₂ h₁)
  theorem rw_star_sub_MinimumMagnitude₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MinimumMagnitude a₀ a₁ a₂ a a₄ a₅) (MinimumMagnitude a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_MinimumMagnitude₃ h)
    | .refl h => .refl (eqe_MinimumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumMagnitude₃ h₀) (rw_star_sub_MinimumMagnitude₃ h₁)
  theorem rw_star_sub_MinimumMagnitude₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (MinimumMagnitude a₀ a₁ a₂ a₃ a a₅) (MinimumMagnitude a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_MinimumMagnitude₄ h)
    | .refl h => .refl (eqe_MinimumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumMagnitude₄ h₀) (rw_star_sub_MinimumMagnitude₄ h₁)
  theorem rw_star_sub_MinimumMagnitude₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (MinimumMagnitude a₀ a₁ a₂ a₃ a₄ a) (MinimumMagnitude a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_MinimumMagnitude₅ h)
    | .refl h => .refl (eqe_MinimumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumMagnitude₅ h₀) (rw_star_sub_MinimumMagnitude₅ h₁)
  theorem rw_star_sub_MaximumMagnitude₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MaximumMagnitude a a₁ a₂ a₃ a₄ a₅) (MaximumMagnitude b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MaximumMagnitude₀ h)
    | .refl h => .refl (eqe_MaximumMagnitude h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumMagnitude₀ h₀) (rw_star_sub_MaximumMagnitude₀ h₁)
  theorem rw_star_sub_MaximumMagnitude₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MaximumMagnitude a₀ a a₂ a₃ a₄ a₅) (MaximumMagnitude a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MaximumMagnitude₁ h)
    | .refl h => .refl (eqe_MaximumMagnitude (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumMagnitude₁ h₀) (rw_star_sub_MaximumMagnitude₁ h₁)
  theorem rw_star_sub_MaximumMagnitude₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MaximumMagnitude a₀ a₁ a a₃ a₄ a₅) (MaximumMagnitude a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MaximumMagnitude₂ h)
    | .refl h => .refl (eqe_MaximumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumMagnitude₂ h₀) (rw_star_sub_MaximumMagnitude₂ h₁)
  theorem rw_star_sub_MaximumMagnitude₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MaximumMagnitude a₀ a₁ a₂ a a₄ a₅) (MaximumMagnitude a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_MaximumMagnitude₃ h)
    | .refl h => .refl (eqe_MaximumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumMagnitude₃ h₀) (rw_star_sub_MaximumMagnitude₃ h₁)
  theorem rw_star_sub_MaximumMagnitude₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (MaximumMagnitude a₀ a₁ a₂ a₃ a a₅) (MaximumMagnitude a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_MaximumMagnitude₄ h)
    | .refl h => .refl (eqe_MaximumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumMagnitude₄ h₀) (rw_star_sub_MaximumMagnitude₄ h₁)
  theorem rw_star_sub_MaximumMagnitude₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (MaximumMagnitude a₀ a₁ a₂ a₃ a₄ a) (MaximumMagnitude a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_MaximumMagnitude₅ h)
    | .refl h => .refl (eqe_MaximumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumMagnitude₅ h₀) (rw_star_sub_MaximumMagnitude₅ h₁)
  theorem rw_star_sub_MinimumMagnitudeNumber₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MinimumMagnitudeNumber a a₁ a₂ a₃ a₄ a₅) (MinimumMagnitudeNumber b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MinimumMagnitudeNumber₀ h)
    | .refl h => .refl (eqe_MinimumMagnitudeNumber h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumMagnitudeNumber₀ h₀) (rw_star_sub_MinimumMagnitudeNumber₀ h₁)
  theorem rw_star_sub_MinimumMagnitudeNumber₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MinimumMagnitudeNumber a₀ a a₂ a₃ a₄ a₅) (MinimumMagnitudeNumber a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MinimumMagnitudeNumber₁ h)
    | .refl h => .refl (eqe_MinimumMagnitudeNumber (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumMagnitudeNumber₁ h₀) (rw_star_sub_MinimumMagnitudeNumber₁ h₁)
  theorem rw_star_sub_MinimumMagnitudeNumber₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MinimumMagnitudeNumber a₀ a₁ a a₃ a₄ a₅) (MinimumMagnitudeNumber a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MinimumMagnitudeNumber₂ h)
    | .refl h => .refl (eqe_MinimumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumMagnitudeNumber₂ h₀) (rw_star_sub_MinimumMagnitudeNumber₂ h₁)
  theorem rw_star_sub_MinimumMagnitudeNumber₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MinimumMagnitudeNumber a₀ a₁ a₂ a a₄ a₅) (MinimumMagnitudeNumber a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_MinimumMagnitudeNumber₃ h)
    | .refl h => .refl (eqe_MinimumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumMagnitudeNumber₃ h₀) (rw_star_sub_MinimumMagnitudeNumber₃ h₁)
  theorem rw_star_sub_MinimumMagnitudeNumber₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (MinimumMagnitudeNumber a₀ a₁ a₂ a₃ a a₅) (MinimumMagnitudeNumber a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_MinimumMagnitudeNumber₄ h)
    | .refl h => .refl (eqe_MinimumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumMagnitudeNumber₄ h₀) (rw_star_sub_MinimumMagnitudeNumber₄ h₁)
  theorem rw_star_sub_MinimumMagnitudeNumber₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (MinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a) (MinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_MinimumMagnitudeNumber₅ h)
    | .refl h => .refl (eqe_MinimumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumMagnitudeNumber₅ h₀) (rw_star_sub_MinimumMagnitudeNumber₅ h₁)
  theorem rw_star_sub_MaximumMagnitudeNumber₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MaximumMagnitudeNumber a a₁ a₂ a₃ a₄ a₅) (MaximumMagnitudeNumber b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MaximumMagnitudeNumber₀ h)
    | .refl h => .refl (eqe_MaximumMagnitudeNumber h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumMagnitudeNumber₀ h₀) (rw_star_sub_MaximumMagnitudeNumber₀ h₁)
  theorem rw_star_sub_MaximumMagnitudeNumber₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MaximumMagnitudeNumber a₀ a a₂ a₃ a₄ a₅) (MaximumMagnitudeNumber a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MaximumMagnitudeNumber₁ h)
    | .refl h => .refl (eqe_MaximumMagnitudeNumber (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumMagnitudeNumber₁ h₀) (rw_star_sub_MaximumMagnitudeNumber₁ h₁)
  theorem rw_star_sub_MaximumMagnitudeNumber₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MaximumMagnitudeNumber a₀ a₁ a a₃ a₄ a₅) (MaximumMagnitudeNumber a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MaximumMagnitudeNumber₂ h)
    | .refl h => .refl (eqe_MaximumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumMagnitudeNumber₂ h₀) (rw_star_sub_MaximumMagnitudeNumber₂ h₁)
  theorem rw_star_sub_MaximumMagnitudeNumber₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MaximumMagnitudeNumber a₀ a₁ a₂ a a₄ a₅) (MaximumMagnitudeNumber a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_MaximumMagnitudeNumber₃ h)
    | .refl h => .refl (eqe_MaximumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumMagnitudeNumber₃ h₀) (rw_star_sub_MaximumMagnitudeNumber₃ h₁)
  theorem rw_star_sub_MaximumMagnitudeNumber₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (MaximumMagnitudeNumber a₀ a₁ a₂ a₃ a a₅) (MaximumMagnitudeNumber a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_MaximumMagnitudeNumber₄ h)
    | .refl h => .refl (eqe_MaximumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumMagnitudeNumber₄ h₀) (rw_star_sub_MaximumMagnitudeNumber₄ h₁)
  theorem rw_star_sub_MaximumMagnitudeNumber₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (MaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a) (MaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_MaximumMagnitudeNumber₅ h)
    | .refl h => .refl (eqe_MaximumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumMagnitudeNumber₅ h₀) (rw_star_sub_MaximumMagnitudeNumber₅ h₁)
  theorem rw_star_sub_MinimumFinite₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MinimumFinite a a₁ a₂ a₃ a₄ a₅) (MinimumFinite b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MinimumFinite₀ h)
    | .refl h => .refl (eqe_MinimumFinite h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumFinite₀ h₀) (rw_star_sub_MinimumFinite₀ h₁)
  theorem rw_star_sub_MinimumFinite₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MinimumFinite a₀ a a₂ a₃ a₄ a₅) (MinimumFinite a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MinimumFinite₁ h)
    | .refl h => .refl (eqe_MinimumFinite (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumFinite₁ h₀) (rw_star_sub_MinimumFinite₁ h₁)
  theorem rw_star_sub_MinimumFinite₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MinimumFinite a₀ a₁ a a₃ a₄ a₅) (MinimumFinite a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MinimumFinite₂ h)
    | .refl h => .refl (eqe_MinimumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumFinite₂ h₀) (rw_star_sub_MinimumFinite₂ h₁)
  theorem rw_star_sub_MinimumFinite₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MinimumFinite a₀ a₁ a₂ a a₄ a₅) (MinimumFinite a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_MinimumFinite₃ h)
    | .refl h => .refl (eqe_MinimumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumFinite₃ h₀) (rw_star_sub_MinimumFinite₃ h₁)
  theorem rw_star_sub_MinimumFinite₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (MinimumFinite a₀ a₁ a₂ a₃ a a₅) (MinimumFinite a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_MinimumFinite₄ h)
    | .refl h => .refl (eqe_MinimumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumFinite₄ h₀) (rw_star_sub_MinimumFinite₄ h₁)
  theorem rw_star_sub_MinimumFinite₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (MinimumFinite a₀ a₁ a₂ a₃ a₄ a) (MinimumFinite a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_MinimumFinite₅ h)
    | .refl h => .refl (eqe_MinimumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_MinimumFinite₅ h₀) (rw_star_sub_MinimumFinite₅ h₁)
  theorem rw_star_sub_MaximumFinite₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MaximumFinite a a₁ a₂ a₃ a₄ a₅) (MaximumFinite b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MaximumFinite₀ h)
    | .refl h => .refl (eqe_MaximumFinite h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumFinite₀ h₀) (rw_star_sub_MaximumFinite₀ h₁)
  theorem rw_star_sub_MaximumFinite₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MaximumFinite a₀ a a₂ a₃ a₄ a₅) (MaximumFinite a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MaximumFinite₁ h)
    | .refl h => .refl (eqe_MaximumFinite (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumFinite₁ h₀) (rw_star_sub_MaximumFinite₁ h₁)
  theorem rw_star_sub_MaximumFinite₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MaximumFinite a₀ a₁ a a₃ a₄ a₅) (MaximumFinite a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_MaximumFinite₂ h)
    | .refl h => .refl (eqe_MaximumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumFinite₂ h₀) (rw_star_sub_MaximumFinite₂ h₁)
  theorem rw_star_sub_MaximumFinite₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (MaximumFinite a₀ a₁ a₂ a a₄ a₅) (MaximumFinite a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_MaximumFinite₃ h)
    | .refl h => .refl (eqe_MaximumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumFinite₃ h₀) (rw_star_sub_MaximumFinite₃ h₁)
  theorem rw_star_sub_MaximumFinite₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (MaximumFinite a₀ a₁ a₂ a₃ a a₅) (MaximumFinite a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_MaximumFinite₄ h)
    | .refl h => .refl (eqe_MaximumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumFinite₄ h₀) (rw_star_sub_MaximumFinite₄ h₁)
  theorem rw_star_sub_MaximumFinite₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (MaximumFinite a₀ a₁ a₂ a₃ a₄ a) (MaximumFinite a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_MaximumFinite₅ h)
    | .refl h => .refl (eqe_MaximumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_MaximumFinite₅ h₀) (rw_star_sub_MaximumFinite₅ h₁)
  theorem rw_star_sub_Clamp₀ {a b a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ a₆ a₇ : MRat} : a.rw_star b →
      MRat.rw_star (Clamp a a₁ a₂ a₃ a₄ a₅ a₆ a₇) (Clamp b a₁ a₂ a₃ a₄ a₅ a₆ a₇)
    | .step h => .step (rw_one.sub_Clamp₀ h)
    | .refl h => .refl (eqe_Clamp h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Clamp₀ h₀) (rw_star_sub_Clamp₀ h₁)
  theorem rw_star_sub_Clamp₁ {a₀ a b a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ a₆ a₇ : MRat} : a.rw_star b →
      MRat.rw_star (Clamp a₀ a a₂ a₃ a₄ a₅ a₆ a₇) (Clamp a₀ b a₂ a₃ a₄ a₅ a₆ a₇)
    | .step h => .step (rw_one.sub_Clamp₁ h)
    | .refl h => .refl (eqe_Clamp (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Clamp₁ h₀) (rw_star_sub_Clamp₁ h₁)
  theorem rw_star_sub_Clamp₂ {a₀ a₁ a b a₃ : kFormat} {a₄ : kProjSpec} {a₅ a₆ a₇ : MRat} : a.rw_star b →
      MRat.rw_star (Clamp a₀ a₁ a a₃ a₄ a₅ a₆ a₇) (Clamp a₀ a₁ b a₃ a₄ a₅ a₆ a₇)
    | .step h => .step (rw_one.sub_Clamp₂ h)
    | .refl h => .refl (eqe_Clamp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Clamp₂ h₀) (rw_star_sub_Clamp₂ h₁)
  theorem rw_star_sub_Clamp₃ {a₀ a₁ a₂ a b : kFormat} {a₄ : kProjSpec} {a₅ a₆ a₇ : MRat} : a.rw_star b →
      MRat.rw_star (Clamp a₀ a₁ a₂ a a₄ a₅ a₆ a₇) (Clamp a₀ a₁ a₂ b a₄ a₅ a₆ a₇)
    | .step h => .step (rw_one.sub_Clamp₃ h)
    | .refl h => .refl (eqe_Clamp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kProjSpec.eqe_refl a₄) rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Clamp₃ h₀) (rw_star_sub_Clamp₃ h₁)
  theorem rw_star_sub_Clamp₄ {a₀ a₁ a₂ a₃ : kFormat} {a b : kProjSpec} {a₅ a₆ a₇ : MRat} : a.rw_star b →
      MRat.rw_star (Clamp a₀ a₁ a₂ a₃ a a₅ a₆ a₇) (Clamp a₀ a₁ a₂ a₃ b a₅ a₆ a₇)
    | .step h => .step (rw_one.sub_Clamp₄ h)
    | .refl h => .refl (eqe_Clamp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Clamp₄ h₀) (rw_star_sub_Clamp₄ h₁)
  theorem rw_star_sub_Clamp₅ {a₀ a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a b a₆ a₇ : MRat} : MRat.rw_star a b →
      MRat.rw_star (Clamp a₀ a₁ a₂ a₃ a₄ a a₆ a₇) (Clamp a₀ a₁ a₂ a₃ a₄ b a₆ a₇)
    | .step h => .step (rw_one.sub_Clamp₅ h)
    | .refl h => .refl (eqe_Clamp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Clamp₅ h₀) (rw_star_sub_Clamp₅ h₁)
  theorem rw_star_sub_Clamp₆ {a₀ a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ a b a₇ : MRat} : MRat.rw_star a b →
      MRat.rw_star (Clamp a₀ a₁ a₂ a₃ a₄ a₅ a a₇) (Clamp a₀ a₁ a₂ a₃ a₄ a₅ b a₇)
    | .step h => .step (rw_one.sub_Clamp₆ h)
    | .refl h => .refl (eqe_Clamp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Clamp₆ h₀) (rw_star_sub_Clamp₆ h₁)
  theorem rw_star_sub_Clamp₇ {a₀ a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ a₆ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Clamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a) (Clamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ b)
    | .step h => .step (rw_one.sub_Clamp₇ h)
    | .refl h => .refl (eqe_Clamp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Clamp₇ h₀) (rw_star_sub_Clamp₇ h₁)
  theorem rw_star_sub_NextGreaterThan₀ {a b : kFormat} {a₁ : MRat} : a.rw_star b →
      MRat.rw_star (NextGreaterThan a a₁) (NextGreaterThan b a₁)
    | .step h => .step (rw_one.sub_NextGreaterThan₀ h)
    | .refl h => .refl (eqe_NextGreaterThan h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_NextGreaterThan₀ h₀) (rw_star_sub_NextGreaterThan₀ h₁)
  theorem rw_star_sub_NextGreaterThan₁ {a₀ : kFormat} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (NextGreaterThan a₀ a) (NextGreaterThan a₀ b)
    | .step h => .step (rw_one.sub_NextGreaterThan₁ h)
    | .refl h => .refl (eqe_NextGreaterThan (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_NextGreaterThan₁ h₀) (rw_star_sub_NextGreaterThan₁ h₁)
  theorem rw_star_sub_NextLessThan₀ {a b : kFormat} {a₁ : MRat} : a.rw_star b →
      MRat.rw_star (NextLessThan a a₁) (NextLessThan b a₁)
    | .step h => .step (rw_one.sub_NextLessThan₀ h)
    | .refl h => .refl (eqe_NextLessThan h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_NextLessThan₀ h₀) (rw_star_sub_NextLessThan₀ h₁)
  theorem rw_star_sub_NextLessThan₁ {a₀ : kFormat} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (NextLessThan a₀ a) (NextLessThan a₀ b)
    | .step h => .step (rw_one.sub_NextLessThan₁ h)
    | .refl h => .refl (eqe_NextLessThan (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_NextLessThan₁ h₀) (rw_star_sub_NextLessThan₁ h₁)
  theorem rw_star_sub_nextCode₀ {a b : kFormat} {a₁ : MRat} {a₂ : kBool} : a.rw_star b →
      MRat.rw_star (nextCode a a₁ a₂) (nextCode b a₁ a₂)
    | .step h => .step (rw_one.sub_nextCode₀ h)
    | .refl h => .refl (eqe_nextCode h rfl (kBool.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_nextCode₀ h₀) (rw_star_sub_nextCode₀ h₁)
  theorem rw_star_sub_nextCode₁ {a₀ : kFormat} {a b : MRat} {a₂ : kBool} : MRat.rw_star a b →
      MRat.rw_star (nextCode a₀ a a₂) (nextCode a₀ b a₂)
    | .step h => .step (rw_one.sub_nextCode₁ h)
    | .refl h => .refl (eqe_nextCode (kFormat.eqe_refl a₀) h (kBool.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_nextCode₁ h₀) (rw_star_sub_nextCode₁ h₁)
  theorem rw_star_sub_nextCode₂ {a₀ : kFormat} {a₁ : MRat} {a b : kBool} : a.rw_star b →
      MRat.rw_star (nextCode a₀ a₁ a) (nextCode a₀ a₁ b)
    | .step h => .step (rw_one.sub_nextCode₂ h)
    | .refl h => .refl (eqe_nextCode (kFormat.eqe_refl a₀) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_nextCode₂ h₀) (rw_star_sub_nextCode₂ h₁)
  theorem rw_star_sub_BlockReduceAdd₀ {a b : MRat} {a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ : MRat} {a₆ : kCodeSeq} : MRat.rw_star a b →
      MRat.rw_star (BlockReduceAdd a a₁ a₂ a₃ a₄ a₅ a₆) (BlockReduceAdd b a₁ a₂ a₃ a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_BlockReduceAdd₀ h)
    | .refl h => .refl (eqe_BlockReduceAdd h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockReduceAdd₀ h₀) (rw_star_sub_BlockReduceAdd₀ h₁)
  theorem rw_star_sub_BlockReduceAdd₁ {a₀ : MRat} {a b a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ : MRat} {a₆ : kCodeSeq} : a.rw_star b →
      MRat.rw_star (BlockReduceAdd a₀ a a₂ a₃ a₄ a₅ a₆) (BlockReduceAdd a₀ b a₂ a₃ a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_BlockReduceAdd₁ h)
    | .refl h => .refl (eqe_BlockReduceAdd rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockReduceAdd₁ h₀) (rw_star_sub_BlockReduceAdd₁ h₁)
  theorem rw_star_sub_BlockReduceAdd₂ {a₀ : MRat} {a₁ a b a₃ : kFormat} {a₄ : kProjSpec} {a₅ : MRat} {a₆ : kCodeSeq} : a.rw_star b →
      MRat.rw_star (BlockReduceAdd a₀ a₁ a a₃ a₄ a₅ a₆) (BlockReduceAdd a₀ a₁ b a₃ a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_BlockReduceAdd₂ h)
    | .refl h => .refl (eqe_BlockReduceAdd rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockReduceAdd₂ h₀) (rw_star_sub_BlockReduceAdd₂ h₁)
  theorem rw_star_sub_BlockReduceAdd₃ {a₀ : MRat} {a₁ a₂ a b : kFormat} {a₄ : kProjSpec} {a₅ : MRat} {a₆ : kCodeSeq} : a.rw_star b →
      MRat.rw_star (BlockReduceAdd a₀ a₁ a₂ a a₄ a₅ a₆) (BlockReduceAdd a₀ a₁ a₂ b a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_BlockReduceAdd₃ h)
    | .refl h => .refl (eqe_BlockReduceAdd rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kProjSpec.eqe_refl a₄) rfl (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockReduceAdd₃ h₀) (rw_star_sub_BlockReduceAdd₃ h₁)
  theorem rw_star_sub_BlockReduceAdd₄ {a₀ : MRat} {a₁ a₂ a₃ : kFormat} {a b : kProjSpec} {a₅ : MRat} {a₆ : kCodeSeq} : a.rw_star b →
      MRat.rw_star (BlockReduceAdd a₀ a₁ a₂ a₃ a a₅ a₆) (BlockReduceAdd a₀ a₁ a₂ a₃ b a₅ a₆)
    | .step h => .step (rw_one.sub_BlockReduceAdd₄ h)
    | .refl h => .refl (eqe_BlockReduceAdd rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h rfl (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockReduceAdd₄ h₀) (rw_star_sub_BlockReduceAdd₄ h₁)
  theorem rw_star_sub_BlockReduceAdd₅ {a₀ : MRat} {a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a b : MRat} {a₆ : kCodeSeq} : MRat.rw_star a b →
      MRat.rw_star (BlockReduceAdd a₀ a₁ a₂ a₃ a₄ a a₆) (BlockReduceAdd a₀ a₁ a₂ a₃ a₄ b a₆)
    | .step h => .step (rw_one.sub_BlockReduceAdd₅ h)
    | .refl h => .refl (eqe_BlockReduceAdd rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) h (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockReduceAdd₅ h₀) (rw_star_sub_BlockReduceAdd₅ h₁)
  theorem rw_star_sub_BlockReduceAdd₆ {a₀ : MRat} {a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ : MRat} {a b : kCodeSeq} : a.rw_star b →
      MRat.rw_star (BlockReduceAdd a₀ a₁ a₂ a₃ a₄ a₅ a) (BlockReduceAdd a₀ a₁ a₂ a₃ a₄ a₅ b)
    | .step h => .step (rw_one.sub_BlockReduceAdd₆ h)
    | .refl h => .refl (eqe_BlockReduceAdd rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockReduceAdd₆ h₀) (rw_star_sub_BlockReduceAdd₆ h₁)
  theorem rw_star_sub_BlockReduceMultiply₀ {a b : MRat} {a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ : MRat} {a₆ : kCodeSeq} : MRat.rw_star a b →
      MRat.rw_star (BlockReduceMultiply a a₁ a₂ a₃ a₄ a₅ a₆) (BlockReduceMultiply b a₁ a₂ a₃ a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_BlockReduceMultiply₀ h)
    | .refl h => .refl (eqe_BlockReduceMultiply h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockReduceMultiply₀ h₀) (rw_star_sub_BlockReduceMultiply₀ h₁)
  theorem rw_star_sub_BlockReduceMultiply₁ {a₀ : MRat} {a b a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ : MRat} {a₆ : kCodeSeq} : a.rw_star b →
      MRat.rw_star (BlockReduceMultiply a₀ a a₂ a₃ a₄ a₅ a₆) (BlockReduceMultiply a₀ b a₂ a₃ a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_BlockReduceMultiply₁ h)
    | .refl h => .refl (eqe_BlockReduceMultiply rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockReduceMultiply₁ h₀) (rw_star_sub_BlockReduceMultiply₁ h₁)
  theorem rw_star_sub_BlockReduceMultiply₂ {a₀ : MRat} {a₁ a b a₃ : kFormat} {a₄ : kProjSpec} {a₅ : MRat} {a₆ : kCodeSeq} : a.rw_star b →
      MRat.rw_star (BlockReduceMultiply a₀ a₁ a a₃ a₄ a₅ a₆) (BlockReduceMultiply a₀ a₁ b a₃ a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_BlockReduceMultiply₂ h)
    | .refl h => .refl (eqe_BlockReduceMultiply rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockReduceMultiply₂ h₀) (rw_star_sub_BlockReduceMultiply₂ h₁)
  theorem rw_star_sub_BlockReduceMultiply₃ {a₀ : MRat} {a₁ a₂ a b : kFormat} {a₄ : kProjSpec} {a₅ : MRat} {a₆ : kCodeSeq} : a.rw_star b →
      MRat.rw_star (BlockReduceMultiply a₀ a₁ a₂ a a₄ a₅ a₆) (BlockReduceMultiply a₀ a₁ a₂ b a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_BlockReduceMultiply₃ h)
    | .refl h => .refl (eqe_BlockReduceMultiply rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kProjSpec.eqe_refl a₄) rfl (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockReduceMultiply₃ h₀) (rw_star_sub_BlockReduceMultiply₃ h₁)
  theorem rw_star_sub_BlockReduceMultiply₄ {a₀ : MRat} {a₁ a₂ a₃ : kFormat} {a b : kProjSpec} {a₅ : MRat} {a₆ : kCodeSeq} : a.rw_star b →
      MRat.rw_star (BlockReduceMultiply a₀ a₁ a₂ a₃ a a₅ a₆) (BlockReduceMultiply a₀ a₁ a₂ a₃ b a₅ a₆)
    | .step h => .step (rw_one.sub_BlockReduceMultiply₄ h)
    | .refl h => .refl (eqe_BlockReduceMultiply rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h rfl (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockReduceMultiply₄ h₀) (rw_star_sub_BlockReduceMultiply₄ h₁)
  theorem rw_star_sub_BlockReduceMultiply₅ {a₀ : MRat} {a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a b : MRat} {a₆ : kCodeSeq} : MRat.rw_star a b →
      MRat.rw_star (BlockReduceMultiply a₀ a₁ a₂ a₃ a₄ a a₆) (BlockReduceMultiply a₀ a₁ a₂ a₃ a₄ b a₆)
    | .step h => .step (rw_one.sub_BlockReduceMultiply₅ h)
    | .refl h => .refl (eqe_BlockReduceMultiply rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) h (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockReduceMultiply₅ h₀) (rw_star_sub_BlockReduceMultiply₅ h₁)
  theorem rw_star_sub_BlockReduceMultiply₆ {a₀ : MRat} {a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ : MRat} {a b : kCodeSeq} : a.rw_star b →
      MRat.rw_star (BlockReduceMultiply a₀ a₁ a₂ a₃ a₄ a₅ a) (BlockReduceMultiply a₀ a₁ a₂ a₃ a₄ a₅ b)
    | .step h => .step (rw_one.sub_BlockReduceMultiply₆ h)
    | .refl h => .refl (eqe_BlockReduceMultiply rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockReduceMultiply₆ h₀) (rw_star_sub_BlockReduceMultiply₆ h₁)
  theorem rw_star_sub_BlockDotProduct₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ : kFormat} {a₆ : kProjSpec} {a₇ : MRat} {a₈ : kCodeSeq} {a₉ : MRat} {a₁₀ : kCodeSeq} : MRat.rw_star a b →
      MRat.rw_star (BlockDotProduct a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀) (BlockDotProduct b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀)
    | .step h => .step (rw_one.sub_BlockDotProduct₀ h)
    | .refl h => .refl (eqe_BlockDotProduct h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kProjSpec.eqe_refl a₆) rfl (kCodeSeq.eqe_refl a₈) rfl (kCodeSeq.eqe_refl a₁₀))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDotProduct₀ h₀) (rw_star_sub_BlockDotProduct₀ h₁)
  theorem rw_star_sub_BlockDotProduct₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ : kFormat} {a₆ : kProjSpec} {a₇ : MRat} {a₈ : kCodeSeq} {a₉ : MRat} {a₁₀ : kCodeSeq} : a.rw_star b →
      MRat.rw_star (BlockDotProduct a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀) (BlockDotProduct a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀)
    | .step h => .step (rw_one.sub_BlockDotProduct₁ h)
    | .refl h => .refl (eqe_BlockDotProduct rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kProjSpec.eqe_refl a₆) rfl (kCodeSeq.eqe_refl a₈) rfl (kCodeSeq.eqe_refl a₁₀))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDotProduct₁ h₀) (rw_star_sub_BlockDotProduct₁ h₁)
  theorem rw_star_sub_BlockDotProduct₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ : kFormat} {a₆ : kProjSpec} {a₇ : MRat} {a₈ : kCodeSeq} {a₉ : MRat} {a₁₀ : kCodeSeq} : a.rw_star b →
      MRat.rw_star (BlockDotProduct a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀) (BlockDotProduct a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀)
    | .step h => .step (rw_one.sub_BlockDotProduct₂ h)
    | .refl h => .refl (eqe_BlockDotProduct rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kProjSpec.eqe_refl a₆) rfl (kCodeSeq.eqe_refl a₈) rfl (kCodeSeq.eqe_refl a₁₀))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDotProduct₂ h₀) (rw_star_sub_BlockDotProduct₂ h₁)
  theorem rw_star_sub_BlockDotProduct₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ : kFormat} {a₆ : kProjSpec} {a₇ : MRat} {a₈ : kCodeSeq} {a₉ : MRat} {a₁₀ : kCodeSeq} : a.rw_star b →
      MRat.rw_star (BlockDotProduct a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀) (BlockDotProduct a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀)
    | .step h => .step (rw_one.sub_BlockDotProduct₃ h)
    | .refl h => .refl (eqe_BlockDotProduct rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kProjSpec.eqe_refl a₆) rfl (kCodeSeq.eqe_refl a₈) rfl (kCodeSeq.eqe_refl a₁₀))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDotProduct₃ h₀) (rw_star_sub_BlockDotProduct₃ h₁)
  theorem rw_star_sub_BlockDotProduct₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ : kFormat} {a₆ : kProjSpec} {a₇ : MRat} {a₈ : kCodeSeq} {a₉ : MRat} {a₁₀ : kCodeSeq} : a.rw_star b →
      MRat.rw_star (BlockDotProduct a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀) (BlockDotProduct a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀)
    | .step h => .step (rw_one.sub_BlockDotProduct₄ h)
    | .refl h => .refl (eqe_BlockDotProduct rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kProjSpec.eqe_refl a₆) rfl (kCodeSeq.eqe_refl a₈) rfl (kCodeSeq.eqe_refl a₁₀))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDotProduct₄ h₀) (rw_star_sub_BlockDotProduct₄ h₁)
  theorem rw_star_sub_BlockDotProduct₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b : kFormat} {a₆ : kProjSpec} {a₇ : MRat} {a₈ : kCodeSeq} {a₉ : MRat} {a₁₀ : kCodeSeq} : a.rw_star b →
      MRat.rw_star (BlockDotProduct a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀) (BlockDotProduct a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀)
    | .step h => .step (rw_one.sub_BlockDotProduct₅ h)
    | .refl h => .refl (eqe_BlockDotProduct rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kProjSpec.eqe_refl a₆) rfl (kCodeSeq.eqe_refl a₈) rfl (kCodeSeq.eqe_refl a₁₀))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDotProduct₅ h₀) (rw_star_sub_BlockDotProduct₅ h₁)
  theorem rw_star_sub_BlockDotProduct₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ : kFormat} {a b : kProjSpec} {a₇ : MRat} {a₈ : kCodeSeq} {a₉ : MRat} {a₁₀ : kCodeSeq} : a.rw_star b →
      MRat.rw_star (BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀) (BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀)
    | .step h => .step (rw_one.sub_BlockDotProduct₆ h)
    | .refl h => .refl (eqe_BlockDotProduct rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h rfl (kCodeSeq.eqe_refl a₈) rfl (kCodeSeq.eqe_refl a₁₀))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDotProduct₆ h₀) (rw_star_sub_BlockDotProduct₆ h₁)
  theorem rw_star_sub_BlockDotProduct₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ : kFormat} {a₆ : kProjSpec} {a b : MRat} {a₈ : kCodeSeq} {a₉ : MRat} {a₁₀ : kCodeSeq} : MRat.rw_star a b →
      MRat.rw_star (BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀) (BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀)
    | .step h => .step (rw_one.sub_BlockDotProduct₇ h)
    | .refl h => .refl (eqe_BlockDotProduct rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kProjSpec.eqe_refl a₆) h (kCodeSeq.eqe_refl a₈) rfl (kCodeSeq.eqe_refl a₁₀))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDotProduct₇ h₀) (rw_star_sub_BlockDotProduct₇ h₁)
  theorem rw_star_sub_BlockDotProduct₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ : kFormat} {a₆ : kProjSpec} {a₇ : MRat} {a b : kCodeSeq} {a₉ : MRat} {a₁₀ : kCodeSeq} : a.rw_star b →
      MRat.rw_star (BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀) (BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀)
    | .step h => .step (rw_one.sub_BlockDotProduct₈ h)
    | .refl h => .refl (eqe_BlockDotProduct rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kProjSpec.eqe_refl a₆) rfl h rfl (kCodeSeq.eqe_refl a₁₀))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDotProduct₈ h₀) (rw_star_sub_BlockDotProduct₈ h₁)
  theorem rw_star_sub_BlockDotProduct₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ : kFormat} {a₆ : kProjSpec} {a₇ : MRat} {a₈ : kCodeSeq} {a b : MRat} {a₁₀ : kCodeSeq} : MRat.rw_star a b →
      MRat.rw_star (BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀) (BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀)
    | .step h => .step (rw_one.sub_BlockDotProduct₉ h)
    | .refl h => .refl (eqe_BlockDotProduct rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kProjSpec.eqe_refl a₆) rfl (kCodeSeq.eqe_refl a₈) h (kCodeSeq.eqe_refl a₁₀))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDotProduct₉ h₀) (rw_star_sub_BlockDotProduct₉ h₁)
  theorem rw_star_sub_BlockDotProduct₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ : kFormat} {a₆ : kProjSpec} {a₇ : MRat} {a₈ : kCodeSeq} {a₉ : MRat} {a b : kCodeSeq} : a.rw_star b →
      MRat.rw_star (BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a) (BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b)
    | .step h => .step (rw_one.sub_BlockDotProduct₁₀ h)
    | .refl h => .refl (eqe_BlockDotProduct rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kProjSpec.eqe_refl a₆) rfl (kCodeSeq.eqe_refl a₈) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDotProduct₁₀ h₀) (rw_star_sub_BlockDotProduct₁₀ h₁)
  theorem rw_star_sub_ScaledConvert₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledConvert a a₁ a₂ a₃ a₄ a₅) (ScaledConvert b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledConvert₀ h)
    | .refl h => .refl (eqe_ScaledConvert h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledConvert₀ h₀) (rw_star_sub_ScaledConvert₀ h₁)
  theorem rw_star_sub_ScaledConvert₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledConvert a₀ a a₂ a₃ a₄ a₅) (ScaledConvert a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledConvert₁ h)
    | .refl h => .refl (eqe_ScaledConvert (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledConvert₁ h₀) (rw_star_sub_ScaledConvert₁ h₁)
  theorem rw_star_sub_ScaledConvert₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledConvert a₀ a₁ a a₃ a₄ a₅) (ScaledConvert a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledConvert₂ h)
    | .refl h => .refl (eqe_ScaledConvert (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledConvert₂ h₀) (rw_star_sub_ScaledConvert₂ h₁)
  theorem rw_star_sub_ScaledConvert₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledConvert a₀ a₁ a₂ a a₄ a₅) (ScaledConvert a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledConvert₃ h)
    | .refl h => .refl (eqe_ScaledConvert (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledConvert₃ h₀) (rw_star_sub_ScaledConvert₃ h₁)
  theorem rw_star_sub_ScaledConvert₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledConvert a₀ a₁ a₂ a₃ a a₅) (ScaledConvert a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledConvert₄ h)
    | .refl h => .refl (eqe_ScaledConvert (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledConvert₄ h₀) (rw_star_sub_ScaledConvert₄ h₁)
  theorem rw_star_sub_ScaledConvert₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledConvert a₀ a₁ a₂ a₃ a₄ a) (ScaledConvert a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledConvert₅ h)
    | .refl h => .refl (eqe_ScaledConvert (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledConvert₅ h₀) (rw_star_sub_ScaledConvert₅ h₁)
  theorem rw_star_sub_ScaledAbs₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledAbs a a₁ a₂ a₃ a₄ a₅) (ScaledAbs b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledAbs₀ h)
    | .refl h => .refl (eqe_ScaledAbs h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledAbs₀ h₀) (rw_star_sub_ScaledAbs₀ h₁)
  theorem rw_star_sub_ScaledAbs₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledAbs a₀ a a₂ a₃ a₄ a₅) (ScaledAbs a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledAbs₁ h)
    | .refl h => .refl (eqe_ScaledAbs (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledAbs₁ h₀) (rw_star_sub_ScaledAbs₁ h₁)
  theorem rw_star_sub_ScaledAbs₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledAbs a₀ a₁ a a₃ a₄ a₅) (ScaledAbs a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledAbs₂ h)
    | .refl h => .refl (eqe_ScaledAbs (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledAbs₂ h₀) (rw_star_sub_ScaledAbs₂ h₁)
  theorem rw_star_sub_ScaledAbs₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledAbs a₀ a₁ a₂ a a₄ a₅) (ScaledAbs a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledAbs₃ h)
    | .refl h => .refl (eqe_ScaledAbs (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledAbs₃ h₀) (rw_star_sub_ScaledAbs₃ h₁)
  theorem rw_star_sub_ScaledAbs₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledAbs a₀ a₁ a₂ a₃ a a₅) (ScaledAbs a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledAbs₄ h)
    | .refl h => .refl (eqe_ScaledAbs (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledAbs₄ h₀) (rw_star_sub_ScaledAbs₄ h₁)
  theorem rw_star_sub_ScaledAbs₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledAbs a₀ a₁ a₂ a₃ a₄ a) (ScaledAbs a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledAbs₅ h)
    | .refl h => .refl (eqe_ScaledAbs (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledAbs₅ h₀) (rw_star_sub_ScaledAbs₅ h₁)
  theorem rw_star_sub_ScaledNegate₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledNegate a a₁ a₂ a₃ a₄ a₅) (ScaledNegate b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledNegate₀ h)
    | .refl h => .refl (eqe_ScaledNegate h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledNegate₀ h₀) (rw_star_sub_ScaledNegate₀ h₁)
  theorem rw_star_sub_ScaledNegate₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledNegate a₀ a a₂ a₃ a₄ a₅) (ScaledNegate a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledNegate₁ h)
    | .refl h => .refl (eqe_ScaledNegate (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledNegate₁ h₀) (rw_star_sub_ScaledNegate₁ h₁)
  theorem rw_star_sub_ScaledNegate₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledNegate a₀ a₁ a a₃ a₄ a₅) (ScaledNegate a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledNegate₂ h)
    | .refl h => .refl (eqe_ScaledNegate (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledNegate₂ h₀) (rw_star_sub_ScaledNegate₂ h₁)
  theorem rw_star_sub_ScaledNegate₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledNegate a₀ a₁ a₂ a a₄ a₅) (ScaledNegate a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledNegate₃ h)
    | .refl h => .refl (eqe_ScaledNegate (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledNegate₃ h₀) (rw_star_sub_ScaledNegate₃ h₁)
  theorem rw_star_sub_ScaledNegate₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledNegate a₀ a₁ a₂ a₃ a a₅) (ScaledNegate a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledNegate₄ h)
    | .refl h => .refl (eqe_ScaledNegate (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledNegate₄ h₀) (rw_star_sub_ScaledNegate₄ h₁)
  theorem rw_star_sub_ScaledNegate₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledNegate a₀ a₁ a₂ a₃ a₄ a) (ScaledNegate a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledNegate₅ h)
    | .refl h => .refl (eqe_ScaledNegate (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledNegate₅ h₀) (rw_star_sub_ScaledNegate₅ h₁)
  theorem rw_star_sub_ScaledCopySign₀ {a b a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledCopySign a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledCopySign b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledCopySign₀ h)
    | .refl h => .refl (eqe_ScaledCopySign h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCopySign₀ h₀) (rw_star_sub_ScaledCopySign₀ h₁)
  theorem rw_star_sub_ScaledCopySign₁ {a₀ a b a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledCopySign a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledCopySign a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledCopySign₁ h)
    | .refl h => .refl (eqe_ScaledCopySign (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCopySign₁ h₀) (rw_star_sub_ScaledCopySign₁ h₁)
  theorem rw_star_sub_ScaledCopySign₂ {a₀ a₁ a b a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledCopySign a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledCopySign a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledCopySign₂ h)
    | .refl h => .refl (eqe_ScaledCopySign (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCopySign₂ h₀) (rw_star_sub_ScaledCopySign₂ h₁)
  theorem rw_star_sub_ScaledCopySign₃ {a₀ a₁ a₂ a b a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledCopySign a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (ScaledCopySign a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledCopySign₃ h)
    | .refl h => .refl (eqe_ScaledCopySign (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCopySign₃ h₀) (rw_star_sub_ScaledCopySign₃ h₁)
  theorem rw_star_sub_ScaledCopySign₄ {a₀ a₁ a₂ a₃ a b : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledCopySign a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (ScaledCopySign a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledCopySign₄ h)
    | .refl h => .refl (eqe_ScaledCopySign (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCopySign₄ h₀) (rw_star_sub_ScaledCopySign₄ h₁)
  theorem rw_star_sub_ScaledCopySign₅ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a b : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledCopySign a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (ScaledCopySign a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledCopySign₅ h)
    | .refl h => .refl (eqe_ScaledCopySign (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCopySign₅ h₀) (rw_star_sub_ScaledCopySign₅ h₁)
  theorem rw_star_sub_ScaledCopySign₆ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a b a₇ a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledCopySign a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (ScaledCopySign a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledCopySign₆ h)
    | .refl h => .refl (eqe_ScaledCopySign (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCopySign₆ h₀) (rw_star_sub_ScaledCopySign₆ h₁)
  theorem rw_star_sub_ScaledCopySign₇ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a b a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (ScaledCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledCopySign₇ h)
    | .refl h => .refl (eqe_ScaledCopySign (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCopySign₇ h₀) (rw_star_sub_ScaledCopySign₇ h₁)
  theorem rw_star_sub_ScaledCopySign₈ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a b a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (ScaledCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | .step h => .step (rw_one.sub_ScaledCopySign₈ h)
    | .refl h => .refl (eqe_ScaledCopySign (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCopySign₈ h₀) (rw_star_sub_ScaledCopySign₈ h₁)
  theorem rw_star_sub_ScaledCopySign₉ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (ScaledCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | .step h => .step (rw_one.sub_ScaledCopySign₉ h)
    | .refl h => .refl (eqe_ScaledCopySign (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCopySign₉ h₀) (rw_star_sub_ScaledCopySign₉ h₁)
  theorem rw_star_sub_ScaledAdd₀ {a b a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledAdd a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledAdd b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledAdd₀ h)
    | .refl h => .refl (eqe_ScaledAdd h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledAdd₀ h₀) (rw_star_sub_ScaledAdd₀ h₁)
  theorem rw_star_sub_ScaledAdd₁ {a₀ a b a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledAdd a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledAdd a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledAdd₁ h)
    | .refl h => .refl (eqe_ScaledAdd (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledAdd₁ h₀) (rw_star_sub_ScaledAdd₁ h₁)
  theorem rw_star_sub_ScaledAdd₂ {a₀ a₁ a b a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledAdd a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledAdd a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledAdd₂ h)
    | .refl h => .refl (eqe_ScaledAdd (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledAdd₂ h₀) (rw_star_sub_ScaledAdd₂ h₁)
  theorem rw_star_sub_ScaledAdd₃ {a₀ a₁ a₂ a b a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledAdd a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (ScaledAdd a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledAdd₃ h)
    | .refl h => .refl (eqe_ScaledAdd (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledAdd₃ h₀) (rw_star_sub_ScaledAdd₃ h₁)
  theorem rw_star_sub_ScaledAdd₄ {a₀ a₁ a₂ a₃ a b : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledAdd a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (ScaledAdd a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledAdd₄ h)
    | .refl h => .refl (eqe_ScaledAdd (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledAdd₄ h₀) (rw_star_sub_ScaledAdd₄ h₁)
  theorem rw_star_sub_ScaledAdd₅ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a b : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledAdd a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (ScaledAdd a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledAdd₅ h)
    | .refl h => .refl (eqe_ScaledAdd (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledAdd₅ h₀) (rw_star_sub_ScaledAdd₅ h₁)
  theorem rw_star_sub_ScaledAdd₆ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a b a₇ a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledAdd a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (ScaledAdd a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledAdd₆ h)
    | .refl h => .refl (eqe_ScaledAdd (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledAdd₆ h₀) (rw_star_sub_ScaledAdd₆ h₁)
  theorem rw_star_sub_ScaledAdd₇ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a b a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (ScaledAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledAdd₇ h)
    | .refl h => .refl (eqe_ScaledAdd (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledAdd₇ h₀) (rw_star_sub_ScaledAdd₇ h₁)
  theorem rw_star_sub_ScaledAdd₈ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a b a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (ScaledAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | .step h => .step (rw_one.sub_ScaledAdd₈ h)
    | .refl h => .refl (eqe_ScaledAdd (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledAdd₈ h₀) (rw_star_sub_ScaledAdd₈ h₁)
  theorem rw_star_sub_ScaledAdd₉ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (ScaledAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | .step h => .step (rw_one.sub_ScaledAdd₉ h)
    | .refl h => .refl (eqe_ScaledAdd (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledAdd₉ h₀) (rw_star_sub_ScaledAdd₉ h₁)
  theorem rw_star_sub_ScaledSubtract₀ {a b a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSubtract a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledSubtract b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledSubtract₀ h)
    | .refl h => .refl (eqe_ScaledSubtract h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSubtract₀ h₀) (rw_star_sub_ScaledSubtract₀ h₁)
  theorem rw_star_sub_ScaledSubtract₁ {a₀ a b a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSubtract a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledSubtract a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledSubtract₁ h)
    | .refl h => .refl (eqe_ScaledSubtract (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSubtract₁ h₀) (rw_star_sub_ScaledSubtract₁ h₁)
  theorem rw_star_sub_ScaledSubtract₂ {a₀ a₁ a b a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSubtract a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledSubtract a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledSubtract₂ h)
    | .refl h => .refl (eqe_ScaledSubtract (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSubtract₂ h₀) (rw_star_sub_ScaledSubtract₂ h₁)
  theorem rw_star_sub_ScaledSubtract₃ {a₀ a₁ a₂ a b a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSubtract a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (ScaledSubtract a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledSubtract₃ h)
    | .refl h => .refl (eqe_ScaledSubtract (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSubtract₃ h₀) (rw_star_sub_ScaledSubtract₃ h₁)
  theorem rw_star_sub_ScaledSubtract₄ {a₀ a₁ a₂ a₃ a b : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSubtract a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (ScaledSubtract a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledSubtract₄ h)
    | .refl h => .refl (eqe_ScaledSubtract (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSubtract₄ h₀) (rw_star_sub_ScaledSubtract₄ h₁)
  theorem rw_star_sub_ScaledSubtract₅ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a b : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSubtract a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (ScaledSubtract a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledSubtract₅ h)
    | .refl h => .refl (eqe_ScaledSubtract (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSubtract₅ h₀) (rw_star_sub_ScaledSubtract₅ h₁)
  theorem rw_star_sub_ScaledSubtract₆ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a b a₇ a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledSubtract a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (ScaledSubtract a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledSubtract₆ h)
    | .refl h => .refl (eqe_ScaledSubtract (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSubtract₆ h₀) (rw_star_sub_ScaledSubtract₆ h₁)
  theorem rw_star_sub_ScaledSubtract₇ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a b a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (ScaledSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledSubtract₇ h)
    | .refl h => .refl (eqe_ScaledSubtract (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSubtract₇ h₀) (rw_star_sub_ScaledSubtract₇ h₁)
  theorem rw_star_sub_ScaledSubtract₈ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a b a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (ScaledSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | .step h => .step (rw_one.sub_ScaledSubtract₈ h)
    | .refl h => .refl (eqe_ScaledSubtract (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSubtract₈ h₀) (rw_star_sub_ScaledSubtract₈ h₁)
  theorem rw_star_sub_ScaledSubtract₉ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (ScaledSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | .step h => .step (rw_one.sub_ScaledSubtract₉ h)
    | .refl h => .refl (eqe_ScaledSubtract (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSubtract₉ h₀) (rw_star_sub_ScaledSubtract₉ h₁)
  theorem rw_star_sub_ScaledMultiply₀ {a b a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMultiply a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMultiply b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMultiply₀ h)
    | .refl h => .refl (eqe_ScaledMultiply h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMultiply₀ h₀) (rw_star_sub_ScaledMultiply₀ h₁)
  theorem rw_star_sub_ScaledMultiply₁ {a₀ a b a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMultiply a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMultiply a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMultiply₁ h)
    | .refl h => .refl (eqe_ScaledMultiply (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMultiply₁ h₀) (rw_star_sub_ScaledMultiply₁ h₁)
  theorem rw_star_sub_ScaledMultiply₂ {a₀ a₁ a b a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMultiply a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMultiply a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMultiply₂ h)
    | .refl h => .refl (eqe_ScaledMultiply (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMultiply₂ h₀) (rw_star_sub_ScaledMultiply₂ h₁)
  theorem rw_star_sub_ScaledMultiply₃ {a₀ a₁ a₂ a b a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMultiply a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMultiply a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMultiply₃ h)
    | .refl h => .refl (eqe_ScaledMultiply (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMultiply₃ h₀) (rw_star_sub_ScaledMultiply₃ h₁)
  theorem rw_star_sub_ScaledMultiply₄ {a₀ a₁ a₂ a₃ a b : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMultiply a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (ScaledMultiply a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMultiply₄ h)
    | .refl h => .refl (eqe_ScaledMultiply (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMultiply₄ h₀) (rw_star_sub_ScaledMultiply₄ h₁)
  theorem rw_star_sub_ScaledMultiply₅ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a b : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMultiply a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (ScaledMultiply a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMultiply₅ h)
    | .refl h => .refl (eqe_ScaledMultiply (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMultiply₅ h₀) (rw_star_sub_ScaledMultiply₅ h₁)
  theorem rw_star_sub_ScaledMultiply₆ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a b a₇ a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMultiply a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (ScaledMultiply a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMultiply₆ h)
    | .refl h => .refl (eqe_ScaledMultiply (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMultiply₆ h₀) (rw_star_sub_ScaledMultiply₆ h₁)
  theorem rw_star_sub_ScaledMultiply₇ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a b a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (ScaledMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMultiply₇ h)
    | .refl h => .refl (eqe_ScaledMultiply (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMultiply₇ h₀) (rw_star_sub_ScaledMultiply₇ h₁)
  theorem rw_star_sub_ScaledMultiply₈ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a b a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (ScaledMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | .step h => .step (rw_one.sub_ScaledMultiply₈ h)
    | .refl h => .refl (eqe_ScaledMultiply (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMultiply₈ h₀) (rw_star_sub_ScaledMultiply₈ h₁)
  theorem rw_star_sub_ScaledMultiply₉ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (ScaledMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | .step h => .step (rw_one.sub_ScaledMultiply₉ h)
    | .refl h => .refl (eqe_ScaledMultiply (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMultiply₉ h₀) (rw_star_sub_ScaledMultiply₉ h₁)
  theorem rw_star_sub_ScaledDivide₀ {a b a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledDivide a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledDivide b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledDivide₀ h)
    | .refl h => .refl (eqe_ScaledDivide h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledDivide₀ h₀) (rw_star_sub_ScaledDivide₀ h₁)
  theorem rw_star_sub_ScaledDivide₁ {a₀ a b a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledDivide a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledDivide a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledDivide₁ h)
    | .refl h => .refl (eqe_ScaledDivide (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledDivide₁ h₀) (rw_star_sub_ScaledDivide₁ h₁)
  theorem rw_star_sub_ScaledDivide₂ {a₀ a₁ a b a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledDivide a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledDivide a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledDivide₂ h)
    | .refl h => .refl (eqe_ScaledDivide (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledDivide₂ h₀) (rw_star_sub_ScaledDivide₂ h₁)
  theorem rw_star_sub_ScaledDivide₃ {a₀ a₁ a₂ a b a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledDivide a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (ScaledDivide a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledDivide₃ h)
    | .refl h => .refl (eqe_ScaledDivide (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledDivide₃ h₀) (rw_star_sub_ScaledDivide₃ h₁)
  theorem rw_star_sub_ScaledDivide₄ {a₀ a₁ a₂ a₃ a b : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledDivide a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (ScaledDivide a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledDivide₄ h)
    | .refl h => .refl (eqe_ScaledDivide (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledDivide₄ h₀) (rw_star_sub_ScaledDivide₄ h₁)
  theorem rw_star_sub_ScaledDivide₅ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a b : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledDivide a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (ScaledDivide a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledDivide₅ h)
    | .refl h => .refl (eqe_ScaledDivide (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledDivide₅ h₀) (rw_star_sub_ScaledDivide₅ h₁)
  theorem rw_star_sub_ScaledDivide₆ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a b a₇ a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledDivide a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (ScaledDivide a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledDivide₆ h)
    | .refl h => .refl (eqe_ScaledDivide (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledDivide₆ h₀) (rw_star_sub_ScaledDivide₆ h₁)
  theorem rw_star_sub_ScaledDivide₇ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a b a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (ScaledDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledDivide₇ h)
    | .refl h => .refl (eqe_ScaledDivide (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledDivide₇ h₀) (rw_star_sub_ScaledDivide₇ h₁)
  theorem rw_star_sub_ScaledDivide₈ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a b a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (ScaledDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | .step h => .step (rw_one.sub_ScaledDivide₈ h)
    | .refl h => .refl (eqe_ScaledDivide (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledDivide₈ h₀) (rw_star_sub_ScaledDivide₈ h₁)
  theorem rw_star_sub_ScaledDivide₉ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (ScaledDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | .step h => .step (rw_one.sub_ScaledDivide₉ h)
    | .refl h => .refl (eqe_ScaledDivide (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledDivide₉ h₀) (rw_star_sub_ScaledDivide₉ h₁)
  theorem rw_star_sub_ScaledFMA₀ {a b a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledFMA a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFMA b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFMA₀ h)
    | .refl h => .refl (eqe_ScaledFMA h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFMA₀ h₀) (rw_star_sub_ScaledFMA₀ h₁)
  theorem rw_star_sub_ScaledFMA₁ {a₀ a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledFMA a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFMA a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFMA₁ h)
    | .refl h => .refl (eqe_ScaledFMA (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFMA₁ h₀) (rw_star_sub_ScaledFMA₁ h₁)
  theorem rw_star_sub_ScaledFMA₂ {a₀ a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledFMA a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFMA a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFMA₂ h)
    | .refl h => .refl (eqe_ScaledFMA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFMA₂ h₀) (rw_star_sub_ScaledFMA₂ h₁)
  theorem rw_star_sub_ScaledFMA₃ {a₀ a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledFMA a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFMA a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFMA₃ h)
    | .refl h => .refl (eqe_ScaledFMA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFMA₃ h₀) (rw_star_sub_ScaledFMA₃ h₁)
  theorem rw_star_sub_ScaledFMA₄ {a₀ a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledFMA a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFMA a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFMA₄ h)
    | .refl h => .refl (eqe_ScaledFMA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFMA₄ h₀) (rw_star_sub_ScaledFMA₄ h₁)
  theorem rw_star_sub_ScaledFMA₅ {a₀ a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledFMA a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFMA a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFMA₅ h)
    | .refl h => .refl (eqe_ScaledFMA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFMA₅ h₀) (rw_star_sub_ScaledFMA₅ h₁)
  theorem rw_star_sub_ScaledFMA₆ {a₀ a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFMA₆ h)
    | .refl h => .refl (eqe_ScaledFMA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFMA₆ h₀) (rw_star_sub_ScaledFMA₆ h₁)
  theorem rw_star_sub_ScaledFMA₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFMA₇ h)
    | .refl h => .refl (eqe_ScaledFMA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFMA₇ h₀) (rw_star_sub_ScaledFMA₇ h₁)
  theorem rw_star_sub_ScaledFMA₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a b a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFMA₈ h)
    | .refl h => .refl (eqe_ScaledFMA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) h rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFMA₈ h₀) (rw_star_sub_ScaledFMA₈ h₁)
  theorem rw_star_sub_ScaledFMA₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a b a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFMA₉ h)
    | .refl h => .refl (eqe_ScaledFMA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFMA₉ h₀) (rw_star_sub_ScaledFMA₉ h₁)
  theorem rw_star_sub_ScaledFMA₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a b a₁₁ a₁₂ a₁₃ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂ a₁₃) (ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFMA₁₀ h)
    | .refl h => .refl (eqe_ScaledFMA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFMA₁₀ h₀) (rw_star_sub_ScaledFMA₁₀ h₁)
  theorem rw_star_sub_ScaledFMA₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a b a₁₂ a₁₃ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂ a₁₃) (ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFMA₁₁ h)
    | .refl h => .refl (eqe_ScaledFMA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFMA₁₁ h₀) (rw_star_sub_ScaledFMA₁₁ h₁)
  theorem rw_star_sub_ScaledFMA₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a b a₁₃ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a a₁₃) (ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b a₁₃)
    | .step h => .step (rw_one.sub_ScaledFMA₁₂ h)
    | .refl h => .refl (eqe_ScaledFMA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFMA₁₂ h₀) (rw_star_sub_ScaledFMA₁₂ h₁)
  theorem rw_star_sub_ScaledFMA₁₃ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a) (ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b)
    | .step h => .step (rw_one.sub_ScaledFMA₁₃ h)
    | .refl h => .refl (eqe_ScaledFMA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFMA₁₃ h₀) (rw_star_sub_ScaledFMA₁₃ h₁)
  theorem rw_star_sub_ScaledFAA₀ {a b a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledFAA a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFAA b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFAA₀ h)
    | .refl h => .refl (eqe_ScaledFAA h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFAA₀ h₀) (rw_star_sub_ScaledFAA₀ h₁)
  theorem rw_star_sub_ScaledFAA₁ {a₀ a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledFAA a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFAA a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFAA₁ h)
    | .refl h => .refl (eqe_ScaledFAA (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFAA₁ h₀) (rw_star_sub_ScaledFAA₁ h₁)
  theorem rw_star_sub_ScaledFAA₂ {a₀ a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledFAA a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFAA a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFAA₂ h)
    | .refl h => .refl (eqe_ScaledFAA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFAA₂ h₀) (rw_star_sub_ScaledFAA₂ h₁)
  theorem rw_star_sub_ScaledFAA₃ {a₀ a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledFAA a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFAA a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFAA₃ h)
    | .refl h => .refl (eqe_ScaledFAA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFAA₃ h₀) (rw_star_sub_ScaledFAA₃ h₁)
  theorem rw_star_sub_ScaledFAA₄ {a₀ a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledFAA a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFAA a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFAA₄ h)
    | .refl h => .refl (eqe_ScaledFAA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFAA₄ h₀) (rw_star_sub_ScaledFAA₄ h₁)
  theorem rw_star_sub_ScaledFAA₅ {a₀ a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledFAA a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFAA a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFAA₅ h)
    | .refl h => .refl (eqe_ScaledFAA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFAA₅ h₀) (rw_star_sub_ScaledFAA₅ h₁)
  theorem rw_star_sub_ScaledFAA₆ {a₀ a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFAA₆ h)
    | .refl h => .refl (eqe_ScaledFAA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFAA₆ h₀) (rw_star_sub_ScaledFAA₆ h₁)
  theorem rw_star_sub_ScaledFAA₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFAA₇ h)
    | .refl h => .refl (eqe_ScaledFAA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFAA₇ h₀) (rw_star_sub_ScaledFAA₇ h₁)
  theorem rw_star_sub_ScaledFAA₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a b a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFAA₈ h)
    | .refl h => .refl (eqe_ScaledFAA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) h rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFAA₈ h₀) (rw_star_sub_ScaledFAA₈ h₁)
  theorem rw_star_sub_ScaledFAA₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a b a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂ a₁₃) (ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFAA₉ h)
    | .refl h => .refl (eqe_ScaledFAA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFAA₉ h₀) (rw_star_sub_ScaledFAA₉ h₁)
  theorem rw_star_sub_ScaledFAA₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a b a₁₁ a₁₂ a₁₃ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂ a₁₃) (ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFAA₁₀ h)
    | .refl h => .refl (eqe_ScaledFAA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFAA₁₀ h₀) (rw_star_sub_ScaledFAA₁₀ h₁)
  theorem rw_star_sub_ScaledFAA₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a b a₁₂ a₁₃ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂ a₁₃) (ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledFAA₁₁ h)
    | .refl h => .refl (eqe_ScaledFAA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFAA₁₁ h₀) (rw_star_sub_ScaledFAA₁₁ h₁)
  theorem rw_star_sub_ScaledFAA₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a b a₁₃ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a a₁₃) (ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b a₁₃)
    | .step h => .step (rw_one.sub_ScaledFAA₁₂ h)
    | .refl h => .refl (eqe_ScaledFAA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFAA₁₂ h₀) (rw_star_sub_ScaledFAA₁₂ h₁)
  theorem rw_star_sub_ScaledFAA₁₃ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a) (ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b)
    | .step h => .step (rw_one.sub_ScaledFAA₁₃ h)
    | .refl h => .refl (eqe_ScaledFAA (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledFAA₁₃ h₀) (rw_star_sub_ScaledFAA₁₃ h₁)
  theorem rw_star_sub_ScaledRecip₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledRecip a a₁ a₂ a₃ a₄ a₅) (ScaledRecip b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledRecip₀ h)
    | .refl h => .refl (eqe_ScaledRecip h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledRecip₀ h₀) (rw_star_sub_ScaledRecip₀ h₁)
  theorem rw_star_sub_ScaledRecip₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledRecip a₀ a a₂ a₃ a₄ a₅) (ScaledRecip a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledRecip₁ h)
    | .refl h => .refl (eqe_ScaledRecip (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledRecip₁ h₀) (rw_star_sub_ScaledRecip₁ h₁)
  theorem rw_star_sub_ScaledRecip₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledRecip a₀ a₁ a a₃ a₄ a₅) (ScaledRecip a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledRecip₂ h)
    | .refl h => .refl (eqe_ScaledRecip (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledRecip₂ h₀) (rw_star_sub_ScaledRecip₂ h₁)
  theorem rw_star_sub_ScaledRecip₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledRecip a₀ a₁ a₂ a a₄ a₅) (ScaledRecip a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledRecip₃ h)
    | .refl h => .refl (eqe_ScaledRecip (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledRecip₃ h₀) (rw_star_sub_ScaledRecip₃ h₁)
  theorem rw_star_sub_ScaledRecip₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledRecip a₀ a₁ a₂ a₃ a a₅) (ScaledRecip a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledRecip₄ h)
    | .refl h => .refl (eqe_ScaledRecip (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledRecip₄ h₀) (rw_star_sub_ScaledRecip₄ h₁)
  theorem rw_star_sub_ScaledRecip₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledRecip a₀ a₁ a₂ a₃ a₄ a) (ScaledRecip a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledRecip₅ h)
    | .refl h => .refl (eqe_ScaledRecip (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledRecip₅ h₀) (rw_star_sub_ScaledRecip₅ h₁)
  theorem rw_star_sub_ScaledMinimum₀ {a b a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimum a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimum b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimum₀ h)
    | .refl h => .refl (eqe_ScaledMinimum h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimum₀ h₀) (rw_star_sub_ScaledMinimum₀ h₁)
  theorem rw_star_sub_ScaledMinimum₁ {a₀ a b a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimum a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimum a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimum₁ h)
    | .refl h => .refl (eqe_ScaledMinimum (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimum₁ h₀) (rw_star_sub_ScaledMinimum₁ h₁)
  theorem rw_star_sub_ScaledMinimum₂ {a₀ a₁ a b a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimum a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimum a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimum₂ h)
    | .refl h => .refl (eqe_ScaledMinimum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimum₂ h₀) (rw_star_sub_ScaledMinimum₂ h₁)
  theorem rw_star_sub_ScaledMinimum₃ {a₀ a₁ a₂ a b a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimum a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimum a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimum₃ h)
    | .refl h => .refl (eqe_ScaledMinimum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimum₃ h₀) (rw_star_sub_ScaledMinimum₃ h₁)
  theorem rw_star_sub_ScaledMinimum₄ {a₀ a₁ a₂ a₃ a b : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimum a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (ScaledMinimum a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimum₄ h)
    | .refl h => .refl (eqe_ScaledMinimum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimum₄ h₀) (rw_star_sub_ScaledMinimum₄ h₁)
  theorem rw_star_sub_ScaledMinimum₅ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a b : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimum a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (ScaledMinimum a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimum₅ h)
    | .refl h => .refl (eqe_ScaledMinimum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimum₅ h₀) (rw_star_sub_ScaledMinimum₅ h₁)
  theorem rw_star_sub_ScaledMinimum₆ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a b a₇ a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimum a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (ScaledMinimum a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimum₆ h)
    | .refl h => .refl (eqe_ScaledMinimum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimum₆ h₀) (rw_star_sub_ScaledMinimum₆ h₁)
  theorem rw_star_sub_ScaledMinimum₇ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a b a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (ScaledMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimum₇ h)
    | .refl h => .refl (eqe_ScaledMinimum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimum₇ h₀) (rw_star_sub_ScaledMinimum₇ h₁)
  theorem rw_star_sub_ScaledMinimum₈ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a b a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (ScaledMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | .step h => .step (rw_one.sub_ScaledMinimum₈ h)
    | .refl h => .refl (eqe_ScaledMinimum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimum₈ h₀) (rw_star_sub_ScaledMinimum₈ h₁)
  theorem rw_star_sub_ScaledMinimum₉ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (ScaledMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | .step h => .step (rw_one.sub_ScaledMinimum₉ h)
    | .refl h => .refl (eqe_ScaledMinimum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimum₉ h₀) (rw_star_sub_ScaledMinimum₉ h₁)
  theorem rw_star_sub_ScaledMaximum₀ {a b a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximum a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximum b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximum₀ h)
    | .refl h => .refl (eqe_ScaledMaximum h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximum₀ h₀) (rw_star_sub_ScaledMaximum₀ h₁)
  theorem rw_star_sub_ScaledMaximum₁ {a₀ a b a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximum a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximum a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximum₁ h)
    | .refl h => .refl (eqe_ScaledMaximum (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximum₁ h₀) (rw_star_sub_ScaledMaximum₁ h₁)
  theorem rw_star_sub_ScaledMaximum₂ {a₀ a₁ a b a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximum a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximum a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximum₂ h)
    | .refl h => .refl (eqe_ScaledMaximum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximum₂ h₀) (rw_star_sub_ScaledMaximum₂ h₁)
  theorem rw_star_sub_ScaledMaximum₃ {a₀ a₁ a₂ a b a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximum a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximum a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximum₃ h)
    | .refl h => .refl (eqe_ScaledMaximum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximum₃ h₀) (rw_star_sub_ScaledMaximum₃ h₁)
  theorem rw_star_sub_ScaledMaximum₄ {a₀ a₁ a₂ a₃ a b : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximum a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (ScaledMaximum a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximum₄ h)
    | .refl h => .refl (eqe_ScaledMaximum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximum₄ h₀) (rw_star_sub_ScaledMaximum₄ h₁)
  theorem rw_star_sub_ScaledMaximum₅ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a b : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximum a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (ScaledMaximum a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximum₅ h)
    | .refl h => .refl (eqe_ScaledMaximum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximum₅ h₀) (rw_star_sub_ScaledMaximum₅ h₁)
  theorem rw_star_sub_ScaledMaximum₆ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a b a₇ a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximum a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (ScaledMaximum a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximum₆ h)
    | .refl h => .refl (eqe_ScaledMaximum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximum₆ h₀) (rw_star_sub_ScaledMaximum₆ h₁)
  theorem rw_star_sub_ScaledMaximum₇ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a b a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (ScaledMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximum₇ h)
    | .refl h => .refl (eqe_ScaledMaximum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximum₇ h₀) (rw_star_sub_ScaledMaximum₇ h₁)
  theorem rw_star_sub_ScaledMaximum₈ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a b a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (ScaledMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | .step h => .step (rw_one.sub_ScaledMaximum₈ h)
    | .refl h => .refl (eqe_ScaledMaximum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximum₈ h₀) (rw_star_sub_ScaledMaximum₈ h₁)
  theorem rw_star_sub_ScaledMaximum₉ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (ScaledMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | .step h => .step (rw_one.sub_ScaledMaximum₉ h)
    | .refl h => .refl (eqe_ScaledMaximum (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximum₉ h₀) (rw_star_sub_ScaledMaximum₉ h₁)
  theorem rw_star_sub_ScaledMinimumNumber₀ {a b a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumNumber a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimumNumber b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumNumber₀ h)
    | .refl h => .refl (eqe_ScaledMinimumNumber h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumNumber₀ h₀) (rw_star_sub_ScaledMinimumNumber₀ h₁)
  theorem rw_star_sub_ScaledMinimumNumber₁ {a₀ a b a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumNumber a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimumNumber a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumNumber₁ h)
    | .refl h => .refl (eqe_ScaledMinimumNumber (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumNumber₁ h₀) (rw_star_sub_ScaledMinimumNumber₁ h₁)
  theorem rw_star_sub_ScaledMinimumNumber₂ {a₀ a₁ a b a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumNumber a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimumNumber a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumNumber₂ h)
    | .refl h => .refl (eqe_ScaledMinimumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumNumber₂ h₀) (rw_star_sub_ScaledMinimumNumber₂ h₁)
  theorem rw_star_sub_ScaledMinimumNumber₃ {a₀ a₁ a₂ a b a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumNumber a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimumNumber a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumNumber₃ h)
    | .refl h => .refl (eqe_ScaledMinimumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumNumber₃ h₀) (rw_star_sub_ScaledMinimumNumber₃ h₁)
  theorem rw_star_sub_ScaledMinimumNumber₄ {a₀ a₁ a₂ a₃ a b : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumNumber a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (ScaledMinimumNumber a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumNumber₄ h)
    | .refl h => .refl (eqe_ScaledMinimumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumNumber₄ h₀) (rw_star_sub_ScaledMinimumNumber₄ h₁)
  theorem rw_star_sub_ScaledMinimumNumber₅ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a b : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumNumber₅ h)
    | .refl h => .refl (eqe_ScaledMinimumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumNumber₅ h₀) (rw_star_sub_ScaledMinimumNumber₅ h₁)
  theorem rw_star_sub_ScaledMinimumNumber₆ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a b a₇ a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumNumber₆ h)
    | .refl h => .refl (eqe_ScaledMinimumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumNumber₆ h₀) (rw_star_sub_ScaledMinimumNumber₆ h₁)
  theorem rw_star_sub_ScaledMinimumNumber₇ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a b a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumNumber₇ h)
    | .refl h => .refl (eqe_ScaledMinimumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumNumber₇ h₀) (rw_star_sub_ScaledMinimumNumber₇ h₁)
  theorem rw_star_sub_ScaledMinimumNumber₈ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a b a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumNumber₈ h)
    | .refl h => .refl (eqe_ScaledMinimumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumNumber₈ h₀) (rw_star_sub_ScaledMinimumNumber₈ h₁)
  theorem rw_star_sub_ScaledMinimumNumber₉ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | .step h => .step (rw_one.sub_ScaledMinimumNumber₉ h)
    | .refl h => .refl (eqe_ScaledMinimumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumNumber₉ h₀) (rw_star_sub_ScaledMinimumNumber₉ h₁)
  theorem rw_star_sub_ScaledMaximumNumber₀ {a b a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumNumber a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximumNumber b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumNumber₀ h)
    | .refl h => .refl (eqe_ScaledMaximumNumber h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumNumber₀ h₀) (rw_star_sub_ScaledMaximumNumber₀ h₁)
  theorem rw_star_sub_ScaledMaximumNumber₁ {a₀ a b a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumNumber a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximumNumber a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumNumber₁ h)
    | .refl h => .refl (eqe_ScaledMaximumNumber (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumNumber₁ h₀) (rw_star_sub_ScaledMaximumNumber₁ h₁)
  theorem rw_star_sub_ScaledMaximumNumber₂ {a₀ a₁ a b a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumNumber a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximumNumber a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumNumber₂ h)
    | .refl h => .refl (eqe_ScaledMaximumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumNumber₂ h₀) (rw_star_sub_ScaledMaximumNumber₂ h₁)
  theorem rw_star_sub_ScaledMaximumNumber₃ {a₀ a₁ a₂ a b a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumNumber a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximumNumber a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumNumber₃ h)
    | .refl h => .refl (eqe_ScaledMaximumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumNumber₃ h₀) (rw_star_sub_ScaledMaximumNumber₃ h₁)
  theorem rw_star_sub_ScaledMaximumNumber₄ {a₀ a₁ a₂ a₃ a b : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumNumber a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (ScaledMaximumNumber a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumNumber₄ h)
    | .refl h => .refl (eqe_ScaledMaximumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumNumber₄ h₀) (rw_star_sub_ScaledMaximumNumber₄ h₁)
  theorem rw_star_sub_ScaledMaximumNumber₅ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a b : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumNumber₅ h)
    | .refl h => .refl (eqe_ScaledMaximumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumNumber₅ h₀) (rw_star_sub_ScaledMaximumNumber₅ h₁)
  theorem rw_star_sub_ScaledMaximumNumber₆ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a b a₇ a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumNumber₆ h)
    | .refl h => .refl (eqe_ScaledMaximumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumNumber₆ h₀) (rw_star_sub_ScaledMaximumNumber₆ h₁)
  theorem rw_star_sub_ScaledMaximumNumber₇ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a b a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumNumber₇ h)
    | .refl h => .refl (eqe_ScaledMaximumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumNumber₇ h₀) (rw_star_sub_ScaledMaximumNumber₇ h₁)
  theorem rw_star_sub_ScaledMaximumNumber₈ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a b a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumNumber₈ h)
    | .refl h => .refl (eqe_ScaledMaximumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumNumber₈ h₀) (rw_star_sub_ScaledMaximumNumber₈ h₁)
  theorem rw_star_sub_ScaledMaximumNumber₉ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | .step h => .step (rw_one.sub_ScaledMaximumNumber₉ h)
    | .refl h => .refl (eqe_ScaledMaximumNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumNumber₉ h₀) (rw_star_sub_ScaledMaximumNumber₉ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitude₀ {a b a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumMagnitude a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimumMagnitude b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitude₀ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitude h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitude₀ h₀) (rw_star_sub_ScaledMinimumMagnitude₀ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitude₁ {a₀ a b a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumMagnitude a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimumMagnitude a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitude₁ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitude (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitude₁ h₀) (rw_star_sub_ScaledMinimumMagnitude₁ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitude₂ {a₀ a₁ a b a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumMagnitude a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimumMagnitude a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitude₂ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitude₂ h₀) (rw_star_sub_ScaledMinimumMagnitude₂ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitude₃ {a₀ a₁ a₂ a b a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumMagnitude a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimumMagnitude a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitude₃ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitude₃ h₀) (rw_star_sub_ScaledMinimumMagnitude₃ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitude₄ {a₀ a₁ a₂ a₃ a b : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (ScaledMinimumMagnitude a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitude₄ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitude₄ h₀) (rw_star_sub_ScaledMinimumMagnitude₄ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitude₅ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a b : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitude₅ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitude₅ h₀) (rw_star_sub_ScaledMinimumMagnitude₅ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitude₆ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a b a₇ a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitude₆ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitude₆ h₀) (rw_star_sub_ScaledMinimumMagnitude₆ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitude₇ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a b a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitude₇ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitude₇ h₀) (rw_star_sub_ScaledMinimumMagnitude₇ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitude₈ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a b a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitude₈ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitude₈ h₀) (rw_star_sub_ScaledMinimumMagnitude₈ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitude₉ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitude₉ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitude₉ h₀) (rw_star_sub_ScaledMinimumMagnitude₉ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitude₀ {a b a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumMagnitude a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximumMagnitude b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitude₀ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitude h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitude₀ h₀) (rw_star_sub_ScaledMaximumMagnitude₀ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitude₁ {a₀ a b a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumMagnitude a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximumMagnitude a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitude₁ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitude (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitude₁ h₀) (rw_star_sub_ScaledMaximumMagnitude₁ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitude₂ {a₀ a₁ a b a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumMagnitude a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximumMagnitude a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitude₂ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitude₂ h₀) (rw_star_sub_ScaledMaximumMagnitude₂ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitude₃ {a₀ a₁ a₂ a b a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumMagnitude a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximumMagnitude a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitude₃ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitude₃ h₀) (rw_star_sub_ScaledMaximumMagnitude₃ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitude₄ {a₀ a₁ a₂ a₃ a b : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (ScaledMaximumMagnitude a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitude₄ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitude₄ h₀) (rw_star_sub_ScaledMaximumMagnitude₄ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitude₅ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a b : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitude₅ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitude₅ h₀) (rw_star_sub_ScaledMaximumMagnitude₅ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitude₆ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a b a₇ a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitude₆ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitude₆ h₀) (rw_star_sub_ScaledMaximumMagnitude₆ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitude₇ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a b a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitude₇ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitude₇ h₀) (rw_star_sub_ScaledMaximumMagnitude₇ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitude₈ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a b a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitude₈ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitude₈ h₀) (rw_star_sub_ScaledMaximumMagnitude₈ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitude₉ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitude₉ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitude (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitude₉ h₀) (rw_star_sub_ScaledMaximumMagnitude₉ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitudeNumber₀ {a b a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumMagnitudeNumber a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimumMagnitudeNumber b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitudeNumber₀ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitudeNumber h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitudeNumber₀ h₀) (rw_star_sub_ScaledMinimumMagnitudeNumber₀ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitudeNumber₁ {a₀ a b a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumMagnitudeNumber a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimumMagnitudeNumber a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitudeNumber₁ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitudeNumber (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitudeNumber₁ h₀) (rw_star_sub_ScaledMinimumMagnitudeNumber₁ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitudeNumber₂ {a₀ a₁ a b a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumMagnitudeNumber a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimumMagnitudeNumber a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitudeNumber₂ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitudeNumber₂ h₀) (rw_star_sub_ScaledMinimumMagnitudeNumber₂ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitudeNumber₃ {a₀ a₁ a₂ a b a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimumMagnitudeNumber a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitudeNumber₃ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitudeNumber₃ h₀) (rw_star_sub_ScaledMinimumMagnitudeNumber₃ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitudeNumber₄ {a₀ a₁ a₂ a₃ a b : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitudeNumber₄ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitudeNumber₄ h₀) (rw_star_sub_ScaledMinimumMagnitudeNumber₄ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitudeNumber₅ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a b : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitudeNumber₅ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitudeNumber₅ h₀) (rw_star_sub_ScaledMinimumMagnitudeNumber₅ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitudeNumber₆ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a b a₇ a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitudeNumber₆ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitudeNumber₆ h₀) (rw_star_sub_ScaledMinimumMagnitudeNumber₆ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitudeNumber₇ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a b a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitudeNumber₇ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitudeNumber₇ h₀) (rw_star_sub_ScaledMinimumMagnitudeNumber₇ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitudeNumber₈ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a b a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitudeNumber₈ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitudeNumber₈ h₀) (rw_star_sub_ScaledMinimumMagnitudeNumber₈ h₁)
  theorem rw_star_sub_ScaledMinimumMagnitudeNumber₉ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | .step h => .step (rw_one.sub_ScaledMinimumMagnitudeNumber₉ h)
    | .refl h => .refl (eqe_ScaledMinimumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumMagnitudeNumber₉ h₀) (rw_star_sub_ScaledMinimumMagnitudeNumber₉ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitudeNumber₀ {a b a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumMagnitudeNumber a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximumMagnitudeNumber b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitudeNumber₀ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitudeNumber h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitudeNumber₀ h₀) (rw_star_sub_ScaledMaximumMagnitudeNumber₀ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitudeNumber₁ {a₀ a b a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumMagnitudeNumber a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximumMagnitudeNumber a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitudeNumber₁ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitudeNumber (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitudeNumber₁ h₀) (rw_star_sub_ScaledMaximumMagnitudeNumber₁ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitudeNumber₂ {a₀ a₁ a b a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumMagnitudeNumber a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximumMagnitudeNumber a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitudeNumber₂ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitudeNumber₂ h₀) (rw_star_sub_ScaledMaximumMagnitudeNumber₂ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitudeNumber₃ {a₀ a₁ a₂ a b a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximumMagnitudeNumber a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitudeNumber₃ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitudeNumber₃ h₀) (rw_star_sub_ScaledMaximumMagnitudeNumber₃ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitudeNumber₄ {a₀ a₁ a₂ a₃ a b : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitudeNumber₄ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitudeNumber₄ h₀) (rw_star_sub_ScaledMaximumMagnitudeNumber₄ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitudeNumber₅ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a b : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitudeNumber₅ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitudeNumber₅ h₀) (rw_star_sub_ScaledMaximumMagnitudeNumber₅ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitudeNumber₆ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a b a₇ a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitudeNumber₆ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitudeNumber₆ h₀) (rw_star_sub_ScaledMaximumMagnitudeNumber₆ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitudeNumber₇ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a b a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitudeNumber₇ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitudeNumber₇ h₀) (rw_star_sub_ScaledMaximumMagnitudeNumber₇ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitudeNumber₈ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a b a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitudeNumber₈ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitudeNumber₈ h₀) (rw_star_sub_ScaledMaximumMagnitudeNumber₈ h₁)
  theorem rw_star_sub_ScaledMaximumMagnitudeNumber₉ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | .step h => .step (rw_one.sub_ScaledMaximumMagnitudeNumber₉ h)
    | .refl h => .refl (eqe_ScaledMaximumMagnitudeNumber (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumMagnitudeNumber₉ h₀) (rw_star_sub_ScaledMaximumMagnitudeNumber₉ h₁)
  theorem rw_star_sub_ScaledMinimumFinite₀ {a b a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumFinite a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimumFinite b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumFinite₀ h)
    | .refl h => .refl (eqe_ScaledMinimumFinite h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumFinite₀ h₀) (rw_star_sub_ScaledMinimumFinite₀ h₁)
  theorem rw_star_sub_ScaledMinimumFinite₁ {a₀ a b a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumFinite a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimumFinite a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumFinite₁ h)
    | .refl h => .refl (eqe_ScaledMinimumFinite (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumFinite₁ h₀) (rw_star_sub_ScaledMinimumFinite₁ h₁)
  theorem rw_star_sub_ScaledMinimumFinite₂ {a₀ a₁ a b a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumFinite a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimumFinite a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumFinite₂ h)
    | .refl h => .refl (eqe_ScaledMinimumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumFinite₂ h₀) (rw_star_sub_ScaledMinimumFinite₂ h₁)
  theorem rw_star_sub_ScaledMinimumFinite₃ {a₀ a₁ a₂ a b a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumFinite a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMinimumFinite a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumFinite₃ h)
    | .refl h => .refl (eqe_ScaledMinimumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumFinite₃ h₀) (rw_star_sub_ScaledMinimumFinite₃ h₁)
  theorem rw_star_sub_ScaledMinimumFinite₄ {a₀ a₁ a₂ a₃ a b : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumFinite a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (ScaledMinimumFinite a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumFinite₄ h)
    | .refl h => .refl (eqe_ScaledMinimumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumFinite₄ h₀) (rw_star_sub_ScaledMinimumFinite₄ h₁)
  theorem rw_star_sub_ScaledMinimumFinite₅ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a b : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumFinite₅ h)
    | .refl h => .refl (eqe_ScaledMinimumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumFinite₅ h₀) (rw_star_sub_ScaledMinimumFinite₅ h₁)
  theorem rw_star_sub_ScaledMinimumFinite₆ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a b a₇ a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumFinite₆ h)
    | .refl h => .refl (eqe_ScaledMinimumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumFinite₆ h₀) (rw_star_sub_ScaledMinimumFinite₆ h₁)
  theorem rw_star_sub_ScaledMinimumFinite₇ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a b a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumFinite₇ h)
    | .refl h => .refl (eqe_ScaledMinimumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumFinite₇ h₀) (rw_star_sub_ScaledMinimumFinite₇ h₁)
  theorem rw_star_sub_ScaledMinimumFinite₈ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a b a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | .step h => .step (rw_one.sub_ScaledMinimumFinite₈ h)
    | .refl h => .refl (eqe_ScaledMinimumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumFinite₈ h₀) (rw_star_sub_ScaledMinimumFinite₈ h₁)
  theorem rw_star_sub_ScaledMinimumFinite₉ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | .step h => .step (rw_one.sub_ScaledMinimumFinite₉ h)
    | .refl h => .refl (eqe_ScaledMinimumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMinimumFinite₉ h₀) (rw_star_sub_ScaledMinimumFinite₉ h₁)
  theorem rw_star_sub_ScaledMaximumFinite₀ {a b a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumFinite a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximumFinite b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumFinite₀ h)
    | .refl h => .refl (eqe_ScaledMaximumFinite h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumFinite₀ h₀) (rw_star_sub_ScaledMaximumFinite₀ h₁)
  theorem rw_star_sub_ScaledMaximumFinite₁ {a₀ a b a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumFinite a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximumFinite a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumFinite₁ h)
    | .refl h => .refl (eqe_ScaledMaximumFinite (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumFinite₁ h₀) (rw_star_sub_ScaledMaximumFinite₁ h₁)
  theorem rw_star_sub_ScaledMaximumFinite₂ {a₀ a₁ a b a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumFinite a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximumFinite a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumFinite₂ h)
    | .refl h => .refl (eqe_ScaledMaximumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumFinite₂ h₀) (rw_star_sub_ScaledMaximumFinite₂ h₁)
  theorem rw_star_sub_ScaledMaximumFinite₃ {a₀ a₁ a₂ a b a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumFinite a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (ScaledMaximumFinite a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumFinite₃ h)
    | .refl h => .refl (eqe_ScaledMaximumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumFinite₃ h₀) (rw_star_sub_ScaledMaximumFinite₃ h₁)
  theorem rw_star_sub_ScaledMaximumFinite₄ {a₀ a₁ a₂ a₃ a b : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumFinite a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (ScaledMaximumFinite a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumFinite₄ h)
    | .refl h => .refl (eqe_ScaledMaximumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumFinite₄ h₀) (rw_star_sub_ScaledMaximumFinite₄ h₁)
  theorem rw_star_sub_ScaledMaximumFinite₅ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a b : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumFinite₅ h)
    | .refl h => .refl (eqe_ScaledMaximumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumFinite₅ h₀) (rw_star_sub_ScaledMaximumFinite₅ h₁)
  theorem rw_star_sub_ScaledMaximumFinite₆ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a b a₇ a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumFinite₆ h)
    | .refl h => .refl (eqe_ScaledMaximumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumFinite₆ h₀) (rw_star_sub_ScaledMaximumFinite₆ h₁)
  theorem rw_star_sub_ScaledMaximumFinite₇ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a b a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumFinite₇ h)
    | .refl h => .refl (eqe_ScaledMaximumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumFinite₇ h₀) (rw_star_sub_ScaledMaximumFinite₇ h₁)
  theorem rw_star_sub_ScaledMaximumFinite₈ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a b a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | .step h => .step (rw_one.sub_ScaledMaximumFinite₈ h)
    | .refl h => .refl (eqe_ScaledMaximumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumFinite₈ h₀) (rw_star_sub_ScaledMaximumFinite₈ h₁)
  theorem rw_star_sub_ScaledMaximumFinite₉ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | .step h => .step (rw_one.sub_ScaledMaximumFinite₉ h)
    | .refl h => .refl (eqe_ScaledMaximumFinite (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledMaximumFinite₉ h₀) (rw_star_sub_ScaledMaximumFinite₉ h₁)
  theorem rw_star_sub_ScaledClamp₀ {a b a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledClamp a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledClamp b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledClamp₀ h)
    | .refl h => .refl (eqe_ScaledClamp h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledClamp₀ h₀) (rw_star_sub_ScaledClamp₀ h₁)
  theorem rw_star_sub_ScaledClamp₁ {a₀ a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledClamp a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledClamp a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledClamp₁ h)
    | .refl h => .refl (eqe_ScaledClamp (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledClamp₁ h₀) (rw_star_sub_ScaledClamp₁ h₁)
  theorem rw_star_sub_ScaledClamp₂ {a₀ a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledClamp a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledClamp a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledClamp₂ h)
    | .refl h => .refl (eqe_ScaledClamp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledClamp₂ h₀) (rw_star_sub_ScaledClamp₂ h₁)
  theorem rw_star_sub_ScaledClamp₃ {a₀ a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledClamp a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledClamp a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledClamp₃ h)
    | .refl h => .refl (eqe_ScaledClamp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledClamp₃ h₀) (rw_star_sub_ScaledClamp₃ h₁)
  theorem rw_star_sub_ScaledClamp₄ {a₀ a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledClamp a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledClamp a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledClamp₄ h)
    | .refl h => .refl (eqe_ScaledClamp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledClamp₄ h₀) (rw_star_sub_ScaledClamp₄ h₁)
  theorem rw_star_sub_ScaledClamp₅ {a₀ a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledClamp a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledClamp a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledClamp₅ h)
    | .refl h => .refl (eqe_ScaledClamp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledClamp₅ h₀) (rw_star_sub_ScaledClamp₅ h₁)
  theorem rw_star_sub_ScaledClamp₆ {a₀ a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledClamp₆ h)
    | .refl h => .refl (eqe_ScaledClamp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledClamp₆ h₀) (rw_star_sub_ScaledClamp₆ h₁)
  theorem rw_star_sub_ScaledClamp₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledClamp₇ h)
    | .refl h => .refl (eqe_ScaledClamp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledClamp₇ h₀) (rw_star_sub_ScaledClamp₇ h₁)
  theorem rw_star_sub_ScaledClamp₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a b a₉ a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂ a₁₃) (ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledClamp₈ h)
    | .refl h => .refl (eqe_ScaledClamp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) h rfl rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledClamp₈ h₀) (rw_star_sub_ScaledClamp₈ h₁)
  theorem rw_star_sub_ScaledClamp₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a b a₁₀ a₁₁ a₁₂ a₁₃ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂ a₁₃) (ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledClamp₉ h)
    | .refl h => .refl (eqe_ScaledClamp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledClamp₉ h₀) (rw_star_sub_ScaledClamp₉ h₁)
  theorem rw_star_sub_ScaledClamp₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a b a₁₁ a₁₂ a₁₃ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂ a₁₃) (ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledClamp₁₀ h)
    | .refl h => .refl (eqe_ScaledClamp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledClamp₁₀ h₀) (rw_star_sub_ScaledClamp₁₀ h₁)
  theorem rw_star_sub_ScaledClamp₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a b a₁₂ a₁₃ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂ a₁₃) (ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂ a₁₃)
    | .step h => .step (rw_one.sub_ScaledClamp₁₁ h)
    | .refl h => .refl (eqe_ScaledClamp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledClamp₁₁ h₀) (rw_star_sub_ScaledClamp₁₁ h₁)
  theorem rw_star_sub_ScaledClamp₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a b a₁₃ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a a₁₃) (ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b a₁₃)
    | .step h => .step (rw_one.sub_ScaledClamp₁₂ h)
    | .refl h => .refl (eqe_ScaledClamp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledClamp₁₂ h₀) (rw_star_sub_ScaledClamp₁₂ h₁)
  theorem rw_star_sub_ScaledClamp₁₃ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kProjSpec} {a₈ a₉ a₁₀ a₁₁ a₁₂ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a) (ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b)
    | .step h => .step (rw_one.sub_ScaledClamp₁₃ h)
    | .refl h => .refl (eqe_ScaledClamp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kProjSpec.eqe_refl a₇) rfl rfl rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledClamp₁₃ h₀) (rw_star_sub_ScaledClamp₁₃ h₁)
  theorem rw_star_sub_numeratorOf {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (numeratorOf a) (numeratorOf b)
    | .step h => .step (rw_one.sub_numeratorOf h)
    | .refl h => .refl (eqe_numeratorOf h)
    | .trans h₀ h₁ => .trans (rw_star_sub_numeratorOf h₀) (rw_star_sub_numeratorOf h₁)
  theorem rw_star_sub_denominatorOf {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (denominatorOf a) (denominatorOf b)
    | .step h => .step (rw_one.sub_denominatorOf h)
    | .refl h => .refl (eqe_denominatorOf h)
    | .trans h₀ h₁ => .trans (rw_star_sub_denominatorOf h₀) (rw_star_sub_denominatorOf h₁)
  theorem rw_star_sub_Sqrt₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Sqrt a a₁ a₂ a₃) (Sqrt b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_Sqrt₀ h)
    | .refl h => .refl (eqe_Sqrt h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Sqrt₀ h₀) (rw_star_sub_Sqrt₀ h₁)
  theorem rw_star_sub_Sqrt₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Sqrt a₀ a a₂ a₃) (Sqrt a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_Sqrt₁ h)
    | .refl h => .refl (eqe_Sqrt (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Sqrt₁ h₀) (rw_star_sub_Sqrt₁ h₁)
  theorem rw_star_sub_Sqrt₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Sqrt a₀ a₁ a a₃) (Sqrt a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_Sqrt₂ h)
    | .refl h => .refl (eqe_Sqrt (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Sqrt₂ h₀) (rw_star_sub_Sqrt₂ h₁)
  theorem rw_star_sub_Sqrt₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Sqrt a₀ a₁ a₂ a) (Sqrt a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_Sqrt₃ h)
    | .refl h => .refl (eqe_Sqrt (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Sqrt₃ h₀) (rw_star_sub_Sqrt₃ h₁)
  theorem rw_star_sub_RSqrt₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (RSqrt a a₁ a₂ a₃) (RSqrt b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_RSqrt₀ h)
    | .refl h => .refl (eqe_RSqrt h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_RSqrt₀ h₀) (rw_star_sub_RSqrt₀ h₁)
  theorem rw_star_sub_RSqrt₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (RSqrt a₀ a a₂ a₃) (RSqrt a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_RSqrt₁ h)
    | .refl h => .refl (eqe_RSqrt (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_RSqrt₁ h₀) (rw_star_sub_RSqrt₁ h₁)
  theorem rw_star_sub_RSqrt₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (RSqrt a₀ a₁ a a₃) (RSqrt a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_RSqrt₂ h)
    | .refl h => .refl (eqe_RSqrt (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_RSqrt₂ h₀) (rw_star_sub_RSqrt₂ h₁)
  theorem rw_star_sub_RSqrt₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (RSqrt a₀ a₁ a₂ a) (RSqrt a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_RSqrt₃ h)
    | .refl h => .refl (eqe_RSqrt (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_RSqrt₃ h₀) (rw_star_sub_RSqrt₃ h₁)
  theorem rw_star_sub_Exp₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Exp a a₁ a₂ a₃) (Exp b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_Exp₀ h)
    | .refl h => .refl (eqe_Exp h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Exp₀ h₀) (rw_star_sub_Exp₀ h₁)
  theorem rw_star_sub_Exp₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Exp a₀ a a₂ a₃) (Exp a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_Exp₁ h)
    | .refl h => .refl (eqe_Exp (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Exp₁ h₀) (rw_star_sub_Exp₁ h₁)
  theorem rw_star_sub_Exp₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Exp a₀ a₁ a a₃) (Exp a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_Exp₂ h)
    | .refl h => .refl (eqe_Exp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Exp₂ h₀) (rw_star_sub_Exp₂ h₁)
  theorem rw_star_sub_Exp₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Exp a₀ a₁ a₂ a) (Exp a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_Exp₃ h)
    | .refl h => .refl (eqe_Exp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Exp₃ h₀) (rw_star_sub_Exp₃ h₁)
  theorem rw_star_sub_Exp2₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Exp2 a a₁ a₂ a₃) (Exp2 b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_Exp2₀ h)
    | .refl h => .refl (eqe_Exp2 h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Exp2₀ h₀) (rw_star_sub_Exp2₀ h₁)
  theorem rw_star_sub_Exp2₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Exp2 a₀ a a₂ a₃) (Exp2 a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_Exp2₁ h)
    | .refl h => .refl (eqe_Exp2 (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Exp2₁ h₀) (rw_star_sub_Exp2₁ h₁)
  theorem rw_star_sub_Exp2₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Exp2 a₀ a₁ a a₃) (Exp2 a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_Exp2₂ h)
    | .refl h => .refl (eqe_Exp2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Exp2₂ h₀) (rw_star_sub_Exp2₂ h₁)
  theorem rw_star_sub_Exp2₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Exp2 a₀ a₁ a₂ a) (Exp2 a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_Exp2₃ h)
    | .refl h => .refl (eqe_Exp2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Exp2₃ h₀) (rw_star_sub_Exp2₃ h₁)
  theorem rw_star_sub_Log₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Log a a₁ a₂ a₃) (Log b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_Log₀ h)
    | .refl h => .refl (eqe_Log h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Log₀ h₀) (rw_star_sub_Log₀ h₁)
  theorem rw_star_sub_Log₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Log a₀ a a₂ a₃) (Log a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_Log₁ h)
    | .refl h => .refl (eqe_Log (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Log₁ h₀) (rw_star_sub_Log₁ h₁)
  theorem rw_star_sub_Log₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Log a₀ a₁ a a₃) (Log a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_Log₂ h)
    | .refl h => .refl (eqe_Log (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Log₂ h₀) (rw_star_sub_Log₂ h₁)
  theorem rw_star_sub_Log₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Log a₀ a₁ a₂ a) (Log a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_Log₃ h)
    | .refl h => .refl (eqe_Log (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Log₃ h₀) (rw_star_sub_Log₃ h₁)
  theorem rw_star_sub_Log2₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Log2 a a₁ a₂ a₃) (Log2 b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_Log2₀ h)
    | .refl h => .refl (eqe_Log2 h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Log2₀ h₀) (rw_star_sub_Log2₀ h₁)
  theorem rw_star_sub_Log2₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Log2 a₀ a a₂ a₃) (Log2 a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_Log2₁ h)
    | .refl h => .refl (eqe_Log2 (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Log2₁ h₀) (rw_star_sub_Log2₁ h₁)
  theorem rw_star_sub_Log2₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Log2 a₀ a₁ a a₃) (Log2 a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_Log2₂ h)
    | .refl h => .refl (eqe_Log2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Log2₂ h₀) (rw_star_sub_Log2₂ h₁)
  theorem rw_star_sub_Log2₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Log2 a₀ a₁ a₂ a) (Log2 a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_Log2₃ h)
    | .refl h => .refl (eqe_Log2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Log2₃ h₀) (rw_star_sub_Log2₃ h₁)
  theorem rw_star_sub_LogOnePlus₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (LogOnePlus a a₁ a₂ a₃) (LogOnePlus b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_LogOnePlus₀ h)
    | .refl h => .refl (eqe_LogOnePlus h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_LogOnePlus₀ h₀) (rw_star_sub_LogOnePlus₀ h₁)
  theorem rw_star_sub_LogOnePlus₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (LogOnePlus a₀ a a₂ a₃) (LogOnePlus a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_LogOnePlus₁ h)
    | .refl h => .refl (eqe_LogOnePlus (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_LogOnePlus₁ h₀) (rw_star_sub_LogOnePlus₁ h₁)
  theorem rw_star_sub_LogOnePlus₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (LogOnePlus a₀ a₁ a a₃) (LogOnePlus a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_LogOnePlus₂ h)
    | .refl h => .refl (eqe_LogOnePlus (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_LogOnePlus₂ h₀) (rw_star_sub_LogOnePlus₂ h₁)
  theorem rw_star_sub_LogOnePlus₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (LogOnePlus a₀ a₁ a₂ a) (LogOnePlus a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_LogOnePlus₃ h)
    | .refl h => .refl (eqe_LogOnePlus (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_LogOnePlus₃ h₀) (rw_star_sub_LogOnePlus₃ h₁)
  theorem rw_star_sub_ExpMinusOne₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ExpMinusOne a a₁ a₂ a₃) (ExpMinusOne b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_ExpMinusOne₀ h)
    | .refl h => .refl (eqe_ExpMinusOne h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ExpMinusOne₀ h₀) (rw_star_sub_ExpMinusOne₀ h₁)
  theorem rw_star_sub_ExpMinusOne₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ExpMinusOne a₀ a a₂ a₃) (ExpMinusOne a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_ExpMinusOne₁ h)
    | .refl h => .refl (eqe_ExpMinusOne (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ExpMinusOne₁ h₀) (rw_star_sub_ExpMinusOne₁ h₁)
  theorem rw_star_sub_ExpMinusOne₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ExpMinusOne a₀ a₁ a a₃) (ExpMinusOne a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_ExpMinusOne₂ h)
    | .refl h => .refl (eqe_ExpMinusOne (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ExpMinusOne₂ h₀) (rw_star_sub_ExpMinusOne₂ h₁)
  theorem rw_star_sub_ExpMinusOne₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ExpMinusOne a₀ a₁ a₂ a) (ExpMinusOne a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_ExpMinusOne₃ h)
    | .refl h => .refl (eqe_ExpMinusOne (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ExpMinusOne₃ h₀) (rw_star_sub_ExpMinusOne₃ h₁)
  theorem rw_star_sub_Sin₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Sin a a₁ a₂ a₃) (Sin b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_Sin₀ h)
    | .refl h => .refl (eqe_Sin h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Sin₀ h₀) (rw_star_sub_Sin₀ h₁)
  theorem rw_star_sub_Sin₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Sin a₀ a a₂ a₃) (Sin a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_Sin₁ h)
    | .refl h => .refl (eqe_Sin (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Sin₁ h₀) (rw_star_sub_Sin₁ h₁)
  theorem rw_star_sub_Sin₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Sin a₀ a₁ a a₃) (Sin a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_Sin₂ h)
    | .refl h => .refl (eqe_Sin (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Sin₂ h₀) (rw_star_sub_Sin₂ h₁)
  theorem rw_star_sub_Sin₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Sin a₀ a₁ a₂ a) (Sin a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_Sin₃ h)
    | .refl h => .refl (eqe_Sin (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Sin₃ h₀) (rw_star_sub_Sin₃ h₁)
  theorem rw_star_sub_Cos₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Cos a a₁ a₂ a₃) (Cos b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_Cos₀ h)
    | .refl h => .refl (eqe_Cos h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Cos₀ h₀) (rw_star_sub_Cos₀ h₁)
  theorem rw_star_sub_Cos₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Cos a₀ a a₂ a₃) (Cos a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_Cos₁ h)
    | .refl h => .refl (eqe_Cos (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Cos₁ h₀) (rw_star_sub_Cos₁ h₁)
  theorem rw_star_sub_Cos₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Cos a₀ a₁ a a₃) (Cos a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_Cos₂ h)
    | .refl h => .refl (eqe_Cos (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Cos₂ h₀) (rw_star_sub_Cos₂ h₁)
  theorem rw_star_sub_Cos₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Cos a₀ a₁ a₂ a) (Cos a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_Cos₃ h)
    | .refl h => .refl (eqe_Cos (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Cos₃ h₀) (rw_star_sub_Cos₃ h₁)
  theorem rw_star_sub_Tan₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Tan a a₁ a₂ a₃) (Tan b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_Tan₀ h)
    | .refl h => .refl (eqe_Tan h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Tan₀ h₀) (rw_star_sub_Tan₀ h₁)
  theorem rw_star_sub_Tan₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Tan a₀ a a₂ a₃) (Tan a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_Tan₁ h)
    | .refl h => .refl (eqe_Tan (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Tan₁ h₀) (rw_star_sub_Tan₁ h₁)
  theorem rw_star_sub_Tan₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Tan a₀ a₁ a a₃) (Tan a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_Tan₂ h)
    | .refl h => .refl (eqe_Tan (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Tan₂ h₀) (rw_star_sub_Tan₂ h₁)
  theorem rw_star_sub_Tan₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Tan a₀ a₁ a₂ a) (Tan a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_Tan₃ h)
    | .refl h => .refl (eqe_Tan (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Tan₃ h₀) (rw_star_sub_Tan₃ h₁)
  theorem rw_star_sub_ArcSin₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcSin a a₁ a₂ a₃) (ArcSin b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_ArcSin₀ h)
    | .refl h => .refl (eqe_ArcSin h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcSin₀ h₀) (rw_star_sub_ArcSin₀ h₁)
  theorem rw_star_sub_ArcSin₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcSin a₀ a a₂ a₃) (ArcSin a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_ArcSin₁ h)
    | .refl h => .refl (eqe_ArcSin (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcSin₁ h₀) (rw_star_sub_ArcSin₁ h₁)
  theorem rw_star_sub_ArcSin₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcSin a₀ a₁ a a₃) (ArcSin a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_ArcSin₂ h)
    | .refl h => .refl (eqe_ArcSin (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcSin₂ h₀) (rw_star_sub_ArcSin₂ h₁)
  theorem rw_star_sub_ArcSin₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ArcSin a₀ a₁ a₂ a) (ArcSin a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_ArcSin₃ h)
    | .refl h => .refl (eqe_ArcSin (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcSin₃ h₀) (rw_star_sub_ArcSin₃ h₁)
  theorem rw_star_sub_ArcCos₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcCos a a₁ a₂ a₃) (ArcCos b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_ArcCos₀ h)
    | .refl h => .refl (eqe_ArcCos h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcCos₀ h₀) (rw_star_sub_ArcCos₀ h₁)
  theorem rw_star_sub_ArcCos₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcCos a₀ a a₂ a₃) (ArcCos a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_ArcCos₁ h)
    | .refl h => .refl (eqe_ArcCos (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcCos₁ h₀) (rw_star_sub_ArcCos₁ h₁)
  theorem rw_star_sub_ArcCos₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcCos a₀ a₁ a a₃) (ArcCos a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_ArcCos₂ h)
    | .refl h => .refl (eqe_ArcCos (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcCos₂ h₀) (rw_star_sub_ArcCos₂ h₁)
  theorem rw_star_sub_ArcCos₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ArcCos a₀ a₁ a₂ a) (ArcCos a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_ArcCos₃ h)
    | .refl h => .refl (eqe_ArcCos (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcCos₃ h₀) (rw_star_sub_ArcCos₃ h₁)
  theorem rw_star_sub_ArcTan₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcTan a a₁ a₂ a₃) (ArcTan b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_ArcTan₀ h)
    | .refl h => .refl (eqe_ArcTan h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTan₀ h₀) (rw_star_sub_ArcTan₀ h₁)
  theorem rw_star_sub_ArcTan₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcTan a₀ a a₂ a₃) (ArcTan a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_ArcTan₁ h)
    | .refl h => .refl (eqe_ArcTan (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTan₁ h₀) (rw_star_sub_ArcTan₁ h₁)
  theorem rw_star_sub_ArcTan₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcTan a₀ a₁ a a₃) (ArcTan a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_ArcTan₂ h)
    | .refl h => .refl (eqe_ArcTan (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTan₂ h₀) (rw_star_sub_ArcTan₂ h₁)
  theorem rw_star_sub_ArcTan₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ArcTan a₀ a₁ a₂ a) (ArcTan a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_ArcTan₃ h)
    | .refl h => .refl (eqe_ArcTan (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTan₃ h₀) (rw_star_sub_ArcTan₃ h₁)
  theorem rw_star_sub_Sinh₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Sinh a a₁ a₂ a₃) (Sinh b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_Sinh₀ h)
    | .refl h => .refl (eqe_Sinh h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Sinh₀ h₀) (rw_star_sub_Sinh₀ h₁)
  theorem rw_star_sub_Sinh₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Sinh a₀ a a₂ a₃) (Sinh a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_Sinh₁ h)
    | .refl h => .refl (eqe_Sinh (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Sinh₁ h₀) (rw_star_sub_Sinh₁ h₁)
  theorem rw_star_sub_Sinh₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Sinh a₀ a₁ a a₃) (Sinh a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_Sinh₂ h)
    | .refl h => .refl (eqe_Sinh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Sinh₂ h₀) (rw_star_sub_Sinh₂ h₁)
  theorem rw_star_sub_Sinh₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Sinh a₀ a₁ a₂ a) (Sinh a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_Sinh₃ h)
    | .refl h => .refl (eqe_Sinh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Sinh₃ h₀) (rw_star_sub_Sinh₃ h₁)
  theorem rw_star_sub_Cosh₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Cosh a a₁ a₂ a₃) (Cosh b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_Cosh₀ h)
    | .refl h => .refl (eqe_Cosh h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Cosh₀ h₀) (rw_star_sub_Cosh₀ h₁)
  theorem rw_star_sub_Cosh₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Cosh a₀ a a₂ a₃) (Cosh a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_Cosh₁ h)
    | .refl h => .refl (eqe_Cosh (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Cosh₁ h₀) (rw_star_sub_Cosh₁ h₁)
  theorem rw_star_sub_Cosh₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Cosh a₀ a₁ a a₃) (Cosh a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_Cosh₂ h)
    | .refl h => .refl (eqe_Cosh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Cosh₂ h₀) (rw_star_sub_Cosh₂ h₁)
  theorem rw_star_sub_Cosh₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Cosh a₀ a₁ a₂ a) (Cosh a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_Cosh₃ h)
    | .refl h => .refl (eqe_Cosh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Cosh₃ h₀) (rw_star_sub_Cosh₃ h₁)
  theorem rw_star_sub_Tanh₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Tanh a a₁ a₂ a₃) (Tanh b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_Tanh₀ h)
    | .refl h => .refl (eqe_Tanh h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Tanh₀ h₀) (rw_star_sub_Tanh₀ h₁)
  theorem rw_star_sub_Tanh₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Tanh a₀ a a₂ a₃) (Tanh a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_Tanh₁ h)
    | .refl h => .refl (eqe_Tanh (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Tanh₁ h₀) (rw_star_sub_Tanh₁ h₁)
  theorem rw_star_sub_Tanh₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Tanh a₀ a₁ a a₃) (Tanh a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_Tanh₂ h)
    | .refl h => .refl (eqe_Tanh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Tanh₂ h₀) (rw_star_sub_Tanh₂ h₁)
  theorem rw_star_sub_Tanh₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Tanh a₀ a₁ a₂ a) (Tanh a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_Tanh₃ h)
    | .refl h => .refl (eqe_Tanh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Tanh₃ h₀) (rw_star_sub_Tanh₃ h₁)
  theorem rw_star_sub_ArcSinh₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcSinh a a₁ a₂ a₃) (ArcSinh b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_ArcSinh₀ h)
    | .refl h => .refl (eqe_ArcSinh h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcSinh₀ h₀) (rw_star_sub_ArcSinh₀ h₁)
  theorem rw_star_sub_ArcSinh₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcSinh a₀ a a₂ a₃) (ArcSinh a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_ArcSinh₁ h)
    | .refl h => .refl (eqe_ArcSinh (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcSinh₁ h₀) (rw_star_sub_ArcSinh₁ h₁)
  theorem rw_star_sub_ArcSinh₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcSinh a₀ a₁ a a₃) (ArcSinh a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_ArcSinh₂ h)
    | .refl h => .refl (eqe_ArcSinh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcSinh₂ h₀) (rw_star_sub_ArcSinh₂ h₁)
  theorem rw_star_sub_ArcSinh₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ArcSinh a₀ a₁ a₂ a) (ArcSinh a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_ArcSinh₃ h)
    | .refl h => .refl (eqe_ArcSinh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcSinh₃ h₀) (rw_star_sub_ArcSinh₃ h₁)
  theorem rw_star_sub_ArcCosh₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcCosh a a₁ a₂ a₃) (ArcCosh b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_ArcCosh₀ h)
    | .refl h => .refl (eqe_ArcCosh h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcCosh₀ h₀) (rw_star_sub_ArcCosh₀ h₁)
  theorem rw_star_sub_ArcCosh₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcCosh a₀ a a₂ a₃) (ArcCosh a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_ArcCosh₁ h)
    | .refl h => .refl (eqe_ArcCosh (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcCosh₁ h₀) (rw_star_sub_ArcCosh₁ h₁)
  theorem rw_star_sub_ArcCosh₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcCosh a₀ a₁ a a₃) (ArcCosh a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_ArcCosh₂ h)
    | .refl h => .refl (eqe_ArcCosh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcCosh₂ h₀) (rw_star_sub_ArcCosh₂ h₁)
  theorem rw_star_sub_ArcCosh₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ArcCosh a₀ a₁ a₂ a) (ArcCosh a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_ArcCosh₃ h)
    | .refl h => .refl (eqe_ArcCosh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcCosh₃ h₀) (rw_star_sub_ArcCosh₃ h₁)
  theorem rw_star_sub_ArcTanh₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcTanh a a₁ a₂ a₃) (ArcTanh b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_ArcTanh₀ h)
    | .refl h => .refl (eqe_ArcTanh h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTanh₀ h₀) (rw_star_sub_ArcTanh₀ h₁)
  theorem rw_star_sub_ArcTanh₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcTanh a₀ a a₂ a₃) (ArcTanh a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_ArcTanh₁ h)
    | .refl h => .refl (eqe_ArcTanh (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTanh₁ h₀) (rw_star_sub_ArcTanh₁ h₁)
  theorem rw_star_sub_ArcTanh₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcTanh a₀ a₁ a a₃) (ArcTanh a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_ArcTanh₂ h)
    | .refl h => .refl (eqe_ArcTanh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTanh₂ h₀) (rw_star_sub_ArcTanh₂ h₁)
  theorem rw_star_sub_ArcTanh₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ArcTanh a₀ a₁ a₂ a) (ArcTanh a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_ArcTanh₃ h)
    | .refl h => .refl (eqe_ArcTanh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTanh₃ h₀) (rw_star_sub_ArcTanh₃ h₁)
  theorem rw_star_sub_SinPi₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (SinPi a a₁ a₂ a₃) (SinPi b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_SinPi₀ h)
    | .refl h => .refl (eqe_SinPi h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_SinPi₀ h₀) (rw_star_sub_SinPi₀ h₁)
  theorem rw_star_sub_SinPi₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (SinPi a₀ a a₂ a₃) (SinPi a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_SinPi₁ h)
    | .refl h => .refl (eqe_SinPi (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_SinPi₁ h₀) (rw_star_sub_SinPi₁ h₁)
  theorem rw_star_sub_SinPi₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (SinPi a₀ a₁ a a₃) (SinPi a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_SinPi₂ h)
    | .refl h => .refl (eqe_SinPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_SinPi₂ h₀) (rw_star_sub_SinPi₂ h₁)
  theorem rw_star_sub_SinPi₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (SinPi a₀ a₁ a₂ a) (SinPi a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_SinPi₃ h)
    | .refl h => .refl (eqe_SinPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_SinPi₃ h₀) (rw_star_sub_SinPi₃ h₁)
  theorem rw_star_sub_CosPi₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (CosPi a a₁ a₂ a₃) (CosPi b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_CosPi₀ h)
    | .refl h => .refl (eqe_CosPi h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CosPi₀ h₀) (rw_star_sub_CosPi₀ h₁)
  theorem rw_star_sub_CosPi₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (CosPi a₀ a a₂ a₃) (CosPi a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_CosPi₁ h)
    | .refl h => .refl (eqe_CosPi (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CosPi₁ h₀) (rw_star_sub_CosPi₁ h₁)
  theorem rw_star_sub_CosPi₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (CosPi a₀ a₁ a a₃) (CosPi a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_CosPi₂ h)
    | .refl h => .refl (eqe_CosPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CosPi₂ h₀) (rw_star_sub_CosPi₂ h₁)
  theorem rw_star_sub_CosPi₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (CosPi a₀ a₁ a₂ a) (CosPi a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_CosPi₃ h)
    | .refl h => .refl (eqe_CosPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_CosPi₃ h₀) (rw_star_sub_CosPi₃ h₁)
  theorem rw_star_sub_TanPi₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (TanPi a a₁ a₂ a₃) (TanPi b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_TanPi₀ h)
    | .refl h => .refl (eqe_TanPi h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_TanPi₀ h₀) (rw_star_sub_TanPi₀ h₁)
  theorem rw_star_sub_TanPi₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (TanPi a₀ a a₂ a₃) (TanPi a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_TanPi₁ h)
    | .refl h => .refl (eqe_TanPi (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_TanPi₁ h₀) (rw_star_sub_TanPi₁ h₁)
  theorem rw_star_sub_TanPi₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (TanPi a₀ a₁ a a₃) (TanPi a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_TanPi₂ h)
    | .refl h => .refl (eqe_TanPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_TanPi₂ h₀) (rw_star_sub_TanPi₂ h₁)
  theorem rw_star_sub_TanPi₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (TanPi a₀ a₁ a₂ a) (TanPi a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_TanPi₃ h)
    | .refl h => .refl (eqe_TanPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_TanPi₃ h₀) (rw_star_sub_TanPi₃ h₁)
  theorem rw_star_sub_ArcSinPi₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcSinPi a a₁ a₂ a₃) (ArcSinPi b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_ArcSinPi₀ h)
    | .refl h => .refl (eqe_ArcSinPi h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcSinPi₀ h₀) (rw_star_sub_ArcSinPi₀ h₁)
  theorem rw_star_sub_ArcSinPi₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcSinPi a₀ a a₂ a₃) (ArcSinPi a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_ArcSinPi₁ h)
    | .refl h => .refl (eqe_ArcSinPi (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcSinPi₁ h₀) (rw_star_sub_ArcSinPi₁ h₁)
  theorem rw_star_sub_ArcSinPi₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcSinPi a₀ a₁ a a₃) (ArcSinPi a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_ArcSinPi₂ h)
    | .refl h => .refl (eqe_ArcSinPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcSinPi₂ h₀) (rw_star_sub_ArcSinPi₂ h₁)
  theorem rw_star_sub_ArcSinPi₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ArcSinPi a₀ a₁ a₂ a) (ArcSinPi a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_ArcSinPi₃ h)
    | .refl h => .refl (eqe_ArcSinPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcSinPi₃ h₀) (rw_star_sub_ArcSinPi₃ h₁)
  theorem rw_star_sub_ArcCosPi₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcCosPi a a₁ a₂ a₃) (ArcCosPi b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_ArcCosPi₀ h)
    | .refl h => .refl (eqe_ArcCosPi h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcCosPi₀ h₀) (rw_star_sub_ArcCosPi₀ h₁)
  theorem rw_star_sub_ArcCosPi₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcCosPi a₀ a a₂ a₃) (ArcCosPi a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_ArcCosPi₁ h)
    | .refl h => .refl (eqe_ArcCosPi (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcCosPi₁ h₀) (rw_star_sub_ArcCosPi₁ h₁)
  theorem rw_star_sub_ArcCosPi₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcCosPi a₀ a₁ a a₃) (ArcCosPi a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_ArcCosPi₂ h)
    | .refl h => .refl (eqe_ArcCosPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcCosPi₂ h₀) (rw_star_sub_ArcCosPi₂ h₁)
  theorem rw_star_sub_ArcCosPi₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ArcCosPi a₀ a₁ a₂ a) (ArcCosPi a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_ArcCosPi₃ h)
    | .refl h => .refl (eqe_ArcCosPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcCosPi₃ h₀) (rw_star_sub_ArcCosPi₃ h₁)
  theorem rw_star_sub_ArcTanPi₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcTanPi a a₁ a₂ a₃) (ArcTanPi b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_ArcTanPi₀ h)
    | .refl h => .refl (eqe_ArcTanPi h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTanPi₀ h₀) (rw_star_sub_ArcTanPi₀ h₁)
  theorem rw_star_sub_ArcTanPi₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcTanPi a₀ a a₂ a₃) (ArcTanPi a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_ArcTanPi₁ h)
    | .refl h => .refl (eqe_ArcTanPi (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTanPi₁ h₀) (rw_star_sub_ArcTanPi₁ h₁)
  theorem rw_star_sub_ArcTanPi₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (ArcTanPi a₀ a₁ a a₃) (ArcTanPi a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_ArcTanPi₂ h)
    | .refl h => .refl (eqe_ArcTanPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTanPi₂ h₀) (rw_star_sub_ArcTanPi₂ h₁)
  theorem rw_star_sub_ArcTanPi₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ArcTanPi a₀ a₁ a₂ a) (ArcTanPi a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_ArcTanPi₃ h)
    | .refl h => .refl (eqe_ArcTanPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTanPi₃ h₀) (rw_star_sub_ArcTanPi₃ h₁)
  theorem rw_star_sub_Softplus₀ {a b a₁ : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Softplus a a₁ a₂ a₃) (Softplus b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_Softplus₀ h)
    | .refl h => .refl (eqe_Softplus h (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Softplus₀ h₀) (rw_star_sub_Softplus₀ h₁)
  theorem rw_star_sub_Softplus₁ {a₀ a b : kFormat} {a₂ : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Softplus a₀ a a₂ a₃) (Softplus a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_Softplus₁ h)
    | .refl h => .refl (eqe_Softplus (kFormat.eqe_refl a₀) h (kProjSpec.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Softplus₁ h₀) (rw_star_sub_Softplus₁ h₁)
  theorem rw_star_sub_Softplus₂ {a₀ a₁ : kFormat} {a b : kProjSpec} {a₃ : MRat} : a.rw_star b →
      MRat.rw_star (Softplus a₀ a₁ a a₃) (Softplus a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_Softplus₂ h)
    | .refl h => .refl (eqe_Softplus (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Softplus₂ h₀) (rw_star_sub_Softplus₂ h₁)
  theorem rw_star_sub_Softplus₃ {a₀ a₁ : kFormat} {a₂ : kProjSpec} {a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Softplus a₀ a₁ a₂ a) (Softplus a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_Softplus₃ h)
    | .refl h => .refl (eqe_Softplus (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kProjSpec.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Softplus₃ h₀) (rw_star_sub_Softplus₃ h₁)
  theorem rw_star_sub_Hypot₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Hypot a a₁ a₂ a₃ a₄ a₅) (Hypot b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Hypot₀ h)
    | .refl h => .refl (eqe_Hypot h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Hypot₀ h₀) (rw_star_sub_Hypot₀ h₁)
  theorem rw_star_sub_Hypot₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Hypot a₀ a a₂ a₃ a₄ a₅) (Hypot a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Hypot₁ h)
    | .refl h => .refl (eqe_Hypot (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Hypot₁ h₀) (rw_star_sub_Hypot₁ h₁)
  theorem rw_star_sub_Hypot₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Hypot a₀ a₁ a a₃ a₄ a₅) (Hypot a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_Hypot₂ h)
    | .refl h => .refl (eqe_Hypot (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Hypot₂ h₀) (rw_star_sub_Hypot₂ h₁)
  theorem rw_star_sub_Hypot₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (Hypot a₀ a₁ a₂ a a₄ a₅) (Hypot a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_Hypot₃ h)
    | .refl h => .refl (eqe_Hypot (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Hypot₃ h₀) (rw_star_sub_Hypot₃ h₁)
  theorem rw_star_sub_Hypot₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (Hypot a₀ a₁ a₂ a₃ a a₅) (Hypot a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_Hypot₄ h)
    | .refl h => .refl (eqe_Hypot (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Hypot₄ h₀) (rw_star_sub_Hypot₄ h₁)
  theorem rw_star_sub_Hypot₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (Hypot a₀ a₁ a₂ a₃ a₄ a) (Hypot a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_Hypot₅ h)
    | .refl h => .refl (eqe_Hypot (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Hypot₅ h₀) (rw_star_sub_Hypot₅ h₁)
  theorem rw_star_sub_ArcTan2₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ArcTan2 a a₁ a₂ a₃ a₄ a₅) (ArcTan2 b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ArcTan2₀ h)
    | .refl h => .refl (eqe_ArcTan2 h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTan2₀ h₀) (rw_star_sub_ArcTan2₀ h₁)
  theorem rw_star_sub_ArcTan2₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ArcTan2 a₀ a a₂ a₃ a₄ a₅) (ArcTan2 a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ArcTan2₁ h)
    | .refl h => .refl (eqe_ArcTan2 (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTan2₁ h₀) (rw_star_sub_ArcTan2₁ h₁)
  theorem rw_star_sub_ArcTan2₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ArcTan2 a₀ a₁ a a₃ a₄ a₅) (ArcTan2 a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ArcTan2₂ h)
    | .refl h => .refl (eqe_ArcTan2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTan2₂ h₀) (rw_star_sub_ArcTan2₂ h₁)
  theorem rw_star_sub_ArcTan2₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ArcTan2 a₀ a₁ a₂ a a₄ a₅) (ArcTan2 a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ArcTan2₃ h)
    | .refl h => .refl (eqe_ArcTan2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTan2₃ h₀) (rw_star_sub_ArcTan2₃ h₁)
  theorem rw_star_sub_ArcTan2₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ArcTan2 a₀ a₁ a₂ a₃ a a₅) (ArcTan2 a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ArcTan2₄ h)
    | .refl h => .refl (eqe_ArcTan2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTan2₄ h₀) (rw_star_sub_ArcTan2₄ h₁)
  theorem rw_star_sub_ArcTan2₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ArcTan2 a₀ a₁ a₂ a₃ a₄ a) (ArcTan2 a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ArcTan2₅ h)
    | .refl h => .refl (eqe_ArcTan2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTan2₅ h₀) (rw_star_sub_ArcTan2₅ h₁)
  theorem rw_star_sub_ArcTan2Pi₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ArcTan2Pi a a₁ a₂ a₃ a₄ a₅) (ArcTan2Pi b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ArcTan2Pi₀ h)
    | .refl h => .refl (eqe_ArcTan2Pi h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTan2Pi₀ h₀) (rw_star_sub_ArcTan2Pi₀ h₁)
  theorem rw_star_sub_ArcTan2Pi₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ArcTan2Pi a₀ a a₂ a₃ a₄ a₅) (ArcTan2Pi a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ArcTan2Pi₁ h)
    | .refl h => .refl (eqe_ArcTan2Pi (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTan2Pi₁ h₀) (rw_star_sub_ArcTan2Pi₁ h₁)
  theorem rw_star_sub_ArcTan2Pi₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ArcTan2Pi a₀ a₁ a a₃ a₄ a₅) (ArcTan2Pi a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ArcTan2Pi₂ h)
    | .refl h => .refl (eqe_ArcTan2Pi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTan2Pi₂ h₀) (rw_star_sub_ArcTan2Pi₂ h₁)
  theorem rw_star_sub_ArcTan2Pi₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ArcTan2Pi a₀ a₁ a₂ a a₄ a₅) (ArcTan2Pi a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ArcTan2Pi₃ h)
    | .refl h => .refl (eqe_ArcTan2Pi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTan2Pi₃ h₀) (rw_star_sub_ArcTan2Pi₃ h₁)
  theorem rw_star_sub_ArcTan2Pi₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ArcTan2Pi a₀ a₁ a₂ a₃ a a₅) (ArcTan2Pi a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ArcTan2Pi₄ h)
    | .refl h => .refl (eqe_ArcTan2Pi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTan2Pi₄ h₀) (rw_star_sub_ArcTan2Pi₄ h₁)
  theorem rw_star_sub_ArcTan2Pi₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ArcTan2Pi a₀ a₁ a₂ a₃ a₄ a) (ArcTan2Pi a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ArcTan2Pi₅ h)
    | .refl h => .refl (eqe_ArcTan2Pi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ArcTan2Pi₅ h₀) (rw_star_sub_ArcTan2Pi₅ h₁)
  theorem rw_star_sub_ScaledSqrt₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSqrt a a₁ a₂ a₃ a₄ a₅) (ScaledSqrt b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSqrt₀ h)
    | .refl h => .refl (eqe_ScaledSqrt h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSqrt₀ h₀) (rw_star_sub_ScaledSqrt₀ h₁)
  theorem rw_star_sub_ScaledSqrt₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSqrt a₀ a a₂ a₃ a₄ a₅) (ScaledSqrt a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSqrt₁ h)
    | .refl h => .refl (eqe_ScaledSqrt (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSqrt₁ h₀) (rw_star_sub_ScaledSqrt₁ h₁)
  theorem rw_star_sub_ScaledSqrt₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSqrt a₀ a₁ a a₃ a₄ a₅) (ScaledSqrt a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSqrt₂ h)
    | .refl h => .refl (eqe_ScaledSqrt (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSqrt₂ h₀) (rw_star_sub_ScaledSqrt₂ h₁)
  theorem rw_star_sub_ScaledSqrt₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSqrt a₀ a₁ a₂ a a₄ a₅) (ScaledSqrt a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSqrt₃ h)
    | .refl h => .refl (eqe_ScaledSqrt (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSqrt₃ h₀) (rw_star_sub_ScaledSqrt₃ h₁)
  theorem rw_star_sub_ScaledSqrt₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledSqrt a₀ a₁ a₂ a₃ a a₅) (ScaledSqrt a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledSqrt₄ h)
    | .refl h => .refl (eqe_ScaledSqrt (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSqrt₄ h₀) (rw_star_sub_ScaledSqrt₄ h₁)
  theorem rw_star_sub_ScaledSqrt₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledSqrt a₀ a₁ a₂ a₃ a₄ a) (ScaledSqrt a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledSqrt₅ h)
    | .refl h => .refl (eqe_ScaledSqrt (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSqrt₅ h₀) (rw_star_sub_ScaledSqrt₅ h₁)
  theorem rw_star_sub_ScaledRSqrt₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledRSqrt a a₁ a₂ a₃ a₄ a₅) (ScaledRSqrt b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledRSqrt₀ h)
    | .refl h => .refl (eqe_ScaledRSqrt h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledRSqrt₀ h₀) (rw_star_sub_ScaledRSqrt₀ h₁)
  theorem rw_star_sub_ScaledRSqrt₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledRSqrt a₀ a a₂ a₃ a₄ a₅) (ScaledRSqrt a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledRSqrt₁ h)
    | .refl h => .refl (eqe_ScaledRSqrt (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledRSqrt₁ h₀) (rw_star_sub_ScaledRSqrt₁ h₁)
  theorem rw_star_sub_ScaledRSqrt₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledRSqrt a₀ a₁ a a₃ a₄ a₅) (ScaledRSqrt a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledRSqrt₂ h)
    | .refl h => .refl (eqe_ScaledRSqrt (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledRSqrt₂ h₀) (rw_star_sub_ScaledRSqrt₂ h₁)
  theorem rw_star_sub_ScaledRSqrt₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledRSqrt a₀ a₁ a₂ a a₄ a₅) (ScaledRSqrt a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledRSqrt₃ h)
    | .refl h => .refl (eqe_ScaledRSqrt (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledRSqrt₃ h₀) (rw_star_sub_ScaledRSqrt₃ h₁)
  theorem rw_star_sub_ScaledRSqrt₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledRSqrt a₀ a₁ a₂ a₃ a a₅) (ScaledRSqrt a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledRSqrt₄ h)
    | .refl h => .refl (eqe_ScaledRSqrt (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledRSqrt₄ h₀) (rw_star_sub_ScaledRSqrt₄ h₁)
  theorem rw_star_sub_ScaledRSqrt₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledRSqrt a₀ a₁ a₂ a₃ a₄ a) (ScaledRSqrt a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledRSqrt₅ h)
    | .refl h => .refl (eqe_ScaledRSqrt (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledRSqrt₅ h₀) (rw_star_sub_ScaledRSqrt₅ h₁)
  theorem rw_star_sub_ScaledExp₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledExp a a₁ a₂ a₃ a₄ a₅) (ScaledExp b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledExp₀ h)
    | .refl h => .refl (eqe_ScaledExp h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledExp₀ h₀) (rw_star_sub_ScaledExp₀ h₁)
  theorem rw_star_sub_ScaledExp₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledExp a₀ a a₂ a₃ a₄ a₅) (ScaledExp a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledExp₁ h)
    | .refl h => .refl (eqe_ScaledExp (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledExp₁ h₀) (rw_star_sub_ScaledExp₁ h₁)
  theorem rw_star_sub_ScaledExp₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledExp a₀ a₁ a a₃ a₄ a₅) (ScaledExp a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledExp₂ h)
    | .refl h => .refl (eqe_ScaledExp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledExp₂ h₀) (rw_star_sub_ScaledExp₂ h₁)
  theorem rw_star_sub_ScaledExp₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledExp a₀ a₁ a₂ a a₄ a₅) (ScaledExp a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledExp₃ h)
    | .refl h => .refl (eqe_ScaledExp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledExp₃ h₀) (rw_star_sub_ScaledExp₃ h₁)
  theorem rw_star_sub_ScaledExp₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledExp a₀ a₁ a₂ a₃ a a₅) (ScaledExp a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledExp₄ h)
    | .refl h => .refl (eqe_ScaledExp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledExp₄ h₀) (rw_star_sub_ScaledExp₄ h₁)
  theorem rw_star_sub_ScaledExp₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledExp a₀ a₁ a₂ a₃ a₄ a) (ScaledExp a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledExp₅ h)
    | .refl h => .refl (eqe_ScaledExp (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledExp₅ h₀) (rw_star_sub_ScaledExp₅ h₁)
  theorem rw_star_sub_ScaledExp2₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledExp2 a a₁ a₂ a₃ a₄ a₅) (ScaledExp2 b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledExp2₀ h)
    | .refl h => .refl (eqe_ScaledExp2 h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledExp2₀ h₀) (rw_star_sub_ScaledExp2₀ h₁)
  theorem rw_star_sub_ScaledExp2₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledExp2 a₀ a a₂ a₃ a₄ a₅) (ScaledExp2 a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledExp2₁ h)
    | .refl h => .refl (eqe_ScaledExp2 (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledExp2₁ h₀) (rw_star_sub_ScaledExp2₁ h₁)
  theorem rw_star_sub_ScaledExp2₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledExp2 a₀ a₁ a a₃ a₄ a₅) (ScaledExp2 a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledExp2₂ h)
    | .refl h => .refl (eqe_ScaledExp2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledExp2₂ h₀) (rw_star_sub_ScaledExp2₂ h₁)
  theorem rw_star_sub_ScaledExp2₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledExp2 a₀ a₁ a₂ a a₄ a₅) (ScaledExp2 a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledExp2₃ h)
    | .refl h => .refl (eqe_ScaledExp2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledExp2₃ h₀) (rw_star_sub_ScaledExp2₃ h₁)
  theorem rw_star_sub_ScaledExp2₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledExp2 a₀ a₁ a₂ a₃ a a₅) (ScaledExp2 a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledExp2₄ h)
    | .refl h => .refl (eqe_ScaledExp2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledExp2₄ h₀) (rw_star_sub_ScaledExp2₄ h₁)
  theorem rw_star_sub_ScaledExp2₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledExp2 a₀ a₁ a₂ a₃ a₄ a) (ScaledExp2 a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledExp2₅ h)
    | .refl h => .refl (eqe_ScaledExp2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledExp2₅ h₀) (rw_star_sub_ScaledExp2₅ h₁)
  theorem rw_star_sub_ScaledLog₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledLog a a₁ a₂ a₃ a₄ a₅) (ScaledLog b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledLog₀ h)
    | .refl h => .refl (eqe_ScaledLog h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledLog₀ h₀) (rw_star_sub_ScaledLog₀ h₁)
  theorem rw_star_sub_ScaledLog₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledLog a₀ a a₂ a₃ a₄ a₅) (ScaledLog a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledLog₁ h)
    | .refl h => .refl (eqe_ScaledLog (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledLog₁ h₀) (rw_star_sub_ScaledLog₁ h₁)
  theorem rw_star_sub_ScaledLog₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledLog a₀ a₁ a a₃ a₄ a₅) (ScaledLog a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledLog₂ h)
    | .refl h => .refl (eqe_ScaledLog (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledLog₂ h₀) (rw_star_sub_ScaledLog₂ h₁)
  theorem rw_star_sub_ScaledLog₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledLog a₀ a₁ a₂ a a₄ a₅) (ScaledLog a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledLog₃ h)
    | .refl h => .refl (eqe_ScaledLog (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledLog₃ h₀) (rw_star_sub_ScaledLog₃ h₁)
  theorem rw_star_sub_ScaledLog₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledLog a₀ a₁ a₂ a₃ a a₅) (ScaledLog a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledLog₄ h)
    | .refl h => .refl (eqe_ScaledLog (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledLog₄ h₀) (rw_star_sub_ScaledLog₄ h₁)
  theorem rw_star_sub_ScaledLog₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledLog a₀ a₁ a₂ a₃ a₄ a) (ScaledLog a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledLog₅ h)
    | .refl h => .refl (eqe_ScaledLog (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledLog₅ h₀) (rw_star_sub_ScaledLog₅ h₁)
  theorem rw_star_sub_ScaledLog2₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledLog2 a a₁ a₂ a₃ a₄ a₅) (ScaledLog2 b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledLog2₀ h)
    | .refl h => .refl (eqe_ScaledLog2 h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledLog2₀ h₀) (rw_star_sub_ScaledLog2₀ h₁)
  theorem rw_star_sub_ScaledLog2₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledLog2 a₀ a a₂ a₃ a₄ a₅) (ScaledLog2 a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledLog2₁ h)
    | .refl h => .refl (eqe_ScaledLog2 (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledLog2₁ h₀) (rw_star_sub_ScaledLog2₁ h₁)
  theorem rw_star_sub_ScaledLog2₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledLog2 a₀ a₁ a a₃ a₄ a₅) (ScaledLog2 a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledLog2₂ h)
    | .refl h => .refl (eqe_ScaledLog2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledLog2₂ h₀) (rw_star_sub_ScaledLog2₂ h₁)
  theorem rw_star_sub_ScaledLog2₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledLog2 a₀ a₁ a₂ a a₄ a₅) (ScaledLog2 a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledLog2₃ h)
    | .refl h => .refl (eqe_ScaledLog2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledLog2₃ h₀) (rw_star_sub_ScaledLog2₃ h₁)
  theorem rw_star_sub_ScaledLog2₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledLog2 a₀ a₁ a₂ a₃ a a₅) (ScaledLog2 a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledLog2₄ h)
    | .refl h => .refl (eqe_ScaledLog2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledLog2₄ h₀) (rw_star_sub_ScaledLog2₄ h₁)
  theorem rw_star_sub_ScaledLog2₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledLog2 a₀ a₁ a₂ a₃ a₄ a) (ScaledLog2 a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledLog2₅ h)
    | .refl h => .refl (eqe_ScaledLog2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledLog2₅ h₀) (rw_star_sub_ScaledLog2₅ h₁)
  theorem rw_star_sub_ScaledLogOnePlus₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledLogOnePlus a a₁ a₂ a₃ a₄ a₅) (ScaledLogOnePlus b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledLogOnePlus₀ h)
    | .refl h => .refl (eqe_ScaledLogOnePlus h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledLogOnePlus₀ h₀) (rw_star_sub_ScaledLogOnePlus₀ h₁)
  theorem rw_star_sub_ScaledLogOnePlus₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledLogOnePlus a₀ a a₂ a₃ a₄ a₅) (ScaledLogOnePlus a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledLogOnePlus₁ h)
    | .refl h => .refl (eqe_ScaledLogOnePlus (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledLogOnePlus₁ h₀) (rw_star_sub_ScaledLogOnePlus₁ h₁)
  theorem rw_star_sub_ScaledLogOnePlus₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledLogOnePlus a₀ a₁ a a₃ a₄ a₅) (ScaledLogOnePlus a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledLogOnePlus₂ h)
    | .refl h => .refl (eqe_ScaledLogOnePlus (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledLogOnePlus₂ h₀) (rw_star_sub_ScaledLogOnePlus₂ h₁)
  theorem rw_star_sub_ScaledLogOnePlus₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledLogOnePlus a₀ a₁ a₂ a a₄ a₅) (ScaledLogOnePlus a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledLogOnePlus₃ h)
    | .refl h => .refl (eqe_ScaledLogOnePlus (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledLogOnePlus₃ h₀) (rw_star_sub_ScaledLogOnePlus₃ h₁)
  theorem rw_star_sub_ScaledLogOnePlus₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledLogOnePlus a₀ a₁ a₂ a₃ a a₅) (ScaledLogOnePlus a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledLogOnePlus₄ h)
    | .refl h => .refl (eqe_ScaledLogOnePlus (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledLogOnePlus₄ h₀) (rw_star_sub_ScaledLogOnePlus₄ h₁)
  theorem rw_star_sub_ScaledLogOnePlus₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledLogOnePlus a₀ a₁ a₂ a₃ a₄ a) (ScaledLogOnePlus a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledLogOnePlus₅ h)
    | .refl h => .refl (eqe_ScaledLogOnePlus (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledLogOnePlus₅ h₀) (rw_star_sub_ScaledLogOnePlus₅ h₁)
  theorem rw_star_sub_ScaledExpMinusOne₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledExpMinusOne a a₁ a₂ a₃ a₄ a₅) (ScaledExpMinusOne b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledExpMinusOne₀ h)
    | .refl h => .refl (eqe_ScaledExpMinusOne h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledExpMinusOne₀ h₀) (rw_star_sub_ScaledExpMinusOne₀ h₁)
  theorem rw_star_sub_ScaledExpMinusOne₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledExpMinusOne a₀ a a₂ a₃ a₄ a₅) (ScaledExpMinusOne a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledExpMinusOne₁ h)
    | .refl h => .refl (eqe_ScaledExpMinusOne (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledExpMinusOne₁ h₀) (rw_star_sub_ScaledExpMinusOne₁ h₁)
  theorem rw_star_sub_ScaledExpMinusOne₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledExpMinusOne a₀ a₁ a a₃ a₄ a₅) (ScaledExpMinusOne a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledExpMinusOne₂ h)
    | .refl h => .refl (eqe_ScaledExpMinusOne (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledExpMinusOne₂ h₀) (rw_star_sub_ScaledExpMinusOne₂ h₁)
  theorem rw_star_sub_ScaledExpMinusOne₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledExpMinusOne a₀ a₁ a₂ a a₄ a₅) (ScaledExpMinusOne a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledExpMinusOne₃ h)
    | .refl h => .refl (eqe_ScaledExpMinusOne (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledExpMinusOne₃ h₀) (rw_star_sub_ScaledExpMinusOne₃ h₁)
  theorem rw_star_sub_ScaledExpMinusOne₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledExpMinusOne a₀ a₁ a₂ a₃ a a₅) (ScaledExpMinusOne a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledExpMinusOne₄ h)
    | .refl h => .refl (eqe_ScaledExpMinusOne (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledExpMinusOne₄ h₀) (rw_star_sub_ScaledExpMinusOne₄ h₁)
  theorem rw_star_sub_ScaledExpMinusOne₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledExpMinusOne a₀ a₁ a₂ a₃ a₄ a) (ScaledExpMinusOne a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledExpMinusOne₅ h)
    | .refl h => .refl (eqe_ScaledExpMinusOne (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledExpMinusOne₅ h₀) (rw_star_sub_ScaledExpMinusOne₅ h₁)
  theorem rw_star_sub_ScaledSin₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSin a a₁ a₂ a₃ a₄ a₅) (ScaledSin b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSin₀ h)
    | .refl h => .refl (eqe_ScaledSin h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSin₀ h₀) (rw_star_sub_ScaledSin₀ h₁)
  theorem rw_star_sub_ScaledSin₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSin a₀ a a₂ a₃ a₄ a₅) (ScaledSin a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSin₁ h)
    | .refl h => .refl (eqe_ScaledSin (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSin₁ h₀) (rw_star_sub_ScaledSin₁ h₁)
  theorem rw_star_sub_ScaledSin₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSin a₀ a₁ a a₃ a₄ a₅) (ScaledSin a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSin₂ h)
    | .refl h => .refl (eqe_ScaledSin (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSin₂ h₀) (rw_star_sub_ScaledSin₂ h₁)
  theorem rw_star_sub_ScaledSin₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSin a₀ a₁ a₂ a a₄ a₅) (ScaledSin a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSin₃ h)
    | .refl h => .refl (eqe_ScaledSin (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSin₃ h₀) (rw_star_sub_ScaledSin₃ h₁)
  theorem rw_star_sub_ScaledSin₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledSin a₀ a₁ a₂ a₃ a a₅) (ScaledSin a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledSin₄ h)
    | .refl h => .refl (eqe_ScaledSin (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSin₄ h₀) (rw_star_sub_ScaledSin₄ h₁)
  theorem rw_star_sub_ScaledSin₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledSin a₀ a₁ a₂ a₃ a₄ a) (ScaledSin a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledSin₅ h)
    | .refl h => .refl (eqe_ScaledSin (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSin₅ h₀) (rw_star_sub_ScaledSin₅ h₁)
  theorem rw_star_sub_ScaledCos₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledCos a a₁ a₂ a₃ a₄ a₅) (ScaledCos b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledCos₀ h)
    | .refl h => .refl (eqe_ScaledCos h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCos₀ h₀) (rw_star_sub_ScaledCos₀ h₁)
  theorem rw_star_sub_ScaledCos₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledCos a₀ a a₂ a₃ a₄ a₅) (ScaledCos a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledCos₁ h)
    | .refl h => .refl (eqe_ScaledCos (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCos₁ h₀) (rw_star_sub_ScaledCos₁ h₁)
  theorem rw_star_sub_ScaledCos₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledCos a₀ a₁ a a₃ a₄ a₅) (ScaledCos a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledCos₂ h)
    | .refl h => .refl (eqe_ScaledCos (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCos₂ h₀) (rw_star_sub_ScaledCos₂ h₁)
  theorem rw_star_sub_ScaledCos₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledCos a₀ a₁ a₂ a a₄ a₅) (ScaledCos a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledCos₃ h)
    | .refl h => .refl (eqe_ScaledCos (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCos₃ h₀) (rw_star_sub_ScaledCos₃ h₁)
  theorem rw_star_sub_ScaledCos₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledCos a₀ a₁ a₂ a₃ a a₅) (ScaledCos a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledCos₄ h)
    | .refl h => .refl (eqe_ScaledCos (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCos₄ h₀) (rw_star_sub_ScaledCos₄ h₁)
  theorem rw_star_sub_ScaledCos₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledCos a₀ a₁ a₂ a₃ a₄ a) (ScaledCos a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledCos₅ h)
    | .refl h => .refl (eqe_ScaledCos (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCos₅ h₀) (rw_star_sub_ScaledCos₅ h₁)
  theorem rw_star_sub_ScaledTan₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledTan a a₁ a₂ a₃ a₄ a₅) (ScaledTan b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledTan₀ h)
    | .refl h => .refl (eqe_ScaledTan h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledTan₀ h₀) (rw_star_sub_ScaledTan₀ h₁)
  theorem rw_star_sub_ScaledTan₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledTan a₀ a a₂ a₃ a₄ a₅) (ScaledTan a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledTan₁ h)
    | .refl h => .refl (eqe_ScaledTan (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledTan₁ h₀) (rw_star_sub_ScaledTan₁ h₁)
  theorem rw_star_sub_ScaledTan₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledTan a₀ a₁ a a₃ a₄ a₅) (ScaledTan a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledTan₂ h)
    | .refl h => .refl (eqe_ScaledTan (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledTan₂ h₀) (rw_star_sub_ScaledTan₂ h₁)
  theorem rw_star_sub_ScaledTan₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledTan a₀ a₁ a₂ a a₄ a₅) (ScaledTan a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledTan₃ h)
    | .refl h => .refl (eqe_ScaledTan (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledTan₃ h₀) (rw_star_sub_ScaledTan₃ h₁)
  theorem rw_star_sub_ScaledTan₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledTan a₀ a₁ a₂ a₃ a a₅) (ScaledTan a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledTan₄ h)
    | .refl h => .refl (eqe_ScaledTan (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledTan₄ h₀) (rw_star_sub_ScaledTan₄ h₁)
  theorem rw_star_sub_ScaledTan₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledTan a₀ a₁ a₂ a₃ a₄ a) (ScaledTan a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledTan₅ h)
    | .refl h => .refl (eqe_ScaledTan (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledTan₅ h₀) (rw_star_sub_ScaledTan₅ h₁)
  theorem rw_star_sub_ScaledArcSin₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcSin a a₁ a₂ a₃ a₄ a₅) (ScaledArcSin b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcSin₀ h)
    | .refl h => .refl (eqe_ScaledArcSin h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcSin₀ h₀) (rw_star_sub_ScaledArcSin₀ h₁)
  theorem rw_star_sub_ScaledArcSin₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcSin a₀ a a₂ a₃ a₄ a₅) (ScaledArcSin a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcSin₁ h)
    | .refl h => .refl (eqe_ScaledArcSin (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcSin₁ h₀) (rw_star_sub_ScaledArcSin₁ h₁)
  theorem rw_star_sub_ScaledArcSin₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcSin a₀ a₁ a a₃ a₄ a₅) (ScaledArcSin a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcSin₂ h)
    | .refl h => .refl (eqe_ScaledArcSin (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcSin₂ h₀) (rw_star_sub_ScaledArcSin₂ h₁)
  theorem rw_star_sub_ScaledArcSin₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcSin a₀ a₁ a₂ a a₄ a₅) (ScaledArcSin a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcSin₃ h)
    | .refl h => .refl (eqe_ScaledArcSin (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcSin₃ h₀) (rw_star_sub_ScaledArcSin₃ h₁)
  theorem rw_star_sub_ScaledArcSin₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcSin a₀ a₁ a₂ a₃ a a₅) (ScaledArcSin a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledArcSin₄ h)
    | .refl h => .refl (eqe_ScaledArcSin (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcSin₄ h₀) (rw_star_sub_ScaledArcSin₄ h₁)
  theorem rw_star_sub_ScaledArcSin₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcSin a₀ a₁ a₂ a₃ a₄ a) (ScaledArcSin a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledArcSin₅ h)
    | .refl h => .refl (eqe_ScaledArcSin (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcSin₅ h₀) (rw_star_sub_ScaledArcSin₅ h₁)
  theorem rw_star_sub_ScaledArcCos₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcCos a a₁ a₂ a₃ a₄ a₅) (ScaledArcCos b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcCos₀ h)
    | .refl h => .refl (eqe_ScaledArcCos h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcCos₀ h₀) (rw_star_sub_ScaledArcCos₀ h₁)
  theorem rw_star_sub_ScaledArcCos₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcCos a₀ a a₂ a₃ a₄ a₅) (ScaledArcCos a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcCos₁ h)
    | .refl h => .refl (eqe_ScaledArcCos (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcCos₁ h₀) (rw_star_sub_ScaledArcCos₁ h₁)
  theorem rw_star_sub_ScaledArcCos₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcCos a₀ a₁ a a₃ a₄ a₅) (ScaledArcCos a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcCos₂ h)
    | .refl h => .refl (eqe_ScaledArcCos (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcCos₂ h₀) (rw_star_sub_ScaledArcCos₂ h₁)
  theorem rw_star_sub_ScaledArcCos₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcCos a₀ a₁ a₂ a a₄ a₅) (ScaledArcCos a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcCos₃ h)
    | .refl h => .refl (eqe_ScaledArcCos (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcCos₃ h₀) (rw_star_sub_ScaledArcCos₃ h₁)
  theorem rw_star_sub_ScaledArcCos₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcCos a₀ a₁ a₂ a₃ a a₅) (ScaledArcCos a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledArcCos₄ h)
    | .refl h => .refl (eqe_ScaledArcCos (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcCos₄ h₀) (rw_star_sub_ScaledArcCos₄ h₁)
  theorem rw_star_sub_ScaledArcCos₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcCos a₀ a₁ a₂ a₃ a₄ a) (ScaledArcCos a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledArcCos₅ h)
    | .refl h => .refl (eqe_ScaledArcCos (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcCos₅ h₀) (rw_star_sub_ScaledArcCos₅ h₁)
  theorem rw_star_sub_ScaledArcTan₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTan a a₁ a₂ a₃ a₄ a₅) (ScaledArcTan b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcTan₀ h)
    | .refl h => .refl (eqe_ScaledArcTan h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan₀ h₀) (rw_star_sub_ScaledArcTan₀ h₁)
  theorem rw_star_sub_ScaledArcTan₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTan a₀ a a₂ a₃ a₄ a₅) (ScaledArcTan a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcTan₁ h)
    | .refl h => .refl (eqe_ScaledArcTan (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan₁ h₀) (rw_star_sub_ScaledArcTan₁ h₁)
  theorem rw_star_sub_ScaledArcTan₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTan a₀ a₁ a a₃ a₄ a₅) (ScaledArcTan a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcTan₂ h)
    | .refl h => .refl (eqe_ScaledArcTan (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan₂ h₀) (rw_star_sub_ScaledArcTan₂ h₁)
  theorem rw_star_sub_ScaledArcTan₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTan a₀ a₁ a₂ a a₄ a₅) (ScaledArcTan a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcTan₃ h)
    | .refl h => .refl (eqe_ScaledArcTan (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan₃ h₀) (rw_star_sub_ScaledArcTan₃ h₁)
  theorem rw_star_sub_ScaledArcTan₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcTan a₀ a₁ a₂ a₃ a a₅) (ScaledArcTan a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledArcTan₄ h)
    | .refl h => .refl (eqe_ScaledArcTan (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan₄ h₀) (rw_star_sub_ScaledArcTan₄ h₁)
  theorem rw_star_sub_ScaledArcTan₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcTan a₀ a₁ a₂ a₃ a₄ a) (ScaledArcTan a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledArcTan₅ h)
    | .refl h => .refl (eqe_ScaledArcTan (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan₅ h₀) (rw_star_sub_ScaledArcTan₅ h₁)
  theorem rw_star_sub_ScaledSinh₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSinh a a₁ a₂ a₃ a₄ a₅) (ScaledSinh b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSinh₀ h)
    | .refl h => .refl (eqe_ScaledSinh h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSinh₀ h₀) (rw_star_sub_ScaledSinh₀ h₁)
  theorem rw_star_sub_ScaledSinh₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSinh a₀ a a₂ a₃ a₄ a₅) (ScaledSinh a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSinh₁ h)
    | .refl h => .refl (eqe_ScaledSinh (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSinh₁ h₀) (rw_star_sub_ScaledSinh₁ h₁)
  theorem rw_star_sub_ScaledSinh₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSinh a₀ a₁ a a₃ a₄ a₅) (ScaledSinh a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSinh₂ h)
    | .refl h => .refl (eqe_ScaledSinh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSinh₂ h₀) (rw_star_sub_ScaledSinh₂ h₁)
  theorem rw_star_sub_ScaledSinh₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSinh a₀ a₁ a₂ a a₄ a₅) (ScaledSinh a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSinh₃ h)
    | .refl h => .refl (eqe_ScaledSinh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSinh₃ h₀) (rw_star_sub_ScaledSinh₃ h₁)
  theorem rw_star_sub_ScaledSinh₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledSinh a₀ a₁ a₂ a₃ a a₅) (ScaledSinh a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledSinh₄ h)
    | .refl h => .refl (eqe_ScaledSinh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSinh₄ h₀) (rw_star_sub_ScaledSinh₄ h₁)
  theorem rw_star_sub_ScaledSinh₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledSinh a₀ a₁ a₂ a₃ a₄ a) (ScaledSinh a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledSinh₅ h)
    | .refl h => .refl (eqe_ScaledSinh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSinh₅ h₀) (rw_star_sub_ScaledSinh₅ h₁)
  theorem rw_star_sub_ScaledCosh₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledCosh a a₁ a₂ a₃ a₄ a₅) (ScaledCosh b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledCosh₀ h)
    | .refl h => .refl (eqe_ScaledCosh h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCosh₀ h₀) (rw_star_sub_ScaledCosh₀ h₁)
  theorem rw_star_sub_ScaledCosh₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledCosh a₀ a a₂ a₃ a₄ a₅) (ScaledCosh a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledCosh₁ h)
    | .refl h => .refl (eqe_ScaledCosh (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCosh₁ h₀) (rw_star_sub_ScaledCosh₁ h₁)
  theorem rw_star_sub_ScaledCosh₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledCosh a₀ a₁ a a₃ a₄ a₅) (ScaledCosh a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledCosh₂ h)
    | .refl h => .refl (eqe_ScaledCosh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCosh₂ h₀) (rw_star_sub_ScaledCosh₂ h₁)
  theorem rw_star_sub_ScaledCosh₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledCosh a₀ a₁ a₂ a a₄ a₅) (ScaledCosh a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledCosh₃ h)
    | .refl h => .refl (eqe_ScaledCosh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCosh₃ h₀) (rw_star_sub_ScaledCosh₃ h₁)
  theorem rw_star_sub_ScaledCosh₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledCosh a₀ a₁ a₂ a₃ a a₅) (ScaledCosh a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledCosh₄ h)
    | .refl h => .refl (eqe_ScaledCosh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCosh₄ h₀) (rw_star_sub_ScaledCosh₄ h₁)
  theorem rw_star_sub_ScaledCosh₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledCosh a₀ a₁ a₂ a₃ a₄ a) (ScaledCosh a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledCosh₅ h)
    | .refl h => .refl (eqe_ScaledCosh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCosh₅ h₀) (rw_star_sub_ScaledCosh₅ h₁)
  theorem rw_star_sub_ScaledTanh₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledTanh a a₁ a₂ a₃ a₄ a₅) (ScaledTanh b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledTanh₀ h)
    | .refl h => .refl (eqe_ScaledTanh h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledTanh₀ h₀) (rw_star_sub_ScaledTanh₀ h₁)
  theorem rw_star_sub_ScaledTanh₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledTanh a₀ a a₂ a₃ a₄ a₅) (ScaledTanh a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledTanh₁ h)
    | .refl h => .refl (eqe_ScaledTanh (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledTanh₁ h₀) (rw_star_sub_ScaledTanh₁ h₁)
  theorem rw_star_sub_ScaledTanh₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledTanh a₀ a₁ a a₃ a₄ a₅) (ScaledTanh a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledTanh₂ h)
    | .refl h => .refl (eqe_ScaledTanh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledTanh₂ h₀) (rw_star_sub_ScaledTanh₂ h₁)
  theorem rw_star_sub_ScaledTanh₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledTanh a₀ a₁ a₂ a a₄ a₅) (ScaledTanh a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledTanh₃ h)
    | .refl h => .refl (eqe_ScaledTanh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledTanh₃ h₀) (rw_star_sub_ScaledTanh₃ h₁)
  theorem rw_star_sub_ScaledTanh₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledTanh a₀ a₁ a₂ a₃ a a₅) (ScaledTanh a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledTanh₄ h)
    | .refl h => .refl (eqe_ScaledTanh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledTanh₄ h₀) (rw_star_sub_ScaledTanh₄ h₁)
  theorem rw_star_sub_ScaledTanh₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledTanh a₀ a₁ a₂ a₃ a₄ a) (ScaledTanh a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledTanh₅ h)
    | .refl h => .refl (eqe_ScaledTanh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledTanh₅ h₀) (rw_star_sub_ScaledTanh₅ h₁)
  theorem rw_star_sub_ScaledArcSinh₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcSinh a a₁ a₂ a₃ a₄ a₅) (ScaledArcSinh b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcSinh₀ h)
    | .refl h => .refl (eqe_ScaledArcSinh h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcSinh₀ h₀) (rw_star_sub_ScaledArcSinh₀ h₁)
  theorem rw_star_sub_ScaledArcSinh₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcSinh a₀ a a₂ a₃ a₄ a₅) (ScaledArcSinh a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcSinh₁ h)
    | .refl h => .refl (eqe_ScaledArcSinh (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcSinh₁ h₀) (rw_star_sub_ScaledArcSinh₁ h₁)
  theorem rw_star_sub_ScaledArcSinh₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcSinh a₀ a₁ a a₃ a₄ a₅) (ScaledArcSinh a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcSinh₂ h)
    | .refl h => .refl (eqe_ScaledArcSinh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcSinh₂ h₀) (rw_star_sub_ScaledArcSinh₂ h₁)
  theorem rw_star_sub_ScaledArcSinh₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcSinh a₀ a₁ a₂ a a₄ a₅) (ScaledArcSinh a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcSinh₃ h)
    | .refl h => .refl (eqe_ScaledArcSinh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcSinh₃ h₀) (rw_star_sub_ScaledArcSinh₃ h₁)
  theorem rw_star_sub_ScaledArcSinh₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcSinh a₀ a₁ a₂ a₃ a a₅) (ScaledArcSinh a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledArcSinh₄ h)
    | .refl h => .refl (eqe_ScaledArcSinh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcSinh₄ h₀) (rw_star_sub_ScaledArcSinh₄ h₁)
  theorem rw_star_sub_ScaledArcSinh₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcSinh a₀ a₁ a₂ a₃ a₄ a) (ScaledArcSinh a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledArcSinh₅ h)
    | .refl h => .refl (eqe_ScaledArcSinh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcSinh₅ h₀) (rw_star_sub_ScaledArcSinh₅ h₁)
  theorem rw_star_sub_ScaledArcCosh₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcCosh a a₁ a₂ a₃ a₄ a₅) (ScaledArcCosh b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcCosh₀ h)
    | .refl h => .refl (eqe_ScaledArcCosh h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcCosh₀ h₀) (rw_star_sub_ScaledArcCosh₀ h₁)
  theorem rw_star_sub_ScaledArcCosh₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcCosh a₀ a a₂ a₃ a₄ a₅) (ScaledArcCosh a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcCosh₁ h)
    | .refl h => .refl (eqe_ScaledArcCosh (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcCosh₁ h₀) (rw_star_sub_ScaledArcCosh₁ h₁)
  theorem rw_star_sub_ScaledArcCosh₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcCosh a₀ a₁ a a₃ a₄ a₅) (ScaledArcCosh a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcCosh₂ h)
    | .refl h => .refl (eqe_ScaledArcCosh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcCosh₂ h₀) (rw_star_sub_ScaledArcCosh₂ h₁)
  theorem rw_star_sub_ScaledArcCosh₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcCosh a₀ a₁ a₂ a a₄ a₅) (ScaledArcCosh a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcCosh₃ h)
    | .refl h => .refl (eqe_ScaledArcCosh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcCosh₃ h₀) (rw_star_sub_ScaledArcCosh₃ h₁)
  theorem rw_star_sub_ScaledArcCosh₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcCosh a₀ a₁ a₂ a₃ a a₅) (ScaledArcCosh a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledArcCosh₄ h)
    | .refl h => .refl (eqe_ScaledArcCosh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcCosh₄ h₀) (rw_star_sub_ScaledArcCosh₄ h₁)
  theorem rw_star_sub_ScaledArcCosh₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcCosh a₀ a₁ a₂ a₃ a₄ a) (ScaledArcCosh a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledArcCosh₅ h)
    | .refl h => .refl (eqe_ScaledArcCosh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcCosh₅ h₀) (rw_star_sub_ScaledArcCosh₅ h₁)
  theorem rw_star_sub_ScaledArcTanh₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTanh a a₁ a₂ a₃ a₄ a₅) (ScaledArcTanh b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcTanh₀ h)
    | .refl h => .refl (eqe_ScaledArcTanh h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTanh₀ h₀) (rw_star_sub_ScaledArcTanh₀ h₁)
  theorem rw_star_sub_ScaledArcTanh₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTanh a₀ a a₂ a₃ a₄ a₅) (ScaledArcTanh a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcTanh₁ h)
    | .refl h => .refl (eqe_ScaledArcTanh (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTanh₁ h₀) (rw_star_sub_ScaledArcTanh₁ h₁)
  theorem rw_star_sub_ScaledArcTanh₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTanh a₀ a₁ a a₃ a₄ a₅) (ScaledArcTanh a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcTanh₂ h)
    | .refl h => .refl (eqe_ScaledArcTanh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTanh₂ h₀) (rw_star_sub_ScaledArcTanh₂ h₁)
  theorem rw_star_sub_ScaledArcTanh₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTanh a₀ a₁ a₂ a a₄ a₅) (ScaledArcTanh a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcTanh₃ h)
    | .refl h => .refl (eqe_ScaledArcTanh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTanh₃ h₀) (rw_star_sub_ScaledArcTanh₃ h₁)
  theorem rw_star_sub_ScaledArcTanh₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcTanh a₀ a₁ a₂ a₃ a a₅) (ScaledArcTanh a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledArcTanh₄ h)
    | .refl h => .refl (eqe_ScaledArcTanh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTanh₄ h₀) (rw_star_sub_ScaledArcTanh₄ h₁)
  theorem rw_star_sub_ScaledArcTanh₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcTanh a₀ a₁ a₂ a₃ a₄ a) (ScaledArcTanh a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledArcTanh₅ h)
    | .refl h => .refl (eqe_ScaledArcTanh (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTanh₅ h₀) (rw_star_sub_ScaledArcTanh₅ h₁)
  theorem rw_star_sub_ScaledSinPi₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSinPi a a₁ a₂ a₃ a₄ a₅) (ScaledSinPi b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSinPi₀ h)
    | .refl h => .refl (eqe_ScaledSinPi h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSinPi₀ h₀) (rw_star_sub_ScaledSinPi₀ h₁)
  theorem rw_star_sub_ScaledSinPi₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSinPi a₀ a a₂ a₃ a₄ a₅) (ScaledSinPi a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSinPi₁ h)
    | .refl h => .refl (eqe_ScaledSinPi (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSinPi₁ h₀) (rw_star_sub_ScaledSinPi₁ h₁)
  theorem rw_star_sub_ScaledSinPi₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSinPi a₀ a₁ a a₃ a₄ a₅) (ScaledSinPi a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSinPi₂ h)
    | .refl h => .refl (eqe_ScaledSinPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSinPi₂ h₀) (rw_star_sub_ScaledSinPi₂ h₁)
  theorem rw_star_sub_ScaledSinPi₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSinPi a₀ a₁ a₂ a a₄ a₅) (ScaledSinPi a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSinPi₃ h)
    | .refl h => .refl (eqe_ScaledSinPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSinPi₃ h₀) (rw_star_sub_ScaledSinPi₃ h₁)
  theorem rw_star_sub_ScaledSinPi₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledSinPi a₀ a₁ a₂ a₃ a a₅) (ScaledSinPi a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledSinPi₄ h)
    | .refl h => .refl (eqe_ScaledSinPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSinPi₄ h₀) (rw_star_sub_ScaledSinPi₄ h₁)
  theorem rw_star_sub_ScaledSinPi₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledSinPi a₀ a₁ a₂ a₃ a₄ a) (ScaledSinPi a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledSinPi₅ h)
    | .refl h => .refl (eqe_ScaledSinPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSinPi₅ h₀) (rw_star_sub_ScaledSinPi₅ h₁)
  theorem rw_star_sub_ScaledCosPi₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledCosPi a a₁ a₂ a₃ a₄ a₅) (ScaledCosPi b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledCosPi₀ h)
    | .refl h => .refl (eqe_ScaledCosPi h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCosPi₀ h₀) (rw_star_sub_ScaledCosPi₀ h₁)
  theorem rw_star_sub_ScaledCosPi₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledCosPi a₀ a a₂ a₃ a₄ a₅) (ScaledCosPi a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledCosPi₁ h)
    | .refl h => .refl (eqe_ScaledCosPi (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCosPi₁ h₀) (rw_star_sub_ScaledCosPi₁ h₁)
  theorem rw_star_sub_ScaledCosPi₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledCosPi a₀ a₁ a a₃ a₄ a₅) (ScaledCosPi a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledCosPi₂ h)
    | .refl h => .refl (eqe_ScaledCosPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCosPi₂ h₀) (rw_star_sub_ScaledCosPi₂ h₁)
  theorem rw_star_sub_ScaledCosPi₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledCosPi a₀ a₁ a₂ a a₄ a₅) (ScaledCosPi a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledCosPi₃ h)
    | .refl h => .refl (eqe_ScaledCosPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCosPi₃ h₀) (rw_star_sub_ScaledCosPi₃ h₁)
  theorem rw_star_sub_ScaledCosPi₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledCosPi a₀ a₁ a₂ a₃ a a₅) (ScaledCosPi a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledCosPi₄ h)
    | .refl h => .refl (eqe_ScaledCosPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCosPi₄ h₀) (rw_star_sub_ScaledCosPi₄ h₁)
  theorem rw_star_sub_ScaledCosPi₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledCosPi a₀ a₁ a₂ a₃ a₄ a) (ScaledCosPi a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledCosPi₅ h)
    | .refl h => .refl (eqe_ScaledCosPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledCosPi₅ h₀) (rw_star_sub_ScaledCosPi₅ h₁)
  theorem rw_star_sub_ScaledTanPi₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledTanPi a a₁ a₂ a₃ a₄ a₅) (ScaledTanPi b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledTanPi₀ h)
    | .refl h => .refl (eqe_ScaledTanPi h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledTanPi₀ h₀) (rw_star_sub_ScaledTanPi₀ h₁)
  theorem rw_star_sub_ScaledTanPi₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledTanPi a₀ a a₂ a₃ a₄ a₅) (ScaledTanPi a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledTanPi₁ h)
    | .refl h => .refl (eqe_ScaledTanPi (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledTanPi₁ h₀) (rw_star_sub_ScaledTanPi₁ h₁)
  theorem rw_star_sub_ScaledTanPi₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledTanPi a₀ a₁ a a₃ a₄ a₅) (ScaledTanPi a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledTanPi₂ h)
    | .refl h => .refl (eqe_ScaledTanPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledTanPi₂ h₀) (rw_star_sub_ScaledTanPi₂ h₁)
  theorem rw_star_sub_ScaledTanPi₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledTanPi a₀ a₁ a₂ a a₄ a₅) (ScaledTanPi a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledTanPi₃ h)
    | .refl h => .refl (eqe_ScaledTanPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledTanPi₃ h₀) (rw_star_sub_ScaledTanPi₃ h₁)
  theorem rw_star_sub_ScaledTanPi₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledTanPi a₀ a₁ a₂ a₃ a a₅) (ScaledTanPi a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledTanPi₄ h)
    | .refl h => .refl (eqe_ScaledTanPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledTanPi₄ h₀) (rw_star_sub_ScaledTanPi₄ h₁)
  theorem rw_star_sub_ScaledTanPi₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledTanPi a₀ a₁ a₂ a₃ a₄ a) (ScaledTanPi a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledTanPi₅ h)
    | .refl h => .refl (eqe_ScaledTanPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledTanPi₅ h₀) (rw_star_sub_ScaledTanPi₅ h₁)
  theorem rw_star_sub_ScaledArcSinPi₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcSinPi a a₁ a₂ a₃ a₄ a₅) (ScaledArcSinPi b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcSinPi₀ h)
    | .refl h => .refl (eqe_ScaledArcSinPi h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcSinPi₀ h₀) (rw_star_sub_ScaledArcSinPi₀ h₁)
  theorem rw_star_sub_ScaledArcSinPi₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcSinPi a₀ a a₂ a₃ a₄ a₅) (ScaledArcSinPi a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcSinPi₁ h)
    | .refl h => .refl (eqe_ScaledArcSinPi (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcSinPi₁ h₀) (rw_star_sub_ScaledArcSinPi₁ h₁)
  theorem rw_star_sub_ScaledArcSinPi₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcSinPi a₀ a₁ a a₃ a₄ a₅) (ScaledArcSinPi a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcSinPi₂ h)
    | .refl h => .refl (eqe_ScaledArcSinPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcSinPi₂ h₀) (rw_star_sub_ScaledArcSinPi₂ h₁)
  theorem rw_star_sub_ScaledArcSinPi₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcSinPi a₀ a₁ a₂ a a₄ a₅) (ScaledArcSinPi a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcSinPi₃ h)
    | .refl h => .refl (eqe_ScaledArcSinPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcSinPi₃ h₀) (rw_star_sub_ScaledArcSinPi₃ h₁)
  theorem rw_star_sub_ScaledArcSinPi₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcSinPi a₀ a₁ a₂ a₃ a a₅) (ScaledArcSinPi a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledArcSinPi₄ h)
    | .refl h => .refl (eqe_ScaledArcSinPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcSinPi₄ h₀) (rw_star_sub_ScaledArcSinPi₄ h₁)
  theorem rw_star_sub_ScaledArcSinPi₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcSinPi a₀ a₁ a₂ a₃ a₄ a) (ScaledArcSinPi a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledArcSinPi₅ h)
    | .refl h => .refl (eqe_ScaledArcSinPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcSinPi₅ h₀) (rw_star_sub_ScaledArcSinPi₅ h₁)
  theorem rw_star_sub_ScaledArcCosPi₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcCosPi a a₁ a₂ a₃ a₄ a₅) (ScaledArcCosPi b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcCosPi₀ h)
    | .refl h => .refl (eqe_ScaledArcCosPi h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcCosPi₀ h₀) (rw_star_sub_ScaledArcCosPi₀ h₁)
  theorem rw_star_sub_ScaledArcCosPi₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcCosPi a₀ a a₂ a₃ a₄ a₅) (ScaledArcCosPi a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcCosPi₁ h)
    | .refl h => .refl (eqe_ScaledArcCosPi (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcCosPi₁ h₀) (rw_star_sub_ScaledArcCosPi₁ h₁)
  theorem rw_star_sub_ScaledArcCosPi₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcCosPi a₀ a₁ a a₃ a₄ a₅) (ScaledArcCosPi a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcCosPi₂ h)
    | .refl h => .refl (eqe_ScaledArcCosPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcCosPi₂ h₀) (rw_star_sub_ScaledArcCosPi₂ h₁)
  theorem rw_star_sub_ScaledArcCosPi₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcCosPi a₀ a₁ a₂ a a₄ a₅) (ScaledArcCosPi a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcCosPi₃ h)
    | .refl h => .refl (eqe_ScaledArcCosPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcCosPi₃ h₀) (rw_star_sub_ScaledArcCosPi₃ h₁)
  theorem rw_star_sub_ScaledArcCosPi₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcCosPi a₀ a₁ a₂ a₃ a a₅) (ScaledArcCosPi a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledArcCosPi₄ h)
    | .refl h => .refl (eqe_ScaledArcCosPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcCosPi₄ h₀) (rw_star_sub_ScaledArcCosPi₄ h₁)
  theorem rw_star_sub_ScaledArcCosPi₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcCosPi a₀ a₁ a₂ a₃ a₄ a) (ScaledArcCosPi a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledArcCosPi₅ h)
    | .refl h => .refl (eqe_ScaledArcCosPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcCosPi₅ h₀) (rw_star_sub_ScaledArcCosPi₅ h₁)
  theorem rw_star_sub_ScaledArcTanPi₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTanPi a a₁ a₂ a₃ a₄ a₅) (ScaledArcTanPi b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcTanPi₀ h)
    | .refl h => .refl (eqe_ScaledArcTanPi h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTanPi₀ h₀) (rw_star_sub_ScaledArcTanPi₀ h₁)
  theorem rw_star_sub_ScaledArcTanPi₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTanPi a₀ a a₂ a₃ a₄ a₅) (ScaledArcTanPi a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcTanPi₁ h)
    | .refl h => .refl (eqe_ScaledArcTanPi (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTanPi₁ h₀) (rw_star_sub_ScaledArcTanPi₁ h₁)
  theorem rw_star_sub_ScaledArcTanPi₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTanPi a₀ a₁ a a₃ a₄ a₅) (ScaledArcTanPi a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcTanPi₂ h)
    | .refl h => .refl (eqe_ScaledArcTanPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTanPi₂ h₀) (rw_star_sub_ScaledArcTanPi₂ h₁)
  theorem rw_star_sub_ScaledArcTanPi₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTanPi a₀ a₁ a₂ a a₄ a₅) (ScaledArcTanPi a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledArcTanPi₃ h)
    | .refl h => .refl (eqe_ScaledArcTanPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTanPi₃ h₀) (rw_star_sub_ScaledArcTanPi₃ h₁)
  theorem rw_star_sub_ScaledArcTanPi₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcTanPi a₀ a₁ a₂ a₃ a a₅) (ScaledArcTanPi a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledArcTanPi₄ h)
    | .refl h => .refl (eqe_ScaledArcTanPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTanPi₄ h₀) (rw_star_sub_ScaledArcTanPi₄ h₁)
  theorem rw_star_sub_ScaledArcTanPi₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcTanPi a₀ a₁ a₂ a₃ a₄ a) (ScaledArcTanPi a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledArcTanPi₅ h)
    | .refl h => .refl (eqe_ScaledArcTanPi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTanPi₅ h₀) (rw_star_sub_ScaledArcTanPi₅ h₁)
  theorem rw_star_sub_ScaledSoftplus₀ {a b a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSoftplus a a₁ a₂ a₃ a₄ a₅) (ScaledSoftplus b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSoftplus₀ h)
    | .refl h => .refl (eqe_ScaledSoftplus h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSoftplus₀ h₀) (rw_star_sub_ScaledSoftplus₀ h₁)
  theorem rw_star_sub_ScaledSoftplus₁ {a₀ a b a₂ : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSoftplus a₀ a a₂ a₃ a₄ a₅) (ScaledSoftplus a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSoftplus₁ h)
    | .refl h => .refl (eqe_ScaledSoftplus (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSoftplus₁ h₀) (rw_star_sub_ScaledSoftplus₁ h₁)
  theorem rw_star_sub_ScaledSoftplus₂ {a₀ a₁ a b : kFormat} {a₃ : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSoftplus a₀ a₁ a a₃ a₄ a₅) (ScaledSoftplus a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSoftplus₂ h)
    | .refl h => .refl (eqe_ScaledSoftplus (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kProjSpec.eqe_refl a₃) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSoftplus₂ h₀) (rw_star_sub_ScaledSoftplus₂ h₁)
  theorem rw_star_sub_ScaledSoftplus₃ {a₀ a₁ a₂ : kFormat} {a b : kProjSpec} {a₄ a₅ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledSoftplus a₀ a₁ a₂ a a₄ a₅) (ScaledSoftplus a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_ScaledSoftplus₃ h)
    | .refl h => .refl (eqe_ScaledSoftplus (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSoftplus₃ h₀) (rw_star_sub_ScaledSoftplus₃ h₁)
  theorem rw_star_sub_ScaledSoftplus₄ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a b a₅ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledSoftplus a₀ a₁ a₂ a₃ a a₅) (ScaledSoftplus a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_ScaledSoftplus₄ h)
    | .refl h => .refl (eqe_ScaledSoftplus (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSoftplus₄ h₀) (rw_star_sub_ScaledSoftplus₄ h₁)
  theorem rw_star_sub_ScaledSoftplus₅ {a₀ a₁ a₂ : kFormat} {a₃ : kProjSpec} {a₄ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledSoftplus a₀ a₁ a₂ a₃ a₄ a) (ScaledSoftplus a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_ScaledSoftplus₅ h)
    | .refl h => .refl (eqe_ScaledSoftplus (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledSoftplus₅ h₀) (rw_star_sub_ScaledSoftplus₅ h₁)
  theorem rw_star_sub_ScaledHypot₀ {a b a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledHypot a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledHypot b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledHypot₀ h)
    | .refl h => .refl (eqe_ScaledHypot h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledHypot₀ h₀) (rw_star_sub_ScaledHypot₀ h₁)
  theorem rw_star_sub_ScaledHypot₁ {a₀ a b a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledHypot a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledHypot a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledHypot₁ h)
    | .refl h => .refl (eqe_ScaledHypot (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledHypot₁ h₀) (rw_star_sub_ScaledHypot₁ h₁)
  theorem rw_star_sub_ScaledHypot₂ {a₀ a₁ a b a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledHypot a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledHypot a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledHypot₂ h)
    | .refl h => .refl (eqe_ScaledHypot (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledHypot₂ h₀) (rw_star_sub_ScaledHypot₂ h₁)
  theorem rw_star_sub_ScaledHypot₃ {a₀ a₁ a₂ a b a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledHypot a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (ScaledHypot a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledHypot₃ h)
    | .refl h => .refl (eqe_ScaledHypot (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledHypot₃ h₀) (rw_star_sub_ScaledHypot₃ h₁)
  theorem rw_star_sub_ScaledHypot₄ {a₀ a₁ a₂ a₃ a b : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledHypot a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (ScaledHypot a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledHypot₄ h)
    | .refl h => .refl (eqe_ScaledHypot (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledHypot₄ h₀) (rw_star_sub_ScaledHypot₄ h₁)
  theorem rw_star_sub_ScaledHypot₅ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a b : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledHypot a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (ScaledHypot a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledHypot₅ h)
    | .refl h => .refl (eqe_ScaledHypot (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledHypot₅ h₀) (rw_star_sub_ScaledHypot₅ h₁)
  theorem rw_star_sub_ScaledHypot₆ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a b a₇ a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledHypot a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (ScaledHypot a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledHypot₆ h)
    | .refl h => .refl (eqe_ScaledHypot (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledHypot₆ h₀) (rw_star_sub_ScaledHypot₆ h₁)
  theorem rw_star_sub_ScaledHypot₇ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a b a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (ScaledHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledHypot₇ h)
    | .refl h => .refl (eqe_ScaledHypot (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledHypot₇ h₀) (rw_star_sub_ScaledHypot₇ h₁)
  theorem rw_star_sub_ScaledHypot₈ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a b a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (ScaledHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | .step h => .step (rw_one.sub_ScaledHypot₈ h)
    | .refl h => .refl (eqe_ScaledHypot (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledHypot₈ h₀) (rw_star_sub_ScaledHypot₈ h₁)
  theorem rw_star_sub_ScaledHypot₉ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (ScaledHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | .step h => .step (rw_one.sub_ScaledHypot₉ h)
    | .refl h => .refl (eqe_ScaledHypot (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledHypot₉ h₀) (rw_star_sub_ScaledHypot₉ h₁)
  theorem rw_star_sub_ScaledArcTan2₀ {a b a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTan2 a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledArcTan2 b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledArcTan2₀ h)
    | .refl h => .refl (eqe_ScaledArcTan2 h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2₀ h₀) (rw_star_sub_ScaledArcTan2₀ h₁)
  theorem rw_star_sub_ScaledArcTan2₁ {a₀ a b a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTan2 a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledArcTan2 a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledArcTan2₁ h)
    | .refl h => .refl (eqe_ScaledArcTan2 (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2₁ h₀) (rw_star_sub_ScaledArcTan2₁ h₁)
  theorem rw_star_sub_ScaledArcTan2₂ {a₀ a₁ a b a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTan2 a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledArcTan2 a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledArcTan2₂ h)
    | .refl h => .refl (eqe_ScaledArcTan2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2₂ h₀) (rw_star_sub_ScaledArcTan2₂ h₁)
  theorem rw_star_sub_ScaledArcTan2₃ {a₀ a₁ a₂ a b a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTan2 a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (ScaledArcTan2 a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledArcTan2₃ h)
    | .refl h => .refl (eqe_ScaledArcTan2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2₃ h₀) (rw_star_sub_ScaledArcTan2₃ h₁)
  theorem rw_star_sub_ScaledArcTan2₄ {a₀ a₁ a₂ a₃ a b : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTan2 a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (ScaledArcTan2 a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledArcTan2₄ h)
    | .refl h => .refl (eqe_ScaledArcTan2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2₄ h₀) (rw_star_sub_ScaledArcTan2₄ h₁)
  theorem rw_star_sub_ScaledArcTan2₅ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a b : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledArcTan2₅ h)
    | .refl h => .refl (eqe_ScaledArcTan2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2₅ h₀) (rw_star_sub_ScaledArcTan2₅ h₁)
  theorem rw_star_sub_ScaledArcTan2₆ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a b a₇ a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledArcTan2₆ h)
    | .refl h => .refl (eqe_ScaledArcTan2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2₆ h₀) (rw_star_sub_ScaledArcTan2₆ h₁)
  theorem rw_star_sub_ScaledArcTan2₇ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a b a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledArcTan2₇ h)
    | .refl h => .refl (eqe_ScaledArcTan2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2₇ h₀) (rw_star_sub_ScaledArcTan2₇ h₁)
  theorem rw_star_sub_ScaledArcTan2₈ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a b a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | .step h => .step (rw_one.sub_ScaledArcTan2₈ h)
    | .refl h => .refl (eqe_ScaledArcTan2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2₈ h₀) (rw_star_sub_ScaledArcTan2₈ h₁)
  theorem rw_star_sub_ScaledArcTan2₉ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | .step h => .step (rw_one.sub_ScaledArcTan2₉ h)
    | .refl h => .refl (eqe_ScaledArcTan2 (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2₉ h₀) (rw_star_sub_ScaledArcTan2₉ h₁)
  theorem rw_star_sub_ScaledArcTan2Pi₀ {a b a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTan2Pi a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledArcTan2Pi b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledArcTan2Pi₀ h)
    | .refl h => .refl (eqe_ScaledArcTan2Pi h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2Pi₀ h₀) (rw_star_sub_ScaledArcTan2Pi₀ h₁)
  theorem rw_star_sub_ScaledArcTan2Pi₁ {a₀ a b a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTan2Pi a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledArcTan2Pi a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledArcTan2Pi₁ h)
    | .refl h => .refl (eqe_ScaledArcTan2Pi (kFormat.eqe_refl a₀) h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2Pi₁ h₀) (rw_star_sub_ScaledArcTan2Pi₁ h₁)
  theorem rw_star_sub_ScaledArcTan2Pi₂ {a₀ a₁ a b a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTan2Pi a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (ScaledArcTan2Pi a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledArcTan2Pi₂ h)
    | .refl h => .refl (eqe_ScaledArcTan2Pi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2Pi₂ h₀) (rw_star_sub_ScaledArcTan2Pi₂ h₁)
  theorem rw_star_sub_ScaledArcTan2Pi₃ {a₀ a₁ a₂ a b a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTan2Pi a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (ScaledArcTan2Pi a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledArcTan2Pi₃ h)
    | .refl h => .refl (eqe_ScaledArcTan2Pi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2Pi₃ h₀) (rw_star_sub_ScaledArcTan2Pi₃ h₁)
  theorem rw_star_sub_ScaledArcTan2Pi₄ {a₀ a₁ a₂ a₃ a b : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTan2Pi a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (ScaledArcTan2Pi a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledArcTan2Pi₄ h)
    | .refl h => .refl (eqe_ScaledArcTan2Pi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kProjSpec.eqe_refl a₅) rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2Pi₄ h₀) (rw_star_sub_ScaledArcTan2Pi₄ h₁)
  theorem rw_star_sub_ScaledArcTan2Pi₅ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a b : kProjSpec} {a₆ a₇ a₈ a₉ : MRat} : a.rw_star b →
      MRat.rw_star (ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledArcTan2Pi₅ h)
    | .refl h => .refl (eqe_ScaledArcTan2Pi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2Pi₅ h₀) (rw_star_sub_ScaledArcTan2Pi₅ h₁)
  theorem rw_star_sub_ScaledArcTan2Pi₆ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a b a₇ a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledArcTan2Pi₆ h)
    | .refl h => .refl (eqe_ScaledArcTan2Pi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) h rfl rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2Pi₆ h₀) (rw_star_sub_ScaledArcTan2Pi₆ h₁)
  theorem rw_star_sub_ScaledArcTan2Pi₇ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a b a₈ a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | .step h => .step (rw_one.sub_ScaledArcTan2Pi₇ h)
    | .refl h => .refl (eqe_ScaledArcTan2Pi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2Pi₇ h₀) (rw_star_sub_ScaledArcTan2Pi₇ h₁)
  theorem rw_star_sub_ScaledArcTan2Pi₈ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a b a₉ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | .step h => .step (rw_one.sub_ScaledArcTan2Pi₈ h)
    | .refl h => .refl (eqe_ScaledArcTan2Pi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2Pi₈ h₀) (rw_star_sub_ScaledArcTan2Pi₈ h₁)
  theorem rw_star_sub_ScaledArcTan2Pi₉ {a₀ a₁ a₂ a₃ a₄ : kFormat} {a₅ : kProjSpec} {a₆ a₇ a₈ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | .step h => .step (rw_one.sub_ScaledArcTan2Pi₉ h)
    | .refl h => .refl (eqe_ScaledArcTan2Pi (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kProjSpec.eqe_refl a₅) rfl rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ScaledArcTan2Pi₉ h₀) (rw_star_sub_ScaledArcTan2Pi₉ h₁)
  theorem rw_star_sub_ifthenelsefi₀ {a b : kBool} {a₁ a₂ : MRat} : a.rw_star b →
      MRat.rw_star (ifthenelsefi a a₁ a₂) (ifthenelsefi b a₁ a₂)
    | .step h => .step (rw_one.sub_ifthenelsefi₀ h)
    | .refl h => .refl (eqe_ifthenelsefi h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ifthenelsefi₀ h₀) (rw_star_sub_ifthenelsefi₀ h₁)
  theorem rw_star_sub_ifthenelsefi₁ {a₀ : kBool} {a b a₂ : MRat} : MRat.rw_star a b →
      MRat.rw_star (ifthenelsefi a₀ a a₂) (ifthenelsefi a₀ b a₂)
    | .step h => .step (rw_one.sub_ifthenelsefi₁ h)
    | .refl h => .refl (eqe_ifthenelsefi (kBool.eqe_refl a₀) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ifthenelsefi₁ h₀) (rw_star_sub_ifthenelsefi₁ h₁)
  theorem rw_star_sub_ifthenelsefi₂ {a₀ : kBool} {a₁ a b : MRat} : MRat.rw_star a b →
      MRat.rw_star (ifthenelsefi a₀ a₁ a) (ifthenelsefi a₀ a₁ b)
    | .step h => .step (rw_one.sub_ifthenelsefi₂ h)
    | .refl h => .refl (eqe_ifthenelsefi (kBool.eqe_refl a₀) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ifthenelsefi₂ h₀) (rw_star_sub_ifthenelsefi₂ h₁)
end MRat

end Maude
