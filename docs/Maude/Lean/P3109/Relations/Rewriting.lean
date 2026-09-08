-- Extracted from ../spec2.lean, lines 3735-7870.
-- See PLAN.md and manifest.json for provenance.
import P3109.Native.Equations

namespace Maude
-- Rewriting relations

mutual
  inductive kBool.rw_one: kBool → kBool → Prop
    | eqe_left {a b c : kBool} : a.eqe b → kBool.rw_one b c → kBool.rw_one a c
    | eqe_right {a b c : kBool} : kBool.rw_one a b → b.eqe c → kBool.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_and₀ {a₁ a b} : kBool.rw_one a b →
    kBool.rw_one (kBool.and a a₁) (kBool.and b a₁)
    | sub_and₁ {a₀ a b} : kBool.rw_one a b →
    kBool.rw_one (kBool.and a₀ a) (kBool.and a₀ b)
    | sub_or₀ {a₁ a b} : kBool.rw_one a b →
    kBool.rw_one (kBool.or a a₁) (kBool.or b a₁)
    | sub_or₁ {a₀ a b} : kBool.rw_one a b →
    kBool.rw_one (kBool.or a₀ a) (kBool.or a₀ b)
    | sub_xor₀ {a₁ a b} : kBool.rw_one a b →
    kBool.rw_one (kBool.xor a a₁) (kBool.xor b a₁)
    | sub_xor₁ {a₀ a b} : kBool.rw_one a b →
    kBool.rw_one (kBool.xor a₀ a) (kBool.xor a₀ b)
    | sub_not {a b} : kBool.rw_one a b →
    kBool.rw_one (kBool.not a) (kBool.not b)
    | sub_implies₀ {a₁ a b} : kBool.rw_one a b →
    kBool.rw_one (kBool.implies a a₁) (kBool.implies b a₁)
    | sub_implies₁ {a₀ a b} : kBool.rw_one a b →
    kBool.rw_one (kBool.implies a₀ a) (kBool.implies a₀ b)
    | sub_lt₀₀ {a₁ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.lt₀ a a₁) (kBool.lt₀ b a₁)
    | sub_lt₀₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.lt₀ a₀ a) (kBool.lt₀ a₀ b)
    | sub_lteq₀₀ {a₁ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.lteq₀ a a₁) (kBool.lteq₀ b a₁)
    | sub_lteq₀₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.lteq₀ a₀ a) (kBool.lteq₀ a₀ b)
    | sub_gt₀₀ {a₁ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.gt₀ a a₁) (kBool.gt₀ b a₁)
    | sub_gt₀₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.gt₀ a₀ a) (kBool.gt₀ a₀ b)
    | sub_gteq₀₀ {a₁ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.gteq₀ a a₁) (kBool.gteq₀ b a₁)
    | sub_gteq₀₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.gteq₀ a₀ a) (kBool.gteq₀ a₀ b)
    | sub_divides₀ {a₁ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.divides a a₁) (kBool.divides b a₁)
    | sub_divides₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.divides a₀ a) (kBool.divides a₀ b)
    | sub_xNaN {a b} : kXReal.rw_one a b →
    kBool.rw_one (kBool.xNaN a) (kBool.xNaN b)
    | sub_xInfinite {a b} : kXReal.rw_one a b →
    kBool.rw_one (kBool.xInfinite a) (kBool.xInfinite b)
    | sub_xFinite {a b} : kXReal.rw_one a b →
    kBool.rw_one (kBool.xFinite a) (kBool.xFinite b)
    | sub_xMinus {a b} : kXReal.rw_one a b →
    kBool.rw_one (kBool.xMinus a) (kBool.xMinus b)
    | sub_xLt₀ {a₁ a b} : kXReal.rw_one a b →
    kBool.rw_one (kBool.xLt a a₁) (kBool.xLt b a₁)
    | sub_xLt₁ {a₀ a b} : kXReal.rw_one a b →
    kBool.rw_one (kBool.xLt a₀ a) (kBool.xLt a₀ b)
    | sub_xLe₀ {a₁ a b} : kXReal.rw_one a b →
    kBool.rw_one (kBool.xLe a a₁) (kBool.xLe b a₁)
    | sub_xLe₁ {a₀ a b} : kXReal.rw_one a b →
    kBool.rw_one (kBool.xLe a₀ a) (kBool.xLe a₀ b)
    | sub_xEq₀ {a₁ a b} : kXReal.rw_one a b →
    kBool.rw_one (kBool.xEq a a₁) (kBool.xEq b a₁)
    | sub_xEq₁ {a₀ a b} : kXReal.rw_one a b →
    kBool.rw_one (kBool.xEq a₀ a) (kBool.xEq a₀ b)
    | sub_even {a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.even a) (kBool.even b)
    | sub_validFormat {a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.validFormat a) (kBool.validFormat b)
    | sub_internalFormat {a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.internalFormat a) (kBool.internalFormat b)
    | sub_externalDatum₀ {a₁ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.externalDatum a a₁) (kBool.externalDatum b a₁)
    | sub_externalDatum₁ {a₀ a b} : kXReal.rw_one a b →
    kBool.rw_one (kBool.externalDatum a₀ a) (kBool.externalDatum a₀ b)
    | sub_validCode₀ {a₁ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.validCode a a₁) (kBool.validCode b a₁)
    | sub_validCode₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.validCode a₀ a) (kBool.validCode a₀ b)
    | sub_datum₀ {a₁ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.datum a a₁) (kBool.datum b a₁)
    | sub_datum₁ {a₀ a b} : kXReal.rw_one a b →
    kBool.rw_one (kBool.datum a₀ a) (kBool.datum a₀ b)
    | sub_candidateDatum₀ {a₁ a₂ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.candidateDatum a a₁ a₂) (kBool.candidateDatum b a₁ a₂)
    | sub_candidateDatum₁ {a₀ a₂ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.candidateDatum a₀ a a₂) (kBool.candidateDatum a₀ b a₂)
    | sub_candidateDatum₂ {a₀ a₁ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.candidateDatum a₀ a₁ a) (kBool.candidateDatum a₀ a₁ b)
    | sub_randomInRange₀ {a₁ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.randomInRange a a₁) (kBool.randomInRange b a₁)
    | sub_randomInRange₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.randomInRange a₀ a) (kBool.randomInRange a₀ b)
    | sub_validRound {a b} : kBlockRoundMode.rw_one a b →
    kBool.rw_one (kBool.validRound a) (kBool.validRound b)
    | sub_validProjection {a b} : kProjSpec.rw_one a b →
    kBool.rw_one (kBool.validProjection a) (kBool.validProjection b)
    | sub_validBlockProjection₀ {a₁ a b} : kBlockProjSpec.rw_one a b →
    kBool.rw_one (kBool.validBlockProjection a a₁) (kBool.validBlockProjection b a₁)
    | sub_validBlockProjection₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.validBlockProjection a₀ a) (kBool.validBlockProjection a₀ b)
    | sub_validRandoms₀ {a₁ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.validRandoms a a₁) (kBool.validRandoms b a₁)
    | sub_validRandoms₁ {a₀ a b} : kRandomSeq.rw_one a b →
    kBool.rw_one (kBool.validRandoms a₀ a) (kBool.validRandoms a₀ b)
    | sub_deterministic {a b} : kBlockRoundMode.rw_one a b →
    kBool.rw_one (kBool.deterministic a) (kBool.deterministic b)
    | sub_roundAway₀ {a₁ a₂ a₃ a b} : kBlockRoundMode.rw_one a b →
    kBool.rw_one (kBool.roundAway a a₁ a₂ a₃) (kBool.roundAway b a₁ a₂ a₃)
    | sub_roundAway₁ {a₀ a₂ a₃ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.roundAway a₀ a a₂ a₃) (kBool.roundAway a₀ b a₂ a₃)
    | sub_roundAway₂ {a₀ a₁ a₃ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.roundAway a₀ a₁ a a₃) (kBool.roundAway a₀ a₁ b a₃)
    | sub_roundAway₃ {a₀ a₁ a₂ a b} : kBool.rw_one a b →
    kBool.rw_one (kBool.roundAway a₀ a₁ a₂ a) (kBool.roundAway a₀ a₁ a₂ b)
    | sub_clipsHigh {a b} : kBlockRoundMode.rw_one a b →
    kBool.rw_one (kBool.clipsHigh a) (kBool.clipsHigh b)
    | sub_clipsLow {a b} : kBlockRoundMode.rw_one a b →
    kBool.rw_one (kBool.clipsLow a) (kBool.clipsLow b)
    | sub_validCodes₀ {a₁ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.validCodes a a₁) (kBool.validCodes b a₁)
    | sub_validCodes₁ {a₀ a b} : kCodeSeq.rw_one a b →
    kBool.rw_one (kBool.validCodes a₀ a) (kBool.validCodes a₀ b)
    | sub_validBlock₀ {a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.validBlock a a₁ a₂ a₃ a₄) (kBool.validBlock b a₁ a₂ a₃ a₄)
    | sub_validBlock₁ {a₀ a₂ a₃ a₄ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.validBlock a₀ a a₂ a₃ a₄) (kBool.validBlock a₀ b a₂ a₃ a₄)
    | sub_validBlock₂ {a₀ a₁ a₃ a₄ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.validBlock a₀ a₁ a a₃ a₄) (kBool.validBlock a₀ a₁ b a₃ a₄)
    | sub_validBlock₃ {a₀ a₁ a₂ a₄ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.validBlock a₀ a₁ a₂ a a₄) (kBool.validBlock a₀ a₁ a₂ b a₄)
    | sub_validBlock₄ {a₀ a₁ a₂ a₃ a b} : kCodeSeq.rw_one a b →
    kBool.rw_one (kBool.validBlock a₀ a₁ a₂ a₃ a) (kBool.validBlock a₀ a₁ a₂ a₃ b)
    | sub_lt₁₀ {a₁ a b} : MString.rw_one a b →
    kBool.rw_one (kBool.lt₁ a a₁) (kBool.lt₁ b a₁)
    | sub_lt₁₁ {a₀ a b} : MString.rw_one a b →
    kBool.rw_one (kBool.lt₁ a₀ a) (kBool.lt₁ a₀ b)
    | sub_lteq₁₀ {a₁ a b} : MString.rw_one a b →
    kBool.rw_one (kBool.lteq₁ a a₁) (kBool.lteq₁ b a₁)
    | sub_lteq₁₁ {a₀ a b} : MString.rw_one a b →
    kBool.rw_one (kBool.lteq₁ a₀ a) (kBool.lteq₁ a₀ b)
    | sub_gt₁₀ {a₁ a b} : MString.rw_one a b →
    kBool.rw_one (kBool.gt₁ a a₁) (kBool.gt₁ b a₁)
    | sub_gt₁₁ {a₀ a b} : MString.rw_one a b →
    kBool.rw_one (kBool.gt₁ a₀ a) (kBool.gt₁ a₀ b)
    | sub_gteq₁₀ {a₁ a b} : MString.rw_one a b →
    kBool.rw_one (kBool.gteq₁ a a₁) (kBool.gteq₁ b a₁)
    | sub_gteq₁₁ {a₀ a b} : MString.rw_one a b →
    kBool.rw_one (kBool.gteq₁ a₀ a) (kBool.gteq₁ a₀ b)
    | sub_CompareLess₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.CompareLess a a₁ a₂ a₃) (kBool.CompareLess b a₁ a₂ a₃)
    | sub_CompareLess₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.CompareLess a₀ a a₂ a₃) (kBool.CompareLess a₀ b a₂ a₃)
    | sub_CompareLess₂ {a₀ a₁ a₃ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.CompareLess a₀ a₁ a a₃) (kBool.CompareLess a₀ a₁ b a₃)
    | sub_CompareLess₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.CompareLess a₀ a₁ a₂ a) (kBool.CompareLess a₀ a₁ a₂ b)
    | sub_CompareLessEqual₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.CompareLessEqual a a₁ a₂ a₃) (kBool.CompareLessEqual b a₁ a₂ a₃)
    | sub_CompareLessEqual₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.CompareLessEqual a₀ a a₂ a₃) (kBool.CompareLessEqual a₀ b a₂ a₃)
    | sub_CompareLessEqual₂ {a₀ a₁ a₃ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.CompareLessEqual a₀ a₁ a a₃) (kBool.CompareLessEqual a₀ a₁ b a₃)
    | sub_CompareLessEqual₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.CompareLessEqual a₀ a₁ a₂ a) (kBool.CompareLessEqual a₀ a₁ a₂ b)
    | sub_CompareEqual₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.CompareEqual a a₁ a₂ a₃) (kBool.CompareEqual b a₁ a₂ a₃)
    | sub_CompareEqual₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.CompareEqual a₀ a a₂ a₃) (kBool.CompareEqual a₀ b a₂ a₃)
    | sub_CompareEqual₂ {a₀ a₁ a₃ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.CompareEqual a₀ a₁ a a₃) (kBool.CompareEqual a₀ a₁ b a₃)
    | sub_CompareEqual₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.CompareEqual a₀ a₁ a₂ a) (kBool.CompareEqual a₀ a₁ a₂ b)
    | sub_CompareGreaterEqual₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.CompareGreaterEqual a a₁ a₂ a₃) (kBool.CompareGreaterEqual b a₁ a₂ a₃)
    | sub_CompareGreaterEqual₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.CompareGreaterEqual a₀ a a₂ a₃) (kBool.CompareGreaterEqual a₀ b a₂ a₃)
    | sub_CompareGreaterEqual₂ {a₀ a₁ a₃ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.CompareGreaterEqual a₀ a₁ a a₃) (kBool.CompareGreaterEqual a₀ a₁ b a₃)
    | sub_CompareGreaterEqual₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.CompareGreaterEqual a₀ a₁ a₂ a) (kBool.CompareGreaterEqual a₀ a₁ a₂ b)
    | sub_CompareGreater₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.CompareGreater a a₁ a₂ a₃) (kBool.CompareGreater b a₁ a₂ a₃)
    | sub_CompareGreater₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.CompareGreater a₀ a a₂ a₃) (kBool.CompareGreater a₀ b a₂ a₃)
    | sub_CompareGreater₂ {a₀ a₁ a₃ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.CompareGreater a₀ a₁ a a₃) (kBool.CompareGreater a₀ a₁ b a₃)
    | sub_CompareGreater₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.CompareGreater a₀ a₁ a₂ a) (kBool.CompareGreater a₀ a₁ a₂ b)
    | sub_IsZero₀ {a₁ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.IsZero a a₁) (kBool.IsZero b a₁)
    | sub_IsZero₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.IsZero a₀ a) (kBool.IsZero a₀ b)
    | sub_IsOne₀ {a₁ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.IsOne a a₁) (kBool.IsOne b a₁)
    | sub_IsOne₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.IsOne a₀ a) (kBool.IsOne a₀ b)
    | sub_IsNaN₀ {a₁ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.IsNaN a a₁) (kBool.IsNaN b a₁)
    | sub_IsNaN₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.IsNaN a₀ a) (kBool.IsNaN a₀ b)
    | sub_IsInfinite₀ {a₁ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.IsInfinite a a₁) (kBool.IsInfinite b a₁)
    | sub_IsInfinite₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.IsInfinite a₀ a) (kBool.IsInfinite a₀ b)
    | sub_IsFinite₀ {a₁ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.IsFinite a a₁) (kBool.IsFinite b a₁)
    | sub_IsFinite₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.IsFinite a₀ a) (kBool.IsFinite a₀ b)
    | sub_IsSignMinus₀ {a₁ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.IsSignMinus a a₁) (kBool.IsSignMinus b a₁)
    | sub_IsSignMinus₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.IsSignMinus a₀ a) (kBool.IsSignMinus a₀ b)
    | sub_IsNormal₀ {a₁ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.IsNormal a a₁) (kBool.IsNormal b a₁)
    | sub_IsNormal₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.IsNormal a₀ a) (kBool.IsNormal a₀ b)
    | sub_IsSubnormal₀ {a₁ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.IsSubnormal a a₁) (kBool.IsSubnormal b a₁)
    | sub_IsSubnormal₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.IsSubnormal a₀ a) (kBool.IsSubnormal a₀ b)
    | sub_inF4 {a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.inF4 a) (kBool.inF4 b)
    | sub_inF8 {a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.inF8 a) (kBool.inF8 b)
    | sub_inFs {a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.inFs a) (kBool.inFs b)
    | sub_allowedExternal {a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.allowedExternal a) (kBool.allowedExternal b)
    | sub_containsFormat₀ {a₁ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.containsFormat a a₁) (kBool.containsFormat b a₁)
    | sub_containsFormat₁ {a₀ a b} : kFormatSeq.rw_one a b →
    kBool.rw_one (kBool.containsFormat a₀ a) (kBool.containsFormat a₀ b)
    | sub_validFX {a b} : kFormatSeq.rw_one a b →
    kBool.rw_one (kBool.validFX a) (kBool.validFX b)
    | sub_validFXTail {a b} : kFormatSeq.rw_one a b →
    kBool.rw_one (kBool.validFXTail a) (kBool.validFXTail b)
    | sub_allFormats {a b} : kFormatSeq.rw_one a b →
    kBool.rw_one (kBool.allFormats a) (kBool.allFormats b)
    | sub_required₀ {a₁ a b} : kSpecialization.rw_one a b →
    kBool.rw_one (kBool.required a a₁) (kBool.required b a₁)
    | sub_required₁ {a₀ a b} : kFormatSeq.rw_one a b →
    kBool.rw_one (kBool.required a₀ a) (kBool.required a₀ b)
    | sub_requiredNumeric₀ {a₁ a₂ a b} : MString.rw_one a b →
    kBool.rw_one (kBool.requiredNumeric a a₁ a₂) (kBool.requiredNumeric b a₁ a₂)
    | sub_requiredNumeric₁ {a₀ a₂ a b} : kFormatSeq.rw_one a b →
    kBool.rw_one (kBool.requiredNumeric a₀ a a₂) (kBool.requiredNumeric a₀ b a₂)
    | sub_requiredNumeric₂ {a₀ a₁ a b} : kFormatSeq.rw_one a b →
    kBool.rw_one (kBool.requiredNumeric a₀ a₁ a) (kBool.requiredNumeric a₀ a₁ b)
    | sub_requiredPlain₀ {a₁ a₂ a b} : MString.rw_one a b →
    kBool.rw_one (kBool.requiredPlain a a₁ a₂) (kBool.requiredPlain b a₁ a₂)
    | sub_requiredPlain₁ {a₀ a₂ a b} : kFormatSeq.rw_one a b →
    kBool.rw_one (kBool.requiredPlain a₀ a a₂) (kBool.requiredPlain a₀ b a₂)
    | sub_requiredPlain₂ {a₀ a₁ a b} : kFormatSeq.rw_one a b →
    kBool.rw_one (kBool.requiredPlain a₀ a₁ a) (kBool.requiredPlain a₀ a₁ b)
    | sub_minmaxName {a b} : MString.rw_one a b →
    kBool.rw_one (kBool.minmaxName a) (kBool.minmaxName b)
    | sub_compareName {a b} : MString.rw_one a b →
    kBool.rw_one (kBool.compareName a) (kBool.compareName b)
    | sub_predicateName {a b} : MString.rw_one a b →
    kBool.rw_one (kBool.predicateName a) (kBool.predicateName b)
    | sub_formatNameOp {a b} : MString.rw_one a b →
    kBool.rw_one (kBool.formatNameOp a) (kBool.formatNameOp b)
    | sub_numericPlainName {a b} : MString.rw_one a b →
    kBool.rw_one (kBool.numericPlainName a) (kBool.numericPlainName b)
    | sub_blockElementArity₀ {a₁ a b} : MString.rw_one a b →
    kBool.rw_one (kBool.blockElementArity a a₁) (kBool.blockElementArity b a₁)
    | sub_blockElementArity₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.blockElementArity a₀ a) (kBool.blockElementArity a₀ b)
    | sub_numericResult {a b} : kSpecialization.rw_one a b →
    kBool.rw_one (kBool.numericResult a) (kBool.numericResult b)
    | sub_hasDeclaration₀ {a₁ a b} : kSpecialization.rw_one a b →
    kBool.rw_one (kBool.hasDeclaration a a₁) (kBool.hasDeclaration b a₁)
    | sub_hasDeclaration₁ {a₀ a b} : kDeclarationSeq.rw_one a b →
    kBool.rw_one (kBool.hasDeclaration a₀ a) (kBool.hasDeclaration a₀ b)
    | sub_declarationsCover₀ {a₁ a b} : kSpecializationSeq.rw_one a b →
    kBool.rw_one (kBool.declarationsCover a a₁) (kBool.declarationsCover b a₁)
    | sub_declarationsCover₁ {a₀ a b} : kDeclarationSeq.rw_one a b →
    kBool.rw_one (kBool.declarationsCover a₀ a) (kBool.declarationsCover a₀ b)
    | sub_partition₀ {a₁ a b} : kCodeSeq.rw_one a b →
    kBool.rw_one (kBool.partition a a₁) (kBool.partition b a₁)
    | sub_partition₁ {a₀ a b} : kPartitionSeq.rw_one a b →
    kBool.rw_one (kBool.partition a₀ a) (kBool.partition a₀ b)
    | sub_partitionDisjoint {a b} : kPartitionSeq.rw_one a b →
    kBool.rw_one (kBool.partitionDisjoint a) (kBool.partitionDisjoint b)
    | sub_validSpecialization {a b} : kSpecialization.rw_one a b →
    kBool.rw_one (kBool.validSpecialization a) (kBool.validSpecialization b)
    | sub_numericArity₀ {a₁ a b} : MString.rw_one a b →
    kBool.rw_one (kBool.numericArity a a₁) (kBool.numericArity b a₁)
    | sub_numericArity₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.numericArity a₀ a) (kBool.numericArity a₀ b)
    | sub_plainArity₀ {a₁ a b} : MString.rw_one a b →
    kBool.rw_one (kBool.plainArity a a₁) (kBool.plainArity b a₁)
    | sub_plainArity₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.plainArity a₀ a) (kBool.plainArity a₀ b)
    | sub_wellFormedDeclaration {a b} : kDeclaration.rw_one a b →
    kBool.rw_one (kBool.wellFormedDeclaration a) (kBool.wellFormedDeclaration b)
    | sub_evidenceComplete {a b} : kEvidence.rw_one a b →
    kBool.rw_one (kBool.evidenceComplete a) (kBool.evidenceComplete b)
    | sub_memberCode₀ {a₁ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.memberCode a a₁) (kBool.memberCode b a₁)
    | sub_memberCode₁ {a₀ a b} : kCodeSeq.rw_one a b →
    kBool.rw_one (kBool.memberCode a₀ a) (kBool.memberCode a₀ b)
    | sub_disjointCodes₀ {a₁ a b} : kCodeSeq.rw_one a b →
    kBool.rw_one (kBool.disjointCodes a a₁) (kBool.disjointCodes b a₁)
    | sub_disjointCodes₁ {a₀ a b} : kCodeSeq.rw_one a b →
    kBool.rw_one (kBool.disjointCodes a₀ a) (kBool.disjointCodes a₀ b)
    | sub_uniqueCodes {a b} : kCodeSeq.rw_one a b →
    kBool.rw_one (kBool.uniqueCodes a) (kBool.uniqueCodes b)
    | sub_subsetCodes₀ {a₁ a b} : kCodeSeq.rw_one a b →
    kBool.rw_one (kBool.subsetCodes a a₁) (kBool.subsetCodes b a₁)
    | sub_subsetCodes₁ {a₀ a b} : kCodeSeq.rw_one a b →
    kBool.rw_one (kBool.subsetCodes a₀ a) (kBool.subsetCodes a₀ b)
    | sub_partition2₀ {a₁ a₂ a b} : kCodeSeq.rw_one a b →
    kBool.rw_one (kBool.partition2 a a₁ a₂) (kBool.partition2 b a₁ a₂)
    | sub_partition2₁ {a₀ a₂ a b} : kCodeSeq.rw_one a b →
    kBool.rw_one (kBool.partition2 a₀ a a₂) (kBool.partition2 a₀ b a₂)
    | sub_partition2₂ {a₀ a₁ a b} : kCodeSeq.rw_one a b →
    kBool.rw_one (kBool.partition2 a₀ a₁ a) (kBool.partition2 a₀ a₁ b)
    | sub_inArityTable₀ {a₁ a₂ a b} : MString.rw_one a b →
    kBool.rw_one (kBool.inArityTable a a₁ a₂) (kBool.inArityTable b a₁ a₂)
    | sub_inArityTable₁ {a₀ a₂ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.inArityTable a₀ a a₂) (kBool.inArityTable a₀ b a₂)
    | sub_inArityTable₂ {a₀ a₁ a b} : kArityTable.rw_one a b →
    kBool.rw_one (kBool.inArityTable a₀ a₁ a) (kBool.inArityTable a₀ a₁ b)
    | sub_TotalOrder₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.TotalOrder a a₁ a₂ a₃) (kBool.TotalOrder b a₁ a₂ a₃)
    | sub_TotalOrder₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.TotalOrder a₀ a a₂ a₃) (kBool.TotalOrder a₀ b a₂ a₃)
    | sub_TotalOrder₂ {a₀ a₁ a₃ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.TotalOrder a₀ a₁ a a₃) (kBool.TotalOrder a₀ a₁ b a₃)
    | sub_TotalOrder₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.TotalOrder a₀ a₁ a₂ a) (kBool.TotalOrder a₀ a₁ a₂ b)
    | sub_eqeq₀₀ {a₁ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.eqeq₀ a a₁) (kBool.eqeq₀ b a₁)
    | sub_eqeq₀₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.eqeq₀ a₀ a) (kBool.eqeq₀ a₀ b)
    | sub_ifthenelsefi₀ {a₁ a₂ a b} : kBool.rw_one a b →
    kBool.rw_one (kBool.ifthenelsefi a a₁ a₂) (kBool.ifthenelsefi b a₁ a₂)
    | sub_ifthenelsefi₁ {a₀ a₂ a b} : kBool.rw_one a b →
    kBool.rw_one (kBool.ifthenelsefi a₀ a a₂) (kBool.ifthenelsefi a₀ b a₂)
    | sub_ifthenelsefi₂ {a₀ a₁ a b} : kBool.rw_one a b →
    kBool.rw_one (kBool.ifthenelsefi a₀ a₁ a) (kBool.ifthenelsefi a₀ a₁ b)
    | sub_eqeq₁₀ {a₁ a b} : kSignedness.rw_one a b →
    kBool.rw_one (kBool.eqeq₁ a a₁) (kBool.eqeq₁ b a₁)
    | sub_eqeq₁₁ {a₀ a b} : kSignedness.rw_one a b →
    kBool.rw_one (kBool.eqeq₁ a₀ a) (kBool.eqeq₁ a₀ b)
    | sub_eqeq₂₀ {a₁ a b} : kDomain.rw_one a b →
    kBool.rw_one (kBool.eqeq₂ a a₁) (kBool.eqeq₂ b a₁)
    | sub_eqeq₂₁ {a₀ a b} : kDomain.rw_one a b →
    kBool.rw_one (kBool.eqeq₂ a₀ a) (kBool.eqeq₂ a₀ b)
    | sub_eqslasheq₀₀ {a₁ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.eqslasheq₀ a a₁) (kBool.eqslasheq₀ b a₁)
    | sub_eqslasheq₀₁ {a₀ a b} : MRat.rw_one a b →
    kBool.rw_one (kBool.eqslasheq₀ a₀ a) (kBool.eqslasheq₀ a₀ b)
    | sub_eqeq₃₀ {a₁ a b} : kBlockRoundMode.rw_one a b →
    kBool.rw_one (kBool.eqeq₃ a a₁) (kBool.eqeq₃ b a₁)
    | sub_eqeq₃₁ {a₀ a b} : kBlockRoundMode.rw_one a b →
    kBool.rw_one (kBool.eqeq₃ a₀ a) (kBool.eqeq₃ a₀ b)
    | sub_eqeq₄₀ {a₁ a b} : kBool.rw_one a b →
    kBool.rw_one (kBool.eqeq₄ a a₁) (kBool.eqeq₄ b a₁)
    | sub_eqeq₄₁ {a₀ a b} : kBool.rw_one a b →
    kBool.rw_one (kBool.eqeq₄ a₀ a) (kBool.eqeq₄ a₀ b)
    | sub_eqeq₅₀ {a₁ a b} : MString.rw_one a b →
    kBool.rw_one (kBool.eqeq₅ a a₁) (kBool.eqeq₅ b a₁)
    | sub_eqeq₅₁ {a₀ a b} : MString.rw_one a b →
    kBool.rw_one (kBool.eqeq₅ a₀ a) (kBool.eqeq₅ a₀ b)
    | sub_eqeq₆₀ {a₁ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.eqeq₆ a a₁) (kBool.eqeq₆ b a₁)
    | sub_eqeq₆₁ {a₀ a b} : kFormat.rw_one a b →
    kBool.rw_one (kBool.eqeq₆ a₀ a) (kBool.eqeq₆ a₀ b)
    | sub_eqeq₇₀ {a₁ a b} : kProjSpec.rw_one a b →
    kBool.rw_one (kBool.eqeq₇ a a₁) (kBool.eqeq₇ b a₁)
    | sub_eqeq₇₁ {a₀ a b} : kProjSpec.rw_one a b →
    kBool.rw_one (kBool.eqeq₇ a₀ a) (kBool.eqeq₇ a₀ b)
    | sub_eqslasheq₁₀ {a₁ a b} : kBool.rw_one a b →
    kBool.rw_one (kBool.eqslasheq₁ a a₁) (kBool.eqslasheq₁ b a₁)
    | sub_eqslasheq₁₁ {a₀ a b} : kBool.rw_one a b →
    kBool.rw_one (kBool.eqslasheq₁ a₀ a) (kBool.eqslasheq₁ a₀ b)
    | sub_eqslasheq₂₀ {a₁ a b} : MString.rw_one a b →
    kBool.rw_one (kBool.eqslasheq₂ a a₁) (kBool.eqslasheq₂ b a₁)
    | sub_eqslasheq₂₁ {a₀ a b} : MString.rw_one a b →
    kBool.rw_one (kBool.eqslasheq₂ a₀ a) (kBool.eqslasheq₂ a₀ b)
    | sub_eqeq₈₀ {a₁ a b} : kSpecialization.rw_one a b →
    kBool.rw_one (kBool.eqeq₈ a a₁) (kBool.eqeq₈ b a₁)
    | sub_eqeq₈₁ {a₀ a b} : kSpecialization.rw_one a b →
    kBool.rw_one (kBool.eqeq₈ a₀ a) (kBool.eqeq₈ a₀ b)

  inductive kXReal.rw_one: kXReal → kXReal → Prop
    | eqe_left {a b c : kXReal} : a.eqe b → kXReal.rw_one b c → kXReal.rw_one a c
    | eqe_right {a b c : kXReal} : kXReal.rw_one a b → b.eqe c → kXReal.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_fin {a b} : MRat.rw_one a b →
    kXReal.rw_one (kXReal.fin a) (kXReal.fin b)
    | sub_externalDecode₀ {a₁ a b} : kFormat.rw_one a b →
    kXReal.rw_one (kXReal.externalDecode a a₁) (kXReal.externalDecode b a₁)
    | sub_externalDecode₁ {a₀ a b} : MRat.rw_one a b →
    kXReal.rw_one (kXReal.externalDecode a₀ a) (kXReal.externalDecode a₀ b)
    | sub_decode₀ {a₁ a b} : kFormat.rw_one a b →
    kXReal.rw_one (kXReal.decode a a₁) (kXReal.decode b a₁)
    | sub_decode₁ {a₀ a b} : MRat.rw_one a b →
    kXReal.rw_one (kXReal.decode a₀ a) (kXReal.decode a₀ b)
    | sub_roundToPrecision₀ {a₁ a₂ a₃ a b} : MRat.rw_one a b →
    kXReal.rw_one (kXReal.roundToPrecision a a₁ a₂ a₃) (kXReal.roundToPrecision b a₁ a₂ a₃)
    | sub_roundToPrecision₁ {a₀ a₂ a₃ a b} : MRat.rw_one a b →
    kXReal.rw_one (kXReal.roundToPrecision a₀ a a₂ a₃) (kXReal.roundToPrecision a₀ b a₂ a₃)
    | sub_roundToPrecision₂ {a₀ a₁ a₃ a b} : kBlockRoundMode.rw_one a b →
    kXReal.rw_one (kXReal.roundToPrecision a₀ a₁ a a₃) (kXReal.roundToPrecision a₀ a₁ b a₃)
    | sub_roundToPrecision₃ {a₀ a₁ a₂ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.roundToPrecision a₀ a₁ a₂ a) (kXReal.roundToPrecision a₀ a₁ a₂ b)
    | sub_saturate₀ {a₁ a₂ a₃ a₄ a₅ a₆ a b} : MRat.rw_one a b →
    kXReal.rw_one (kXReal.saturate a a₁ a₂ a₃ a₄ a₅ a₆) (kXReal.saturate b a₁ a₂ a₃ a₄ a₅ a₆)
    | sub_saturate₁ {a₀ a₂ a₃ a₄ a₅ a₆ a b} : MRat.rw_one a b →
    kXReal.rw_one (kXReal.saturate a₀ a a₂ a₃ a₄ a₅ a₆) (kXReal.saturate a₀ b a₂ a₃ a₄ a₅ a₆)
    | sub_saturate₂ {a₀ a₁ a₃ a₄ a₅ a₆ a b} : kSatMode.rw_one a b →
    kXReal.rw_one (kXReal.saturate a₀ a₁ a a₃ a₄ a₅ a₆) (kXReal.saturate a₀ a₁ b a₃ a₄ a₅ a₆)
    | sub_saturate₃ {a₀ a₁ a₂ a₄ a₅ a₆ a b} : kBlockRoundMode.rw_one a b →
    kXReal.rw_one (kXReal.saturate a₀ a₁ a₂ a a₄ a₅ a₆) (kXReal.saturate a₀ a₁ a₂ b a₄ a₅ a₆)
    | sub_saturate₄ {a₀ a₁ a₂ a₃ a₅ a₆ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.saturate a₀ a₁ a₂ a₃ a a₅ a₆) (kXReal.saturate a₀ a₁ a₂ a₃ b a₅ a₆)
    | sub_saturate₅ {a₀ a₁ a₂ a₃ a₄ a₆ a b} : kSignedness.rw_one a b →
    kXReal.rw_one (kXReal.saturate a₀ a₁ a₂ a₃ a₄ a a₆) (kXReal.saturate a₀ a₁ a₂ a₃ a₄ b a₆)
    | sub_saturate₆ {a₀ a₁ a₂ a₃ a₄ a₅ a b} : kDomain.rw_one a b →
    kXReal.rw_one (kXReal.saturate a₀ a₁ a₂ a₃ a₄ a₅ a) (kXReal.saturate a₀ a₁ a₂ a₃ a₄ a₅ b)
    | sub_overflow₀ {a₁ a₂ a b} : kSignedness.rw_one a b →
    kXReal.rw_one (kXReal.overflow a a₁ a₂) (kXReal.overflow b a₁ a₂)
    | sub_overflow₁ {a₀ a₂ a b} : kDomain.rw_one a b →
    kXReal.rw_one (kXReal.overflow a₀ a a₂) (kXReal.overflow a₀ b a₂)
    | sub_overflow₂ {a₀ a₁ a b} : kBool.rw_one a b →
    kXReal.rw_one (kXReal.overflow a₀ a₁ a) (kXReal.overflow a₀ a₁ b)
    | sub_omegaConvert {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaConvert a) (kXReal.omegaConvert b)
    | sub_omegaAbs {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaAbs a) (kXReal.omegaAbs b)
    | sub_omegaNegate {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaNegate a) (kXReal.omegaNegate b)
    | sub_omegaRecip {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaRecip a) (kXReal.omegaRecip b)
    | sub_omegaCopySign₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaCopySign a a₁) (kXReal.omegaCopySign b a₁)
    | sub_omegaCopySign₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaCopySign a₀ a) (kXReal.omegaCopySign a₀ b)
    | sub_omegaAdd₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaAdd a a₁) (kXReal.omegaAdd b a₁)
    | sub_omegaAdd₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaAdd a₀ a) (kXReal.omegaAdd a₀ b)
    | sub_omegaSubtract₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaSubtract a a₁) (kXReal.omegaSubtract b a₁)
    | sub_omegaSubtract₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaSubtract a₀ a) (kXReal.omegaSubtract a₀ b)
    | sub_omegaMultiply₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMultiply a a₁) (kXReal.omegaMultiply b a₁)
    | sub_omegaMultiply₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMultiply a₀ a) (kXReal.omegaMultiply a₀ b)
    | sub_omegaDivide₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaDivide a a₁) (kXReal.omegaDivide b a₁)
    | sub_omegaDivide₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaDivide a₀ a) (kXReal.omegaDivide a₀ b)
    | sub_omegaFMA₀ {a₁ a₂ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaFMA a a₁ a₂) (kXReal.omegaFMA b a₁ a₂)
    | sub_omegaFMA₁ {a₀ a₂ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaFMA a₀ a a₂) (kXReal.omegaFMA a₀ b a₂)
    | sub_omegaFMA₂ {a₀ a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaFMA a₀ a₁ a) (kXReal.omegaFMA a₀ a₁ b)
    | sub_omegaFAA₀ {a₁ a₂ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaFAA a a₁ a₂) (kXReal.omegaFAA b a₁ a₂)
    | sub_omegaFAA₁ {a₀ a₂ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaFAA a₀ a a₂) (kXReal.omegaFAA a₀ b a₂)
    | sub_omegaFAA₂ {a₀ a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaFAA a₀ a₁ a) (kXReal.omegaFAA a₀ a₁ b)
    | sub_at₀ {a₁ a b} : kXSeq.rw_one a b →
    kXReal.rw_one (kXReal.«at» a a₁) (kXReal.«at» b a₁)
    | sub_at₁ {a₀ a b} : MRat.rw_one a b →
    kXReal.rw_one (kXReal.«at» a₀ a) (kXReal.«at» a₀ b)
    | sub_normalizeElement₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.normalizeElement a a₁) (kXReal.normalizeElement b a₁)
    | sub_normalizeElement₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.normalizeElement a₀ a) (kXReal.normalizeElement a₀ b)
    | sub_omegaMinimum₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMinimum a a₁) (kXReal.omegaMinimum b a₁)
    | sub_omegaMinimum₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMinimum a₀ a) (kXReal.omegaMinimum a₀ b)
    | sub_omegaMaximum₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMaximum a a₁) (kXReal.omegaMaximum b a₁)
    | sub_omegaMaximum₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMaximum a₀ a) (kXReal.omegaMaximum a₀ b)
    | sub_omegaMinimumNumber₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMinimumNumber a a₁) (kXReal.omegaMinimumNumber b a₁)
    | sub_omegaMinimumNumber₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMinimumNumber a₀ a) (kXReal.omegaMinimumNumber a₀ b)
    | sub_omegaMaximumNumber₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMaximumNumber a a₁) (kXReal.omegaMaximumNumber b a₁)
    | sub_omegaMaximumNumber₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMaximumNumber a₀ a) (kXReal.omegaMaximumNumber a₀ b)
    | sub_omegaMinimumMagnitude₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMinimumMagnitude a a₁) (kXReal.omegaMinimumMagnitude b a₁)
    | sub_omegaMinimumMagnitude₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMinimumMagnitude a₀ a) (kXReal.omegaMinimumMagnitude a₀ b)
    | sub_omegaMaximumMagnitude₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMaximumMagnitude a a₁) (kXReal.omegaMaximumMagnitude b a₁)
    | sub_omegaMaximumMagnitude₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMaximumMagnitude a₀ a) (kXReal.omegaMaximumMagnitude a₀ b)
    | sub_omegaMinimumMagnitudeNumber₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMinimumMagnitudeNumber a a₁) (kXReal.omegaMinimumMagnitudeNumber b a₁)
    | sub_omegaMinimumMagnitudeNumber₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMinimumMagnitudeNumber a₀ a) (kXReal.omegaMinimumMagnitudeNumber a₀ b)
    | sub_omegaMaximumMagnitudeNumber₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMaximumMagnitudeNumber a a₁) (kXReal.omegaMaximumMagnitudeNumber b a₁)
    | sub_omegaMaximumMagnitudeNumber₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMaximumMagnitudeNumber a₀ a) (kXReal.omegaMaximumMagnitudeNumber a₀ b)
    | sub_omegaMinimumFinite₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMinimumFinite a a₁) (kXReal.omegaMinimumFinite b a₁)
    | sub_omegaMinimumFinite₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMinimumFinite a₀ a) (kXReal.omegaMinimumFinite a₀ b)
    | sub_omegaMaximumFinite₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMaximumFinite a a₁) (kXReal.omegaMaximumFinite b a₁)
    | sub_omegaMaximumFinite₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaMaximumFinite a₀ a) (kXReal.omegaMaximumFinite a₀ b)
    | sub_omegaClamp₀ {a₁ a₂ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaClamp a a₁ a₂) (kXReal.omegaClamp b a₁ a₂)
    | sub_omegaClamp₁ {a₀ a₂ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaClamp a₀ a a₂) (kXReal.omegaClamp a₀ b a₂)
    | sub_omegaClamp₂ {a₀ a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaClamp a₀ a₁ a) (kXReal.omegaClamp a₀ a₁ b)
    | sub_foldAdd₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.foldAdd a a₁) (kXReal.foldAdd b a₁)
    | sub_foldAdd₁ {a₀ a b} : kXSeq.rw_one a b →
    kXReal.rw_one (kXReal.foldAdd a₀ a) (kXReal.foldAdd a₀ b)
    | sub_foldMultiply₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.foldMultiply a a₁) (kXReal.foldMultiply b a₁)
    | sub_foldMultiply₁ {a₀ a b} : kXSeq.rw_one a b →
    kXReal.rw_one (kXReal.foldMultiply a₀ a) (kXReal.foldMultiply a₀ b)
    | sub_foldMaximumFinite₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.foldMaximumFinite a a₁) (kXReal.foldMaximumFinite b a₁)
    | sub_foldMaximumFinite₁ {a₀ a b} : kXSeq.rw_one a b →
    kXReal.rw_one (kXReal.foldMaximumFinite a₀ a) (kXReal.foldMaximumFinite a₀ b)
    | sub_realAdd₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.realAdd a a₁) (kXReal.realAdd b a₁)
    | sub_realAdd₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.realAdd a₀ a) (kXReal.realAdd a₀ b)
    | sub_realMultiply₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.realMultiply a a₁) (kXReal.realMultiply b a₁)
    | sub_realMultiply₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.realMultiply a₀ a) (kXReal.realMultiply a₀ b)
    | sub_realNegate {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.realNegate a) (kXReal.realNegate b)
    | sub_realAbs {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.realAbs a) (kXReal.realAbs b)
    | sub_realDivide₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.realDivide a a₁) (kXReal.realDivide b a₁)
    | sub_realDivide₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.realDivide a₀ a) (kXReal.realDivide a₀ b)
    | sub_piMultiple {a b} : MRat.rw_one a b →
    kXReal.rw_one (kXReal.piMultiple a) (kXReal.piMultiple b)
    | sub_omegaHypot₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaHypot a a₁) (kXReal.omegaHypot b a₁)
    | sub_omegaHypot₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaHypot a₀ a) (kXReal.omegaHypot a₀ b)
    | sub_omegaArcTan2₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaArcTan2 a a₁) (kXReal.omegaArcTan2 b a₁)
    | sub_omegaArcTan2₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaArcTan2 a₀ a) (kXReal.omegaArcTan2 a₀ b)
    | sub_omegaArcTan2Pi₀ {a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaArcTan2Pi a a₁) (kXReal.omegaArcTan2Pi b a₁)
    | sub_omegaArcTan2Pi₁ {a₀ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaArcTan2Pi a₀ a) (kXReal.omegaArcTan2Pi a₀ b)
    | sub_omegaSqrt {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaSqrt a) (kXReal.omegaSqrt b)
    | sub_omegaRSqrt {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaRSqrt a) (kXReal.omegaRSqrt b)
    | sub_omegaExp {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaExp a) (kXReal.omegaExp b)
    | sub_omegaExp2 {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaExp2 a) (kXReal.omegaExp2 b)
    | sub_omegaLog {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaLog a) (kXReal.omegaLog b)
    | sub_omegaLog2 {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaLog2 a) (kXReal.omegaLog2 b)
    | sub_omegaLogOnePlus {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaLogOnePlus a) (kXReal.omegaLogOnePlus b)
    | sub_omegaExpMinusOne {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaExpMinusOne a) (kXReal.omegaExpMinusOne b)
    | sub_omegaSin {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaSin a) (kXReal.omegaSin b)
    | sub_omegaCos {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaCos a) (kXReal.omegaCos b)
    | sub_omegaTan {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaTan a) (kXReal.omegaTan b)
    | sub_omegaArcSin {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaArcSin a) (kXReal.omegaArcSin b)
    | sub_omegaArcCos {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaArcCos a) (kXReal.omegaArcCos b)
    | sub_omegaArcTan {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaArcTan a) (kXReal.omegaArcTan b)
    | sub_omegaSinh {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaSinh a) (kXReal.omegaSinh b)
    | sub_omegaCosh {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaCosh a) (kXReal.omegaCosh b)
    | sub_omegaTanh {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaTanh a) (kXReal.omegaTanh b)
    | sub_omegaArcSinh {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaArcSinh a) (kXReal.omegaArcSinh b)
    | sub_omegaArcCosh {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaArcCosh a) (kXReal.omegaArcCosh b)
    | sub_omegaArcTanh {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaArcTanh a) (kXReal.omegaArcTanh b)
    | sub_omegaSinPi {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaSinPi a) (kXReal.omegaSinPi b)
    | sub_omegaCosPi {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaCosPi a) (kXReal.omegaCosPi b)
    | sub_omegaTanPi {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaTanPi a) (kXReal.omegaTanPi b)
    | sub_omegaArcSinPi {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaArcSinPi a) (kXReal.omegaArcSinPi b)
    | sub_omegaArcCosPi {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaArcCosPi a) (kXReal.omegaArcCosPi b)
    | sub_omegaArcTanPi {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaArcTanPi a) (kXReal.omegaArcTanPi b)
    | sub_omegaSoftplus {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.omegaSoftplus a) (kXReal.omegaSoftplus b)
    | sub_exprSqrt {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.exprSqrt a) (kXReal.exprSqrt b)
    | sub_exprExp {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.exprExp a) (kXReal.exprExp b)
    | sub_exprExp2 {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.exprExp2 a) (kXReal.exprExp2 b)
    | sub_exprLog {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.exprLog a) (kXReal.exprLog b)
    | sub_exprLog2 {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.exprLog2 a) (kXReal.exprLog2 b)
    | sub_exprSin {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.exprSin a) (kXReal.exprSin b)
    | sub_exprCos {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.exprCos a) (kXReal.exprCos b)
    | sub_exprTan {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.exprTan a) (kXReal.exprTan b)
    | sub_exprArcSin {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.exprArcSin a) (kXReal.exprArcSin b)
    | sub_exprArcCos {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.exprArcCos a) (kXReal.exprArcCos b)
    | sub_exprArcTan {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.exprArcTan a) (kXReal.exprArcTan b)
    | sub_exprSinh {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.exprSinh a) (kXReal.exprSinh b)
    | sub_exprCosh {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.exprCosh a) (kXReal.exprCosh b)
    | sub_exprTanh {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.exprTanh a) (kXReal.exprTanh b)
    | sub_exprArcSinh {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.exprArcSinh a) (kXReal.exprArcSinh b)
    | sub_exprArcCosh {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.exprArcCosh a) (kXReal.exprArcCosh b)
    | sub_exprArcTanh {a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.exprArcTanh a) (kXReal.exprArcTanh b)
    | sub_ifthenelsefi₀ {a₁ a₂ a b} : kBool.rw_one a b →
    kXReal.rw_one (kXReal.ifthenelsefi a a₁ a₂) (kXReal.ifthenelsefi b a₁ a₂)
    | sub_ifthenelsefi₁ {a₀ a₂ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.ifthenelsefi a₀ a a₂) (kXReal.ifthenelsefi a₀ b a₂)
    | sub_ifthenelsefi₂ {a₀ a₁ a b} : kXReal.rw_one a b →
    kXReal.rw_one (kXReal.ifthenelsefi a₀ a₁ a) (kXReal.ifthenelsefi a₀ a₁ b)

  inductive kFormat.rw_one: kFormat → kFormat → Prop
    | eqe_left {a b c : kFormat} : a.eqe b → kFormat.rw_one b c → kFormat.rw_one a c
    | eqe_right {a b c : kFormat} : kFormat.rw_one a b → b.eqe c → kFormat.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_Binary₀ {a₁ a₂ a₃ a b} : MRat.rw_one a b →
    kFormat.rw_one (kFormat.Binary a a₁ a₂ a₃) (kFormat.Binary b a₁ a₂ a₃)
    | sub_Binary₁ {a₀ a₂ a₃ a b} : MRat.rw_one a b →
    kFormat.rw_one (kFormat.Binary a₀ a a₂ a₃) (kFormat.Binary a₀ b a₂ a₃)
    | sub_Binary₂ {a₀ a₁ a₃ a b} : kSignedness.rw_one a b →
    kFormat.rw_one (kFormat.Binary a₀ a₁ a a₃) (kFormat.Binary a₀ a₁ b a₃)
    | sub_Binary₃ {a₀ a₁ a₂ a b} : kDomain.rw_one a b →
    kFormat.rw_one (kFormat.Binary a₀ a₁ a₂ a) (kFormat.Binary a₀ a₁ a₂ b)
    | sub_at₀ {a₁ a b} : kFormatSeq.rw_one a b →
    kFormat.rw_one (kFormat.«at» a a₁) (kFormat.«at» b a₁)
    | sub_at₁ {a₀ a b} : MRat.rw_one a b →
    kFormat.rw_one (kFormat.«at» a₀ a) (kFormat.«at» a₀ b)

  inductive kSignedness.rw_one: kSignedness → kSignedness → Prop
    | eqe_left {a b c : kSignedness} : a.eqe b → kSignedness.rw_one b c → kSignedness.rw_one a c
    | eqe_right {a b c : kSignedness} : kSignedness.rw_one a b → b.eqe c → kSignedness.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_SignednessOf {a b} : kFormat.rw_one a b →
    kSignedness.rw_one (kSignedness.SignednessOf a) (kSignedness.SignednessOf b)

  inductive kDomain.rw_one: kDomain → kDomain → Prop
    | eqe_left {a b c : kDomain} : a.eqe b → kDomain.rw_one b c → kDomain.rw_one a c
    | eqe_right {a b c : kDomain} : kDomain.rw_one a b → b.eqe c → kDomain.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_DomainOf {a b} : kFormat.rw_one a b →
    kDomain.rw_one (kDomain.DomainOf a) (kDomain.DomainOf b)

  inductive kBoundQuery.rw_one: kBoundQuery → kBoundQuery → Prop
    | eqe_left {a b c : kBoundQuery} : a.eqe b → kBoundQuery.rw_one b c → kBoundQuery.rw_one a c
    | eqe_right {a b c : kBoundQuery} : kBoundQuery.rw_one a b → b.eqe c → kBoundQuery.rw_one a c
    -- Axioms for rewriting inside subterms

  inductive kRandomSeq.rw_one: kRandomSeq → kRandomSeq → Prop
    | eqe_left {a b c : kRandomSeq} : a.eqe b → kRandomSeq.rw_one b c → kRandomSeq.rw_one a c
    | eqe_right {a b c : kRandomSeq} : kRandomSeq.rw_one a b → b.eqe c → kRandomSeq.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_rcons₀ {a₁ a b} : MRat.rw_one a b →
    kRandomSeq.rw_one (kRandomSeq.rcons a a₁) (kRandomSeq.rcons b a₁)
    | sub_rcons₁ {a₀ a b} : kRandomSeq.rw_one a b →
    kRandomSeq.rw_one (kRandomSeq.rcons a₀ a) (kRandomSeq.rcons a₀ b)

  inductive kBlockRoundMode.rw_one: kBlockRoundMode → kBlockRoundMode → Prop
    | eqe_left {a b c : kBlockRoundMode} : a.eqe b → kBlockRoundMode.rw_one b c → kBlockRoundMode.rw_one a c
    | eqe_right {a b c : kBlockRoundMode} : kBlockRoundMode.rw_one a b → b.eqe c → kBlockRoundMode.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_StochasticA₀ {a₁ a b} : MRat.rw_one a b →
    kBlockRoundMode.rw_one (kBlockRoundMode.StochasticA a a₁) (kBlockRoundMode.StochasticA b a₁)
    | sub_StochasticA₁ {a₀ a b} : MRat.rw_one a b →
    kBlockRoundMode.rw_one (kBlockRoundMode.StochasticA a₀ a) (kBlockRoundMode.StochasticA a₀ b)
    | sub_StochasticB₀ {a₁ a b} : MRat.rw_one a b →
    kBlockRoundMode.rw_one (kBlockRoundMode.StochasticB a a₁) (kBlockRoundMode.StochasticB b a₁)
    | sub_StochasticB₁ {a₀ a b} : MRat.rw_one a b →
    kBlockRoundMode.rw_one (kBlockRoundMode.StochasticB a₀ a) (kBlockRoundMode.StochasticB a₀ b)
    | sub_StochasticC₀ {a₁ a b} : MRat.rw_one a b →
    kBlockRoundMode.rw_one (kBlockRoundMode.StochasticC a a₁) (kBlockRoundMode.StochasticC b a₁)
    | sub_StochasticC₁ {a₀ a b} : MRat.rw_one a b →
    kBlockRoundMode.rw_one (kBlockRoundMode.StochasticC a₀ a) (kBlockRoundMode.StochasticC a₀ b)
    | sub_BlockStochasticA₀ {a₁ a b} : MRat.rw_one a b →
    kBlockRoundMode.rw_one (kBlockRoundMode.BlockStochasticA a a₁) (kBlockRoundMode.BlockStochasticA b a₁)
    | sub_BlockStochasticA₁ {a₀ a b} : kRandomSeq.rw_one a b →
    kBlockRoundMode.rw_one (kBlockRoundMode.BlockStochasticA a₀ a) (kBlockRoundMode.BlockStochasticA a₀ b)
    | sub_BlockStochasticB₀ {a₁ a b} : MRat.rw_one a b →
    kBlockRoundMode.rw_one (kBlockRoundMode.BlockStochasticB a a₁) (kBlockRoundMode.BlockStochasticB b a₁)
    | sub_BlockStochasticB₁ {a₀ a b} : kRandomSeq.rw_one a b →
    kBlockRoundMode.rw_one (kBlockRoundMode.BlockStochasticB a₀ a) (kBlockRoundMode.BlockStochasticB a₀ b)
    | sub_BlockStochasticC₀ {a₁ a b} : MRat.rw_one a b →
    kBlockRoundMode.rw_one (kBlockRoundMode.BlockStochasticC a a₁) (kBlockRoundMode.BlockStochasticC b a₁)
    | sub_BlockStochasticC₁ {a₀ a b} : kRandomSeq.rw_one a b →
    kBlockRoundMode.rw_one (kBlockRoundMode.BlockStochasticC a₀ a) (kBlockRoundMode.BlockStochasticC a₀ b)
    | sub_RoundOf {a b} : kProjSpec.rw_one a b →
    kBlockRoundMode.rw_one (kBlockRoundMode.RoundOf a) (kBlockRoundMode.RoundOf b)

  inductive kSatMode.rw_one: kSatMode → kSatMode → Prop
    | eqe_left {a b c : kSatMode} : a.eqe b → kSatMode.rw_one b c → kSatMode.rw_one a c
    | eqe_right {a b c : kSatMode} : kSatMode.rw_one a b → b.eqe c → kSatMode.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_SatOf {a b} : kProjSpec.rw_one a b →
    kSatMode.rw_one (kSatMode.SatOf a) (kSatMode.SatOf b)

  inductive kProjSpec.rw_one: kProjSpec → kProjSpec → Prop
    | eqe_left {a b c : kProjSpec} : a.eqe b → kProjSpec.rw_one b c → kProjSpec.rw_one a c
    | eqe_right {a b c : kProjSpec} : kProjSpec.rw_one a b → b.eqe c → kProjSpec.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_proj₀ {a₁ a b} : kBlockRoundMode.rw_one a b →
    kProjSpec.rw_one (kProjSpec.proj a a₁) (kProjSpec.proj b a₁)
    | sub_proj₁ {a₀ a b} : kSatMode.rw_one a b →
    kProjSpec.rw_one (kProjSpec.proj a₀ a) (kProjSpec.proj a₀ b)
    | sub_projectionAt₀ {a₁ a b} : kBlockProjSpec.rw_one a b →
    kProjSpec.rw_one (kProjSpec.projectionAt a a₁) (kProjSpec.projectionAt b a₁)
    | sub_projectionAt₁ {a₀ a b} : MRat.rw_one a b →
    kProjSpec.rw_one (kProjSpec.projectionAt a₀ a) (kProjSpec.projectionAt a₀ b)

  inductive kBlockProjSpec.rw_one: kBlockProjSpec → kBlockProjSpec → Prop
    | eqe_left {a b c : kBlockProjSpec} : a.eqe b → kBlockProjSpec.rw_one b c → kBlockProjSpec.rw_one a c
    | eqe_right {a b c : kBlockProjSpec} : kBlockProjSpec.rw_one a b → b.eqe c → kBlockProjSpec.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_bproj₀ {a₁ a b} : kBlockRoundMode.rw_one a b →
    kBlockProjSpec.rw_one (kBlockProjSpec.bproj a a₁) (kBlockProjSpec.bproj b a₁)
    | sub_bproj₁ {a₀ a b} : kSatMode.rw_one a b →
    kBlockProjSpec.rw_one (kBlockProjSpec.bproj a₀ a) (kBlockProjSpec.bproj a₀ b)
    | sub_singletonLift {a b} : kProjSpec.rw_one a b →
    kBlockProjSpec.rw_one (kBlockProjSpec.singletonLift a) (kBlockProjSpec.singletonLift b)

  inductive kXSeq.rw_one: kXSeq → kXSeq → Prop
    | eqe_left {a b c : kXSeq} : a.eqe b → kXSeq.rw_one b c → kXSeq.rw_one a c
    | eqe_right {a b c : kXSeq} : kXSeq.rw_one a b → b.eqe c → kXSeq.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_xcons₀ {a₁ a b} : kXReal.rw_one a b →
    kXSeq.rw_one (kXSeq.xcons a a₁) (kXSeq.xcons b a₁)
    | sub_xcons₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.xcons a₀ a) (kXSeq.xcons a₀ b)
    | sub_decodeElements₀ {a₁ a b} : kFormat.rw_one a b →
    kXSeq.rw_one (kXSeq.decodeElements a a₁) (kXSeq.decodeElements b a₁)
    | sub_decodeElements₁ {a₀ a b} : kCodeSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.decodeElements a₀ a) (kXSeq.decodeElements a₀ b)
    | sub_multiplyElements₀ {a₁ a b} : kXReal.rw_one a b →
    kXSeq.rw_one (kXSeq.multiplyElements a a₁) (kXSeq.multiplyElements b a₁)
    | sub_multiplyElements₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.multiplyElements a₀ a) (kXSeq.multiplyElements a₀ b)
    | sub_blockDecode₀ {a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    kXSeq.rw_one (kXSeq.blockDecode a a₁ a₂ a₃ a₄) (kXSeq.blockDecode b a₁ a₂ a₃ a₄)
    | sub_blockDecode₁ {a₀ a₂ a₃ a₄ a b} : kFormat.rw_one a b →
    kXSeq.rw_one (kXSeq.blockDecode a₀ a a₂ a₃ a₄) (kXSeq.blockDecode a₀ b a₂ a₃ a₄)
    | sub_blockDecode₂ {a₀ a₁ a₃ a₄ a b} : kFormat.rw_one a b →
    kXSeq.rw_one (kXSeq.blockDecode a₀ a₁ a a₃ a₄) (kXSeq.blockDecode a₀ a₁ b a₃ a₄)
    | sub_blockDecode₃ {a₀ a₁ a₂ a₄ a b} : MRat.rw_one a b →
    kXSeq.rw_one (kXSeq.blockDecode a₀ a₁ a₂ a a₄) (kXSeq.blockDecode a₀ a₁ a₂ b a₄)
    | sub_blockDecode₄ {a₀ a₁ a₂ a₃ a b} : kCodeSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.blockDecode a₀ a₁ a₂ a₃ a) (kXSeq.blockDecode a₀ a₁ a₂ a₃ b)
    | sub_absElements {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.absElements a) (kXSeq.absElements b)
    | sub_pairProducts₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.pairProducts a a₁) (kXSeq.pairProducts b a₁)
    | sub_pairProducts₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.pairProducts a₀ a) (kXSeq.pairProducts a₀ b)
    | sub_mapConvert {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapConvert a) (kXSeq.mapConvert b)
    | sub_mapAbs {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapAbs a) (kXSeq.mapAbs b)
    | sub_mapNegate {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapNegate a) (kXSeq.mapNegate b)
    | sub_mapCopySign₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapCopySign a a₁) (kXSeq.mapCopySign b a₁)
    | sub_mapCopySign₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapCopySign a₀ a) (kXSeq.mapCopySign a₀ b)
    | sub_mapAdd₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapAdd a a₁) (kXSeq.mapAdd b a₁)
    | sub_mapAdd₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapAdd a₀ a) (kXSeq.mapAdd a₀ b)
    | sub_mapSubtract₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapSubtract a a₁) (kXSeq.mapSubtract b a₁)
    | sub_mapSubtract₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapSubtract a₀ a) (kXSeq.mapSubtract a₀ b)
    | sub_mapMultiply₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMultiply a a₁) (kXSeq.mapMultiply b a₁)
    | sub_mapMultiply₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMultiply a₀ a) (kXSeq.mapMultiply a₀ b)
    | sub_mapDivide₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapDivide a a₁) (kXSeq.mapDivide b a₁)
    | sub_mapDivide₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapDivide a₀ a) (kXSeq.mapDivide a₀ b)
    | sub_mapFMA₀ {a₁ a₂ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapFMA a a₁ a₂) (kXSeq.mapFMA b a₁ a₂)
    | sub_mapFMA₁ {a₀ a₂ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapFMA a₀ a a₂) (kXSeq.mapFMA a₀ b a₂)
    | sub_mapFMA₂ {a₀ a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapFMA a₀ a₁ a) (kXSeq.mapFMA a₀ a₁ b)
    | sub_mapFAA₀ {a₁ a₂ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapFAA a a₁ a₂) (kXSeq.mapFAA b a₁ a₂)
    | sub_mapFAA₁ {a₀ a₂ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapFAA a₀ a a₂) (kXSeq.mapFAA a₀ b a₂)
    | sub_mapFAA₂ {a₀ a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapFAA a₀ a₁ a) (kXSeq.mapFAA a₀ a₁ b)
    | sub_mapRecip {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapRecip a) (kXSeq.mapRecip b)
    | sub_mapMinimum₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMinimum a a₁) (kXSeq.mapMinimum b a₁)
    | sub_mapMinimum₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMinimum a₀ a) (kXSeq.mapMinimum a₀ b)
    | sub_mapMaximum₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMaximum a a₁) (kXSeq.mapMaximum b a₁)
    | sub_mapMaximum₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMaximum a₀ a) (kXSeq.mapMaximum a₀ b)
    | sub_mapMinimumNumber₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMinimumNumber a a₁) (kXSeq.mapMinimumNumber b a₁)
    | sub_mapMinimumNumber₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMinimumNumber a₀ a) (kXSeq.mapMinimumNumber a₀ b)
    | sub_mapMaximumNumber₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMaximumNumber a a₁) (kXSeq.mapMaximumNumber b a₁)
    | sub_mapMaximumNumber₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMaximumNumber a₀ a) (kXSeq.mapMaximumNumber a₀ b)
    | sub_mapMinimumMagnitude₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMinimumMagnitude a a₁) (kXSeq.mapMinimumMagnitude b a₁)
    | sub_mapMinimumMagnitude₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMinimumMagnitude a₀ a) (kXSeq.mapMinimumMagnitude a₀ b)
    | sub_mapMaximumMagnitude₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMaximumMagnitude a a₁) (kXSeq.mapMaximumMagnitude b a₁)
    | sub_mapMaximumMagnitude₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMaximumMagnitude a₀ a) (kXSeq.mapMaximumMagnitude a₀ b)
    | sub_mapMinimumMagnitudeNumber₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMinimumMagnitudeNumber a a₁) (kXSeq.mapMinimumMagnitudeNumber b a₁)
    | sub_mapMinimumMagnitudeNumber₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMinimumMagnitudeNumber a₀ a) (kXSeq.mapMinimumMagnitudeNumber a₀ b)
    | sub_mapMaximumMagnitudeNumber₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMaximumMagnitudeNumber a a₁) (kXSeq.mapMaximumMagnitudeNumber b a₁)
    | sub_mapMaximumMagnitudeNumber₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMaximumMagnitudeNumber a₀ a) (kXSeq.mapMaximumMagnitudeNumber a₀ b)
    | sub_mapMinimumFinite₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMinimumFinite a a₁) (kXSeq.mapMinimumFinite b a₁)
    | sub_mapMinimumFinite₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMinimumFinite a₀ a) (kXSeq.mapMinimumFinite a₀ b)
    | sub_mapMaximumFinite₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMaximumFinite a a₁) (kXSeq.mapMaximumFinite b a₁)
    | sub_mapMaximumFinite₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapMaximumFinite a₀ a) (kXSeq.mapMaximumFinite a₀ b)
    | sub_mapClamp₀ {a₁ a₂ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapClamp a a₁ a₂) (kXSeq.mapClamp b a₁ a₂)
    | sub_mapClamp₁ {a₀ a₂ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapClamp a₀ a a₂) (kXSeq.mapClamp a₀ b a₂)
    | sub_mapClamp₂ {a₀ a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapClamp a₀ a₁ a) (kXSeq.mapClamp a₀ a₁ b)
    | sub_mapSqrt {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapSqrt a) (kXSeq.mapSqrt b)
    | sub_mapRSqrt {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapRSqrt a) (kXSeq.mapRSqrt b)
    | sub_mapExp {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapExp a) (kXSeq.mapExp b)
    | sub_mapExp2 {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapExp2 a) (kXSeq.mapExp2 b)
    | sub_mapLog {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapLog a) (kXSeq.mapLog b)
    | sub_mapLog2 {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapLog2 a) (kXSeq.mapLog2 b)
    | sub_mapLogOnePlus {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapLogOnePlus a) (kXSeq.mapLogOnePlus b)
    | sub_mapExpMinusOne {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapExpMinusOne a) (kXSeq.mapExpMinusOne b)
    | sub_mapSin {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapSin a) (kXSeq.mapSin b)
    | sub_mapCos {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapCos a) (kXSeq.mapCos b)
    | sub_mapTan {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapTan a) (kXSeq.mapTan b)
    | sub_mapArcSin {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapArcSin a) (kXSeq.mapArcSin b)
    | sub_mapArcCos {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapArcCos a) (kXSeq.mapArcCos b)
    | sub_mapArcTan {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapArcTan a) (kXSeq.mapArcTan b)
    | sub_mapSinh {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapSinh a) (kXSeq.mapSinh b)
    | sub_mapCosh {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapCosh a) (kXSeq.mapCosh b)
    | sub_mapTanh {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapTanh a) (kXSeq.mapTanh b)
    | sub_mapArcSinh {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapArcSinh a) (kXSeq.mapArcSinh b)
    | sub_mapArcCosh {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapArcCosh a) (kXSeq.mapArcCosh b)
    | sub_mapArcTanh {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapArcTanh a) (kXSeq.mapArcTanh b)
    | sub_mapSinPi {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapSinPi a) (kXSeq.mapSinPi b)
    | sub_mapCosPi {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapCosPi a) (kXSeq.mapCosPi b)
    | sub_mapTanPi {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapTanPi a) (kXSeq.mapTanPi b)
    | sub_mapArcSinPi {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapArcSinPi a) (kXSeq.mapArcSinPi b)
    | sub_mapArcCosPi {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapArcCosPi a) (kXSeq.mapArcCosPi b)
    | sub_mapArcTanPi {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapArcTanPi a) (kXSeq.mapArcTanPi b)
    | sub_mapSoftplus {a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapSoftplus a) (kXSeq.mapSoftplus b)
    | sub_mapHypot₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapHypot a a₁) (kXSeq.mapHypot b a₁)
    | sub_mapHypot₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapHypot a₀ a) (kXSeq.mapHypot a₀ b)
    | sub_mapArcTan2₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapArcTan2 a a₁) (kXSeq.mapArcTan2 b a₁)
    | sub_mapArcTan2₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapArcTan2 a₀ a) (kXSeq.mapArcTan2 a₀ b)
    | sub_mapArcTan2Pi₀ {a₁ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapArcTan2Pi a a₁) (kXSeq.mapArcTan2Pi b a₁)
    | sub_mapArcTan2Pi₁ {a₀ a b} : kXSeq.rw_one a b →
    kXSeq.rw_one (kXSeq.mapArcTan2Pi a₀ a) (kXSeq.mapArcTan2Pi a₀ b)

  inductive kCodeSeq.rw_one: kCodeSeq → kCodeSeq → Prop
    | eqe_left {a b c : kCodeSeq} : a.eqe b → kCodeSeq.rw_one b c → kCodeSeq.rw_one a c
    | eqe_right {a b c : kCodeSeq} : kCodeSeq.rw_one a b → b.eqe c → kCodeSeq.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_ccons₀ {a₁ a b} : MRat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.ccons a a₁) (kCodeSeq.ccons b a₁)
    | sub_ccons₁ {a₀ a b} : kCodeSeq.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.ccons a₀ a) (kCodeSeq.ccons a₀ b)
    | sub_blockProject₀ {a₁ a₂ a₃ a₄ a₅ a b} : MRat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.blockProject a a₁ a₂ a₃ a₄ a₅) (kCodeSeq.blockProject b a₁ a₂ a₃ a₄ a₅)
    | sub_blockProject₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.blockProject a₀ a a₂ a₃ a₄ a₅) (kCodeSeq.blockProject a₀ b a₂ a₃ a₄ a₅)
    | sub_blockProject₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.blockProject a₀ a₁ a a₃ a₄ a₅) (kCodeSeq.blockProject a₀ a₁ b a₃ a₄ a₅)
    | sub_blockProject₃ {a₀ a₁ a₂ a₄ a₅ a b} : kBlockProjSpec.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.blockProject a₀ a₁ a₂ a a₄ a₅) (kCodeSeq.blockProject a₀ a₁ a₂ b a₄ a₅)
    | sub_blockProject₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.blockProject a₀ a₁ a₂ a₃ a a₅) (kCodeSeq.blockProject a₀ a₁ a₂ a₃ b a₅)
    | sub_blockProject₅ {a₀ a₁ a₂ a₃ a₄ a b} : kXSeq.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.blockProject a₀ a₁ a₂ a₃ a₄ a) (kCodeSeq.blockProject a₀ a₁ a₂ a₃ a₄ b)
    | sub_projectElements₀ {a₁ a₂ a₃ a₄ a b} : kFormat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.projectElements a a₁ a₂ a₃ a₄) (kCodeSeq.projectElements b a₁ a₂ a₃ a₄)
    | sub_projectElements₁ {a₀ a₂ a₃ a₄ a b} : kBlockProjSpec.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.projectElements a₀ a a₂ a₃ a₄) (kCodeSeq.projectElements a₀ b a₂ a₃ a₄)
    | sub_projectElements₂ {a₀ a₁ a₃ a₄ a b} : kXReal.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.projectElements a₀ a₁ a a₃ a₄) (kCodeSeq.projectElements a₀ a₁ b a₃ a₄)
    | sub_projectElements₃ {a₀ a₁ a₂ a₄ a b} : kXSeq.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.projectElements a₀ a₁ a₂ a a₄) (kCodeSeq.projectElements a₀ a₁ a₂ b a₄)
    | sub_projectElements₄ {a₀ a₁ a₂ a₃ a b} : MRat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.projectElements a₀ a₁ a₂ a₃ a) (kCodeSeq.projectElements a₀ a₁ a₂ a₃ b)
    | sub_projectUnscaled₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.projectUnscaled a a₁ a₂ a₃) (kCodeSeq.projectUnscaled b a₁ a₂ a₃)
    | sub_projectUnscaled₁ {a₀ a₂ a₃ a b} : kBlockProjSpec.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.projectUnscaled a₀ a a₂ a₃) (kCodeSeq.projectUnscaled a₀ b a₂ a₃)
    | sub_projectUnscaled₂ {a₀ a₁ a₃ a b} : kXSeq.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.projectUnscaled a₀ a₁ a a₃) (kCodeSeq.projectUnscaled a₀ a₁ b a₃)
    | sub_projectUnscaled₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.projectUnscaled a₀ a₁ a₂ a) (kCodeSeq.projectUnscaled a₀ a₁ a₂ b)
    | sub_at₀ {a₁ a b} : kPartitionSeq.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.«at» a a₁) (kCodeSeq.«at» b a₁)
    | sub_at₁ {a₀ a b} : MRat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.«at» a₀ a) (kCodeSeq.«at» a₀ b)
    | sub_partitionUnion {a b} : kPartitionSeq.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.partitionUnion a) (kCodeSeq.partitionUnion b)
    | sub_appendCodes₀ {a₁ a b} : kCodeSeq.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.appendCodes a a₁) (kCodeSeq.appendCodes b a₁)
    | sub_appendCodes₁ {a₀ a b} : kCodeSeq.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.appendCodes a₀ a) (kCodeSeq.appendCodes a₀ b)
    | sub_ConvertFromBlock₀ {a₁ a₂ a₃ a₄ a₅ a₆ a b} : MRat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.ConvertFromBlock a a₁ a₂ a₃ a₄ a₅ a₆) (kCodeSeq.ConvertFromBlock b a₁ a₂ a₃ a₄ a₅ a₆)
    | sub_ConvertFromBlock₁ {a₀ a₂ a₃ a₄ a₅ a₆ a b} : kFormat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.ConvertFromBlock a₀ a a₂ a₃ a₄ a₅ a₆) (kCodeSeq.ConvertFromBlock a₀ b a₂ a₃ a₄ a₅ a₆)
    | sub_ConvertFromBlock₂ {a₀ a₁ a₃ a₄ a₅ a₆ a b} : kFormat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.ConvertFromBlock a₀ a₁ a a₃ a₄ a₅ a₆) (kCodeSeq.ConvertFromBlock a₀ a₁ b a₃ a₄ a₅ a₆)
    | sub_ConvertFromBlock₃ {a₀ a₁ a₂ a₄ a₅ a₆ a b} : kFormat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.ConvertFromBlock a₀ a₁ a₂ a a₄ a₅ a₆) (kCodeSeq.ConvertFromBlock a₀ a₁ a₂ b a₄ a₅ a₆)
    | sub_ConvertFromBlock₄ {a₀ a₁ a₂ a₃ a₅ a₆ a b} : kBlockProjSpec.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.ConvertFromBlock a₀ a₁ a₂ a₃ a a₅ a₆) (kCodeSeq.ConvertFromBlock a₀ a₁ a₂ a₃ b a₅ a₆)
    | sub_ConvertFromBlock₅ {a₀ a₁ a₂ a₃ a₄ a₆ a b} : MRat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.ConvertFromBlock a₀ a₁ a₂ a₃ a₄ a a₆) (kCodeSeq.ConvertFromBlock a₀ a₁ a₂ a₃ a₄ b a₆)
    | sub_ConvertFromBlock₆ {a₀ a₁ a₂ a₃ a₄ a₅ a b} : kCodeSeq.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.ConvertFromBlock a₀ a₁ a₂ a₃ a₄ a₅ a) (kCodeSeq.ConvertFromBlock a₀ a₁ a₂ a₃ a₄ a₅ b)
    | sub_ConvertToBlock₀ {a₁ a₂ a₃ a₄ a₅ a₆ a b} : MRat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.ConvertToBlock a a₁ a₂ a₃ a₄ a₅ a₆) (kCodeSeq.ConvertToBlock b a₁ a₂ a₃ a₄ a₅ a₆)
    | sub_ConvertToBlock₁ {a₀ a₂ a₃ a₄ a₅ a₆ a b} : kFormat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.ConvertToBlock a₀ a a₂ a₃ a₄ a₅ a₆) (kCodeSeq.ConvertToBlock a₀ b a₂ a₃ a₄ a₅ a₆)
    | sub_ConvertToBlock₂ {a₀ a₁ a₃ a₄ a₅ a₆ a b} : kFormat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.ConvertToBlock a₀ a₁ a a₃ a₄ a₅ a₆) (kCodeSeq.ConvertToBlock a₀ a₁ b a₃ a₄ a₅ a₆)
    | sub_ConvertToBlock₃ {a₀ a₁ a₂ a₄ a₅ a₆ a b} : kFormat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.ConvertToBlock a₀ a₁ a₂ a a₄ a₅ a₆) (kCodeSeq.ConvertToBlock a₀ a₁ a₂ b a₄ a₅ a₆)
    | sub_ConvertToBlock₄ {a₀ a₁ a₂ a₃ a₅ a₆ a b} : kBlockProjSpec.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.ConvertToBlock a₀ a₁ a₂ a₃ a a₅ a₆) (kCodeSeq.ConvertToBlock a₀ a₁ a₂ a₃ b a₅ a₆)
    | sub_ConvertToBlock₅ {a₀ a₁ a₂ a₃ a₄ a₆ a b} : kCodeSeq.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.ConvertToBlock a₀ a₁ a₂ a₃ a₄ a a₆) (kCodeSeq.ConvertToBlock a₀ a₁ a₂ a₃ a₄ b a₆)
    | sub_ConvertToBlock₆ {a₀ a₁ a₂ a₃ a₄ a₅ a b} : MRat.rw_one a b →
    kCodeSeq.rw_one (kCodeSeq.ConvertToBlock a₀ a₁ a₂ a₃ a₄ a₅ a) (kCodeSeq.ConvertToBlock a₀ a₁ a₂ a₃ a₄ a₅ b)

  inductive kBlock.rw_one: kBlock → kBlock → Prop
    | eqe_left {a b c : kBlock} : a.eqe b → kBlock.rw_one b c → kBlock.rw_one a c
    | eqe_right {a b c : kBlock} : kBlock.rw_one a b → b.eqe c → kBlock.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_block₀ {a₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.block a a₁) (kBlock.block b a₁)
    | sub_block₁ {a₀ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.block a₀ a) (kBlock.block a₀ b)
    | sub_ConvertToBlockMaxAbsFinite₀ {a₁ a₂ a₃ a₄ a₅ a₆ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.ConvertToBlockMaxAbsFinite a a₁ a₂ a₃ a₄ a₅ a₆) (kBlock.ConvertToBlockMaxAbsFinite b a₁ a₂ a₃ a₄ a₅ a₆)
    | sub_ConvertToBlockMaxAbsFinite₁ {a₀ a₂ a₃ a₄ a₅ a₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.ConvertToBlockMaxAbsFinite a₀ a a₂ a₃ a₄ a₅ a₆) (kBlock.ConvertToBlockMaxAbsFinite a₀ b a₂ a₃ a₄ a₅ a₆)
    | sub_ConvertToBlockMaxAbsFinite₂ {a₀ a₁ a₃ a₄ a₅ a₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.ConvertToBlockMaxAbsFinite a₀ a₁ a a₃ a₄ a₅ a₆) (kBlock.ConvertToBlockMaxAbsFinite a₀ a₁ b a₃ a₄ a₅ a₆)
    | sub_ConvertToBlockMaxAbsFinite₃ {a₀ a₁ a₂ a₄ a₅ a₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.ConvertToBlockMaxAbsFinite a₀ a₁ a₂ a a₄ a₅ a₆) (kBlock.ConvertToBlockMaxAbsFinite a₀ a₁ a₂ b a₄ a₅ a₆)
    | sub_ConvertToBlockMaxAbsFinite₄ {a₀ a₁ a₂ a₃ a₅ a₆ a b} : kProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.ConvertToBlockMaxAbsFinite a₀ a₁ a₂ a₃ a a₅ a₆) (kBlock.ConvertToBlockMaxAbsFinite a₀ a₁ a₂ a₃ b a₅ a₆)
    | sub_ConvertToBlockMaxAbsFinite₅ {a₀ a₁ a₂ a₃ a₄ a₆ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.ConvertToBlockMaxAbsFinite a₀ a₁ a₂ a₃ a₄ a a₆) (kBlock.ConvertToBlockMaxAbsFinite a₀ a₁ a₂ a₃ a₄ b a₆)
    | sub_ConvertToBlockMaxAbsFinite₆ {a₀ a₁ a₂ a₃ a₄ a₅ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.ConvertToBlockMaxAbsFinite a₀ a₁ a₂ a₃ a₄ a₅ a) (kBlock.ConvertToBlockMaxAbsFinite a₀ a₁ a₂ a₃ a₄ a₅ b)
    | sub_computedBlock₀ {a₁ a₂ a₃ a₄ a₅ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.computedBlock a a₁ a₂ a₃ a₄ a₅) (kBlock.computedBlock b a₁ a₂ a₃ a₄ a₅)
    | sub_computedBlock₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.computedBlock a₀ a a₂ a₃ a₄ a₅) (kBlock.computedBlock a₀ b a₂ a₃ a₄ a₅)
    | sub_computedBlock₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.computedBlock a₀ a₁ a a₃ a₄ a₅) (kBlock.computedBlock a₀ a₁ b a₃ a₄ a₅)
    | sub_computedBlock₃ {a₀ a₁ a₂ a₄ a₅ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.computedBlock a₀ a₁ a₂ a a₄ a₅) (kBlock.computedBlock a₀ a₁ a₂ b a₄ a₅)
    | sub_computedBlock₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.computedBlock a₀ a₁ a₂ a₃ a a₅) (kBlock.computedBlock a₀ a₁ a₂ a₃ b a₅)
    | sub_computedBlock₅ {a₀ a₁ a₂ a₃ a₄ a b} : kXSeq.rw_one a b →
    kBlock.rw_one (kBlock.computedBlock a₀ a₁ a₂ a₃ a₄ a) (kBlock.computedBlock a₀ a₁ a₂ a₃ a₄ b)
    | sub_BlockConvert₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockConvert a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockConvert b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockConvert₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockConvert a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockConvert a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockConvert₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockConvert a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockConvert a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockConvert₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockConvert a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockConvert a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockConvert₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockConvert a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockConvert a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockConvert₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockConvert a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockConvert a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockConvert₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockConvert a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockConvert a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockConvert₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockConvert a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockConvert a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockConvert₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockConvert a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockConvert a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockAbs₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockAbs a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockAbs b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockAbs₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockAbs a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockAbs a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockAbs₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockAbs a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockAbs a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockAbs₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockAbs a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockAbs a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockAbs₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockAbs a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockAbs a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockAbs₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockAbs a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockAbs a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockAbs₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockAbs a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockAbs a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockAbs₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockAbs a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockAbs a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockAbs₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockAbs a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockAbs a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockNegate₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockNegate a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockNegate b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockNegate₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockNegate a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockNegate a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockNegate₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockNegate a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockNegate a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockNegate₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockNegate a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockNegate a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockNegate₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockNegate a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockNegate a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockNegate₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockNegate a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockNegate a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockNegate₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockNegate a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockNegate a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockNegate₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockNegate a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockNegate a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockNegate₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockNegate a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockNegate a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockCopySign₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCopySign a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockCopySign b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockCopySign₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCopySign a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockCopySign a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockCopySign₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCopySign a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockCopySign a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockCopySign₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCopySign a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockCopySign a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockCopySign₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockCopySign a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockCopySign₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockCopySign₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockCopySign₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockCopySign₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockCopySign₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂) (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | sub_BlockCopySign₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂) (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | sub_BlockCopySign₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂) (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | sub_BlockCopySign₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a) (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | sub_BlockAdd₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockAdd a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockAdd b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockAdd₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockAdd a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockAdd a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockAdd₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockAdd a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockAdd a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockAdd₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockAdd a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockAdd a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockAdd₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockAdd a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockAdd a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockAdd₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockAdd a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockAdd a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockAdd₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockAdd₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockAdd₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockAdd₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂) (kBlock.BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | sub_BlockAdd₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂) (kBlock.BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | sub_BlockAdd₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂) (kBlock.BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | sub_BlockAdd₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a) (kBlock.BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | sub_BlockSubtract₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSubtract a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockSubtract b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockSubtract₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSubtract a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockSubtract a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockSubtract₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSubtract a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockSubtract a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockSubtract₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSubtract a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockSubtract a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockSubtract₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockSubtract a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockSubtract₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockSubtract₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockSubtract₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockSubtract₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockSubtract₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂) (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | sub_BlockSubtract₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂) (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | sub_BlockSubtract₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂) (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | sub_BlockSubtract₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a) (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | sub_BlockMultiply₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMultiply a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMultiply b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMultiply₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMultiply a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMultiply a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMultiply₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMultiply a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMultiply a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMultiply₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMultiply a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMultiply a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMultiply₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMultiply a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMultiply₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMultiply₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMultiply₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMultiply₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMultiply₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂) (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | sub_BlockMultiply₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂) (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | sub_BlockMultiply₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂) (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | sub_BlockMultiply₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a) (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | sub_BlockDivide₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockDivide a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockDivide b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockDivide₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockDivide a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockDivide a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockDivide₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockDivide a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockDivide a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockDivide₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockDivide a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockDivide a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockDivide₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockDivide a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockDivide a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockDivide₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockDivide a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockDivide a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockDivide₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockDivide₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockDivide₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockDivide₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂) (kBlock.BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | sub_BlockDivide₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂) (kBlock.BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | sub_BlockDivide₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂) (kBlock.BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | sub_BlockDivide₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a) (kBlock.BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | sub_BlockFMA₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFMA a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFMA b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFMA₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFMA a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFMA a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFMA₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFMA a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFMA a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFMA₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFMA a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFMA a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFMA₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFMA a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFMA a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFMA₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFMA₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFMA₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFMA₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFMA₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFMA₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFMA₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFMA₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₃ a₁₄ a₁₅ a₁₆ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFMA₁₃ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₄ a₁₅ a₁₆ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a a₁₄ a₁₅ a₁₆) (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b a₁₄ a₁₅ a₁₆)
    | sub_BlockFMA₁₄ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₅ a₁₆ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a a₁₅ a₁₆) (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b a₁₅ a₁₆)
    | sub_BlockFMA₁₅ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₆ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a a₁₆) (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ b a₁₆)
    | sub_BlockFMA₁₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a) (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ b)
    | sub_BlockFAA₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFAA a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFAA b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFAA₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFAA a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFAA a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFAA₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFAA a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFAA a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFAA₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFAA a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFAA a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFAA₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFAA a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFAA a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFAA₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFAA₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFAA₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFAA₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFAA₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFAA₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFAA₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFAA₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₃ a₁₄ a₁₅ a₁₆ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockFAA₁₃ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₄ a₁₅ a₁₆ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a a₁₄ a₁₅ a₁₆) (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b a₁₄ a₁₅ a₁₆)
    | sub_BlockFAA₁₄ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₅ a₁₆ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a a₁₅ a₁₆) (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b a₁₅ a₁₆)
    | sub_BlockFAA₁₅ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₆ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a a₁₆) (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ b a₁₆)
    | sub_BlockFAA₁₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a) (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ b)
    | sub_BlockRecip₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockRecip a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockRecip b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockRecip₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockRecip a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockRecip a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockRecip₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockRecip a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockRecip a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockRecip₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockRecip a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockRecip a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockRecip₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockRecip a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockRecip a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockRecip₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockRecip a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockRecip a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockRecip₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockRecip a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockRecip a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockRecip₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockRecip a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockRecip a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockRecip₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockRecip a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockRecip a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockMinimum₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimum a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimum b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimum₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimum a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimum a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimum₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimum a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimum a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimum₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimum a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimum a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimum₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimum a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimum₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimum₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimum₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimum₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimum₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimum₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂) (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | sub_BlockMinimum₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂) (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | sub_BlockMinimum₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a) (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | sub_BlockMaximum₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximum a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximum b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximum₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximum a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximum a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximum₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximum a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximum a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximum₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximum a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximum a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximum₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximum a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximum₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximum₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximum₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximum₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximum₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximum₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂) (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | sub_BlockMaximum₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂) (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | sub_BlockMaximum₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a) (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | sub_BlockMinimumNumber₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumNumber a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumNumber b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumNumber₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumNumber a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumNumber a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumNumber₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumNumber a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumNumber a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumNumber₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumNumber a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumNumber a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumNumber₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumNumber₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumNumber₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumNumber₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumNumber₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumNumber₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumNumber₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂) (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | sub_BlockMinimumNumber₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂) (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | sub_BlockMinimumNumber₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a) (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | sub_BlockMaximumNumber₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumNumber a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumNumber b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumNumber₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumNumber a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumNumber a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumNumber₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumNumber a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumNumber a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumNumber₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumNumber a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumNumber a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumNumber₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumNumber₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumNumber₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumNumber₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumNumber₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumNumber₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumNumber₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂) (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | sub_BlockMaximumNumber₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂) (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | sub_BlockMaximumNumber₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a) (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | sub_BlockMinimumMagnitude₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitude a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitude b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitude₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitude a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitude a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitude₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitude a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitude a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitude₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitude₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitude₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitude₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitude₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitude₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitude₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitude₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂) (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | sub_BlockMinimumMagnitude₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂) (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | sub_BlockMinimumMagnitude₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a) (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | sub_BlockMaximumMagnitude₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitude a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitude b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitude₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitude a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitude a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitude₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitude a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitude a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitude₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitude₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitude₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitude₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitude₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitude₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitude₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitude₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂) (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | sub_BlockMaximumMagnitude₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂) (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | sub_BlockMaximumMagnitude₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a) (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | sub_BlockMinimumMagnitudeNumber₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitudeNumber a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitudeNumber b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitudeNumber₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitudeNumber a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitudeNumber a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitudeNumber₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitudeNumber₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitudeNumber₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitudeNumber₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitudeNumber₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitudeNumber₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitudeNumber₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitudeNumber₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumMagnitudeNumber₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂) (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | sub_BlockMinimumMagnitudeNumber₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂) (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | sub_BlockMinimumMagnitudeNumber₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a) (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | sub_BlockMaximumMagnitudeNumber₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitudeNumber a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitudeNumber b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitudeNumber₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitudeNumber a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitudeNumber a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitudeNumber₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitudeNumber₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitudeNumber₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitudeNumber₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitudeNumber₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitudeNumber₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitudeNumber₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitudeNumber₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumMagnitudeNumber₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂) (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | sub_BlockMaximumMagnitudeNumber₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂) (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | sub_BlockMaximumMagnitudeNumber₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a) (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | sub_BlockMinimumFinite₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumFinite a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumFinite b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumFinite₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumFinite a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumFinite a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumFinite₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumFinite a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumFinite a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumFinite₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumFinite a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumFinite a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumFinite₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumFinite₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumFinite₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumFinite₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumFinite₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumFinite₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | sub_BlockMinimumFinite₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂) (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | sub_BlockMinimumFinite₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂) (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | sub_BlockMinimumFinite₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a) (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | sub_BlockMaximumFinite₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumFinite a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumFinite b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumFinite₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumFinite a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumFinite a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumFinite₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumFinite a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumFinite a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumFinite₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumFinite a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumFinite a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumFinite₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumFinite₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumFinite₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumFinite₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumFinite₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumFinite₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | sub_BlockMaximumFinite₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂) (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | sub_BlockMaximumFinite₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂) (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | sub_BlockMaximumFinite₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a) (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | sub_BlockClamp₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockClamp a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockClamp b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockClamp₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockClamp a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockClamp a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockClamp₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockClamp a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockClamp a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockClamp₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockClamp a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockClamp a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockClamp₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockClamp a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockClamp a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockClamp₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockClamp₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockClamp₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockClamp₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockClamp₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockClamp₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockClamp₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockClamp₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₃ a₁₄ a₁₅ a₁₆ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b a₁₃ a₁₄ a₁₅ a₁₆)
    | sub_BlockClamp₁₃ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₄ a₁₅ a₁₆ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a a₁₄ a₁₅ a₁₆) (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b a₁₄ a₁₅ a₁₆)
    | sub_BlockClamp₁₄ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₅ a₁₆ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a a₁₅ a₁₆) (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b a₁₅ a₁₆)
    | sub_BlockClamp₁₅ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₆ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a a₁₆) (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ b a₁₆)
    | sub_BlockClamp₁₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a) (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ b)
    | sub_BlockSqrt₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSqrt a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSqrt b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSqrt₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSqrt a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSqrt a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSqrt₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSqrt a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSqrt a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSqrt₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSqrt a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSqrt a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSqrt₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSqrt a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockSqrt a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockSqrt₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockSqrt a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockSqrt a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockSqrt₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSqrt a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockSqrt a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockSqrt₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockSqrt₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockRSqrt₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockRSqrt a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockRSqrt b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockRSqrt₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockRSqrt a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockRSqrt a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockRSqrt₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockRSqrt a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockRSqrt a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockRSqrt₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockRSqrt a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockRSqrt a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockRSqrt₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockRSqrt a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockRSqrt a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockRSqrt₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockRSqrt a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockRSqrt a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockRSqrt₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockRSqrt a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockRSqrt a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockRSqrt₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockRSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockRSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockRSqrt₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockRSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockRSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockExp₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExp a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockExp b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockExp₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExp a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockExp a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockExp₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExp a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockExp a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockExp₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExp a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockExp a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockExp₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExp a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockExp a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockExp₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockExp a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockExp a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockExp₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExp a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockExp a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockExp₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockExp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockExp a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockExp₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockExp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockExp2₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExp2 a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockExp2 b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockExp2₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExp2 a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockExp2 a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockExp2₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExp2 a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockExp2 a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockExp2₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExp2 a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockExp2 a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockExp2₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExp2 a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockExp2 a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockExp2₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockExp2 a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockExp2 a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockExp2₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExp2 a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockExp2 a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockExp2₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockExp2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockExp2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockExp2₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExp2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockExp2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockLog₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLog a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockLog b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockLog₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLog a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockLog a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockLog₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLog a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockLog a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockLog₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLog a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockLog a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockLog₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLog a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockLog a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockLog₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockLog a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockLog a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockLog₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLog a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockLog a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockLog₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockLog a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockLog a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockLog₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLog a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockLog a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockLog2₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLog2 a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockLog2 b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockLog2₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLog2 a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockLog2 a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockLog2₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLog2 a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockLog2 a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockLog2₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLog2 a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockLog2 a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockLog2₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLog2 a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockLog2 a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockLog2₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockLog2 a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockLog2 a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockLog2₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLog2 a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockLog2 a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockLog2₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockLog2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockLog2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockLog2₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLog2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockLog2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockLogOnePlus₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLogOnePlus a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockLogOnePlus b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockLogOnePlus₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLogOnePlus a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockLogOnePlus a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockLogOnePlus₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLogOnePlus a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockLogOnePlus a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockLogOnePlus₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLogOnePlus a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockLogOnePlus a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockLogOnePlus₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLogOnePlus a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockLogOnePlus a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockLogOnePlus₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockLogOnePlus a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockLogOnePlus a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockLogOnePlus₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLogOnePlus a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockLogOnePlus a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockLogOnePlus₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockLogOnePlus a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockLogOnePlus a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockLogOnePlus₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockLogOnePlus a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockLogOnePlus a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockExpMinusOne₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExpMinusOne a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockExpMinusOne b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockExpMinusOne₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExpMinusOne a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockExpMinusOne a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockExpMinusOne₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExpMinusOne a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockExpMinusOne a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockExpMinusOne₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExpMinusOne a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockExpMinusOne a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockExpMinusOne₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExpMinusOne a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockExpMinusOne a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockExpMinusOne₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockExpMinusOne a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockExpMinusOne a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockExpMinusOne₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExpMinusOne a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockExpMinusOne a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockExpMinusOne₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockExpMinusOne a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockExpMinusOne a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockExpMinusOne₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockExpMinusOne a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockExpMinusOne a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockSin₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSin a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSin b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSin₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSin a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSin a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSin₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSin a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSin a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSin₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSin a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSin a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSin₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSin a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockSin a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockSin₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockSin a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockSin a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockSin₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSin a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockSin a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockSin₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockSin₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockCos₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCos a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockCos b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockCos₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCos a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockCos a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockCos₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCos a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockCos a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockCos₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCos a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockCos a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockCos₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCos a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockCos a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockCos₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockCos a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockCos a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockCos₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCos a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockCos a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockCos₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockCos₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockTan₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTan a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockTan b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockTan₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTan a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockTan a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockTan₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTan a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockTan a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockTan₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTan a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockTan a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockTan₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTan a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockTan a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockTan₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockTan a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockTan a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockTan₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTan a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockTan a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockTan₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockTan₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockArcSin₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSin a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcSin b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcSin₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSin a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcSin a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcSin₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSin a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcSin a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcSin₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSin a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcSin a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcSin₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSin a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockArcSin a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockArcSin₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSin a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockArcSin a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockArcSin₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSin a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockArcSin a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockArcSin₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockArcSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockArcSin₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockArcSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockArcCos₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCos a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcCos b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcCos₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCos a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcCos a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcCos₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCos a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcCos a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcCos₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCos a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcCos a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcCos₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCos a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockArcCos a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockArcCos₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCos a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockArcCos a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockArcCos₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCos a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockArcCos a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockArcCos₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockArcCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockArcCos₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockArcCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockArcTan₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcTan b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcTan₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcTan a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcTan₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcTan a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcTan₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcTan a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcTan₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockArcTan a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockArcTan₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockArcTan a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockArcTan₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockArcTan a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockArcTan₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockArcTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockArcTan₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockArcTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockSinh₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSinh a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSinh b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSinh₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSinh a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSinh a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSinh₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSinh a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSinh a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSinh₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSinh a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSinh a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSinh₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSinh a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockSinh a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockSinh₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockSinh a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockSinh a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockSinh₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSinh a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockSinh a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockSinh₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockSinh₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockCosh₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCosh a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockCosh b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockCosh₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCosh a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockCosh a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockCosh₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCosh a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockCosh a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockCosh₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCosh a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockCosh a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockCosh₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCosh a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockCosh a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockCosh₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockCosh a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockCosh a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockCosh₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCosh a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockCosh a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockCosh₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockCosh₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockTanh₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTanh a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockTanh b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockTanh₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTanh a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockTanh a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockTanh₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTanh a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockTanh a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockTanh₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTanh a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockTanh a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockTanh₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTanh a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockTanh a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockTanh₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockTanh a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockTanh a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockTanh₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTanh a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockTanh a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockTanh₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockTanh₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockArcSinh₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSinh a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcSinh b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcSinh₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSinh a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcSinh a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcSinh₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSinh a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcSinh a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcSinh₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSinh a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcSinh a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcSinh₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSinh a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockArcSinh a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockArcSinh₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSinh a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockArcSinh a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockArcSinh₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSinh a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockArcSinh a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockArcSinh₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockArcSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockArcSinh₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockArcSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockArcCosh₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCosh a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcCosh b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcCosh₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCosh a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcCosh a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcCosh₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCosh a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcCosh a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcCosh₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCosh a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcCosh a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcCosh₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCosh a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockArcCosh a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockArcCosh₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCosh a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockArcCosh a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockArcCosh₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCosh a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockArcCosh a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockArcCosh₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockArcCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockArcCosh₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockArcCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockArcTanh₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTanh a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcTanh b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcTanh₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTanh a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcTanh a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcTanh₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTanh a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcTanh a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcTanh₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTanh a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcTanh a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcTanh₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTanh a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockArcTanh a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockArcTanh₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTanh a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockArcTanh a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockArcTanh₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTanh a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockArcTanh a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockArcTanh₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockArcTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockArcTanh₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockArcTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockSinPi₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSinPi a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSinPi b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSinPi₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSinPi a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSinPi a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSinPi₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSinPi a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSinPi a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSinPi₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSinPi a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSinPi a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSinPi₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSinPi a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockSinPi a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockSinPi₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockSinPi a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockSinPi a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockSinPi₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSinPi a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockSinPi a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockSinPi₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockSinPi₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockCosPi₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCosPi a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockCosPi b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockCosPi₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCosPi a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockCosPi a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockCosPi₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCosPi a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockCosPi a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockCosPi₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCosPi a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockCosPi a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockCosPi₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCosPi a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockCosPi a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockCosPi₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockCosPi a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockCosPi a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockCosPi₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCosPi a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockCosPi a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockCosPi₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockCosPi₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockTanPi₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTanPi a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockTanPi b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockTanPi₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTanPi a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockTanPi a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockTanPi₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTanPi a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockTanPi a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockTanPi₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTanPi a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockTanPi a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockTanPi₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTanPi a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockTanPi a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockTanPi₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockTanPi a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockTanPi a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockTanPi₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTanPi a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockTanPi a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockTanPi₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockTanPi₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockArcSinPi₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSinPi a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcSinPi b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcSinPi₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSinPi a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcSinPi a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcSinPi₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSinPi a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcSinPi a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcSinPi₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSinPi a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcSinPi a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcSinPi₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSinPi a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockArcSinPi a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockArcSinPi₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSinPi a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockArcSinPi a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockArcSinPi₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSinPi a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockArcSinPi a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockArcSinPi₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockArcSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockArcSinPi₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockArcSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockArcCosPi₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCosPi a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcCosPi b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcCosPi₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCosPi a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcCosPi a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcCosPi₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCosPi a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcCosPi a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcCosPi₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCosPi a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcCosPi a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcCosPi₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCosPi a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockArcCosPi a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockArcCosPi₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCosPi a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockArcCosPi a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockArcCosPi₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCosPi a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockArcCosPi a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockArcCosPi₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockArcCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockArcCosPi₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockArcCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockArcTanPi₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTanPi a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcTanPi b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcTanPi₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTanPi a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcTanPi a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcTanPi₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTanPi a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcTanPi a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcTanPi₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTanPi a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcTanPi a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockArcTanPi₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTanPi a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockArcTanPi a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockArcTanPi₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTanPi a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockArcTanPi a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockArcTanPi₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTanPi a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockArcTanPi a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockArcTanPi₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockArcTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockArcTanPi₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockArcTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockSoftplus₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSoftplus a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSoftplus b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSoftplus₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSoftplus a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSoftplus a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSoftplus₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSoftplus a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSoftplus a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSoftplus₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSoftplus a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSoftplus a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | sub_BlockSoftplus₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSoftplus a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈) (kBlock.BlockSoftplus a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | sub_BlockSoftplus₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockSoftplus a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈) (kBlock.BlockSoftplus a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | sub_BlockSoftplus₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSoftplus a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈) (kBlock.BlockSoftplus a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | sub_BlockSoftplus₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockSoftplus a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈) (kBlock.BlockSoftplus a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | sub_BlockSoftplus₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockSoftplus a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a) (kBlock.BlockSoftplus a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | sub_BlockHypot₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockHypot a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockHypot b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockHypot₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockHypot a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockHypot a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockHypot₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockHypot a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockHypot a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockHypot₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockHypot a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockHypot a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockHypot₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockHypot a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockHypot a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockHypot₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockHypot a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockHypot a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockHypot₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockHypot₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockHypot₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockHypot₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂) (kBlock.BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | sub_BlockHypot₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂) (kBlock.BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | sub_BlockHypot₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂) (kBlock.BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | sub_BlockHypot₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a) (kBlock.BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | sub_BlockArcTan2₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2 a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2 b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2 a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2 a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2 a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2 a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2 a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2 a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂) (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | sub_BlockArcTan2₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂) (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | sub_BlockArcTan2₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a) (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | sub_BlockArcTan2Pi₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2Pi a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2Pi b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2Pi₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2Pi a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2Pi a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2Pi₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2Pi a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2Pi a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2Pi₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2Pi a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2Pi₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2Pi₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2Pi₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kFormat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2Pi₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : kBlockProjSpec.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2Pi₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2Pi₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | sub_BlockArcTan2Pi₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂) (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | sub_BlockArcTan2Pi₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a b} : kCodeSeq.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂) (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | sub_BlockArcTan2Pi₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a b} : MRat.rw_one a b →
    kBlock.rw_one (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a) (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)

  inductive kFormatSeq.rw_one: kFormatSeq → kFormatSeq → Prop
    | eqe_left {a b c : kFormatSeq} : a.eqe b → kFormatSeq.rw_one b c → kFormatSeq.rw_one a c
    | eqe_right {a b c : kFormatSeq} : kFormatSeq.rw_one a b → b.eqe c → kFormatSeq.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_fcons₀ {a₁ a b} : kFormat.rw_one a b →
    kFormatSeq.rw_one (kFormatSeq.fcons a a₁) (kFormatSeq.fcons b a₁)
    | sub_fcons₁ {a₀ a b} : kFormatSeq.rw_one a b →
    kFormatSeq.rw_one (kFormatSeq.fcons a₀ a) (kFormatSeq.fcons a₀ b)

  inductive kSpecialization.rw_one: kSpecialization → kSpecialization → Prop
    | eqe_left {a b c : kSpecialization} : a.eqe b → kSpecialization.rw_one b c → kSpecialization.rw_one a c
    | eqe_right {a b c : kSpecialization} : kSpecialization.rw_one a b → b.eqe c → kSpecialization.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_numeric₀ {a₁ a₂ a b} : MString.rw_one a b →
    kSpecialization.rw_one (kSpecialization.numeric a a₁ a₂) (kSpecialization.numeric b a₁ a₂)
    | sub_numeric₁ {a₀ a₂ a b} : kFormatSeq.rw_one a b →
    kSpecialization.rw_one (kSpecialization.numeric a₀ a a₂) (kSpecialization.numeric a₀ b a₂)
    | sub_numeric₂ {a₀ a₁ a b} : kProjSpec.rw_one a b →
    kSpecialization.rw_one (kSpecialization.numeric a₀ a₁ a) (kSpecialization.numeric a₀ a₁ b)
    | sub_plain₀ {a₁ a b} : MString.rw_one a b →
    kSpecialization.rw_one (kSpecialization.plain a a₁) (kSpecialization.plain b a₁)
    | sub_plain₁ {a₀ a b} : kFormatSeq.rw_one a b →
    kSpecialization.rw_one (kSpecialization.plain a₀ a) (kSpecialization.plain a₀ b)
    | sub_blockElements₀ {a₁ a₂ a₃ a b} : MString.rw_one a b →
    kSpecialization.rw_one (kSpecialization.blockElements a a₁ a₂ a₃) (kSpecialization.blockElements b a₁ a₂ a₃)
    | sub_blockElements₁ {a₀ a₂ a₃ a b} : MRat.rw_one a b →
    kSpecialization.rw_one (kSpecialization.blockElements a₀ a a₂ a₃) (kSpecialization.blockElements a₀ b a₂ a₃)
    | sub_blockElements₂ {a₀ a₁ a₃ a b} : kFormatSeq.rw_one a b →
    kSpecialization.rw_one (kSpecialization.blockElements a₀ a₁ a a₃) (kSpecialization.blockElements a₀ a₁ b a₃)
    | sub_blockElements₃ {a₀ a₁ a₂ a b} : kBlockProjSpec.rw_one a b →
    kSpecialization.rw_one (kSpecialization.blockElements a₀ a₁ a₂ a) (kSpecialization.blockElements a₀ a₁ a₂ b)
    | sub_blockReduction₀ {a₁ a₂ a₃ a b} : MString.rw_one a b →
    kSpecialization.rw_one (kSpecialization.blockReduction a a₁ a₂ a₃) (kSpecialization.blockReduction b a₁ a₂ a₃)
    | sub_blockReduction₁ {a₀ a₂ a₃ a b} : MRat.rw_one a b →
    kSpecialization.rw_one (kSpecialization.blockReduction a₀ a a₂ a₃) (kSpecialization.blockReduction a₀ b a₂ a₃)
    | sub_blockReduction₂ {a₀ a₁ a₃ a b} : kFormatSeq.rw_one a b →
    kSpecialization.rw_one (kSpecialization.blockReduction a₀ a₁ a a₃) (kSpecialization.blockReduction a₀ a₁ b a₃)
    | sub_blockReduction₃ {a₀ a₁ a₂ a b} : kProjSpec.rw_one a b →
    kSpecialization.rw_one (kSpecialization.blockReduction a₀ a₁ a₂ a) (kSpecialization.blockReduction a₀ a₁ a₂ b)
    | sub_blockScale₀ {a₁ a₂ a₃ a₄ a b} : MString.rw_one a b →
    kSpecialization.rw_one (kSpecialization.blockScale a a₁ a₂ a₃ a₄) (kSpecialization.blockScale b a₁ a₂ a₃ a₄)
    | sub_blockScale₁ {a₀ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    kSpecialization.rw_one (kSpecialization.blockScale a₀ a a₂ a₃ a₄) (kSpecialization.blockScale a₀ b a₂ a₃ a₄)
    | sub_blockScale₂ {a₀ a₁ a₃ a₄ a b} : kFormatSeq.rw_one a b →
    kSpecialization.rw_one (kSpecialization.blockScale a₀ a₁ a a₃ a₄) (kSpecialization.blockScale a₀ a₁ b a₃ a₄)
    | sub_blockScale₃ {a₀ a₁ a₂ a₄ a b} : kProjSpec.rw_one a b →
    kSpecialization.rw_one (kSpecialization.blockScale a₀ a₁ a₂ a a₄) (kSpecialization.blockScale a₀ a₁ a₂ b a₄)
    | sub_blockScale₄ {a₀ a₁ a₂ a₃ a b} : kBlockProjSpec.rw_one a b →
    kSpecialization.rw_one (kSpecialization.blockScale a₀ a₁ a₂ a₃ a) (kSpecialization.blockScale a₀ a₁ a₂ a₃ b)
    | sub_at₀ {a₁ a b} : kSpecializationSeq.rw_one a b →
    kSpecialization.rw_one (kSpecialization.«at» a a₁) (kSpecialization.«at» b a₁)
    | sub_at₁ {a₀ a b} : MRat.rw_one a b →
    kSpecialization.rw_one (kSpecialization.«at» a₀ a) (kSpecialization.«at» a₀ b)
    | sub_declaredIdentity {a b} : kDeclaration.rw_one a b →
    kSpecialization.rw_one (kSpecialization.declaredIdentity a) (kSpecialization.declaredIdentity b)

  inductive kKappa.rw_one: kKappa → kKappa → Prop
    | eqe_left {a b c : kKappa} : a.eqe b → kKappa.rw_one b c → kKappa.rw_one a c
    | eqe_right {a b c : kKappa} : kKappa.rw_one a b → b.eqe c → kKappa.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_steps {a b} : MRat.rw_one a b →
    kKappa.rw_one (kKappa.steps a) (kKappa.steps b)
    | sub_partBound {a b} : kKappaPartSeq.rw_one a b →
    kKappa.rw_one (kKappa.partBound a) (kKappa.partBound b)
    | sub_declarationKappa {a b} : kDeclaration.rw_one a b →
    kKappa.rw_one (kKappa.declarationKappa a) (kKappa.declarationKappa b)
    | sub_observationKappa {a b} : kObservation.rw_one a b →
    kKappa.rw_one (kKappa.observationKappa a) (kKappa.observationKappa b)
    | sub_batchKappa {a b} : kObservationSeq.rw_one a b →
    kKappa.rw_one (kKappa.batchKappa a) (kKappa.batchKappa b)
    | sub_mergeKappa₀ {a₁ a b} : kKappa.rw_one a b →
    kKappa.rw_one (kKappa.mergeKappa a a₁) (kKappa.mergeKappa b a₁)
    | sub_mergeKappa₁ {a₀ a b} : kKappa.rw_one a b →
    kKappa.rw_one (kKappa.mergeKappa a₀ a) (kKappa.mergeKappa a₀ b)

  inductive kObservation.rw_one: kObservation → kObservation → Prop
    | eqe_left {a b c : kObservation} : a.eqe b → kObservation.rw_one b c → kObservation.rw_one a c
    | eqe_right {a b c : kObservation} : kObservation.rw_one a b → b.eqe c → kObservation.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_observation₀ {a₁ a₂ a₃ a₄ a b} : MString.rw_one a b →
    kObservation.rw_one (kObservation.observation a a₁ a₂ a₃ a₄) (kObservation.observation b a₁ a₂ a₃ a₄)
    | sub_observation₁ {a₀ a₂ a₃ a₄ a b} : kCodeSeq.rw_one a b →
    kObservation.rw_one (kObservation.observation a₀ a a₂ a₃ a₄) (kObservation.observation a₀ b a₂ a₃ a₄)
    | sub_observation₂ {a₀ a₁ a₃ a₄ a b} : kFormat.rw_one a b →
    kObservation.rw_one (kObservation.observation a₀ a₁ a a₃ a₄) (kObservation.observation a₀ a₁ b a₃ a₄)
    | sub_observation₃ {a₀ a₁ a₂ a₄ a b} : MRat.rw_one a b →
    kObservation.rw_one (kObservation.observation a₀ a₁ a₂ a a₄) (kObservation.observation a₀ a₁ a₂ b a₄)
    | sub_observation₄ {a₀ a₁ a₂ a₃ a b} : MRat.rw_one a b →
    kObservation.rw_one (kObservation.observation a₀ a₁ a₂ a₃ a) (kObservation.observation a₀ a₁ a₂ a₃ b)
    | sub_at₀ {a₁ a b} : kObservationSeq.rw_one a b →
    kObservation.rw_one (kObservation.«at» a a₁) (kObservation.«at» b a₁)
    | sub_at₁ {a₀ a b} : MRat.rw_one a b →
    kObservation.rw_one (kObservation.«at» a₀ a) (kObservation.«at» a₀ b)

  inductive kDeclaration.rw_one: kDeclaration → kDeclaration → Prop
    | eqe_left {a b c : kDeclaration} : a.eqe b → kDeclaration.rw_one b c → kDeclaration.rw_one a c
    | eqe_right {a b c : kDeclaration} : kDeclaration.rw_one a b → b.eqe c → kDeclaration.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_exact₀ {a₁ a₂ a b} : kSpecialization.rw_one a b →
    kDeclaration.rw_one (kDeclaration.exact a a₁ a₂) (kDeclaration.exact b a₁ a₂)
    | sub_exact₁ {a₀ a₂ a b} : MString.rw_one a b →
    kDeclaration.rw_one (kDeclaration.exact a₀ a a₂) (kDeclaration.exact a₀ b a₂)
    | sub_exact₂ {a₀ a₁ a b} : kEvidence.rw_one a b →
    kDeclaration.rw_one (kDeclaration.exact a₀ a₁ a) (kDeclaration.exact a₀ a₁ b)
    | sub_approximate₀ {a₁ a₂ a₃ a b} : kSpecialization.rw_one a b →
    kDeclaration.rw_one (kDeclaration.approximate a a₁ a₂ a₃) (kDeclaration.approximate b a₁ a₂ a₃)
    | sub_approximate₁ {a₀ a₂ a₃ a b} : MString.rw_one a b →
    kDeclaration.rw_one (kDeclaration.approximate a₀ a a₂ a₃) (kDeclaration.approximate a₀ b a₂ a₃)
    | sub_approximate₂ {a₀ a₁ a₃ a b} : kKappa.rw_one a b →
    kDeclaration.rw_one (kDeclaration.approximate a₀ a₁ a a₃) (kDeclaration.approximate a₀ a₁ b a₃)
    | sub_approximate₃ {a₀ a₁ a₂ a b} : kEvidence.rw_one a b →
    kDeclaration.rw_one (kDeclaration.approximate a₀ a₁ a₂ a) (kDeclaration.approximate a₀ a₁ a₂ b)
    | sub_at₀ {a₁ a b} : kDeclarationSeq.rw_one a b →
    kDeclaration.rw_one (kDeclaration.«at» a a₁) (kDeclaration.«at» b a₁)
    | sub_at₁ {a₀ a b} : MRat.rw_one a b →
    kDeclaration.rw_one (kDeclaration.«at» a₀ a) (kDeclaration.«at» a₀ b)
    | sub_partitioned₀ {a₁ a₂ a₃ a₄ a b} : kSpecialization.rw_one a b →
    kDeclaration.rw_one (kDeclaration.partitioned a a₁ a₂ a₃ a₄) (kDeclaration.partitioned b a₁ a₂ a₃ a₄)
    | sub_partitioned₁ {a₀ a₂ a₃ a₄ a b} : MString.rw_one a b →
    kDeclaration.rw_one (kDeclaration.partitioned a₀ a a₂ a₃ a₄) (kDeclaration.partitioned a₀ b a₂ a₃ a₄)
    | sub_partitioned₂ {a₀ a₁ a₃ a₄ a b} : kCodeSeq.rw_one a b →
    kDeclaration.rw_one (kDeclaration.partitioned a₀ a₁ a a₃ a₄) (kDeclaration.partitioned a₀ a₁ b a₃ a₄)
    | sub_partitioned₃ {a₀ a₁ a₂ a₄ a b} : kKappaPartSeq.rw_one a b →
    kDeclaration.rw_one (kDeclaration.partitioned a₀ a₁ a₂ a a₄) (kDeclaration.partitioned a₀ a₁ a₂ b a₄)
    | sub_partitioned₄ {a₀ a₁ a₂ a₃ a b} : kEvidence.rw_one a b →
    kDeclaration.rw_one (kDeclaration.partitioned a₀ a₁ a₂ a₃ a) (kDeclaration.partitioned a₀ a₁ a₂ a₃ b)

  inductive kEvidence.rw_one: kEvidence → kEvidence → Prop
    | eqe_left {a b c : kEvidence} : a.eqe b → kEvidence.rw_one b c → kEvidence.rw_one a c
    | eqe_right {a b c : kEvidence} : kEvidence.rw_one a b → b.eqe c → kEvidence.rw_one a c
    -- Axioms for rewriting inside subterms

  inductive kKappaPart.rw_one: kKappaPart → kKappaPart → Prop
    | eqe_left {a b c : kKappaPart} : a.eqe b → kKappaPart.rw_one b c → kKappaPart.rw_one a c
    | eqe_right {a b c : kKappaPart} : kKappaPart.rw_one a b → b.eqe c → kKappaPart.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_kappaPart₀ {a₁ a b} : kCodeSeq.rw_one a b →
    kKappaPart.rw_one (kKappaPart.kappaPart a a₁) (kKappaPart.kappaPart b a₁)
    | sub_kappaPart₁ {a₀ a b} : kKappa.rw_one a b →
    kKappaPart.rw_one (kKappaPart.kappaPart a₀ a) (kKappaPart.kappaPart a₀ b)
    | sub_at₀ {a₁ a b} : kKappaPartSeq.rw_one a b →
    kKappaPart.rw_one (kKappaPart.«at» a a₁) (kKappaPart.«at» b a₁)
    | sub_at₁ {a₀ a b} : MRat.rw_one a b →
    kKappaPart.rw_one (kKappaPart.«at» a₀ a) (kKappaPart.«at» a₀ b)

  inductive kArityEntry.rw_one: kArityEntry → kArityEntry → Prop
    | eqe_left {a b c : kArityEntry} : a.eqe b → kArityEntry.rw_one b c → kArityEntry.rw_one a c
    | eqe_right {a b c : kArityEntry} : kArityEntry.rw_one a b → b.eqe c → kArityEntry.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_entry₀ {a₁ a b} : MString.rw_one a b →
    kArityEntry.rw_one (kArityEntry.entry a a₁) (kArityEntry.entry b a₁)
    | sub_entry₁ {a₀ a b} : MRat.rw_one a b →
    kArityEntry.rw_one (kArityEntry.entry a₀ a) (kArityEntry.entry a₀ b)
    | sub_at₀ {a₁ a b} : kArityTable.rw_one a b →
    kArityEntry.rw_one (kArityEntry.«at» a a₁) (kArityEntry.«at» b a₁)
    | sub_at₁ {a₀ a b} : MRat.rw_one a b →
    kArityEntry.rw_one (kArityEntry.«at» a₀ a) (kArityEntry.«at» a₀ b)

  inductive kKappaPartSeq.rw_one: kKappaPartSeq → kKappaPartSeq → Prop
    | eqe_left {a b c : kKappaPartSeq} : a.eqe b → kKappaPartSeq.rw_one b c → kKappaPartSeq.rw_one a c
    | eqe_right {a b c : kKappaPartSeq} : kKappaPartSeq.rw_one a b → b.eqe c → kKappaPartSeq.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_kcons₀ {a₁ a b} : kKappaPart.rw_one a b →
    kKappaPartSeq.rw_one (kKappaPartSeq.kcons a a₁) (kKappaPartSeq.kcons b a₁)
    | sub_kcons₁ {a₀ a b} : kKappaPartSeq.rw_one a b →
    kKappaPartSeq.rw_one (kKappaPartSeq.kcons a₀ a) (kKappaPartSeq.kcons a₀ b)

  inductive kPartitionSeq.rw_one: kPartitionSeq → kPartitionSeq → Prop
    | eqe_left {a b c : kPartitionSeq} : a.eqe b → kPartitionSeq.rw_one b c → kPartitionSeq.rw_one a c
    | eqe_right {a b c : kPartitionSeq} : kPartitionSeq.rw_one a b → b.eqe c → kPartitionSeq.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_pcons₀ {a₁ a b} : kCodeSeq.rw_one a b →
    kPartitionSeq.rw_one (kPartitionSeq.pcons a a₁) (kPartitionSeq.pcons b a₁)
    | sub_pcons₁ {a₀ a b} : kPartitionSeq.rw_one a b →
    kPartitionSeq.rw_one (kPartitionSeq.pcons a₀ a) (kPartitionSeq.pcons a₀ b)
    | sub_partRegions {a b} : kKappaPartSeq.rw_one a b →
    kPartitionSeq.rw_one (kPartitionSeq.partRegions a) (kPartitionSeq.partRegions b)

  inductive kDeclarationSeq.rw_one: kDeclarationSeq → kDeclarationSeq → Prop
    | eqe_left {a b c : kDeclarationSeq} : a.eqe b → kDeclarationSeq.rw_one b c → kDeclarationSeq.rw_one a c
    | eqe_right {a b c : kDeclarationSeq} : kDeclarationSeq.rw_one a b → b.eqe c → kDeclarationSeq.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_dcons₀ {a₁ a b} : kDeclaration.rw_one a b →
    kDeclarationSeq.rw_one (kDeclarationSeq.dcons a a₁) (kDeclarationSeq.dcons b a₁)
    | sub_dcons₁ {a₀ a b} : kDeclarationSeq.rw_one a b →
    kDeclarationSeq.rw_one (kDeclarationSeq.dcons a₀ a) (kDeclarationSeq.dcons a₀ b)

  inductive kSpecializationSeq.rw_one: kSpecializationSeq → kSpecializationSeq → Prop
    | eqe_left {a b c : kSpecializationSeq} : a.eqe b → kSpecializationSeq.rw_one b c → kSpecializationSeq.rw_one a c
    | eqe_right {a b c : kSpecializationSeq} : kSpecializationSeq.rw_one a b → b.eqe c → kSpecializationSeq.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_scons₀ {a₁ a b} : kSpecialization.rw_one a b →
    kSpecializationSeq.rw_one (kSpecializationSeq.scons a a₁) (kSpecializationSeq.scons b a₁)
    | sub_scons₁ {a₀ a b} : kSpecializationSeq.rw_one a b →
    kSpecializationSeq.rw_one (kSpecializationSeq.scons a₀ a) (kSpecializationSeq.scons a₀ b)

  inductive kClassEnum.rw_one: kClassEnum → kClassEnum → Prop
    | eqe_left {a b c : kClassEnum} : a.eqe b → kClassEnum.rw_one b c → kClassEnum.rw_one a c
    | eqe_right {a b c : kClassEnum} : kClassEnum.rw_one a b → b.eqe c → kClassEnum.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_Class₀ {a₁ a b} : kFormat.rw_one a b →
    kClassEnum.rw_one (kClassEnum.Class a a₁) (kClassEnum.Class b a₁)
    | sub_Class₁ {a₀ a b} : MRat.rw_one a b →
    kClassEnum.rw_one (kClassEnum.Class a₀ a) (kClassEnum.Class a₀ b)
    | sub_ifthenelsefi₀ {a₁ a₂ a b} : kBool.rw_one a b →
    kClassEnum.rw_one (kClassEnum.ifthenelsefi a a₁ a₂) (kClassEnum.ifthenelsefi b a₁ a₂)
    | sub_ifthenelsefi₁ {a₀ a₂ a b} : kClassEnum.rw_one a b →
    kClassEnum.rw_one (kClassEnum.ifthenelsefi a₀ a a₂) (kClassEnum.ifthenelsefi a₀ b a₂)
    | sub_ifthenelsefi₂ {a₀ a₁ a b} : kClassEnum.rw_one a b →
    kClassEnum.rw_one (kClassEnum.ifthenelsefi a₀ a₁ a) (kClassEnum.ifthenelsefi a₀ a₁ b)

  inductive kObservationSeq.rw_one: kObservationSeq → kObservationSeq → Prop
    | eqe_left {a b c : kObservationSeq} : a.eqe b → kObservationSeq.rw_one b c → kObservationSeq.rw_one a c
    | eqe_right {a b c : kObservationSeq} : kObservationSeq.rw_one a b → b.eqe c → kObservationSeq.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_ocons₀ {a₁ a b} : kObservation.rw_one a b →
    kObservationSeq.rw_one (kObservationSeq.ocons a a₁) (kObservationSeq.ocons b a₁)
    | sub_ocons₁ {a₀ a b} : kObservationSeq.rw_one a b →
    kObservationSeq.rw_one (kObservationSeq.ocons a₀ a) (kObservationSeq.ocons a₀ b)

  inductive kArityTable.rw_one: kArityTable → kArityTable → Prop
    | eqe_left {a b c : kArityTable} : a.eqe b → kArityTable.rw_one b c → kArityTable.rw_one a c
    | eqe_right {a b c : kArityTable} : kArityTable.rw_one a b → b.eqe c → kArityTable.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_acons₀ {a₁ a b} : kArityEntry.rw_one a b →
    kArityTable.rw_one (kArityTable.acons a a₁) (kArityTable.acons b a₁)
    | sub_acons₁ {a₀ a b} : kArityTable.rw_one a b →
    kArityTable.rw_one (kArityTable.acons a₀ a) (kArityTable.acons a₀ b)

  inductive MRat.rw_one: MRat → MRat → Prop
    | eqe_left {a b c : MRat} : a = b → MRat.rw_one b c → MRat.rw_one a c
    | eqe_right {a b c : MRat} : MRat.rw_one a b → b = c → MRat.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_modExp₀ {a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.modExp a a₁ a₂) (MRat.modExp b a₁ a₂)
    | sub_modExp₁ {a₀ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.modExp a₀ a a₂) (MRat.modExp a₀ b a₂)
    | sub_modExp₂ {a₀ a₁ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.modExp a₀ a₁ a) (MRat.modExp a₀ a₁ b)
    | sub_trunc {a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.trunc a) (MRat.trunc b)
    | sub_frac {a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.frac a) (MRat.frac b)
    | sub_floor {a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.floor a) (MRat.floor b)
    | sub_ceiling {a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ceiling a) (MRat.ceiling b)
    | sub_ratOf {a b} : kXReal.rw_one a b →
    MRat.rw_one (MRat.ratOf a) (MRat.ratOf b)
    | sub_xSign {a b} : kXReal.rw_one a b →
    MRat.rw_one (MRat.xSign a) (MRat.xSign b)
    | sub_pow2 {a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.pow2 a) (MRat.pow2 b)
    | sub_floorLog2 {a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.floorLog2 a) (MRat.floorLog2 b)
    | sub_nearestEvenInteger {a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.nearestEvenInteger a) (MRat.nearestEvenInteger b)
    | sub_integerSqrt {a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.integerSqrt a) (MRat.integerSqrt b)
    | sub_sqrtSearch₀ {a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.sqrtSearch a a₁ a₂) (MRat.sqrtSearch b a₁ a₂)
    | sub_sqrtSearch₁ {a₀ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.sqrtSearch a₀ a a₂) (MRat.sqrtSearch a₀ b a₂)
    | sub_sqrtSearch₂ {a₀ a₁ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.sqrtSearch a₀ a₁ a) (MRat.sqrtSearch a₀ a₁ b)
    | sub_BitwidthOf {a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.BitwidthOf a) (MRat.BitwidthOf b)
    | sub_PrecisionOf {a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.PrecisionOf a) (MRat.PrecisionOf b)
    | sub_ExponentBitwidthOf {a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ExponentBitwidthOf a) (MRat.ExponentBitwidthOf b)
    | sub_TrailingSignificandBitwidthOf {a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.TrailingSignificandBitwidthOf a) (MRat.TrailingSignificandBitwidthOf b)
    | sub_ExponentBiasOf {a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ExponentBiasOf a) (MRat.ExponentBiasOf b)
    | sub_externalEncode₀ {a₁ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.externalEncode a a₁) (MRat.externalEncode b a₁)
    | sub_externalEncode₁ {a₀ a b} : kXReal.rw_one a b →
    MRat.rw_one (MRat.externalEncode a₀ a) (MRat.externalEncode a₀ b)
    | sub_externalBound₀ {a₁ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.externalBound a a₁) (MRat.externalBound b a₁)
    | sub_externalBound₁ {a₀ a b} : kBoundQuery.rw_one a b →
    MRat.rw_one (MRat.externalBound a₀ a) (MRat.externalBound a₀ b)
    | sub_nanCode {a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.nanCode a) (MRat.nanCode b)
    | sub_positiveLimit {a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.positiveLimit a) (MRat.positiveLimit b)
    | sub_decodePositive₀ {a₁ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.decodePositive a a₁) (MRat.decodePositive b a₁)
    | sub_decodePositive₁ {a₀ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.decodePositive a₀ a) (MRat.decodePositive a₀ b)
    | sub_encode₀ {a₁ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.encode a a₁) (MRat.encode b a₁)
    | sub_encode₁ {a₀ a b} : kXReal.rw_one a b →
    MRat.rw_one (MRat.encode a₀ a) (MRat.encode a₀ b)
    | sub_magnitudeCode₀ {a₁ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.magnitudeCode a a₁) (MRat.magnitudeCode b a₁)
    | sub_magnitudeCode₁ {a₀ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.magnitudeCode a₀ a) (MRat.magnitudeCode a₀ b)
    | sub_MaxFiniteOf {a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MaxFiniteOf a) (MRat.MaxFiniteOf b)
    | sub_MinFiniteOf {a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MinFiniteOf a) (MRat.MinFiniteOf b)
    | sub_MinPositiveOf {a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MinPositiveOf a) (MRat.MinPositiveOf b)
    | sub_MaxSubnormalOf {a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MaxSubnormalOf a) (MRat.MaxSubnormalOf b)
    | sub_MinNormalOf {a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MinNormalOf a) (MRat.MinNormalOf b)
    | sub_length₀ {a b} : kRandomSeq.rw_one a b →
    MRat.rw_one (MRat.length₀ a) (MRat.length₀ b)
    | sub_at₀₀ {a₁ a b} : kRandomSeq.rw_one a b →
    MRat.rw_one (MRat.at₀ a a₁) (MRat.at₀ b a₁)
    | sub_at₀₁ {a₀ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.at₀ a₀ a) (MRat.at₀ a₀ b)
    | sub_roundScaled₀ {a₁ a₂ a₃ a₄ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.roundScaled a a₁ a₂ a₃ a₄ a₅) (MRat.roundScaled b a₁ a₂ a₃ a₄ a₅)
    | sub_roundScaled₁ {a₀ a₂ a₃ a₄ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.roundScaled a₀ a a₂ a₃ a₄ a₅) (MRat.roundScaled a₀ b a₂ a₃ a₄ a₅)
    | sub_roundScaled₂ {a₀ a₁ a₃ a₄ a₅ a b} : kBlockRoundMode.rw_one a b →
    MRat.rw_one (MRat.roundScaled a₀ a₁ a a₃ a₄ a₅) (MRat.roundScaled a₀ a₁ b a₃ a₄ a₅)
    | sub_roundScaled₃ {a₀ a₁ a₂ a₄ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.roundScaled a₀ a₁ a₂ a a₄ a₅) (MRat.roundScaled a₀ a₁ a₂ b a₄ a₅)
    | sub_roundScaled₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.roundScaled a₀ a₁ a₂ a₃ a a₅) (MRat.roundScaled a₀ a₁ a₂ a₃ b a₅)
    | sub_roundScaled₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.roundScaled a₀ a₁ a₂ a₃ a₄ a) (MRat.roundScaled a₀ a₁ a₂ a₃ a₄ b)
    | sub_project₀ {a₁ a₂ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.project a a₁ a₂) (MRat.project b a₁ a₂)
    | sub_project₁ {a₀ a₂ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.project a₀ a a₂) (MRat.project a₀ b a₂)
    | sub_project₂ {a₀ a₁ a b} : kXReal.rw_one a b →
    MRat.rw_one (MRat.project a₀ a₁ a) (MRat.project a₀ a₁ b)
    | sub_length₁ {a b} : kXSeq.rw_one a b →
    MRat.rw_one (MRat.length₁ a) (MRat.length₁ b)
    | sub_length₂ {a b} : kCodeSeq.rw_one a b →
    MRat.rw_one (MRat.length₂ a) (MRat.length₂ b)
    | sub_at₁₀ {a₁ a b} : kCodeSeq.rw_one a b →
    MRat.rw_one (MRat.at₁ a a₁) (MRat.at₁ b a₁)
    | sub_at₁₁ {a₀ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.at₁ a₀ a) (MRat.at₁ a₀ b)
    | sub_scaledResult {a b} : kBlock.rw_one a b →
    MRat.rw_one (MRat.scaledResult a) (MRat.scaledResult b)
    | sub_ascii {a b} : MString.rw_one a b →
    MRat.rw_one (MRat.ascii a) (MRat.ascii b)
    | sub_find₀ {a₁ a₂ a b} : MString.rw_one a b →
    MRat.rw_one (MRat.find a a₁ a₂) (MRat.find b a₁ a₂)
    | sub_find₁ {a₀ a₂ a b} : MString.rw_one a b →
    MRat.rw_one (MRat.find a₀ a a₂) (MRat.find a₀ b a₂)
    | sub_find₂ {a₀ a₁ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.find a₀ a₁ a) (MRat.find a₀ a₁ b)
    | sub_rfind₀ {a₁ a₂ a b} : MString.rw_one a b →
    MRat.rw_one (MRat.rfind a a₁ a₂) (MRat.rfind b a₁ a₂)
    | sub_rfind₁ {a₀ a₂ a b} : MString.rw_one a b →
    MRat.rw_one (MRat.rfind a₀ a a₂) (MRat.rfind a₀ b a₂)
    | sub_rfind₂ {a₀ a₁ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.rfind a₀ a₁ a) (MRat.rfind a₀ a₁ b)
    | sub_length₄ {a b} : kFormatSeq.rw_one a b →
    MRat.rw_one (MRat.length₄ a) (MRat.length₄ b)
    | sub_length₅ {a b} : kKappaPartSeq.rw_one a b →
    MRat.rw_one (MRat.length₅ a) (MRat.length₅ b)
    | sub_length₆ {a b} : kPartitionSeq.rw_one a b →
    MRat.rw_one (MRat.length₆ a) (MRat.length₆ b)
    | sub_length₇ {a b} : kDeclarationSeq.rw_one a b →
    MRat.rw_one (MRat.length₇ a) (MRat.length₇ b)
    | sub_length₈ {a b} : kSpecializationSeq.rw_one a b →
    MRat.rw_one (MRat.length₈ a) (MRat.length₈ b)
    | sub_length₉ {a b} : kObservationSeq.rw_one a b →
    MRat.rw_one (MRat.length₉ a) (MRat.length₉ b)
    | sub_length₁₀ {a b} : kArityTable.rw_one a b →
    MRat.rw_one (MRat.length₁₀ a) (MRat.length₁₀ b)
    | sub_finiteRank₀ {a₁ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.finiteRank a a₁) (MRat.finiteRank b a₁)
    | sub_finiteRank₁ {a₀ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.finiteRank a₀ a) (MRat.finiteRank a₀ b)
    | sub_Convert₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Convert a a₁ a₂ a₃) (MRat.Convert b a₁ a₂ a₃)
    | sub_Convert₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Convert a₀ a a₂ a₃) (MRat.Convert a₀ b a₂ a₃)
    | sub_Convert₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Convert a₀ a₁ a a₃) (MRat.Convert a₀ a₁ b a₃)
    | sub_Convert₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Convert a₀ a₁ a₂ a) (MRat.Convert a₀ a₁ a₂ b)
    | sub_Abs₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Abs a a₁ a₂ a₃) (MRat.Abs b a₁ a₂ a₃)
    | sub_Abs₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Abs a₀ a a₂ a₃) (MRat.Abs a₀ b a₂ a₃)
    | sub_Abs₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Abs a₀ a₁ a a₃) (MRat.Abs a₀ a₁ b a₃)
    | sub_Abs₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Abs a₀ a₁ a₂ a) (MRat.Abs a₀ a₁ a₂ b)
    | sub_Negate₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Negate a a₁ a₂ a₃) (MRat.Negate b a₁ a₂ a₃)
    | sub_Negate₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Negate a₀ a a₂ a₃) (MRat.Negate a₀ b a₂ a₃)
    | sub_Negate₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Negate a₀ a₁ a a₃) (MRat.Negate a₀ a₁ b a₃)
    | sub_Negate₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Negate a₀ a₁ a₂ a) (MRat.Negate a₀ a₁ a₂ b)
    | sub_CopySign₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.CopySign a a₁ a₂ a₃ a₄ a₅) (MRat.CopySign b a₁ a₂ a₃ a₄ a₅)
    | sub_CopySign₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.CopySign a₀ a a₂ a₃ a₄ a₅) (MRat.CopySign a₀ b a₂ a₃ a₄ a₅)
    | sub_CopySign₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.CopySign a₀ a₁ a a₃ a₄ a₅) (MRat.CopySign a₀ a₁ b a₃ a₄ a₅)
    | sub_CopySign₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.CopySign a₀ a₁ a₂ a a₄ a₅) (MRat.CopySign a₀ a₁ a₂ b a₄ a₅)
    | sub_CopySign₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.CopySign a₀ a₁ a₂ a₃ a a₅) (MRat.CopySign a₀ a₁ a₂ a₃ b a₅)
    | sub_CopySign₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.CopySign a₀ a₁ a₂ a₃ a₄ a) (MRat.CopySign a₀ a₁ a₂ a₃ a₄ b)
    | sub_Add₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Add a a₁ a₂ a₃ a₄ a₅) (MRat.Add b a₁ a₂ a₃ a₄ a₅)
    | sub_Add₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Add a₀ a a₂ a₃ a₄ a₅) (MRat.Add a₀ b a₂ a₃ a₄ a₅)
    | sub_Add₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Add a₀ a₁ a a₃ a₄ a₅) (MRat.Add a₀ a₁ b a₃ a₄ a₅)
    | sub_Add₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Add a₀ a₁ a₂ a a₄ a₅) (MRat.Add a₀ a₁ a₂ b a₄ a₅)
    | sub_Add₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Add a₀ a₁ a₂ a₃ a a₅) (MRat.Add a₀ a₁ a₂ a₃ b a₅)
    | sub_Add₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Add a₀ a₁ a₂ a₃ a₄ a) (MRat.Add a₀ a₁ a₂ a₃ a₄ b)
    | sub_Subtract₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Subtract a a₁ a₂ a₃ a₄ a₅) (MRat.Subtract b a₁ a₂ a₃ a₄ a₅)
    | sub_Subtract₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Subtract a₀ a a₂ a₃ a₄ a₅) (MRat.Subtract a₀ b a₂ a₃ a₄ a₅)
    | sub_Subtract₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Subtract a₀ a₁ a a₃ a₄ a₅) (MRat.Subtract a₀ a₁ b a₃ a₄ a₅)
    | sub_Subtract₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Subtract a₀ a₁ a₂ a a₄ a₅) (MRat.Subtract a₀ a₁ a₂ b a₄ a₅)
    | sub_Subtract₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Subtract a₀ a₁ a₂ a₃ a a₅) (MRat.Subtract a₀ a₁ a₂ a₃ b a₅)
    | sub_Subtract₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Subtract a₀ a₁ a₂ a₃ a₄ a) (MRat.Subtract a₀ a₁ a₂ a₃ a₄ b)
    | sub_Multiply₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Multiply a a₁ a₂ a₃ a₄ a₅) (MRat.Multiply b a₁ a₂ a₃ a₄ a₅)
    | sub_Multiply₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Multiply a₀ a a₂ a₃ a₄ a₅) (MRat.Multiply a₀ b a₂ a₃ a₄ a₅)
    | sub_Multiply₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Multiply a₀ a₁ a a₃ a₄ a₅) (MRat.Multiply a₀ a₁ b a₃ a₄ a₅)
    | sub_Multiply₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Multiply a₀ a₁ a₂ a a₄ a₅) (MRat.Multiply a₀ a₁ a₂ b a₄ a₅)
    | sub_Multiply₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Multiply a₀ a₁ a₂ a₃ a a₅) (MRat.Multiply a₀ a₁ a₂ a₃ b a₅)
    | sub_Multiply₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Multiply a₀ a₁ a₂ a₃ a₄ a) (MRat.Multiply a₀ a₁ a₂ a₃ a₄ b)
    | sub_Divide₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Divide a a₁ a₂ a₃ a₄ a₅) (MRat.Divide b a₁ a₂ a₃ a₄ a₅)
    | sub_Divide₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Divide a₀ a a₂ a₃ a₄ a₅) (MRat.Divide a₀ b a₂ a₃ a₄ a₅)
    | sub_Divide₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Divide a₀ a₁ a a₃ a₄ a₅) (MRat.Divide a₀ a₁ b a₃ a₄ a₅)
    | sub_Divide₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Divide a₀ a₁ a₂ a a₄ a₅) (MRat.Divide a₀ a₁ a₂ b a₄ a₅)
    | sub_Divide₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Divide a₀ a₁ a₂ a₃ a a₅) (MRat.Divide a₀ a₁ a₂ a₃ b a₅)
    | sub_Divide₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Divide a₀ a₁ a₂ a₃ a₄ a) (MRat.Divide a₀ a₁ a₂ a₃ a₄ b)
    | sub_FMA₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.FMA a a₁ a₂ a₃ a₄ a₅ a₆ a₇) (MRat.FMA b a₁ a₂ a₃ a₄ a₅ a₆ a₇)
    | sub_FMA₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.FMA a₀ a a₂ a₃ a₄ a₅ a₆ a₇) (MRat.FMA a₀ b a₂ a₃ a₄ a₅ a₆ a₇)
    | sub_FMA₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.FMA a₀ a₁ a a₃ a₄ a₅ a₆ a₇) (MRat.FMA a₀ a₁ b a₃ a₄ a₅ a₆ a₇)
    | sub_FMA₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.FMA a₀ a₁ a₂ a a₄ a₅ a₆ a₇) (MRat.FMA a₀ a₁ a₂ b a₄ a₅ a₆ a₇)
    | sub_FMA₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.FMA a₀ a₁ a₂ a₃ a a₅ a₆ a₇) (MRat.FMA a₀ a₁ a₂ a₃ b a₅ a₆ a₇)
    | sub_FMA₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.FMA a₀ a₁ a₂ a₃ a₄ a a₆ a₇) (MRat.FMA a₀ a₁ a₂ a₃ a₄ b a₆ a₇)
    | sub_FMA₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.FMA a₀ a₁ a₂ a₃ a₄ a₅ a a₇) (MRat.FMA a₀ a₁ a₂ a₃ a₄ a₅ b a₇)
    | sub_FMA₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.FMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a) (MRat.FMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ b)
    | sub_FAA₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.FAA a a₁ a₂ a₃ a₄ a₅ a₆ a₇) (MRat.FAA b a₁ a₂ a₃ a₄ a₅ a₆ a₇)
    | sub_FAA₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.FAA a₀ a a₂ a₃ a₄ a₅ a₆ a₇) (MRat.FAA a₀ b a₂ a₃ a₄ a₅ a₆ a₇)
    | sub_FAA₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.FAA a₀ a₁ a a₃ a₄ a₅ a₆ a₇) (MRat.FAA a₀ a₁ b a₃ a₄ a₅ a₆ a₇)
    | sub_FAA₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.FAA a₀ a₁ a₂ a a₄ a₅ a₆ a₇) (MRat.FAA a₀ a₁ a₂ b a₄ a₅ a₆ a₇)
    | sub_FAA₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.FAA a₀ a₁ a₂ a₃ a a₅ a₆ a₇) (MRat.FAA a₀ a₁ a₂ a₃ b a₅ a₆ a₇)
    | sub_FAA₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.FAA a₀ a₁ a₂ a₃ a₄ a a₆ a₇) (MRat.FAA a₀ a₁ a₂ a₃ a₄ b a₆ a₇)
    | sub_FAA₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.FAA a₀ a₁ a₂ a₃ a₄ a₅ a a₇) (MRat.FAA a₀ a₁ a₂ a₃ a₄ a₅ b a₇)
    | sub_FAA₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.FAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a) (MRat.FAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ b)
    | sub_Recip₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Recip a a₁ a₂ a₃) (MRat.Recip b a₁ a₂ a₃)
    | sub_Recip₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Recip a₀ a a₂ a₃) (MRat.Recip a₀ b a₂ a₃)
    | sub_Recip₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Recip a₀ a₁ a a₃) (MRat.Recip a₀ a₁ b a₃)
    | sub_Recip₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Recip a₀ a₁ a₂ a) (MRat.Recip a₀ a₁ a₂ b)
    | sub_Minimum₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Minimum a a₁ a₂ a₃ a₄ a₅) (MRat.Minimum b a₁ a₂ a₃ a₄ a₅)
    | sub_Minimum₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Minimum a₀ a a₂ a₃ a₄ a₅) (MRat.Minimum a₀ b a₂ a₃ a₄ a₅)
    | sub_Minimum₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Minimum a₀ a₁ a a₃ a₄ a₅) (MRat.Minimum a₀ a₁ b a₃ a₄ a₅)
    | sub_Minimum₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Minimum a₀ a₁ a₂ a a₄ a₅) (MRat.Minimum a₀ a₁ a₂ b a₄ a₅)
    | sub_Minimum₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Minimum a₀ a₁ a₂ a₃ a a₅) (MRat.Minimum a₀ a₁ a₂ a₃ b a₅)
    | sub_Minimum₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Minimum a₀ a₁ a₂ a₃ a₄ a) (MRat.Minimum a₀ a₁ a₂ a₃ a₄ b)
    | sub_Maximum₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Maximum a a₁ a₂ a₃ a₄ a₅) (MRat.Maximum b a₁ a₂ a₃ a₄ a₅)
    | sub_Maximum₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Maximum a₀ a a₂ a₃ a₄ a₅) (MRat.Maximum a₀ b a₂ a₃ a₄ a₅)
    | sub_Maximum₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Maximum a₀ a₁ a a₃ a₄ a₅) (MRat.Maximum a₀ a₁ b a₃ a₄ a₅)
    | sub_Maximum₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Maximum a₀ a₁ a₂ a a₄ a₅) (MRat.Maximum a₀ a₁ a₂ b a₄ a₅)
    | sub_Maximum₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Maximum a₀ a₁ a₂ a₃ a a₅) (MRat.Maximum a₀ a₁ a₂ a₃ b a₅)
    | sub_Maximum₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Maximum a₀ a₁ a₂ a₃ a₄ a) (MRat.Maximum a₀ a₁ a₂ a₃ a₄ b)
    | sub_MinimumNumber₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MinimumNumber a a₁ a₂ a₃ a₄ a₅) (MRat.MinimumNumber b a₁ a₂ a₃ a₄ a₅)
    | sub_MinimumNumber₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MinimumNumber a₀ a a₂ a₃ a₄ a₅) (MRat.MinimumNumber a₀ b a₂ a₃ a₄ a₅)
    | sub_MinimumNumber₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MinimumNumber a₀ a₁ a a₃ a₄ a₅) (MRat.MinimumNumber a₀ a₁ b a₃ a₄ a₅)
    | sub_MinimumNumber₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.MinimumNumber a₀ a₁ a₂ a a₄ a₅) (MRat.MinimumNumber a₀ a₁ a₂ b a₄ a₅)
    | sub_MinimumNumber₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.MinimumNumber a₀ a₁ a₂ a₃ a a₅) (MRat.MinimumNumber a₀ a₁ a₂ a₃ b a₅)
    | sub_MinimumNumber₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.MinimumNumber a₀ a₁ a₂ a₃ a₄ a) (MRat.MinimumNumber a₀ a₁ a₂ a₃ a₄ b)
    | sub_MaximumNumber₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MaximumNumber a a₁ a₂ a₃ a₄ a₅) (MRat.MaximumNumber b a₁ a₂ a₃ a₄ a₅)
    | sub_MaximumNumber₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MaximumNumber a₀ a a₂ a₃ a₄ a₅) (MRat.MaximumNumber a₀ b a₂ a₃ a₄ a₅)
    | sub_MaximumNumber₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MaximumNumber a₀ a₁ a a₃ a₄ a₅) (MRat.MaximumNumber a₀ a₁ b a₃ a₄ a₅)
    | sub_MaximumNumber₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.MaximumNumber a₀ a₁ a₂ a a₄ a₅) (MRat.MaximumNumber a₀ a₁ a₂ b a₄ a₅)
    | sub_MaximumNumber₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.MaximumNumber a₀ a₁ a₂ a₃ a a₅) (MRat.MaximumNumber a₀ a₁ a₂ a₃ b a₅)
    | sub_MaximumNumber₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.MaximumNumber a₀ a₁ a₂ a₃ a₄ a) (MRat.MaximumNumber a₀ a₁ a₂ a₃ a₄ b)
    | sub_MinimumMagnitude₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MinimumMagnitude a a₁ a₂ a₃ a₄ a₅) (MRat.MinimumMagnitude b a₁ a₂ a₃ a₄ a₅)
    | sub_MinimumMagnitude₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MinimumMagnitude a₀ a a₂ a₃ a₄ a₅) (MRat.MinimumMagnitude a₀ b a₂ a₃ a₄ a₅)
    | sub_MinimumMagnitude₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MinimumMagnitude a₀ a₁ a a₃ a₄ a₅) (MRat.MinimumMagnitude a₀ a₁ b a₃ a₄ a₅)
    | sub_MinimumMagnitude₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.MinimumMagnitude a₀ a₁ a₂ a a₄ a₅) (MRat.MinimumMagnitude a₀ a₁ a₂ b a₄ a₅)
    | sub_MinimumMagnitude₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.MinimumMagnitude a₀ a₁ a₂ a₃ a a₅) (MRat.MinimumMagnitude a₀ a₁ a₂ a₃ b a₅)
    | sub_MinimumMagnitude₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.MinimumMagnitude a₀ a₁ a₂ a₃ a₄ a) (MRat.MinimumMagnitude a₀ a₁ a₂ a₃ a₄ b)
    | sub_MaximumMagnitude₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MaximumMagnitude a a₁ a₂ a₃ a₄ a₅) (MRat.MaximumMagnitude b a₁ a₂ a₃ a₄ a₅)
    | sub_MaximumMagnitude₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MaximumMagnitude a₀ a a₂ a₃ a₄ a₅) (MRat.MaximumMagnitude a₀ b a₂ a₃ a₄ a₅)
    | sub_MaximumMagnitude₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MaximumMagnitude a₀ a₁ a a₃ a₄ a₅) (MRat.MaximumMagnitude a₀ a₁ b a₃ a₄ a₅)
    | sub_MaximumMagnitude₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.MaximumMagnitude a₀ a₁ a₂ a a₄ a₅) (MRat.MaximumMagnitude a₀ a₁ a₂ b a₄ a₅)
    | sub_MaximumMagnitude₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.MaximumMagnitude a₀ a₁ a₂ a₃ a a₅) (MRat.MaximumMagnitude a₀ a₁ a₂ a₃ b a₅)
    | sub_MaximumMagnitude₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.MaximumMagnitude a₀ a₁ a₂ a₃ a₄ a) (MRat.MaximumMagnitude a₀ a₁ a₂ a₃ a₄ b)
    | sub_MinimumMagnitudeNumber₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MinimumMagnitudeNumber a a₁ a₂ a₃ a₄ a₅) (MRat.MinimumMagnitudeNumber b a₁ a₂ a₃ a₄ a₅)
    | sub_MinimumMagnitudeNumber₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MinimumMagnitudeNumber a₀ a a₂ a₃ a₄ a₅) (MRat.MinimumMagnitudeNumber a₀ b a₂ a₃ a₄ a₅)
    | sub_MinimumMagnitudeNumber₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MinimumMagnitudeNumber a₀ a₁ a a₃ a₄ a₅) (MRat.MinimumMagnitudeNumber a₀ a₁ b a₃ a₄ a₅)
    | sub_MinimumMagnitudeNumber₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.MinimumMagnitudeNumber a₀ a₁ a₂ a a₄ a₅) (MRat.MinimumMagnitudeNumber a₀ a₁ a₂ b a₄ a₅)
    | sub_MinimumMagnitudeNumber₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.MinimumMagnitudeNumber a₀ a₁ a₂ a₃ a a₅) (MRat.MinimumMagnitudeNumber a₀ a₁ a₂ a₃ b a₅)
    | sub_MinimumMagnitudeNumber₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.MinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a) (MRat.MinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ b)
    | sub_MaximumMagnitudeNumber₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MaximumMagnitudeNumber a a₁ a₂ a₃ a₄ a₅) (MRat.MaximumMagnitudeNumber b a₁ a₂ a₃ a₄ a₅)
    | sub_MaximumMagnitudeNumber₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MaximumMagnitudeNumber a₀ a a₂ a₃ a₄ a₅) (MRat.MaximumMagnitudeNumber a₀ b a₂ a₃ a₄ a₅)
    | sub_MaximumMagnitudeNumber₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MaximumMagnitudeNumber a₀ a₁ a a₃ a₄ a₅) (MRat.MaximumMagnitudeNumber a₀ a₁ b a₃ a₄ a₅)
    | sub_MaximumMagnitudeNumber₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.MaximumMagnitudeNumber a₀ a₁ a₂ a a₄ a₅) (MRat.MaximumMagnitudeNumber a₀ a₁ a₂ b a₄ a₅)
    | sub_MaximumMagnitudeNumber₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.MaximumMagnitudeNumber a₀ a₁ a₂ a₃ a a₅) (MRat.MaximumMagnitudeNumber a₀ a₁ a₂ a₃ b a₅)
    | sub_MaximumMagnitudeNumber₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.MaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a) (MRat.MaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ b)
    | sub_MinimumFinite₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MinimumFinite a a₁ a₂ a₃ a₄ a₅) (MRat.MinimumFinite b a₁ a₂ a₃ a₄ a₅)
    | sub_MinimumFinite₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MinimumFinite a₀ a a₂ a₃ a₄ a₅) (MRat.MinimumFinite a₀ b a₂ a₃ a₄ a₅)
    | sub_MinimumFinite₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MinimumFinite a₀ a₁ a a₃ a₄ a₅) (MRat.MinimumFinite a₀ a₁ b a₃ a₄ a₅)
    | sub_MinimumFinite₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.MinimumFinite a₀ a₁ a₂ a a₄ a₅) (MRat.MinimumFinite a₀ a₁ a₂ b a₄ a₅)
    | sub_MinimumFinite₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.MinimumFinite a₀ a₁ a₂ a₃ a a₅) (MRat.MinimumFinite a₀ a₁ a₂ a₃ b a₅)
    | sub_MinimumFinite₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.MinimumFinite a₀ a₁ a₂ a₃ a₄ a) (MRat.MinimumFinite a₀ a₁ a₂ a₃ a₄ b)
    | sub_MaximumFinite₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MaximumFinite a a₁ a₂ a₃ a₄ a₅) (MRat.MaximumFinite b a₁ a₂ a₃ a₄ a₅)
    | sub_MaximumFinite₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MaximumFinite a₀ a a₂ a₃ a₄ a₅) (MRat.MaximumFinite a₀ b a₂ a₃ a₄ a₅)
    | sub_MaximumFinite₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.MaximumFinite a₀ a₁ a a₃ a₄ a₅) (MRat.MaximumFinite a₀ a₁ b a₃ a₄ a₅)
    | sub_MaximumFinite₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.MaximumFinite a₀ a₁ a₂ a a₄ a₅) (MRat.MaximumFinite a₀ a₁ a₂ b a₄ a₅)
    | sub_MaximumFinite₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.MaximumFinite a₀ a₁ a₂ a₃ a a₅) (MRat.MaximumFinite a₀ a₁ a₂ a₃ b a₅)
    | sub_MaximumFinite₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.MaximumFinite a₀ a₁ a₂ a₃ a₄ a) (MRat.MaximumFinite a₀ a₁ a₂ a₃ a₄ b)
    | sub_Clamp₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Clamp a a₁ a₂ a₃ a₄ a₅ a₆ a₇) (MRat.Clamp b a₁ a₂ a₃ a₄ a₅ a₆ a₇)
    | sub_Clamp₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Clamp a₀ a a₂ a₃ a₄ a₅ a₆ a₇) (MRat.Clamp a₀ b a₂ a₃ a₄ a₅ a₆ a₇)
    | sub_Clamp₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Clamp a₀ a₁ a a₃ a₄ a₅ a₆ a₇) (MRat.Clamp a₀ a₁ b a₃ a₄ a₅ a₆ a₇)
    | sub_Clamp₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Clamp a₀ a₁ a₂ a a₄ a₅ a₆ a₇) (MRat.Clamp a₀ a₁ a₂ b a₄ a₅ a₆ a₇)
    | sub_Clamp₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Clamp a₀ a₁ a₂ a₃ a a₅ a₆ a₇) (MRat.Clamp a₀ a₁ a₂ a₃ b a₅ a₆ a₇)
    | sub_Clamp₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Clamp a₀ a₁ a₂ a₃ a₄ a a₆ a₇) (MRat.Clamp a₀ a₁ a₂ a₃ a₄ b a₆ a₇)
    | sub_Clamp₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Clamp a₀ a₁ a₂ a₃ a₄ a₅ a a₇) (MRat.Clamp a₀ a₁ a₂ a₃ a₄ a₅ b a₇)
    | sub_Clamp₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Clamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a) (MRat.Clamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ b)
    | sub_NextGreaterThan₀ {a₁ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.NextGreaterThan a a₁) (MRat.NextGreaterThan b a₁)
    | sub_NextGreaterThan₁ {a₀ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.NextGreaterThan a₀ a) (MRat.NextGreaterThan a₀ b)
    | sub_NextLessThan₀ {a₁ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.NextLessThan a a₁) (MRat.NextLessThan b a₁)
    | sub_NextLessThan₁ {a₀ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.NextLessThan a₀ a) (MRat.NextLessThan a₀ b)
    | sub_nextCode₀ {a₁ a₂ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.nextCode a a₁ a₂) (MRat.nextCode b a₁ a₂)
    | sub_nextCode₁ {a₀ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.nextCode a₀ a a₂) (MRat.nextCode a₀ b a₂)
    | sub_nextCode₂ {a₀ a₁ a b} : kBool.rw_one a b →
    MRat.rw_one (MRat.nextCode a₀ a₁ a) (MRat.nextCode a₀ a₁ b)
    | sub_BlockReduceAdd₀ {a₁ a₂ a₃ a₄ a₅ a₆ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.BlockReduceAdd a a₁ a₂ a₃ a₄ a₅ a₆) (MRat.BlockReduceAdd b a₁ a₂ a₃ a₄ a₅ a₆)
    | sub_BlockReduceAdd₁ {a₀ a₂ a₃ a₄ a₅ a₆ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.BlockReduceAdd a₀ a a₂ a₃ a₄ a₅ a₆) (MRat.BlockReduceAdd a₀ b a₂ a₃ a₄ a₅ a₆)
    | sub_BlockReduceAdd₂ {a₀ a₁ a₃ a₄ a₅ a₆ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.BlockReduceAdd a₀ a₁ a a₃ a₄ a₅ a₆) (MRat.BlockReduceAdd a₀ a₁ b a₃ a₄ a₅ a₆)
    | sub_BlockReduceAdd₃ {a₀ a₁ a₂ a₄ a₅ a₆ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.BlockReduceAdd a₀ a₁ a₂ a a₄ a₅ a₆) (MRat.BlockReduceAdd a₀ a₁ a₂ b a₄ a₅ a₆)
    | sub_BlockReduceAdd₄ {a₀ a₁ a₂ a₃ a₅ a₆ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.BlockReduceAdd a₀ a₁ a₂ a₃ a a₅ a₆) (MRat.BlockReduceAdd a₀ a₁ a₂ a₃ b a₅ a₆)
    | sub_BlockReduceAdd₅ {a₀ a₁ a₂ a₃ a₄ a₆ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.BlockReduceAdd a₀ a₁ a₂ a₃ a₄ a a₆) (MRat.BlockReduceAdd a₀ a₁ a₂ a₃ a₄ b a₆)
    | sub_BlockReduceAdd₆ {a₀ a₁ a₂ a₃ a₄ a₅ a b} : kCodeSeq.rw_one a b →
    MRat.rw_one (MRat.BlockReduceAdd a₀ a₁ a₂ a₃ a₄ a₅ a) (MRat.BlockReduceAdd a₀ a₁ a₂ a₃ a₄ a₅ b)
    | sub_BlockReduceMultiply₀ {a₁ a₂ a₃ a₄ a₅ a₆ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.BlockReduceMultiply a a₁ a₂ a₃ a₄ a₅ a₆) (MRat.BlockReduceMultiply b a₁ a₂ a₃ a₄ a₅ a₆)
    | sub_BlockReduceMultiply₁ {a₀ a₂ a₃ a₄ a₅ a₆ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.BlockReduceMultiply a₀ a a₂ a₃ a₄ a₅ a₆) (MRat.BlockReduceMultiply a₀ b a₂ a₃ a₄ a₅ a₆)
    | sub_BlockReduceMultiply₂ {a₀ a₁ a₃ a₄ a₅ a₆ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.BlockReduceMultiply a₀ a₁ a a₃ a₄ a₅ a₆) (MRat.BlockReduceMultiply a₀ a₁ b a₃ a₄ a₅ a₆)
    | sub_BlockReduceMultiply₃ {a₀ a₁ a₂ a₄ a₅ a₆ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.BlockReduceMultiply a₀ a₁ a₂ a a₄ a₅ a₆) (MRat.BlockReduceMultiply a₀ a₁ a₂ b a₄ a₅ a₆)
    | sub_BlockReduceMultiply₄ {a₀ a₁ a₂ a₃ a₅ a₆ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.BlockReduceMultiply a₀ a₁ a₂ a₃ a a₅ a₆) (MRat.BlockReduceMultiply a₀ a₁ a₂ a₃ b a₅ a₆)
    | sub_BlockReduceMultiply₅ {a₀ a₁ a₂ a₃ a₄ a₆ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.BlockReduceMultiply a₀ a₁ a₂ a₃ a₄ a a₆) (MRat.BlockReduceMultiply a₀ a₁ a₂ a₃ a₄ b a₆)
    | sub_BlockReduceMultiply₆ {a₀ a₁ a₂ a₃ a₄ a₅ a b} : kCodeSeq.rw_one a b →
    MRat.rw_one (MRat.BlockReduceMultiply a₀ a₁ a₂ a₃ a₄ a₅ a) (MRat.BlockReduceMultiply a₀ a₁ a₂ a₃ a₄ a₅ b)
    | sub_BlockDotProduct₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.BlockDotProduct a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀) (MRat.BlockDotProduct b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀)
    | sub_BlockDotProduct₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.BlockDotProduct a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀) (MRat.BlockDotProduct a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀)
    | sub_BlockDotProduct₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.BlockDotProduct a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀) (MRat.BlockDotProduct a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀)
    | sub_BlockDotProduct₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.BlockDotProduct a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀) (MRat.BlockDotProduct a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀)
    | sub_BlockDotProduct₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.BlockDotProduct a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀) (MRat.BlockDotProduct a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀)
    | sub_BlockDotProduct₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.BlockDotProduct a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀) (MRat.BlockDotProduct a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀)
    | sub_BlockDotProduct₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀) (MRat.BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀)
    | sub_BlockDotProduct₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀) (MRat.BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀)
    | sub_BlockDotProduct₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a b} : kCodeSeq.rw_one a b →
    MRat.rw_one (MRat.BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀) (MRat.BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀)
    | sub_BlockDotProduct₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀) (MRat.BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀)
    | sub_BlockDotProduct₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kCodeSeq.rw_one a b →
    MRat.rw_one (MRat.BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a) (MRat.BlockDotProduct a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b)
    | sub_ScaledConvert₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledConvert a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledConvert b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledConvert₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledConvert a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledConvert a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledConvert₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledConvert a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledConvert a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledConvert₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledConvert a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledConvert a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledConvert₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledConvert a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledConvert a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledConvert₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledConvert a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledConvert a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledAbs₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledAbs a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledAbs b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledAbs₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledAbs a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledAbs a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledAbs₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledAbs a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledAbs a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledAbs₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledAbs a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledAbs a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledAbs₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledAbs a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledAbs a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledAbs₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledAbs a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledAbs a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledNegate₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledNegate a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledNegate b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledNegate₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledNegate a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledNegate a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledNegate₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledNegate a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledNegate a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledNegate₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledNegate a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledNegate a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledNegate₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledNegate a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledNegate a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledNegate₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledNegate a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledNegate a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledCopySign₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledCopySign a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledCopySign b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledCopySign₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledCopySign a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledCopySign a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledCopySign₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledCopySign a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledCopySign a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledCopySign₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledCopySign a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledCopySign a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledCopySign₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledCopySign a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (MRat.ScaledCopySign a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledCopySign₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledCopySign a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (MRat.ScaledCopySign a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | sub_ScaledCopySign₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledCopySign a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (MRat.ScaledCopySign a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | sub_ScaledCopySign₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (MRat.ScaledCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | sub_ScaledCopySign₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (MRat.ScaledCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | sub_ScaledCopySign₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (MRat.ScaledCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | sub_ScaledAdd₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledAdd a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledAdd b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledAdd₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledAdd a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledAdd a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledAdd₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledAdd a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledAdd a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledAdd₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledAdd a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledAdd a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledAdd₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledAdd a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (MRat.ScaledAdd a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledAdd₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledAdd a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (MRat.ScaledAdd a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | sub_ScaledAdd₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledAdd a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (MRat.ScaledAdd a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | sub_ScaledAdd₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (MRat.ScaledAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | sub_ScaledAdd₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (MRat.ScaledAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | sub_ScaledAdd₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (MRat.ScaledAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | sub_ScaledSubtract₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSubtract a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledSubtract b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledSubtract₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSubtract a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledSubtract a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledSubtract₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSubtract a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledSubtract a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledSubtract₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSubtract a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledSubtract a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledSubtract₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSubtract a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (MRat.ScaledSubtract a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledSubtract₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledSubtract a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (MRat.ScaledSubtract a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | sub_ScaledSubtract₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledSubtract a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (MRat.ScaledSubtract a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | sub_ScaledSubtract₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (MRat.ScaledSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | sub_ScaledSubtract₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (MRat.ScaledSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | sub_ScaledSubtract₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (MRat.ScaledSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | sub_ScaledMultiply₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMultiply a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMultiply b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMultiply₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMultiply a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMultiply a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMultiply₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMultiply a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMultiply a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMultiply₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMultiply a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMultiply a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMultiply₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMultiply a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMultiply a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMultiply₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledMultiply a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (MRat.ScaledMultiply a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | sub_ScaledMultiply₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMultiply a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (MRat.ScaledMultiply a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | sub_ScaledMultiply₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (MRat.ScaledMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | sub_ScaledMultiply₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (MRat.ScaledMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | sub_ScaledMultiply₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (MRat.ScaledMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | sub_ScaledDivide₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledDivide a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledDivide b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledDivide₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledDivide a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledDivide a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledDivide₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledDivide a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledDivide a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledDivide₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledDivide a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledDivide a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledDivide₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledDivide a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (MRat.ScaledDivide a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledDivide₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledDivide a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (MRat.ScaledDivide a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | sub_ScaledDivide₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledDivide a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (MRat.ScaledDivide a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | sub_ScaledDivide₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (MRat.ScaledDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | sub_ScaledDivide₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (MRat.ScaledDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | sub_ScaledDivide₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (MRat.ScaledDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | sub_ScaledFMA₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledFMA a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFMA b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFMA₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledFMA a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFMA a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFMA₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledFMA a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFMA a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFMA₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledFMA a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFMA a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFMA₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledFMA a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFMA a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFMA₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledFMA a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFMA a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFMA₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFMA₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFMA₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFMA₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a₁₃ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFMA₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a₁₃ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂ a₁₃) (MRat.ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂ a₁₃)
    | sub_ScaledFMA₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a₁₃ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂ a₁₃) (MRat.ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂ a₁₃)
    | sub_ScaledFMA₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₃ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a a₁₃) (MRat.ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b a₁₃)
    | sub_ScaledFMA₁₃ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a) (MRat.ScaledFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b)
    | sub_ScaledFAA₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledFAA a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFAA b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFAA₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledFAA a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFAA a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFAA₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledFAA a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFAA a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFAA₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledFAA a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFAA a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFAA₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledFAA a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFAA a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFAA₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledFAA a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFAA a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFAA₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFAA₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFAA₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFAA₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a₁₃ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledFAA₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a₁₃ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂ a₁₃) (MRat.ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂ a₁₃)
    | sub_ScaledFAA₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a₁₃ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂ a₁₃) (MRat.ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂ a₁₃)
    | sub_ScaledFAA₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₃ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a a₁₃) (MRat.ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b a₁₃)
    | sub_ScaledFAA₁₃ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a) (MRat.ScaledFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b)
    | sub_ScaledRecip₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledRecip a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledRecip b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledRecip₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledRecip a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledRecip a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledRecip₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledRecip a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledRecip a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledRecip₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledRecip a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledRecip a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledRecip₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledRecip a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledRecip a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledRecip₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledRecip a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledRecip a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledMinimum₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimum a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimum b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimum₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimum a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimum a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimum₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimum a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimum a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimum₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimum a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimum a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimum₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimum a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimum a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimum₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimum a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (MRat.ScaledMinimum a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | sub_ScaledMinimum₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimum a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (MRat.ScaledMinimum a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | sub_ScaledMinimum₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (MRat.ScaledMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | sub_ScaledMinimum₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (MRat.ScaledMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | sub_ScaledMinimum₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (MRat.ScaledMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | sub_ScaledMaximum₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximum a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximum b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximum₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximum a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximum a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximum₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximum a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximum a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximum₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximum a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximum a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximum₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximum a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximum a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximum₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximum a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (MRat.ScaledMaximum a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | sub_ScaledMaximum₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximum a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (MRat.ScaledMaximum a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | sub_ScaledMaximum₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (MRat.ScaledMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | sub_ScaledMaximum₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (MRat.ScaledMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | sub_ScaledMaximum₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (MRat.ScaledMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | sub_ScaledMinimumNumber₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumNumber a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumNumber b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumNumber₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumNumber a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumNumber a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumNumber₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumNumber a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumNumber a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumNumber₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumNumber a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumNumber a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumNumber₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumNumber a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumNumber a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumNumber₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (MRat.ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumNumber₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (MRat.ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | sub_ScaledMinimumNumber₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (MRat.ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | sub_ScaledMinimumNumber₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (MRat.ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | sub_ScaledMinimumNumber₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (MRat.ScaledMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | sub_ScaledMaximumNumber₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumNumber a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumNumber b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumNumber₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumNumber a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumNumber a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumNumber₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumNumber a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumNumber a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumNumber₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumNumber a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumNumber a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumNumber₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumNumber a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumNumber a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumNumber₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (MRat.ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumNumber₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (MRat.ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | sub_ScaledMaximumNumber₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (MRat.ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | sub_ScaledMaximumNumber₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (MRat.ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | sub_ScaledMaximumNumber₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (MRat.ScaledMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | sub_ScaledMinimumMagnitude₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitude a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumMagnitude b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumMagnitude₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitude a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumMagnitude a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumMagnitude₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitude a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumMagnitude a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumMagnitude₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitude a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumMagnitude a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumMagnitude₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumMagnitude a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumMagnitude₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (MRat.ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumMagnitude₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (MRat.ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | sub_ScaledMinimumMagnitude₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (MRat.ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | sub_ScaledMinimumMagnitude₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (MRat.ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | sub_ScaledMinimumMagnitude₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (MRat.ScaledMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | sub_ScaledMaximumMagnitude₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitude a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumMagnitude b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumMagnitude₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitude a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumMagnitude a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumMagnitude₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitude a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumMagnitude a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumMagnitude₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitude a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumMagnitude a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumMagnitude₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumMagnitude a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumMagnitude₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (MRat.ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumMagnitude₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (MRat.ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | sub_ScaledMaximumMagnitude₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (MRat.ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | sub_ScaledMaximumMagnitude₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (MRat.ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | sub_ScaledMaximumMagnitude₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (MRat.ScaledMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | sub_ScaledMinimumMagnitudeNumber₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitudeNumber a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumMagnitudeNumber b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumMagnitudeNumber₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitudeNumber a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumMagnitudeNumber a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumMagnitudeNumber₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitudeNumber a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumMagnitudeNumber a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumMagnitudeNumber₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumMagnitudeNumber a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumMagnitudeNumber₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumMagnitudeNumber₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (MRat.ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumMagnitudeNumber₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (MRat.ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | sub_ScaledMinimumMagnitudeNumber₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (MRat.ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | sub_ScaledMinimumMagnitudeNumber₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (MRat.ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | sub_ScaledMinimumMagnitudeNumber₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (MRat.ScaledMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | sub_ScaledMaximumMagnitudeNumber₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitudeNumber a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumMagnitudeNumber b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumMagnitudeNumber₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitudeNumber a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumMagnitudeNumber a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumMagnitudeNumber₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitudeNumber a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumMagnitudeNumber a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumMagnitudeNumber₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumMagnitudeNumber a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumMagnitudeNumber₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumMagnitudeNumber₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (MRat.ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumMagnitudeNumber₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (MRat.ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | sub_ScaledMaximumMagnitudeNumber₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (MRat.ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | sub_ScaledMaximumMagnitudeNumber₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (MRat.ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | sub_ScaledMaximumMagnitudeNumber₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (MRat.ScaledMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | sub_ScaledMinimumFinite₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumFinite a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumFinite b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumFinite₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumFinite a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumFinite a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumFinite₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumFinite a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumFinite a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumFinite₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumFinite a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumFinite a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumFinite₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumFinite a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMinimumFinite a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumFinite₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (MRat.ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | sub_ScaledMinimumFinite₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (MRat.ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | sub_ScaledMinimumFinite₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (MRat.ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | sub_ScaledMinimumFinite₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (MRat.ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | sub_ScaledMinimumFinite₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (MRat.ScaledMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | sub_ScaledMaximumFinite₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumFinite a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumFinite b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumFinite₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumFinite a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumFinite a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumFinite₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumFinite a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumFinite a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumFinite₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumFinite a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumFinite a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumFinite₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumFinite a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (MRat.ScaledMaximumFinite a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumFinite₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (MRat.ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | sub_ScaledMaximumFinite₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (MRat.ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | sub_ScaledMaximumFinite₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (MRat.ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | sub_ScaledMaximumFinite₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (MRat.ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | sub_ScaledMaximumFinite₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (MRat.ScaledMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | sub_ScaledClamp₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledClamp a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledClamp b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledClamp₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledClamp a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledClamp a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledClamp₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledClamp a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledClamp a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledClamp₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledClamp a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledClamp a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledClamp₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledClamp a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledClamp a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledClamp₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledClamp a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledClamp a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledClamp₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledClamp₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledClamp₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledClamp₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₁₀ a₁₁ a₁₂ a₁₃ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂ a₁₃) (MRat.ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂ a₁₃)
    | sub_ScaledClamp₁₀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₁ a₁₂ a₁₃ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂ a₁₃) (MRat.ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂ a₁₃)
    | sub_ScaledClamp₁₁ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₂ a₁₃ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂ a₁₃) (MRat.ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂ a₁₃)
    | sub_ScaledClamp₁₂ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₃ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a a₁₃) (MRat.ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b a₁₃)
    | sub_ScaledClamp₁₃ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a) (MRat.ScaledClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b)
    | sub_numeratorOf {a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.numeratorOf a) (MRat.numeratorOf b)
    | sub_denominatorOf {a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.denominatorOf a) (MRat.denominatorOf b)
    | sub_Sqrt₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Sqrt a a₁ a₂ a₃) (MRat.Sqrt b a₁ a₂ a₃)
    | sub_Sqrt₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Sqrt a₀ a a₂ a₃) (MRat.Sqrt a₀ b a₂ a₃)
    | sub_Sqrt₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Sqrt a₀ a₁ a a₃) (MRat.Sqrt a₀ a₁ b a₃)
    | sub_Sqrt₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Sqrt a₀ a₁ a₂ a) (MRat.Sqrt a₀ a₁ a₂ b)
    | sub_RSqrt₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.RSqrt a a₁ a₂ a₃) (MRat.RSqrt b a₁ a₂ a₃)
    | sub_RSqrt₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.RSqrt a₀ a a₂ a₃) (MRat.RSqrt a₀ b a₂ a₃)
    | sub_RSqrt₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.RSqrt a₀ a₁ a a₃) (MRat.RSqrt a₀ a₁ b a₃)
    | sub_RSqrt₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.RSqrt a₀ a₁ a₂ a) (MRat.RSqrt a₀ a₁ a₂ b)
    | sub_Exp₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Exp a a₁ a₂ a₃) (MRat.Exp b a₁ a₂ a₃)
    | sub_Exp₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Exp a₀ a a₂ a₃) (MRat.Exp a₀ b a₂ a₃)
    | sub_Exp₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Exp a₀ a₁ a a₃) (MRat.Exp a₀ a₁ b a₃)
    | sub_Exp₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Exp a₀ a₁ a₂ a) (MRat.Exp a₀ a₁ a₂ b)
    | sub_Exp2₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Exp2 a a₁ a₂ a₃) (MRat.Exp2 b a₁ a₂ a₃)
    | sub_Exp2₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Exp2 a₀ a a₂ a₃) (MRat.Exp2 a₀ b a₂ a₃)
    | sub_Exp2₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Exp2 a₀ a₁ a a₃) (MRat.Exp2 a₀ a₁ b a₃)
    | sub_Exp2₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Exp2 a₀ a₁ a₂ a) (MRat.Exp2 a₀ a₁ a₂ b)
    | sub_Log₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Log a a₁ a₂ a₃) (MRat.Log b a₁ a₂ a₃)
    | sub_Log₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Log a₀ a a₂ a₃) (MRat.Log a₀ b a₂ a₃)
    | sub_Log₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Log a₀ a₁ a a₃) (MRat.Log a₀ a₁ b a₃)
    | sub_Log₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Log a₀ a₁ a₂ a) (MRat.Log a₀ a₁ a₂ b)
    | sub_Log2₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Log2 a a₁ a₂ a₃) (MRat.Log2 b a₁ a₂ a₃)
    | sub_Log2₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Log2 a₀ a a₂ a₃) (MRat.Log2 a₀ b a₂ a₃)
    | sub_Log2₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Log2 a₀ a₁ a a₃) (MRat.Log2 a₀ a₁ b a₃)
    | sub_Log2₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Log2 a₀ a₁ a₂ a) (MRat.Log2 a₀ a₁ a₂ b)
    | sub_LogOnePlus₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.LogOnePlus a a₁ a₂ a₃) (MRat.LogOnePlus b a₁ a₂ a₃)
    | sub_LogOnePlus₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.LogOnePlus a₀ a a₂ a₃) (MRat.LogOnePlus a₀ b a₂ a₃)
    | sub_LogOnePlus₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.LogOnePlus a₀ a₁ a a₃) (MRat.LogOnePlus a₀ a₁ b a₃)
    | sub_LogOnePlus₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.LogOnePlus a₀ a₁ a₂ a) (MRat.LogOnePlus a₀ a₁ a₂ b)
    | sub_ExpMinusOne₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ExpMinusOne a a₁ a₂ a₃) (MRat.ExpMinusOne b a₁ a₂ a₃)
    | sub_ExpMinusOne₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ExpMinusOne a₀ a a₂ a₃) (MRat.ExpMinusOne a₀ b a₂ a₃)
    | sub_ExpMinusOne₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ExpMinusOne a₀ a₁ a a₃) (MRat.ExpMinusOne a₀ a₁ b a₃)
    | sub_ExpMinusOne₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ExpMinusOne a₀ a₁ a₂ a) (MRat.ExpMinusOne a₀ a₁ a₂ b)
    | sub_Sin₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Sin a a₁ a₂ a₃) (MRat.Sin b a₁ a₂ a₃)
    | sub_Sin₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Sin a₀ a a₂ a₃) (MRat.Sin a₀ b a₂ a₃)
    | sub_Sin₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Sin a₀ a₁ a a₃) (MRat.Sin a₀ a₁ b a₃)
    | sub_Sin₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Sin a₀ a₁ a₂ a) (MRat.Sin a₀ a₁ a₂ b)
    | sub_Cos₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Cos a a₁ a₂ a₃) (MRat.Cos b a₁ a₂ a₃)
    | sub_Cos₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Cos a₀ a a₂ a₃) (MRat.Cos a₀ b a₂ a₃)
    | sub_Cos₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Cos a₀ a₁ a a₃) (MRat.Cos a₀ a₁ b a₃)
    | sub_Cos₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Cos a₀ a₁ a₂ a) (MRat.Cos a₀ a₁ a₂ b)
    | sub_Tan₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Tan a a₁ a₂ a₃) (MRat.Tan b a₁ a₂ a₃)
    | sub_Tan₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Tan a₀ a a₂ a₃) (MRat.Tan a₀ b a₂ a₃)
    | sub_Tan₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Tan a₀ a₁ a a₃) (MRat.Tan a₀ a₁ b a₃)
    | sub_Tan₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Tan a₀ a₁ a₂ a) (MRat.Tan a₀ a₁ a₂ b)
    | sub_ArcSin₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcSin a a₁ a₂ a₃) (MRat.ArcSin b a₁ a₂ a₃)
    | sub_ArcSin₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcSin a₀ a a₂ a₃) (MRat.ArcSin a₀ b a₂ a₃)
    | sub_ArcSin₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ArcSin a₀ a₁ a a₃) (MRat.ArcSin a₀ a₁ b a₃)
    | sub_ArcSin₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ArcSin a₀ a₁ a₂ a) (MRat.ArcSin a₀ a₁ a₂ b)
    | sub_ArcCos₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcCos a a₁ a₂ a₃) (MRat.ArcCos b a₁ a₂ a₃)
    | sub_ArcCos₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcCos a₀ a a₂ a₃) (MRat.ArcCos a₀ b a₂ a₃)
    | sub_ArcCos₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ArcCos a₀ a₁ a a₃) (MRat.ArcCos a₀ a₁ b a₃)
    | sub_ArcCos₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ArcCos a₀ a₁ a₂ a) (MRat.ArcCos a₀ a₁ a₂ b)
    | sub_ArcTan₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcTan a a₁ a₂ a₃) (MRat.ArcTan b a₁ a₂ a₃)
    | sub_ArcTan₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcTan a₀ a a₂ a₃) (MRat.ArcTan a₀ b a₂ a₃)
    | sub_ArcTan₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ArcTan a₀ a₁ a a₃) (MRat.ArcTan a₀ a₁ b a₃)
    | sub_ArcTan₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ArcTan a₀ a₁ a₂ a) (MRat.ArcTan a₀ a₁ a₂ b)
    | sub_Sinh₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Sinh a a₁ a₂ a₃) (MRat.Sinh b a₁ a₂ a₃)
    | sub_Sinh₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Sinh a₀ a a₂ a₃) (MRat.Sinh a₀ b a₂ a₃)
    | sub_Sinh₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Sinh a₀ a₁ a a₃) (MRat.Sinh a₀ a₁ b a₃)
    | sub_Sinh₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Sinh a₀ a₁ a₂ a) (MRat.Sinh a₀ a₁ a₂ b)
    | sub_Cosh₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Cosh a a₁ a₂ a₃) (MRat.Cosh b a₁ a₂ a₃)
    | sub_Cosh₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Cosh a₀ a a₂ a₃) (MRat.Cosh a₀ b a₂ a₃)
    | sub_Cosh₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Cosh a₀ a₁ a a₃) (MRat.Cosh a₀ a₁ b a₃)
    | sub_Cosh₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Cosh a₀ a₁ a₂ a) (MRat.Cosh a₀ a₁ a₂ b)
    | sub_Tanh₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Tanh a a₁ a₂ a₃) (MRat.Tanh b a₁ a₂ a₃)
    | sub_Tanh₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Tanh a₀ a a₂ a₃) (MRat.Tanh a₀ b a₂ a₃)
    | sub_Tanh₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Tanh a₀ a₁ a a₃) (MRat.Tanh a₀ a₁ b a₃)
    | sub_Tanh₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Tanh a₀ a₁ a₂ a) (MRat.Tanh a₀ a₁ a₂ b)
    | sub_ArcSinh₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcSinh a a₁ a₂ a₃) (MRat.ArcSinh b a₁ a₂ a₃)
    | sub_ArcSinh₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcSinh a₀ a a₂ a₃) (MRat.ArcSinh a₀ b a₂ a₃)
    | sub_ArcSinh₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ArcSinh a₀ a₁ a a₃) (MRat.ArcSinh a₀ a₁ b a₃)
    | sub_ArcSinh₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ArcSinh a₀ a₁ a₂ a) (MRat.ArcSinh a₀ a₁ a₂ b)
    | sub_ArcCosh₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcCosh a a₁ a₂ a₃) (MRat.ArcCosh b a₁ a₂ a₃)
    | sub_ArcCosh₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcCosh a₀ a a₂ a₃) (MRat.ArcCosh a₀ b a₂ a₃)
    | sub_ArcCosh₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ArcCosh a₀ a₁ a a₃) (MRat.ArcCosh a₀ a₁ b a₃)
    | sub_ArcCosh₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ArcCosh a₀ a₁ a₂ a) (MRat.ArcCosh a₀ a₁ a₂ b)
    | sub_ArcTanh₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcTanh a a₁ a₂ a₃) (MRat.ArcTanh b a₁ a₂ a₃)
    | sub_ArcTanh₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcTanh a₀ a a₂ a₃) (MRat.ArcTanh a₀ b a₂ a₃)
    | sub_ArcTanh₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ArcTanh a₀ a₁ a a₃) (MRat.ArcTanh a₀ a₁ b a₃)
    | sub_ArcTanh₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ArcTanh a₀ a₁ a₂ a) (MRat.ArcTanh a₀ a₁ a₂ b)
    | sub_SinPi₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.SinPi a a₁ a₂ a₃) (MRat.SinPi b a₁ a₂ a₃)
    | sub_SinPi₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.SinPi a₀ a a₂ a₃) (MRat.SinPi a₀ b a₂ a₃)
    | sub_SinPi₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.SinPi a₀ a₁ a a₃) (MRat.SinPi a₀ a₁ b a₃)
    | sub_SinPi₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.SinPi a₀ a₁ a₂ a) (MRat.SinPi a₀ a₁ a₂ b)
    | sub_CosPi₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.CosPi a a₁ a₂ a₃) (MRat.CosPi b a₁ a₂ a₃)
    | sub_CosPi₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.CosPi a₀ a a₂ a₃) (MRat.CosPi a₀ b a₂ a₃)
    | sub_CosPi₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.CosPi a₀ a₁ a a₃) (MRat.CosPi a₀ a₁ b a₃)
    | sub_CosPi₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.CosPi a₀ a₁ a₂ a) (MRat.CosPi a₀ a₁ a₂ b)
    | sub_TanPi₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.TanPi a a₁ a₂ a₃) (MRat.TanPi b a₁ a₂ a₃)
    | sub_TanPi₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.TanPi a₀ a a₂ a₃) (MRat.TanPi a₀ b a₂ a₃)
    | sub_TanPi₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.TanPi a₀ a₁ a a₃) (MRat.TanPi a₀ a₁ b a₃)
    | sub_TanPi₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.TanPi a₀ a₁ a₂ a) (MRat.TanPi a₀ a₁ a₂ b)
    | sub_ArcSinPi₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcSinPi a a₁ a₂ a₃) (MRat.ArcSinPi b a₁ a₂ a₃)
    | sub_ArcSinPi₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcSinPi a₀ a a₂ a₃) (MRat.ArcSinPi a₀ b a₂ a₃)
    | sub_ArcSinPi₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ArcSinPi a₀ a₁ a a₃) (MRat.ArcSinPi a₀ a₁ b a₃)
    | sub_ArcSinPi₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ArcSinPi a₀ a₁ a₂ a) (MRat.ArcSinPi a₀ a₁ a₂ b)
    | sub_ArcCosPi₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcCosPi a a₁ a₂ a₃) (MRat.ArcCosPi b a₁ a₂ a₃)
    | sub_ArcCosPi₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcCosPi a₀ a a₂ a₃) (MRat.ArcCosPi a₀ b a₂ a₃)
    | sub_ArcCosPi₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ArcCosPi a₀ a₁ a a₃) (MRat.ArcCosPi a₀ a₁ b a₃)
    | sub_ArcCosPi₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ArcCosPi a₀ a₁ a₂ a) (MRat.ArcCosPi a₀ a₁ a₂ b)
    | sub_ArcTanPi₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcTanPi a a₁ a₂ a₃) (MRat.ArcTanPi b a₁ a₂ a₃)
    | sub_ArcTanPi₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcTanPi a₀ a a₂ a₃) (MRat.ArcTanPi a₀ b a₂ a₃)
    | sub_ArcTanPi₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ArcTanPi a₀ a₁ a a₃) (MRat.ArcTanPi a₀ a₁ b a₃)
    | sub_ArcTanPi₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ArcTanPi a₀ a₁ a₂ a) (MRat.ArcTanPi a₀ a₁ a₂ b)
    | sub_Softplus₀ {a₁ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Softplus a a₁ a₂ a₃) (MRat.Softplus b a₁ a₂ a₃)
    | sub_Softplus₁ {a₀ a₂ a₃ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Softplus a₀ a a₂ a₃) (MRat.Softplus a₀ b a₂ a₃)
    | sub_Softplus₂ {a₀ a₁ a₃ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Softplus a₀ a₁ a a₃) (MRat.Softplus a₀ a₁ b a₃)
    | sub_Softplus₃ {a₀ a₁ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Softplus a₀ a₁ a₂ a) (MRat.Softplus a₀ a₁ a₂ b)
    | sub_Hypot₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Hypot a a₁ a₂ a₃ a₄ a₅) (MRat.Hypot b a₁ a₂ a₃ a₄ a₅)
    | sub_Hypot₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Hypot a₀ a a₂ a₃ a₄ a₅) (MRat.Hypot a₀ b a₂ a₃ a₄ a₅)
    | sub_Hypot₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.Hypot a₀ a₁ a a₃ a₄ a₅) (MRat.Hypot a₀ a₁ b a₃ a₄ a₅)
    | sub_Hypot₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.Hypot a₀ a₁ a₂ a a₄ a₅) (MRat.Hypot a₀ a₁ a₂ b a₄ a₅)
    | sub_Hypot₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Hypot a₀ a₁ a₂ a₃ a a₅) (MRat.Hypot a₀ a₁ a₂ a₃ b a₅)
    | sub_Hypot₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.Hypot a₀ a₁ a₂ a₃ a₄ a) (MRat.Hypot a₀ a₁ a₂ a₃ a₄ b)
    | sub_ArcTan2₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcTan2 a a₁ a₂ a₃ a₄ a₅) (MRat.ArcTan2 b a₁ a₂ a₃ a₄ a₅)
    | sub_ArcTan2₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcTan2 a₀ a a₂ a₃ a₄ a₅) (MRat.ArcTan2 a₀ b a₂ a₃ a₄ a₅)
    | sub_ArcTan2₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcTan2 a₀ a₁ a a₃ a₄ a₅) (MRat.ArcTan2 a₀ a₁ b a₃ a₄ a₅)
    | sub_ArcTan2₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ArcTan2 a₀ a₁ a₂ a a₄ a₅) (MRat.ArcTan2 a₀ a₁ a₂ b a₄ a₅)
    | sub_ArcTan2₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ArcTan2 a₀ a₁ a₂ a₃ a a₅) (MRat.ArcTan2 a₀ a₁ a₂ a₃ b a₅)
    | sub_ArcTan2₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ArcTan2 a₀ a₁ a₂ a₃ a₄ a) (MRat.ArcTan2 a₀ a₁ a₂ a₃ a₄ b)
    | sub_ArcTan2Pi₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcTan2Pi a a₁ a₂ a₃ a₄ a₅) (MRat.ArcTan2Pi b a₁ a₂ a₃ a₄ a₅)
    | sub_ArcTan2Pi₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcTan2Pi a₀ a a₂ a₃ a₄ a₅) (MRat.ArcTan2Pi a₀ b a₂ a₃ a₄ a₅)
    | sub_ArcTan2Pi₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ArcTan2Pi a₀ a₁ a a₃ a₄ a₅) (MRat.ArcTan2Pi a₀ a₁ b a₃ a₄ a₅)
    | sub_ArcTan2Pi₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ArcTan2Pi a₀ a₁ a₂ a a₄ a₅) (MRat.ArcTan2Pi a₀ a₁ a₂ b a₄ a₅)
    | sub_ArcTan2Pi₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ArcTan2Pi a₀ a₁ a₂ a₃ a a₅) (MRat.ArcTan2Pi a₀ a₁ a₂ a₃ b a₅)
    | sub_ArcTan2Pi₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ArcTan2Pi a₀ a₁ a₂ a₃ a₄ a) (MRat.ArcTan2Pi a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledSqrt₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSqrt a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledSqrt b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledSqrt₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSqrt a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledSqrt a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledSqrt₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSqrt a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledSqrt a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledSqrt₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledSqrt a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledSqrt a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledSqrt₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledSqrt a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledSqrt a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledSqrt₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledSqrt a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledSqrt a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledRSqrt₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledRSqrt a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledRSqrt b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledRSqrt₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledRSqrt a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledRSqrt a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledRSqrt₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledRSqrt a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledRSqrt a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledRSqrt₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledRSqrt a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledRSqrt a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledRSqrt₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledRSqrt a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledRSqrt a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledRSqrt₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledRSqrt a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledRSqrt a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledExp₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledExp a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledExp b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledExp₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledExp a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledExp a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledExp₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledExp a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledExp a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledExp₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledExp a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledExp a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledExp₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledExp a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledExp a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledExp₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledExp a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledExp a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledExp2₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledExp2 a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledExp2 b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledExp2₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledExp2 a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledExp2 a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledExp2₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledExp2 a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledExp2 a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledExp2₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledExp2 a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledExp2 a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledExp2₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledExp2 a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledExp2 a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledExp2₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledExp2 a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledExp2 a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledLog₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledLog a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledLog b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledLog₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledLog a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledLog a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledLog₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledLog a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledLog a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledLog₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledLog a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledLog a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledLog₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledLog a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledLog a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledLog₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledLog a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledLog a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledLog2₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledLog2 a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledLog2 b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledLog2₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledLog2 a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledLog2 a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledLog2₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledLog2 a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledLog2 a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledLog2₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledLog2 a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledLog2 a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledLog2₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledLog2 a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledLog2 a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledLog2₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledLog2 a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledLog2 a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledLogOnePlus₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledLogOnePlus a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledLogOnePlus b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledLogOnePlus₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledLogOnePlus a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledLogOnePlus a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledLogOnePlus₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledLogOnePlus a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledLogOnePlus a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledLogOnePlus₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledLogOnePlus a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledLogOnePlus a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledLogOnePlus₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledLogOnePlus a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledLogOnePlus a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledLogOnePlus₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledLogOnePlus a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledLogOnePlus a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledExpMinusOne₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledExpMinusOne a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledExpMinusOne b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledExpMinusOne₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledExpMinusOne a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledExpMinusOne a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledExpMinusOne₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledExpMinusOne a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledExpMinusOne a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledExpMinusOne₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledExpMinusOne a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledExpMinusOne a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledExpMinusOne₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledExpMinusOne a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledExpMinusOne a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledExpMinusOne₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledExpMinusOne a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledExpMinusOne a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledSin₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSin a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledSin b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledSin₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSin a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledSin a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledSin₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSin a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledSin a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledSin₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledSin a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledSin a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledSin₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledSin a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledSin a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledSin₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledSin a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledSin a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledCos₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledCos a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledCos b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledCos₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledCos a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledCos a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledCos₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledCos a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledCos a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledCos₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledCos a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledCos a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledCos₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledCos a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledCos a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledCos₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledCos a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledCos a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledTan₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledTan a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledTan b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledTan₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledTan a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledTan a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledTan₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledTan a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledTan a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledTan₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledTan a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledTan a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledTan₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledTan a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledTan a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledTan₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledTan a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledTan a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledArcSin₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcSin a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledArcSin b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledArcSin₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcSin a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledArcSin a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledArcSin₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcSin a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledArcSin a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledArcSin₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledArcSin a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledArcSin a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledArcSin₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcSin a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledArcSin a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledArcSin₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcSin a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledArcSin a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledArcCos₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcCos a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledArcCos b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledArcCos₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcCos a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledArcCos a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledArcCos₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcCos a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledArcCos a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledArcCos₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledArcCos a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledArcCos a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledArcCos₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcCos a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledArcCos a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledArcCos₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcCos a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledArcCos a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledArcTan₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledArcTan b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledArcTan₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledArcTan a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledArcTan₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledArcTan a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledArcTan₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledArcTan a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledArcTan₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledArcTan a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledArcTan₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledArcTan a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledSinh₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSinh a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledSinh b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledSinh₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSinh a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledSinh a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledSinh₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSinh a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledSinh a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledSinh₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledSinh a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledSinh a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledSinh₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledSinh a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledSinh a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledSinh₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledSinh a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledSinh a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledCosh₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledCosh a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledCosh b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledCosh₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledCosh a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledCosh a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledCosh₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledCosh a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledCosh a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledCosh₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledCosh a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledCosh a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledCosh₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledCosh a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledCosh a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledCosh₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledCosh a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledCosh a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledTanh₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledTanh a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledTanh b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledTanh₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledTanh a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledTanh a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledTanh₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledTanh a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledTanh a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledTanh₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledTanh a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledTanh a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledTanh₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledTanh a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledTanh a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledTanh₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledTanh a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledTanh a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledArcSinh₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcSinh a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledArcSinh b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledArcSinh₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcSinh a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledArcSinh a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledArcSinh₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcSinh a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledArcSinh a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledArcSinh₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledArcSinh a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledArcSinh a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledArcSinh₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcSinh a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledArcSinh a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledArcSinh₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcSinh a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledArcSinh a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledArcCosh₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcCosh a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledArcCosh b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledArcCosh₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcCosh a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledArcCosh a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledArcCosh₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcCosh a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledArcCosh a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledArcCosh₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledArcCosh a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledArcCosh a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledArcCosh₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcCosh a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledArcCosh a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledArcCosh₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcCosh a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledArcCosh a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledArcTanh₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTanh a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledArcTanh b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledArcTanh₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTanh a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledArcTanh a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledArcTanh₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTanh a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledArcTanh a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledArcTanh₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTanh a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledArcTanh a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledArcTanh₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTanh a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledArcTanh a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledArcTanh₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTanh a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledArcTanh a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledSinPi₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSinPi a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledSinPi b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledSinPi₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSinPi a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledSinPi a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledSinPi₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSinPi a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledSinPi a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledSinPi₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledSinPi a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledSinPi a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledSinPi₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledSinPi a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledSinPi a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledSinPi₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledSinPi a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledSinPi a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledCosPi₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledCosPi a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledCosPi b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledCosPi₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledCosPi a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledCosPi a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledCosPi₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledCosPi a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledCosPi a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledCosPi₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledCosPi a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledCosPi a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledCosPi₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledCosPi a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledCosPi a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledCosPi₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledCosPi a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledCosPi a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledTanPi₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledTanPi a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledTanPi b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledTanPi₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledTanPi a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledTanPi a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledTanPi₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledTanPi a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledTanPi a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledTanPi₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledTanPi a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledTanPi a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledTanPi₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledTanPi a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledTanPi a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledTanPi₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledTanPi a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledTanPi a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledArcSinPi₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcSinPi a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledArcSinPi b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledArcSinPi₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcSinPi a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledArcSinPi a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledArcSinPi₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcSinPi a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledArcSinPi a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledArcSinPi₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledArcSinPi a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledArcSinPi a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledArcSinPi₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcSinPi a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledArcSinPi a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledArcSinPi₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcSinPi a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledArcSinPi a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledArcCosPi₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcCosPi a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledArcCosPi b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledArcCosPi₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcCosPi a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledArcCosPi a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledArcCosPi₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcCosPi a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledArcCosPi a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledArcCosPi₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledArcCosPi a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledArcCosPi a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledArcCosPi₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcCosPi a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledArcCosPi a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledArcCosPi₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcCosPi a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledArcCosPi a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledArcTanPi₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTanPi a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledArcTanPi b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledArcTanPi₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTanPi a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledArcTanPi a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledArcTanPi₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTanPi a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledArcTanPi a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledArcTanPi₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTanPi a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledArcTanPi a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledArcTanPi₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTanPi a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledArcTanPi a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledArcTanPi₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTanPi a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledArcTanPi a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledSoftplus₀ {a₁ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSoftplus a a₁ a₂ a₃ a₄ a₅) (MRat.ScaledSoftplus b a₁ a₂ a₃ a₄ a₅)
    | sub_ScaledSoftplus₁ {a₀ a₂ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSoftplus a₀ a a₂ a₃ a₄ a₅) (MRat.ScaledSoftplus a₀ b a₂ a₃ a₄ a₅)
    | sub_ScaledSoftplus₂ {a₀ a₁ a₃ a₄ a₅ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledSoftplus a₀ a₁ a a₃ a₄ a₅) (MRat.ScaledSoftplus a₀ a₁ b a₃ a₄ a₅)
    | sub_ScaledSoftplus₃ {a₀ a₁ a₂ a₄ a₅ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledSoftplus a₀ a₁ a₂ a a₄ a₅) (MRat.ScaledSoftplus a₀ a₁ a₂ b a₄ a₅)
    | sub_ScaledSoftplus₄ {a₀ a₁ a₂ a₃ a₅ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledSoftplus a₀ a₁ a₂ a₃ a a₅) (MRat.ScaledSoftplus a₀ a₁ a₂ a₃ b a₅)
    | sub_ScaledSoftplus₅ {a₀ a₁ a₂ a₃ a₄ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledSoftplus a₀ a₁ a₂ a₃ a₄ a) (MRat.ScaledSoftplus a₀ a₁ a₂ a₃ a₄ b)
    | sub_ScaledHypot₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledHypot a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledHypot b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledHypot₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledHypot a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledHypot a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledHypot₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledHypot a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledHypot a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledHypot₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledHypot a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledHypot a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledHypot₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledHypot a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (MRat.ScaledHypot a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledHypot₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledHypot a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (MRat.ScaledHypot a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | sub_ScaledHypot₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledHypot a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (MRat.ScaledHypot a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | sub_ScaledHypot₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (MRat.ScaledHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | sub_ScaledHypot₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (MRat.ScaledHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | sub_ScaledHypot₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (MRat.ScaledHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | sub_ScaledArcTan2₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2 a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledArcTan2 b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledArcTan2₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2 a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledArcTan2 a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledArcTan2₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2 a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledArcTan2 a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledArcTan2₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2 a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledArcTan2 a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledArcTan2₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2 a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (MRat.ScaledArcTan2 a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledArcTan2₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (MRat.ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | sub_ScaledArcTan2₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (MRat.ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | sub_ScaledArcTan2₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (MRat.ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | sub_ScaledArcTan2₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (MRat.ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | sub_ScaledArcTan2₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (MRat.ScaledArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | sub_ScaledArcTan2Pi₀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2Pi a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledArcTan2Pi b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledArcTan2Pi₁ {a₀ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2Pi a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledArcTan2Pi a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledArcTan2Pi₂ {a₀ a₁ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2Pi a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledArcTan2Pi a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledArcTan2Pi₃ {a₀ a₁ a₂ a₄ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2Pi a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉) (MRat.ScaledArcTan2Pi a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledArcTan2Pi₄ {a₀ a₁ a₂ a₃ a₅ a₆ a₇ a₈ a₉ a b} : kFormat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2Pi a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉) (MRat.ScaledArcTan2Pi a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉)
    | sub_ScaledArcTan2Pi₅ {a₀ a₁ a₂ a₃ a₄ a₆ a₇ a₈ a₉ a b} : kProjSpec.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉) (MRat.ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉)
    | sub_ScaledArcTan2Pi₆ {a₀ a₁ a₂ a₃ a₄ a₅ a₇ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉) (MRat.ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉)
    | sub_ScaledArcTan2Pi₇ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₈ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉) (MRat.ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉)
    | sub_ScaledArcTan2Pi₈ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₉ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉) (MRat.ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉)
    | sub_ScaledArcTan2Pi₉ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a) (MRat.ScaledArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b)
    | sub_ifthenelsefi₀ {a₁ a₂ a b} : kBool.rw_one a b →
    MRat.rw_one (MRat.ifthenelsefi a a₁ a₂) (MRat.ifthenelsefi b a₁ a₂)
    | sub_ifthenelsefi₁ {a₀ a₂ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ifthenelsefi a₀ a a₂) (MRat.ifthenelsefi a₀ b a₂)
    | sub_ifthenelsefi₂ {a₀ a₁ a b} : MRat.rw_one a b →
    MRat.rw_one (MRat.ifthenelsefi a₀ a₁ a) (MRat.ifthenelsefi a₀ a₁ b)

  inductive MString.rw_one: MString → MString → Prop
    | eqe_left {a b c : MString} : a = b → MString.rw_one b c → MString.rw_one a c
    | eqe_right {a b c : MString} : MString.rw_one a b → b = c → MString.rw_one a c
    -- Axioms for rewriting inside subterms
    | sub_char {a b} : MRat.rw_one a b →
    MString.rw_one (MString.char a) (MString.char b)
    | sub_specializationName {a b} : kSpecialization.rw_one a b →
    MString.rw_one (MString.specializationName a) (MString.specializationName b)

  inductive kBool.rw_star: kBool → kBool → Prop
    | step {a b} : kBool.rw_one a b → kBool.rw_star a b
    | refl {a b : kBool} : a.eqe b → kBool.rw_star a b
    | trans {a b c} : kBool.rw_star a b → kBool.rw_star b c → kBool.rw_star a c

  inductive kXReal.rw_star: kXReal → kXReal → Prop
    | step {a b} : kXReal.rw_one a b → kXReal.rw_star a b
    | refl {a b : kXReal} : a.eqe b → kXReal.rw_star a b
    | trans {a b c} : kXReal.rw_star a b → kXReal.rw_star b c → kXReal.rw_star a c

  inductive kFormat.rw_star: kFormat → kFormat → Prop
    | step {a b} : kFormat.rw_one a b → kFormat.rw_star a b
    | refl {a b : kFormat} : a.eqe b → kFormat.rw_star a b
    | trans {a b c} : kFormat.rw_star a b → kFormat.rw_star b c → kFormat.rw_star a c

  inductive kSignedness.rw_star: kSignedness → kSignedness → Prop
    | step {a b} : kSignedness.rw_one a b → kSignedness.rw_star a b
    | refl {a b : kSignedness} : a.eqe b → kSignedness.rw_star a b
    | trans {a b c} : kSignedness.rw_star a b → kSignedness.rw_star b c → kSignedness.rw_star a c

  inductive kDomain.rw_star: kDomain → kDomain → Prop
    | step {a b} : kDomain.rw_one a b → kDomain.rw_star a b
    | refl {a b : kDomain} : a.eqe b → kDomain.rw_star a b
    | trans {a b c} : kDomain.rw_star a b → kDomain.rw_star b c → kDomain.rw_star a c

  inductive kBoundQuery.rw_star: kBoundQuery → kBoundQuery → Prop
    | step {a b} : kBoundQuery.rw_one a b → kBoundQuery.rw_star a b
    | refl {a b : kBoundQuery} : a.eqe b → kBoundQuery.rw_star a b
    | trans {a b c} : kBoundQuery.rw_star a b → kBoundQuery.rw_star b c → kBoundQuery.rw_star a c

  inductive kRandomSeq.rw_star: kRandomSeq → kRandomSeq → Prop
    | step {a b} : kRandomSeq.rw_one a b → kRandomSeq.rw_star a b
    | refl {a b : kRandomSeq} : a.eqe b → kRandomSeq.rw_star a b
    | trans {a b c} : kRandomSeq.rw_star a b → kRandomSeq.rw_star b c → kRandomSeq.rw_star a c

  inductive kBlockRoundMode.rw_star: kBlockRoundMode → kBlockRoundMode → Prop
    | step {a b} : kBlockRoundMode.rw_one a b → kBlockRoundMode.rw_star a b
    | refl {a b : kBlockRoundMode} : a.eqe b → kBlockRoundMode.rw_star a b
    | trans {a b c} : kBlockRoundMode.rw_star a b → kBlockRoundMode.rw_star b c → kBlockRoundMode.rw_star a c

  inductive kSatMode.rw_star: kSatMode → kSatMode → Prop
    | step {a b} : kSatMode.rw_one a b → kSatMode.rw_star a b
    | refl {a b : kSatMode} : a.eqe b → kSatMode.rw_star a b
    | trans {a b c} : kSatMode.rw_star a b → kSatMode.rw_star b c → kSatMode.rw_star a c

  inductive kProjSpec.rw_star: kProjSpec → kProjSpec → Prop
    | step {a b} : kProjSpec.rw_one a b → kProjSpec.rw_star a b
    | refl {a b : kProjSpec} : a.eqe b → kProjSpec.rw_star a b
    | trans {a b c} : kProjSpec.rw_star a b → kProjSpec.rw_star b c → kProjSpec.rw_star a c

  inductive kBlockProjSpec.rw_star: kBlockProjSpec → kBlockProjSpec → Prop
    | step {a b} : kBlockProjSpec.rw_one a b → kBlockProjSpec.rw_star a b
    | refl {a b : kBlockProjSpec} : a.eqe b → kBlockProjSpec.rw_star a b
    | trans {a b c} : kBlockProjSpec.rw_star a b → kBlockProjSpec.rw_star b c → kBlockProjSpec.rw_star a c

  inductive kXSeq.rw_star: kXSeq → kXSeq → Prop
    | step {a b} : kXSeq.rw_one a b → kXSeq.rw_star a b
    | refl {a b : kXSeq} : a.eqe b → kXSeq.rw_star a b
    | trans {a b c} : kXSeq.rw_star a b → kXSeq.rw_star b c → kXSeq.rw_star a c

  inductive kCodeSeq.rw_star: kCodeSeq → kCodeSeq → Prop
    | step {a b} : kCodeSeq.rw_one a b → kCodeSeq.rw_star a b
    | refl {a b : kCodeSeq} : a.eqe b → kCodeSeq.rw_star a b
    | trans {a b c} : kCodeSeq.rw_star a b → kCodeSeq.rw_star b c → kCodeSeq.rw_star a c

  inductive kBlock.rw_star: kBlock → kBlock → Prop
    | step {a b} : kBlock.rw_one a b → kBlock.rw_star a b
    | refl {a b : kBlock} : a.eqe b → kBlock.rw_star a b
    | trans {a b c} : kBlock.rw_star a b → kBlock.rw_star b c → kBlock.rw_star a c

  inductive kFormatSeq.rw_star: kFormatSeq → kFormatSeq → Prop
    | step {a b} : kFormatSeq.rw_one a b → kFormatSeq.rw_star a b
    | refl {a b : kFormatSeq} : a.eqe b → kFormatSeq.rw_star a b
    | trans {a b c} : kFormatSeq.rw_star a b → kFormatSeq.rw_star b c → kFormatSeq.rw_star a c

  inductive kSpecialization.rw_star: kSpecialization → kSpecialization → Prop
    | step {a b} : kSpecialization.rw_one a b → kSpecialization.rw_star a b
    | refl {a b : kSpecialization} : a.eqe b → kSpecialization.rw_star a b
    | trans {a b c} : kSpecialization.rw_star a b → kSpecialization.rw_star b c → kSpecialization.rw_star a c

  inductive kKappa.rw_star: kKappa → kKappa → Prop
    | step {a b} : kKappa.rw_one a b → kKappa.rw_star a b
    | refl {a b : kKappa} : a.eqe b → kKappa.rw_star a b
    | trans {a b c} : kKappa.rw_star a b → kKappa.rw_star b c → kKappa.rw_star a c

  inductive kObservation.rw_star: kObservation → kObservation → Prop
    | step {a b} : kObservation.rw_one a b → kObservation.rw_star a b
    | refl {a b : kObservation} : a.eqe b → kObservation.rw_star a b
    | trans {a b c} : kObservation.rw_star a b → kObservation.rw_star b c → kObservation.rw_star a c

  inductive kDeclaration.rw_star: kDeclaration → kDeclaration → Prop
    | step {a b} : kDeclaration.rw_one a b → kDeclaration.rw_star a b
    | refl {a b : kDeclaration} : a.eqe b → kDeclaration.rw_star a b
    | trans {a b c} : kDeclaration.rw_star a b → kDeclaration.rw_star b c → kDeclaration.rw_star a c

  inductive kEvidence.rw_star: kEvidence → kEvidence → Prop
    | step {a b} : kEvidence.rw_one a b → kEvidence.rw_star a b
    | refl {a b : kEvidence} : a.eqe b → kEvidence.rw_star a b
    | trans {a b c} : kEvidence.rw_star a b → kEvidence.rw_star b c → kEvidence.rw_star a c

  inductive kKappaPart.rw_star: kKappaPart → kKappaPart → Prop
    | step {a b} : kKappaPart.rw_one a b → kKappaPart.rw_star a b
    | refl {a b : kKappaPart} : a.eqe b → kKappaPart.rw_star a b
    | trans {a b c} : kKappaPart.rw_star a b → kKappaPart.rw_star b c → kKappaPart.rw_star a c

  inductive kArityEntry.rw_star: kArityEntry → kArityEntry → Prop
    | step {a b} : kArityEntry.rw_one a b → kArityEntry.rw_star a b
    | refl {a b : kArityEntry} : a.eqe b → kArityEntry.rw_star a b
    | trans {a b c} : kArityEntry.rw_star a b → kArityEntry.rw_star b c → kArityEntry.rw_star a c

  inductive kKappaPartSeq.rw_star: kKappaPartSeq → kKappaPartSeq → Prop
    | step {a b} : kKappaPartSeq.rw_one a b → kKappaPartSeq.rw_star a b
    | refl {a b : kKappaPartSeq} : a.eqe b → kKappaPartSeq.rw_star a b
    | trans {a b c} : kKappaPartSeq.rw_star a b → kKappaPartSeq.rw_star b c → kKappaPartSeq.rw_star a c

  inductive kPartitionSeq.rw_star: kPartitionSeq → kPartitionSeq → Prop
    | step {a b} : kPartitionSeq.rw_one a b → kPartitionSeq.rw_star a b
    | refl {a b : kPartitionSeq} : a.eqe b → kPartitionSeq.rw_star a b
    | trans {a b c} : kPartitionSeq.rw_star a b → kPartitionSeq.rw_star b c → kPartitionSeq.rw_star a c

  inductive kDeclarationSeq.rw_star: kDeclarationSeq → kDeclarationSeq → Prop
    | step {a b} : kDeclarationSeq.rw_one a b → kDeclarationSeq.rw_star a b
    | refl {a b : kDeclarationSeq} : a.eqe b → kDeclarationSeq.rw_star a b
    | trans {a b c} : kDeclarationSeq.rw_star a b → kDeclarationSeq.rw_star b c → kDeclarationSeq.rw_star a c

  inductive kSpecializationSeq.rw_star: kSpecializationSeq → kSpecializationSeq → Prop
    | step {a b} : kSpecializationSeq.rw_one a b → kSpecializationSeq.rw_star a b
    | refl {a b : kSpecializationSeq} : a.eqe b → kSpecializationSeq.rw_star a b
    | trans {a b c} : kSpecializationSeq.rw_star a b → kSpecializationSeq.rw_star b c → kSpecializationSeq.rw_star a c

  inductive kClassEnum.rw_star: kClassEnum → kClassEnum → Prop
    | step {a b} : kClassEnum.rw_one a b → kClassEnum.rw_star a b
    | refl {a b : kClassEnum} : a.eqe b → kClassEnum.rw_star a b
    | trans {a b c} : kClassEnum.rw_star a b → kClassEnum.rw_star b c → kClassEnum.rw_star a c

  inductive kObservationSeq.rw_star: kObservationSeq → kObservationSeq → Prop
    | step {a b} : kObservationSeq.rw_one a b → kObservationSeq.rw_star a b
    | refl {a b : kObservationSeq} : a.eqe b → kObservationSeq.rw_star a b
    | trans {a b c} : kObservationSeq.rw_star a b → kObservationSeq.rw_star b c → kObservationSeq.rw_star a c

  inductive kArityTable.rw_star: kArityTable → kArityTable → Prop
    | step {a b} : kArityTable.rw_one a b → kArityTable.rw_star a b
    | refl {a b : kArityTable} : a.eqe b → kArityTable.rw_star a b
    | trans {a b c} : kArityTable.rw_star a b → kArityTable.rw_star b c → kArityTable.rw_star a c

  inductive MRat.rw_star: MRat → MRat → Prop
    | step {a b} : MRat.rw_one a b → MRat.rw_star a b
    | refl {a b : MRat} : a = b → MRat.rw_star a b
    | trans {a b c} : MRat.rw_star a b → MRat.rw_star b c → MRat.rw_star a c

  inductive MString.rw_star: MString → MString → Prop
    | step {a b} : MString.rw_one a b → MString.rw_star a b
    | refl {a b : MString} : a = b → MString.rw_star a b
    | trans {a b c} : MString.rw_star a b → MString.rw_star b c → MString.rw_star a c

end
end Maude
