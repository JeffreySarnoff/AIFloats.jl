-- Extracted from ../spec2.lean, lines 962-1504.
-- See PLAN.md and manifest.json for provenance.
import P3109.Predicates

namespace Maude
-- Equality modulo axioms
mutual

  inductive kBool.eqa: kBool → kBool → Prop
    | refl {a} : kBool.eqa a a
    | symm {a b} : kBool.eqa a b → kBool.eqa b a
    | trans {a b c} : kBool.eqa a b → kBool.eqa b c → kBool.eqa a c
    -- Congruence axioms for each operator
    | eqa_and {a₀ b₀ a₁ b₁ : kBool} : kBool.eqa a₀ b₀ → kBool.eqa a₁ b₁ → kBool.eqa (kBool.and a₀ a₁) (kBool.and b₀ b₁)
    | eqa_or {a₀ b₀ a₁ b₁ : kBool} : kBool.eqa a₀ b₀ → kBool.eqa a₁ b₁ → kBool.eqa (kBool.or a₀ a₁) (kBool.or b₀ b₁)
    | eqa_xor {a₀ b₀ a₁ b₁ : kBool} : kBool.eqa a₀ b₀ → kBool.eqa a₁ b₁ → kBool.eqa (kBool.xor a₀ a₁) (kBool.xor b₀ b₁)
    | eqa_not {a b : kBool} : kBool.eqa a b → kBool.eqa (kBool.not a) (kBool.not b)
    | eqa_implies {a₀ b₀ a₁ b₁ : kBool} : kBool.eqa a₀ b₀ → kBool.eqa a₁ b₁ → kBool.eqa (kBool.implies a₀ a₁) (kBool.implies b₀ b₁)
    | eqa_lt₀ {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqa (kBool.lt₀ a₀ a₁) (kBool.lt₀ b₀ b₁)
    | eqa_lteq₀ {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqa (kBool.lteq₀ a₀ a₁) (kBool.lteq₀ b₀ b₁)
    | eqa_gt₀ {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqa (kBool.gt₀ a₀ a₁) (kBool.gt₀ b₀ b₁)
    | eqa_gteq₀ {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqa (kBool.gteq₀ a₀ a₁) (kBool.gteq₀ b₀ b₁)
    | eqa_divides {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqa (kBool.divides a₀ a₁) (kBool.divides b₀ b₁)
    | eqa_xNaN {a b : kXReal} : kXReal.eqa a b → kBool.eqa (kBool.xNaN a) (kBool.xNaN b)
    | eqa_xInfinite {a b : kXReal} : kXReal.eqa a b → kBool.eqa (kBool.xInfinite a) (kBool.xInfinite b)
    | eqa_xFinite {a b : kXReal} : kXReal.eqa a b → kBool.eqa (kBool.xFinite a) (kBool.xFinite b)
    | eqa_xMinus {a b : kXReal} : kXReal.eqa a b → kBool.eqa (kBool.xMinus a) (kBool.xMinus b)
    | eqa_xLt {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kBool.eqa (kBool.xLt a₀ a₁) (kBool.xLt b₀ b₁)
    | eqa_xLe {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kBool.eqa (kBool.xLe a₀ a₁) (kBool.xLe b₀ b₁)
    | eqa_xEq {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kBool.eqa (kBool.xEq a₀ a₁) (kBool.xEq b₀ b₁)
    | eqa_even {a b : MRat} : a = b → kBool.eqa (kBool.even a) (kBool.even b)
    | eqa_validFormat {a b : kFormat} : kFormat.eqa a b → kBool.eqa (kBool.validFormat a) (kBool.validFormat b)
    | eqa_internalFormat {a b : kFormat} : kFormat.eqa a b → kBool.eqa (kBool.internalFormat a) (kBool.internalFormat b)
    | eqa_externalDatum {a₀ b₀ : kFormat} {a₁ b₁ : kXReal} : kFormat.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kBool.eqa (kBool.externalDatum a₀ a₁) (kBool.externalDatum b₀ b₁)
    | eqa_validCode {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqa a₀ b₀ → a₁ = b₁ → kBool.eqa (kBool.validCode a₀ a₁) (kBool.validCode b₀ b₁)
    | eqa_datum {a₀ b₀ : kFormat} {a₁ b₁ : kXReal} : kFormat.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kBool.eqa (kBool.datum a₀ a₁) (kBool.datum b₀ b₁)
    | eqa_candidateDatum {a₀ b₀ : kFormat} {a₁ b₁ a₂ b₂ : MRat} : kFormat.eqa a₀ b₀ → a₁ = b₁ → a₂ = b₂ → kBool.eqa (kBool.candidateDatum a₀ a₁ a₂) (kBool.candidateDatum b₀ b₁ b₂)
    | eqa_randomInRange {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqa (kBool.randomInRange a₀ a₁) (kBool.randomInRange b₀ b₁)
    | eqa_validRound {a b : kBlockRoundMode} : kBlockRoundMode.eqa a b → kBool.eqa (kBool.validRound a) (kBool.validRound b)
    | eqa_validProjection {a b : kProjSpec} : kProjSpec.eqa a b → kBool.eqa (kBool.validProjection a) (kBool.validProjection b)
    | eqa_validBlockProjection {a₀ b₀ : kBlockProjSpec} {a₁ b₁ : MRat} : kBlockProjSpec.eqa a₀ b₀ → a₁ = b₁ → kBool.eqa (kBool.validBlockProjection a₀ a₁) (kBool.validBlockProjection b₀ b₁)
    | eqa_validRandoms {a₀ b₀ : MRat} {a₁ b₁ : kRandomSeq} : a₀ = b₀ → kRandomSeq.eqa a₁ b₁ → kBool.eqa (kBool.validRandoms a₀ a₁) (kBool.validRandoms b₀ b₁)
    | eqa_deterministic {a b : kBlockRoundMode} : kBlockRoundMode.eqa a b → kBool.eqa (kBool.deterministic a) (kBool.deterministic b)
    | eqa_roundAway {a₀ b₀ : kBlockRoundMode} {a₁ b₁ a₂ b₂ : MRat} {a₃ b₃ : kBool} : kBlockRoundMode.eqa a₀ b₀ → a₁ = b₁ → a₂ = b₂ → kBool.eqa a₃ b₃ → kBool.eqa (kBool.roundAway a₀ a₁ a₂ a₃) (kBool.roundAway b₀ b₁ b₂ b₃)
    | eqa_clipsHigh {a b : kBlockRoundMode} : kBlockRoundMode.eqa a b → kBool.eqa (kBool.clipsHigh a) (kBool.clipsHigh b)
    | eqa_clipsLow {a b : kBlockRoundMode} : kBlockRoundMode.eqa a b → kBool.eqa (kBool.clipsLow a) (kBool.clipsLow b)
    | eqa_validCodes {a₀ b₀ : kFormat} {a₁ b₁ : kCodeSeq} : kFormat.eqa a₀ b₀ → kCodeSeq.eqa a₁ b₁ → kBool.eqa (kBool.validCodes a₀ a₁) (kBool.validCodes b₀ b₁)
    | eqa_validBlock {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ : kFormat} {a₃ b₃ : MRat} {a₄ b₄ : kCodeSeq} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → a₃ = b₃ → kCodeSeq.eqa a₄ b₄ → kBool.eqa (kBool.validBlock a₀ a₁ a₂ a₃ a₄) (kBool.validBlock b₀ b₁ b₂ b₃ b₄)
    | eqa_lt₁ {a₀ b₀ a₁ b₁ : MString} : a₀ = b₀ → a₁ = b₁ → kBool.eqa (kBool.lt₁ a₀ a₁) (kBool.lt₁ b₀ b₁)
    | eqa_lteq₁ {a₀ b₀ a₁ b₁ : MString} : a₀ = b₀ → a₁ = b₁ → kBool.eqa (kBool.lteq₁ a₀ a₁) (kBool.lteq₁ b₀ b₁)
    | eqa_gt₁ {a₀ b₀ a₁ b₁ : MString} : a₀ = b₀ → a₁ = b₁ → kBool.eqa (kBool.gt₁ a₀ a₁) (kBool.gt₁ b₀ b₁)
    | eqa_gteq₁ {a₀ b₀ a₁ b₁ : MString} : a₀ = b₀ → a₁ = b₁ → kBool.eqa (kBool.gteq₁ a₀ a₁) (kBool.gteq₁ b₀ b₁)
    | eqa_CompareLess {a₀ b₀ a₁ b₁ : kFormat} {a₂ b₂ a₃ b₃ : MRat} : kFormat.eqa a₀ b₀ → kFormat.eqa a₁ b₁ → a₂ = b₂ → a₃ = b₃ → kBool.eqa (kBool.CompareLess a₀ a₁ a₂ a₃) (kBool.CompareLess b₀ b₁ b₂ b₃)
    | eqa_CompareLessEqual {a₀ b₀ a₁ b₁ : kFormat} {a₂ b₂ a₃ b₃ : MRat} : kFormat.eqa a₀ b₀ → kFormat.eqa a₁ b₁ → a₂ = b₂ → a₃ = b₃ → kBool.eqa (kBool.CompareLessEqual a₀ a₁ a₂ a₃) (kBool.CompareLessEqual b₀ b₁ b₂ b₃)
    | eqa_CompareEqual {a₀ b₀ a₁ b₁ : kFormat} {a₂ b₂ a₃ b₃ : MRat} : kFormat.eqa a₀ b₀ → kFormat.eqa a₁ b₁ → a₂ = b₂ → a₃ = b₃ → kBool.eqa (kBool.CompareEqual a₀ a₁ a₂ a₃) (kBool.CompareEqual b₀ b₁ b₂ b₃)
    | eqa_CompareGreaterEqual {a₀ b₀ a₁ b₁ : kFormat} {a₂ b₂ a₃ b₃ : MRat} : kFormat.eqa a₀ b₀ → kFormat.eqa a₁ b₁ → a₂ = b₂ → a₃ = b₃ → kBool.eqa (kBool.CompareGreaterEqual a₀ a₁ a₂ a₃) (kBool.CompareGreaterEqual b₀ b₁ b₂ b₃)
    | eqa_CompareGreater {a₀ b₀ a₁ b₁ : kFormat} {a₂ b₂ a₃ b₃ : MRat} : kFormat.eqa a₀ b₀ → kFormat.eqa a₁ b₁ → a₂ = b₂ → a₃ = b₃ → kBool.eqa (kBool.CompareGreater a₀ a₁ a₂ a₃) (kBool.CompareGreater b₀ b₁ b₂ b₃)
    | eqa_IsZero {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqa a₀ b₀ → a₁ = b₁ → kBool.eqa (kBool.IsZero a₀ a₁) (kBool.IsZero b₀ b₁)
    | eqa_IsOne {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqa a₀ b₀ → a₁ = b₁ → kBool.eqa (kBool.IsOne a₀ a₁) (kBool.IsOne b₀ b₁)
    | eqa_IsNaN {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqa a₀ b₀ → a₁ = b₁ → kBool.eqa (kBool.IsNaN a₀ a₁) (kBool.IsNaN b₀ b₁)
    | eqa_IsInfinite {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqa a₀ b₀ → a₁ = b₁ → kBool.eqa (kBool.IsInfinite a₀ a₁) (kBool.IsInfinite b₀ b₁)
    | eqa_IsFinite {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqa a₀ b₀ → a₁ = b₁ → kBool.eqa (kBool.IsFinite a₀ a₁) (kBool.IsFinite b₀ b₁)
    | eqa_IsSignMinus {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqa a₀ b₀ → a₁ = b₁ → kBool.eqa (kBool.IsSignMinus a₀ a₁) (kBool.IsSignMinus b₀ b₁)
    | eqa_IsNormal {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqa a₀ b₀ → a₁ = b₁ → kBool.eqa (kBool.IsNormal a₀ a₁) (kBool.IsNormal b₀ b₁)
    | eqa_IsSubnormal {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqa a₀ b₀ → a₁ = b₁ → kBool.eqa (kBool.IsSubnormal a₀ a₁) (kBool.IsSubnormal b₀ b₁)
    | eqa_inF4 {a b : kFormat} : kFormat.eqa a b → kBool.eqa (kBool.inF4 a) (kBool.inF4 b)
    | eqa_inF8 {a b : kFormat} : kFormat.eqa a b → kBool.eqa (kBool.inF8 a) (kBool.inF8 b)
    | eqa_inFs {a b : kFormat} : kFormat.eqa a b → kBool.eqa (kBool.inFs a) (kBool.inFs b)
    | eqa_allowedExternal {a b : kFormat} : kFormat.eqa a b → kBool.eqa (kBool.allowedExternal a) (kBool.allowedExternal b)
    | eqa_containsFormat {a₀ b₀ : kFormat} {a₁ b₁ : kFormatSeq} : kFormat.eqa a₀ b₀ → kFormatSeq.eqa a₁ b₁ → kBool.eqa (kBool.containsFormat a₀ a₁) (kBool.containsFormat b₀ b₁)
    | eqa_validFX {a b : kFormatSeq} : kFormatSeq.eqa a b → kBool.eqa (kBool.validFX a) (kBool.validFX b)
    | eqa_validFXTail {a b : kFormatSeq} : kFormatSeq.eqa a b → kBool.eqa (kBool.validFXTail a) (kBool.validFXTail b)
    | eqa_allFormats {a b : kFormatSeq} : kFormatSeq.eqa a b → kBool.eqa (kBool.allFormats a) (kBool.allFormats b)
    | eqa_required {a₀ b₀ : kSpecialization} {a₁ b₁ : kFormatSeq} : kSpecialization.eqa a₀ b₀ → kFormatSeq.eqa a₁ b₁ → kBool.eqa (kBool.required a₀ a₁) (kBool.required b₀ b₁)
    | eqa_requiredNumeric {a₀ b₀ : MString} {a₁ b₁ a₂ b₂ : kFormatSeq} : a₀ = b₀ → kFormatSeq.eqa a₁ b₁ → kFormatSeq.eqa a₂ b₂ → kBool.eqa (kBool.requiredNumeric a₀ a₁ a₂) (kBool.requiredNumeric b₀ b₁ b₂)
    | eqa_requiredPlain {a₀ b₀ : MString} {a₁ b₁ a₂ b₂ : kFormatSeq} : a₀ = b₀ → kFormatSeq.eqa a₁ b₁ → kFormatSeq.eqa a₂ b₂ → kBool.eqa (kBool.requiredPlain a₀ a₁ a₂) (kBool.requiredPlain b₀ b₁ b₂)
    | eqa_minmaxName {a b : MString} : a = b → kBool.eqa (kBool.minmaxName a) (kBool.minmaxName b)
    | eqa_compareName {a b : MString} : a = b → kBool.eqa (kBool.compareName a) (kBool.compareName b)
    | eqa_predicateName {a b : MString} : a = b → kBool.eqa (kBool.predicateName a) (kBool.predicateName b)
    | eqa_formatNameOp {a b : MString} : a = b → kBool.eqa (kBool.formatNameOp a) (kBool.formatNameOp b)
    | eqa_numericPlainName {a b : MString} : a = b → kBool.eqa (kBool.numericPlainName a) (kBool.numericPlainName b)
    | eqa_blockElementArity {a₀ b₀ : MString} {a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqa (kBool.blockElementArity a₀ a₁) (kBool.blockElementArity b₀ b₁)
    | eqa_numericResult {a b : kSpecialization} : kSpecialization.eqa a b → kBool.eqa (kBool.numericResult a) (kBool.numericResult b)
    | eqa_hasDeclaration {a₀ b₀ : kSpecialization} {a₁ b₁ : kDeclarationSeq} : kSpecialization.eqa a₀ b₀ → kDeclarationSeq.eqa a₁ b₁ → kBool.eqa (kBool.hasDeclaration a₀ a₁) (kBool.hasDeclaration b₀ b₁)
    | eqa_declarationsCover {a₀ b₀ : kSpecializationSeq} {a₁ b₁ : kDeclarationSeq} : kSpecializationSeq.eqa a₀ b₀ → kDeclarationSeq.eqa a₁ b₁ → kBool.eqa (kBool.declarationsCover a₀ a₁) (kBool.declarationsCover b₀ b₁)
    | eqa_partition {a₀ b₀ : kCodeSeq} {a₁ b₁ : kPartitionSeq} : kCodeSeq.eqa a₀ b₀ → kPartitionSeq.eqa a₁ b₁ → kBool.eqa (kBool.partition a₀ a₁) (kBool.partition b₀ b₁)
    | eqa_partitionDisjoint {a b : kPartitionSeq} : kPartitionSeq.eqa a b → kBool.eqa (kBool.partitionDisjoint a) (kBool.partitionDisjoint b)
    | eqa_validSpecialization {a b : kSpecialization} : kSpecialization.eqa a b → kBool.eqa (kBool.validSpecialization a) (kBool.validSpecialization b)
    | eqa_numericArity {a₀ b₀ : MString} {a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqa (kBool.numericArity a₀ a₁) (kBool.numericArity b₀ b₁)
    | eqa_plainArity {a₀ b₀ : MString} {a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqa (kBool.plainArity a₀ a₁) (kBool.plainArity b₀ b₁)
    | eqa_wellFormedDeclaration {a b : kDeclaration} : kDeclaration.eqa a b → kBool.eqa (kBool.wellFormedDeclaration a) (kBool.wellFormedDeclaration b)
    | eqa_evidenceComplete {a b : kEvidence} : kEvidence.eqa a b → kBool.eqa (kBool.evidenceComplete a) (kBool.evidenceComplete b)
    | eqa_memberCode {a₀ b₀ : MRat} {a₁ b₁ : kCodeSeq} : a₀ = b₀ → kCodeSeq.eqa a₁ b₁ → kBool.eqa (kBool.memberCode a₀ a₁) (kBool.memberCode b₀ b₁)
    | eqa_disjointCodes {a₀ b₀ a₁ b₁ : kCodeSeq} : kCodeSeq.eqa a₀ b₀ → kCodeSeq.eqa a₁ b₁ → kBool.eqa (kBool.disjointCodes a₀ a₁) (kBool.disjointCodes b₀ b₁)
    | eqa_uniqueCodes {a b : kCodeSeq} : kCodeSeq.eqa a b → kBool.eqa (kBool.uniqueCodes a) (kBool.uniqueCodes b)
    | eqa_subsetCodes {a₀ b₀ a₁ b₁ : kCodeSeq} : kCodeSeq.eqa a₀ b₀ → kCodeSeq.eqa a₁ b₁ → kBool.eqa (kBool.subsetCodes a₀ a₁) (kBool.subsetCodes b₀ b₁)
    | eqa_partition2 {a₀ b₀ a₁ b₁ a₂ b₂ : kCodeSeq} : kCodeSeq.eqa a₀ b₀ → kCodeSeq.eqa a₁ b₁ → kCodeSeq.eqa a₂ b₂ → kBool.eqa (kBool.partition2 a₀ a₁ a₂) (kBool.partition2 b₀ b₁ b₂)
    | eqa_inArityTable {a₀ b₀ : MString} {a₁ b₁ : MRat} {a₂ b₂ : kArityTable} : a₀ = b₀ → a₁ = b₁ → kArityTable.eqa a₂ b₂ → kBool.eqa (kBool.inArityTable a₀ a₁ a₂) (kBool.inArityTable b₀ b₁ b₂)
    | eqa_TotalOrder {a₀ b₀ a₁ b₁ : kFormat} {a₂ b₂ a₃ b₃ : MRat} : kFormat.eqa a₀ b₀ → kFormat.eqa a₁ b₁ → a₂ = b₂ → a₃ = b₃ → kBool.eqa (kBool.TotalOrder a₀ a₁ a₂ a₃) (kBool.TotalOrder b₀ b₁ b₂ b₃)
    | eqa_eqeq₀ {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqa (kBool.eqeq₀ a₀ a₁) (kBool.eqeq₀ b₀ b₁)
    | eqa_ifthenelsefi {a₀ b₀ a₁ b₁ a₂ b₂ : kBool} : kBool.eqa a₀ b₀ → kBool.eqa a₁ b₁ → kBool.eqa a₂ b₂ → kBool.eqa (kBool.ifthenelsefi a₀ a₁ a₂) (kBool.ifthenelsefi b₀ b₁ b₂)
    | eqa_eqeq₁ {a₀ b₀ a₁ b₁ : kSignedness} : kSignedness.eqa a₀ b₀ → kSignedness.eqa a₁ b₁ → kBool.eqa (kBool.eqeq₁ a₀ a₁) (kBool.eqeq₁ b₀ b₁)
    | eqa_eqeq₂ {a₀ b₀ a₁ b₁ : kDomain} : kDomain.eqa a₀ b₀ → kDomain.eqa a₁ b₁ → kBool.eqa (kBool.eqeq₂ a₀ a₁) (kBool.eqeq₂ b₀ b₁)
    | eqa_eqslasheq₀ {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqa (kBool.eqslasheq₀ a₀ a₁) (kBool.eqslasheq₀ b₀ b₁)
    | eqa_eqeq₃ {a₀ b₀ a₁ b₁ : kBlockRoundMode} : kBlockRoundMode.eqa a₀ b₀ → kBlockRoundMode.eqa a₁ b₁ → kBool.eqa (kBool.eqeq₃ a₀ a₁) (kBool.eqeq₃ b₀ b₁)
    | eqa_eqeq₄ {a₀ b₀ a₁ b₁ : kBool} : kBool.eqa a₀ b₀ → kBool.eqa a₁ b₁ → kBool.eqa (kBool.eqeq₄ a₀ a₁) (kBool.eqeq₄ b₀ b₁)
    | eqa_eqeq₅ {a₀ b₀ a₁ b₁ : MString} : a₀ = b₀ → a₁ = b₁ → kBool.eqa (kBool.eqeq₅ a₀ a₁) (kBool.eqeq₅ b₀ b₁)
    | eqa_eqeq₆ {a₀ b₀ a₁ b₁ : kFormat} : kFormat.eqa a₀ b₀ → kFormat.eqa a₁ b₁ → kBool.eqa (kBool.eqeq₆ a₀ a₁) (kBool.eqeq₆ b₀ b₁)
    | eqa_eqeq₇ {a₀ b₀ a₁ b₁ : kProjSpec} : kProjSpec.eqa a₀ b₀ → kProjSpec.eqa a₁ b₁ → kBool.eqa (kBool.eqeq₇ a₀ a₁) (kBool.eqeq₇ b₀ b₁)
    | eqa_eqslasheq₁ {a₀ b₀ a₁ b₁ : kBool} : kBool.eqa a₀ b₀ → kBool.eqa a₁ b₁ → kBool.eqa (kBool.eqslasheq₁ a₀ a₁) (kBool.eqslasheq₁ b₀ b₁)
    | eqa_eqslasheq₂ {a₀ b₀ a₁ b₁ : MString} : a₀ = b₀ → a₁ = b₁ → kBool.eqa (kBool.eqslasheq₂ a₀ a₁) (kBool.eqslasheq₂ b₀ b₁)
    | eqa_eqeq₈ {a₀ b₀ a₁ b₁ : kSpecialization} : kSpecialization.eqa a₀ b₀ → kSpecialization.eqa a₁ b₁ → kBool.eqa (kBool.eqeq₈ a₀ a₁) (kBool.eqeq₈ b₀ b₁)
    -- Structural axioms
    | and_comm {a b} : kBool.eqa (kBool.and a b) (kBool.and b a)
    | and_assoc {a b c} : kBool.eqa (kBool.and a (kBool.and b c)) (kBool.and (kBool.and a b) c)
    | or_comm {a b} : kBool.eqa (kBool.or a b) (kBool.or b a)
    | or_assoc {a b c} : kBool.eqa (kBool.or a (kBool.or b c)) (kBool.or (kBool.or a b) c)
    | xor_comm {a b} : kBool.eqa (kBool.xor a b) (kBool.xor b a)
    | xor_assoc {a b c} : kBool.eqa (kBool.xor a (kBool.xor b c)) (kBool.xor (kBool.xor a b) c)

  inductive kXReal.eqa: kXReal → kXReal → Prop
    | refl {a} : kXReal.eqa a a
    | symm {a b} : kXReal.eqa a b → kXReal.eqa b a
    | trans {a b c} : kXReal.eqa a b → kXReal.eqa b c → kXReal.eqa a c
    -- Congruence axioms for each operator
    | eqa_fin {a b : MRat} : a = b → kXReal.eqa (kXReal.fin a) (kXReal.fin b)
    | eqa_externalDecode {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqa a₀ b₀ → a₁ = b₁ → kXReal.eqa (kXReal.externalDecode a₀ a₁) (kXReal.externalDecode b₀ b₁)
    | eqa_decode {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqa a₀ b₀ → a₁ = b₁ → kXReal.eqa (kXReal.decode a₀ a₁) (kXReal.decode b₀ b₁)
    | eqa_roundToPrecision {a₀ b₀ a₁ b₁ : MRat} {a₂ b₂ : kBlockRoundMode} {a₃ b₃ : kXReal} : a₀ = b₀ → a₁ = b₁ → kBlockRoundMode.eqa a₂ b₂ → kXReal.eqa a₃ b₃ → kXReal.eqa (kXReal.roundToPrecision a₀ a₁ a₂ a₃) (kXReal.roundToPrecision b₀ b₁ b₂ b₃)
    | eqa_saturate {a₀ b₀ a₁ b₁ : MRat} {a₂ b₂ : kSatMode} {a₃ b₃ : kBlockRoundMode} {a₄ b₄ : kXReal} {a₅ b₅ : kSignedness} {a₆ b₆ : kDomain} : a₀ = b₀ → a₁ = b₁ → kSatMode.eqa a₂ b₂ → kBlockRoundMode.eqa a₃ b₃ → kXReal.eqa a₄ b₄ → kSignedness.eqa a₅ b₅ → kDomain.eqa a₆ b₆ → kXReal.eqa (kXReal.saturate a₀ a₁ a₂ a₃ a₄ a₅ a₆) (kXReal.saturate b₀ b₁ b₂ b₃ b₄ b₅ b₆)
    | eqa_overflow {a₀ b₀ : kSignedness} {a₁ b₁ : kDomain} {a₂ b₂ : kBool} : kSignedness.eqa a₀ b₀ → kDomain.eqa a₁ b₁ → kBool.eqa a₂ b₂ → kXReal.eqa (kXReal.overflow a₀ a₁ a₂) (kXReal.overflow b₀ b₁ b₂)
    | eqa_omegaConvert {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaConvert a) (kXReal.omegaConvert b)
    | eqa_omegaAbs {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaAbs a) (kXReal.omegaAbs b)
    | eqa_omegaNegate {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaNegate a) (kXReal.omegaNegate b)
    | eqa_omegaRecip {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaRecip a) (kXReal.omegaRecip b)
    | eqa_omegaCopySign {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.omegaCopySign a₀ a₁) (kXReal.omegaCopySign b₀ b₁)
    | eqa_omegaAdd {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.omegaAdd a₀ a₁) (kXReal.omegaAdd b₀ b₁)
    | eqa_omegaSubtract {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.omegaSubtract a₀ a₁) (kXReal.omegaSubtract b₀ b₁)
    | eqa_omegaMultiply {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.omegaMultiply a₀ a₁) (kXReal.omegaMultiply b₀ b₁)
    | eqa_omegaDivide {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.omegaDivide a₀ a₁) (kXReal.omegaDivide b₀ b₁)
    | eqa_omegaFMA {a₀ b₀ a₁ b₁ a₂ b₂ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa a₂ b₂ → kXReal.eqa (kXReal.omegaFMA a₀ a₁ a₂) (kXReal.omegaFMA b₀ b₁ b₂)
    | eqa_omegaFAA {a₀ b₀ a₁ b₁ a₂ b₂ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa a₂ b₂ → kXReal.eqa (kXReal.omegaFAA a₀ a₁ a₂) (kXReal.omegaFAA b₀ b₁ b₂)
    | eqa_at {a₀ b₀ : kXSeq} {a₁ b₁ : MRat} : kXSeq.eqa a₀ b₀ → a₁ = b₁ → kXReal.eqa (kXReal.«at» a₀ a₁) (kXReal.«at» b₀ b₁)
    | eqa_normalizeElement {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.normalizeElement a₀ a₁) (kXReal.normalizeElement b₀ b₁)
    | eqa_omegaMinimum {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.omegaMinimum a₀ a₁) (kXReal.omegaMinimum b₀ b₁)
    | eqa_omegaMaximum {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.omegaMaximum a₀ a₁) (kXReal.omegaMaximum b₀ b₁)
    | eqa_omegaMinimumNumber {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.omegaMinimumNumber a₀ a₁) (kXReal.omegaMinimumNumber b₀ b₁)
    | eqa_omegaMaximumNumber {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.omegaMaximumNumber a₀ a₁) (kXReal.omegaMaximumNumber b₀ b₁)
    | eqa_omegaMinimumMagnitude {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.omegaMinimumMagnitude a₀ a₁) (kXReal.omegaMinimumMagnitude b₀ b₁)
    | eqa_omegaMaximumMagnitude {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.omegaMaximumMagnitude a₀ a₁) (kXReal.omegaMaximumMagnitude b₀ b₁)
    | eqa_omegaMinimumMagnitudeNumber {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.omegaMinimumMagnitudeNumber a₀ a₁) (kXReal.omegaMinimumMagnitudeNumber b₀ b₁)
    | eqa_omegaMaximumMagnitudeNumber {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.omegaMaximumMagnitudeNumber a₀ a₁) (kXReal.omegaMaximumMagnitudeNumber b₀ b₁)
    | eqa_omegaMinimumFinite {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.omegaMinimumFinite a₀ a₁) (kXReal.omegaMinimumFinite b₀ b₁)
    | eqa_omegaMaximumFinite {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.omegaMaximumFinite a₀ a₁) (kXReal.omegaMaximumFinite b₀ b₁)
    | eqa_omegaClamp {a₀ b₀ a₁ b₁ a₂ b₂ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa a₂ b₂ → kXReal.eqa (kXReal.omegaClamp a₀ a₁ a₂) (kXReal.omegaClamp b₀ b₁ b₂)
    | eqa_foldAdd {a₀ b₀ : kXReal} {a₁ b₁ : kXSeq} : kXReal.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXReal.eqa (kXReal.foldAdd a₀ a₁) (kXReal.foldAdd b₀ b₁)
    | eqa_foldMultiply {a₀ b₀ : kXReal} {a₁ b₁ : kXSeq} : kXReal.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXReal.eqa (kXReal.foldMultiply a₀ a₁) (kXReal.foldMultiply b₀ b₁)
    | eqa_foldMaximumFinite {a₀ b₀ : kXReal} {a₁ b₁ : kXSeq} : kXReal.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXReal.eqa (kXReal.foldMaximumFinite a₀ a₁) (kXReal.foldMaximumFinite b₀ b₁)
    | eqa_realAdd {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.realAdd a₀ a₁) (kXReal.realAdd b₀ b₁)
    | eqa_realMultiply {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.realMultiply a₀ a₁) (kXReal.realMultiply b₀ b₁)
    | eqa_realNegate {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.realNegate a) (kXReal.realNegate b)
    | eqa_realAbs {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.realAbs a) (kXReal.realAbs b)
    | eqa_realDivide {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.realDivide a₀ a₁) (kXReal.realDivide b₀ b₁)
    | eqa_piMultiple {a b : MRat} : a = b → kXReal.eqa (kXReal.piMultiple a) (kXReal.piMultiple b)
    | eqa_omegaHypot {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.omegaHypot a₀ a₁) (kXReal.omegaHypot b₀ b₁)
    | eqa_omegaArcTan2 {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.omegaArcTan2 a₀ a₁) (kXReal.omegaArcTan2 b₀ b₁)
    | eqa_omegaArcTan2Pi {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa (kXReal.omegaArcTan2Pi a₀ a₁) (kXReal.omegaArcTan2Pi b₀ b₁)
    | eqa_omegaSqrt {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaSqrt a) (kXReal.omegaSqrt b)
    | eqa_omegaRSqrt {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaRSqrt a) (kXReal.omegaRSqrt b)
    | eqa_omegaExp {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaExp a) (kXReal.omegaExp b)
    | eqa_omegaExp2 {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaExp2 a) (kXReal.omegaExp2 b)
    | eqa_omegaLog {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaLog a) (kXReal.omegaLog b)
    | eqa_omegaLog2 {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaLog2 a) (kXReal.omegaLog2 b)
    | eqa_omegaLogOnePlus {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaLogOnePlus a) (kXReal.omegaLogOnePlus b)
    | eqa_omegaExpMinusOne {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaExpMinusOne a) (kXReal.omegaExpMinusOne b)
    | eqa_omegaSin {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaSin a) (kXReal.omegaSin b)
    | eqa_omegaCos {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaCos a) (kXReal.omegaCos b)
    | eqa_omegaTan {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaTan a) (kXReal.omegaTan b)
    | eqa_omegaArcSin {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaArcSin a) (kXReal.omegaArcSin b)
    | eqa_omegaArcCos {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaArcCos a) (kXReal.omegaArcCos b)
    | eqa_omegaArcTan {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaArcTan a) (kXReal.omegaArcTan b)
    | eqa_omegaSinh {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaSinh a) (kXReal.omegaSinh b)
    | eqa_omegaCosh {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaCosh a) (kXReal.omegaCosh b)
    | eqa_omegaTanh {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaTanh a) (kXReal.omegaTanh b)
    | eqa_omegaArcSinh {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaArcSinh a) (kXReal.omegaArcSinh b)
    | eqa_omegaArcCosh {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaArcCosh a) (kXReal.omegaArcCosh b)
    | eqa_omegaArcTanh {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaArcTanh a) (kXReal.omegaArcTanh b)
    | eqa_omegaSinPi {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaSinPi a) (kXReal.omegaSinPi b)
    | eqa_omegaCosPi {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaCosPi a) (kXReal.omegaCosPi b)
    | eqa_omegaTanPi {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaTanPi a) (kXReal.omegaTanPi b)
    | eqa_omegaArcSinPi {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaArcSinPi a) (kXReal.omegaArcSinPi b)
    | eqa_omegaArcCosPi {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaArcCosPi a) (kXReal.omegaArcCosPi b)
    | eqa_omegaArcTanPi {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaArcTanPi a) (kXReal.omegaArcTanPi b)
    | eqa_omegaSoftplus {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.omegaSoftplus a) (kXReal.omegaSoftplus b)
    | eqa_exprSqrt {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.exprSqrt a) (kXReal.exprSqrt b)
    | eqa_exprExp {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.exprExp a) (kXReal.exprExp b)
    | eqa_exprExp2 {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.exprExp2 a) (kXReal.exprExp2 b)
    | eqa_exprLog {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.exprLog a) (kXReal.exprLog b)
    | eqa_exprLog2 {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.exprLog2 a) (kXReal.exprLog2 b)
    | eqa_exprSin {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.exprSin a) (kXReal.exprSin b)
    | eqa_exprCos {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.exprCos a) (kXReal.exprCos b)
    | eqa_exprTan {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.exprTan a) (kXReal.exprTan b)
    | eqa_exprArcSin {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.exprArcSin a) (kXReal.exprArcSin b)
    | eqa_exprArcCos {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.exprArcCos a) (kXReal.exprArcCos b)
    | eqa_exprArcTan {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.exprArcTan a) (kXReal.exprArcTan b)
    | eqa_exprSinh {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.exprSinh a) (kXReal.exprSinh b)
    | eqa_exprCosh {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.exprCosh a) (kXReal.exprCosh b)
    | eqa_exprTanh {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.exprTanh a) (kXReal.exprTanh b)
    | eqa_exprArcSinh {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.exprArcSinh a) (kXReal.exprArcSinh b)
    | eqa_exprArcCosh {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.exprArcCosh a) (kXReal.exprArcCosh b)
    | eqa_exprArcTanh {a b : kXReal} : kXReal.eqa a b → kXReal.eqa (kXReal.exprArcTanh a) (kXReal.exprArcTanh b)
    | eqa_ifthenelsefi {a₀ b₀ : kBool} {a₁ b₁ a₂ b₂ : kXReal} : kBool.eqa a₀ b₀ → kXReal.eqa a₁ b₁ → kXReal.eqa a₂ b₂ → kXReal.eqa (kXReal.ifthenelsefi a₀ a₁ a₂) (kXReal.ifthenelsefi b₀ b₁ b₂)

  inductive kFormat.eqa: kFormat → kFormat → Prop
    | refl {a} : kFormat.eqa a a
    | symm {a b} : kFormat.eqa a b → kFormat.eqa b a
    | trans {a b c} : kFormat.eqa a b → kFormat.eqa b c → kFormat.eqa a c
    -- Congruence axioms for each operator
    | eqa_Binary {a₀ b₀ a₁ b₁ : MRat} {a₂ b₂ : kSignedness} {a₃ b₃ : kDomain} : a₀ = b₀ → a₁ = b₁ → kSignedness.eqa a₂ b₂ → kDomain.eqa a₃ b₃ → kFormat.eqa (kFormat.Binary a₀ a₁ a₂ a₃) (kFormat.Binary b₀ b₁ b₂ b₃)
    | eqa_at {a₀ b₀ : kFormatSeq} {a₁ b₁ : MRat} : kFormatSeq.eqa a₀ b₀ → a₁ = b₁ → kFormat.eqa (kFormat.«at» a₀ a₁) (kFormat.«at» b₀ b₁)

  inductive kSignedness.eqa: kSignedness → kSignedness → Prop
    | refl {a} : kSignedness.eqa a a
    | symm {a b} : kSignedness.eqa a b → kSignedness.eqa b a
    | trans {a b c} : kSignedness.eqa a b → kSignedness.eqa b c → kSignedness.eqa a c
    -- Congruence axioms for each operator
    | eqa_SignednessOf {a b : kFormat} : kFormat.eqa a b → kSignedness.eqa (kSignedness.SignednessOf a) (kSignedness.SignednessOf b)

  inductive kDomain.eqa: kDomain → kDomain → Prop
    | refl {a} : kDomain.eqa a a
    | symm {a b} : kDomain.eqa a b → kDomain.eqa b a
    | trans {a b c} : kDomain.eqa a b → kDomain.eqa b c → kDomain.eqa a c
    -- Congruence axioms for each operator
    | eqa_DomainOf {a b : kFormat} : kFormat.eqa a b → kDomain.eqa (kDomain.DomainOf a) (kDomain.DomainOf b)

  inductive kBoundQuery.eqa: kBoundQuery → kBoundQuery → Prop
    | refl {a} : kBoundQuery.eqa a a
    | symm {a b} : kBoundQuery.eqa a b → kBoundQuery.eqa b a
    | trans {a b c} : kBoundQuery.eqa a b → kBoundQuery.eqa b c → kBoundQuery.eqa a c
    -- Congruence axioms for each operator

  inductive kRandomSeq.eqa: kRandomSeq → kRandomSeq → Prop
    | refl {a} : kRandomSeq.eqa a a
    | symm {a b} : kRandomSeq.eqa a b → kRandomSeq.eqa b a
    | trans {a b c} : kRandomSeq.eqa a b → kRandomSeq.eqa b c → kRandomSeq.eqa a c
    -- Congruence axioms for each operator
    | eqa_rcons {a₀ b₀ : MRat} {a₁ b₁ : kRandomSeq} : a₀ = b₀ → kRandomSeq.eqa a₁ b₁ → kRandomSeq.eqa (kRandomSeq.rcons a₀ a₁) (kRandomSeq.rcons b₀ b₁)

  inductive kBlockRoundMode.eqa: kBlockRoundMode → kBlockRoundMode → Prop
    | refl {a} : kBlockRoundMode.eqa a a
    | symm {a b} : kBlockRoundMode.eqa a b → kBlockRoundMode.eqa b a
    | trans {a b c} : kBlockRoundMode.eqa a b → kBlockRoundMode.eqa b c → kBlockRoundMode.eqa a c
    -- Congruence axioms for each operator
    | eqa_StochasticA {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBlockRoundMode.eqa (kBlockRoundMode.StochasticA a₀ a₁) (kBlockRoundMode.StochasticA b₀ b₁)
    | eqa_StochasticB {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBlockRoundMode.eqa (kBlockRoundMode.StochasticB a₀ a₁) (kBlockRoundMode.StochasticB b₀ b₁)
    | eqa_StochasticC {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBlockRoundMode.eqa (kBlockRoundMode.StochasticC a₀ a₁) (kBlockRoundMode.StochasticC b₀ b₁)
    | eqa_BlockStochasticA {a₀ b₀ : MRat} {a₁ b₁ : kRandomSeq} : a₀ = b₀ → kRandomSeq.eqa a₁ b₁ → kBlockRoundMode.eqa (kBlockRoundMode.BlockStochasticA a₀ a₁) (kBlockRoundMode.BlockStochasticA b₀ b₁)
    | eqa_BlockStochasticB {a₀ b₀ : MRat} {a₁ b₁ : kRandomSeq} : a₀ = b₀ → kRandomSeq.eqa a₁ b₁ → kBlockRoundMode.eqa (kBlockRoundMode.BlockStochasticB a₀ a₁) (kBlockRoundMode.BlockStochasticB b₀ b₁)
    | eqa_BlockStochasticC {a₀ b₀ : MRat} {a₁ b₁ : kRandomSeq} : a₀ = b₀ → kRandomSeq.eqa a₁ b₁ → kBlockRoundMode.eqa (kBlockRoundMode.BlockStochasticC a₀ a₁) (kBlockRoundMode.BlockStochasticC b₀ b₁)
    | eqa_RoundOf {a b : kProjSpec} : kProjSpec.eqa a b → kBlockRoundMode.eqa (kBlockRoundMode.RoundOf a) (kBlockRoundMode.RoundOf b)

  inductive kSatMode.eqa: kSatMode → kSatMode → Prop
    | refl {a} : kSatMode.eqa a a
    | symm {a b} : kSatMode.eqa a b → kSatMode.eqa b a
    | trans {a b c} : kSatMode.eqa a b → kSatMode.eqa b c → kSatMode.eqa a c
    -- Congruence axioms for each operator
    | eqa_SatOf {a b : kProjSpec} : kProjSpec.eqa a b → kSatMode.eqa (kSatMode.SatOf a) (kSatMode.SatOf b)

  inductive kProjSpec.eqa: kProjSpec → kProjSpec → Prop
    | refl {a} : kProjSpec.eqa a a
    | symm {a b} : kProjSpec.eqa a b → kProjSpec.eqa b a
    | trans {a b c} : kProjSpec.eqa a b → kProjSpec.eqa b c → kProjSpec.eqa a c
    -- Congruence axioms for each operator
    | eqa_proj {a₀ b₀ : kBlockRoundMode} {a₁ b₁ : kSatMode} : kBlockRoundMode.eqa a₀ b₀ → kSatMode.eqa a₁ b₁ → kProjSpec.eqa (kProjSpec.proj a₀ a₁) (kProjSpec.proj b₀ b₁)
    | eqa_projectionAt {a₀ b₀ : kBlockProjSpec} {a₁ b₁ : MRat} : kBlockProjSpec.eqa a₀ b₀ → a₁ = b₁ → kProjSpec.eqa (kProjSpec.projectionAt a₀ a₁) (kProjSpec.projectionAt b₀ b₁)

  inductive kBlockProjSpec.eqa: kBlockProjSpec → kBlockProjSpec → Prop
    | refl {a} : kBlockProjSpec.eqa a a
    | symm {a b} : kBlockProjSpec.eqa a b → kBlockProjSpec.eqa b a
    | trans {a b c} : kBlockProjSpec.eqa a b → kBlockProjSpec.eqa b c → kBlockProjSpec.eqa a c
    -- Congruence axioms for each operator
    | eqa_bproj {a₀ b₀ : kBlockRoundMode} {a₁ b₁ : kSatMode} : kBlockRoundMode.eqa a₀ b₀ → kSatMode.eqa a₁ b₁ → kBlockProjSpec.eqa (kBlockProjSpec.bproj a₀ a₁) (kBlockProjSpec.bproj b₀ b₁)
    | eqa_singletonLift {a b : kProjSpec} : kProjSpec.eqa a b → kBlockProjSpec.eqa (kBlockProjSpec.singletonLift a) (kBlockProjSpec.singletonLift b)

  inductive kXSeq.eqa: kXSeq → kXSeq → Prop
    | refl {a} : kXSeq.eqa a a
    | symm {a b} : kXSeq.eqa a b → kXSeq.eqa b a
    | trans {a b c} : kXSeq.eqa a b → kXSeq.eqa b c → kXSeq.eqa a c
    -- Congruence axioms for each operator
    | eqa_xcons {a₀ b₀ : kXReal} {a₁ b₁ : kXSeq} : kXReal.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.xcons a₀ a₁) (kXSeq.xcons b₀ b₁)
    | eqa_decodeElements {a₀ b₀ : kFormat} {a₁ b₁ : kCodeSeq} : kFormat.eqa a₀ b₀ → kCodeSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.decodeElements a₀ a₁) (kXSeq.decodeElements b₀ b₁)
    | eqa_multiplyElements {a₀ b₀ : kXReal} {a₁ b₁ : kXSeq} : kXReal.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.multiplyElements a₀ a₁) (kXSeq.multiplyElements b₀ b₁)
    | eqa_blockDecode {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ : kFormat} {a₃ b₃ : MRat} {a₄ b₄ : kCodeSeq} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → a₃ = b₃ → kCodeSeq.eqa a₄ b₄ → kXSeq.eqa (kXSeq.blockDecode a₀ a₁ a₂ a₃ a₄) (kXSeq.blockDecode b₀ b₁ b₂ b₃ b₄)
    | eqa_absElements {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.absElements a) (kXSeq.absElements b)
    | eqa_pairProducts {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.pairProducts a₀ a₁) (kXSeq.pairProducts b₀ b₁)
    | eqa_mapConvert {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapConvert a) (kXSeq.mapConvert b)
    | eqa_mapAbs {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapAbs a) (kXSeq.mapAbs b)
    | eqa_mapNegate {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapNegate a) (kXSeq.mapNegate b)
    | eqa_mapCopySign {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.mapCopySign a₀ a₁) (kXSeq.mapCopySign b₀ b₁)
    | eqa_mapAdd {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.mapAdd a₀ a₁) (kXSeq.mapAdd b₀ b₁)
    | eqa_mapSubtract {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.mapSubtract a₀ a₁) (kXSeq.mapSubtract b₀ b₁)
    | eqa_mapMultiply {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.mapMultiply a₀ a₁) (kXSeq.mapMultiply b₀ b₁)
    | eqa_mapDivide {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.mapDivide a₀ a₁) (kXSeq.mapDivide b₀ b₁)
    | eqa_mapFMA {a₀ b₀ a₁ b₁ a₂ b₂ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa a₂ b₂ → kXSeq.eqa (kXSeq.mapFMA a₀ a₁ a₂) (kXSeq.mapFMA b₀ b₁ b₂)
    | eqa_mapFAA {a₀ b₀ a₁ b₁ a₂ b₂ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa a₂ b₂ → kXSeq.eqa (kXSeq.mapFAA a₀ a₁ a₂) (kXSeq.mapFAA b₀ b₁ b₂)
    | eqa_mapRecip {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapRecip a) (kXSeq.mapRecip b)
    | eqa_mapMinimum {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.mapMinimum a₀ a₁) (kXSeq.mapMinimum b₀ b₁)
    | eqa_mapMaximum {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.mapMaximum a₀ a₁) (kXSeq.mapMaximum b₀ b₁)
    | eqa_mapMinimumNumber {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.mapMinimumNumber a₀ a₁) (kXSeq.mapMinimumNumber b₀ b₁)
    | eqa_mapMaximumNumber {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.mapMaximumNumber a₀ a₁) (kXSeq.mapMaximumNumber b₀ b₁)
    | eqa_mapMinimumMagnitude {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.mapMinimumMagnitude a₀ a₁) (kXSeq.mapMinimumMagnitude b₀ b₁)
    | eqa_mapMaximumMagnitude {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.mapMaximumMagnitude a₀ a₁) (kXSeq.mapMaximumMagnitude b₀ b₁)
    | eqa_mapMinimumMagnitudeNumber {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.mapMinimumMagnitudeNumber a₀ a₁) (kXSeq.mapMinimumMagnitudeNumber b₀ b₁)
    | eqa_mapMaximumMagnitudeNumber {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.mapMaximumMagnitudeNumber a₀ a₁) (kXSeq.mapMaximumMagnitudeNumber b₀ b₁)
    | eqa_mapMinimumFinite {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.mapMinimumFinite a₀ a₁) (kXSeq.mapMinimumFinite b₀ b₁)
    | eqa_mapMaximumFinite {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.mapMaximumFinite a₀ a₁) (kXSeq.mapMaximumFinite b₀ b₁)
    | eqa_mapClamp {a₀ b₀ a₁ b₁ a₂ b₂ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa a₂ b₂ → kXSeq.eqa (kXSeq.mapClamp a₀ a₁ a₂) (kXSeq.mapClamp b₀ b₁ b₂)
    | eqa_mapSqrt {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapSqrt a) (kXSeq.mapSqrt b)
    | eqa_mapRSqrt {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapRSqrt a) (kXSeq.mapRSqrt b)
    | eqa_mapExp {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapExp a) (kXSeq.mapExp b)
    | eqa_mapExp2 {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapExp2 a) (kXSeq.mapExp2 b)
    | eqa_mapLog {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapLog a) (kXSeq.mapLog b)
    | eqa_mapLog2 {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapLog2 a) (kXSeq.mapLog2 b)
    | eqa_mapLogOnePlus {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapLogOnePlus a) (kXSeq.mapLogOnePlus b)
    | eqa_mapExpMinusOne {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapExpMinusOne a) (kXSeq.mapExpMinusOne b)
    | eqa_mapSin {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapSin a) (kXSeq.mapSin b)
    | eqa_mapCos {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapCos a) (kXSeq.mapCos b)
    | eqa_mapTan {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapTan a) (kXSeq.mapTan b)
    | eqa_mapArcSin {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapArcSin a) (kXSeq.mapArcSin b)
    | eqa_mapArcCos {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapArcCos a) (kXSeq.mapArcCos b)
    | eqa_mapArcTan {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapArcTan a) (kXSeq.mapArcTan b)
    | eqa_mapSinh {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapSinh a) (kXSeq.mapSinh b)
    | eqa_mapCosh {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapCosh a) (kXSeq.mapCosh b)
    | eqa_mapTanh {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapTanh a) (kXSeq.mapTanh b)
    | eqa_mapArcSinh {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapArcSinh a) (kXSeq.mapArcSinh b)
    | eqa_mapArcCosh {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapArcCosh a) (kXSeq.mapArcCosh b)
    | eqa_mapArcTanh {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapArcTanh a) (kXSeq.mapArcTanh b)
    | eqa_mapSinPi {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapSinPi a) (kXSeq.mapSinPi b)
    | eqa_mapCosPi {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapCosPi a) (kXSeq.mapCosPi b)
    | eqa_mapTanPi {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapTanPi a) (kXSeq.mapTanPi b)
    | eqa_mapArcSinPi {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapArcSinPi a) (kXSeq.mapArcSinPi b)
    | eqa_mapArcCosPi {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapArcCosPi a) (kXSeq.mapArcCosPi b)
    | eqa_mapArcTanPi {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapArcTanPi a) (kXSeq.mapArcTanPi b)
    | eqa_mapSoftplus {a b : kXSeq} : kXSeq.eqa a b → kXSeq.eqa (kXSeq.mapSoftplus a) (kXSeq.mapSoftplus b)
    | eqa_mapHypot {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.mapHypot a₀ a₁) (kXSeq.mapHypot b₀ b₁)
    | eqa_mapArcTan2 {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.mapArcTan2 a₀ a₁) (kXSeq.mapArcTan2 b₀ b₁)
    | eqa_mapArcTan2Pi {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqa a₀ b₀ → kXSeq.eqa a₁ b₁ → kXSeq.eqa (kXSeq.mapArcTan2Pi a₀ a₁) (kXSeq.mapArcTan2Pi b₀ b₁)

  inductive kCodeSeq.eqa: kCodeSeq → kCodeSeq → Prop
    | refl {a} : kCodeSeq.eqa a a
    | symm {a b} : kCodeSeq.eqa a b → kCodeSeq.eqa b a
    | trans {a b c} : kCodeSeq.eqa a b → kCodeSeq.eqa b c → kCodeSeq.eqa a c
    -- Congruence axioms for each operator
    | eqa_ccons {a₀ b₀ : MRat} {a₁ b₁ : kCodeSeq} : a₀ = b₀ → kCodeSeq.eqa a₁ b₁ → kCodeSeq.eqa (kCodeSeq.ccons a₀ a₁) (kCodeSeq.ccons b₀ b₁)
    | eqa_blockProject {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ : kFormat} {a₃ b₃ : kBlockProjSpec} {a₄ b₄ : MRat} {a₅ b₅ : kXSeq} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kBlockProjSpec.eqa a₃ b₃ → a₄ = b₄ → kXSeq.eqa a₅ b₅ → kCodeSeq.eqa (kCodeSeq.blockProject a₀ a₁ a₂ a₃ a₄ a₅) (kCodeSeq.blockProject b₀ b₁ b₂ b₃ b₄ b₅)
    | eqa_projectElements {a₀ b₀ : kFormat} {a₁ b₁ : kBlockProjSpec} {a₂ b₂ : kXReal} {a₃ b₃ : kXSeq} {a₄ b₄ : MRat} : kFormat.eqa a₀ b₀ → kBlockProjSpec.eqa a₁ b₁ → kXReal.eqa a₂ b₂ → kXSeq.eqa a₃ b₃ → a₄ = b₄ → kCodeSeq.eqa (kCodeSeq.projectElements a₀ a₁ a₂ a₃ a₄) (kCodeSeq.projectElements b₀ b₁ b₂ b₃ b₄)
    | eqa_projectUnscaled {a₀ b₀ : kFormat} {a₁ b₁ : kBlockProjSpec} {a₂ b₂ : kXSeq} {a₃ b₃ : MRat} : kFormat.eqa a₀ b₀ → kBlockProjSpec.eqa a₁ b₁ → kXSeq.eqa a₂ b₂ → a₃ = b₃ → kCodeSeq.eqa (kCodeSeq.projectUnscaled a₀ a₁ a₂ a₃) (kCodeSeq.projectUnscaled b₀ b₁ b₂ b₃)
    | eqa_at {a₀ b₀ : kPartitionSeq} {a₁ b₁ : MRat} : kPartitionSeq.eqa a₀ b₀ → a₁ = b₁ → kCodeSeq.eqa (kCodeSeq.«at» a₀ a₁) (kCodeSeq.«at» b₀ b₁)
    | eqa_partitionUnion {a b : kPartitionSeq} : kPartitionSeq.eqa a b → kCodeSeq.eqa (kCodeSeq.partitionUnion a) (kCodeSeq.partitionUnion b)
    | eqa_appendCodes {a₀ b₀ a₁ b₁ : kCodeSeq} : kCodeSeq.eqa a₀ b₀ → kCodeSeq.eqa a₁ b₁ → kCodeSeq.eqa (kCodeSeq.appendCodes a₀ a₁) (kCodeSeq.appendCodes b₀ b₁)
    | eqa_ConvertFromBlock {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ : kFormat} {a₄ b₄ : kBlockProjSpec} {a₅ b₅ : MRat} {a₆ b₆ : kCodeSeq} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kBlockProjSpec.eqa a₄ b₄ → a₅ = b₅ → kCodeSeq.eqa a₆ b₆ → kCodeSeq.eqa (kCodeSeq.ConvertFromBlock a₀ a₁ a₂ a₃ a₄ a₅ a₆) (kCodeSeq.ConvertFromBlock b₀ b₁ b₂ b₃ b₄ b₅ b₆)
    | eqa_ConvertToBlock {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ : kFormat} {a₄ b₄ : kBlockProjSpec} {a₅ b₅ : kCodeSeq} {a₆ b₆ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kBlockProjSpec.eqa a₄ b₄ → kCodeSeq.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa (kCodeSeq.ConvertToBlock a₀ a₁ a₂ a₃ a₄ a₅ a₆) (kCodeSeq.ConvertToBlock b₀ b₁ b₂ b₃ b₄ b₅ b₆)

  inductive kBlock.eqa: kBlock → kBlock → Prop
    | refl {a} : kBlock.eqa a a
    | symm {a b} : kBlock.eqa a b → kBlock.eqa b a
    | trans {a b c} : kBlock.eqa a b → kBlock.eqa b c → kBlock.eqa a c
    -- Congruence axioms for each operator
    | eqa_block {a₀ b₀ : MRat} {a₁ b₁ : kCodeSeq} : a₀ = b₀ → kCodeSeq.eqa a₁ b₁ → kBlock.eqa (kBlock.block a₀ a₁) (kBlock.block b₀ b₁)
    | eqa_ConvertToBlockMaxAbsFinite {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ : kFormat} {a₄ b₄ : kProjSpec} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : kCodeSeq} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kProjSpec.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → kCodeSeq.eqa a₆ b₆ → kBlock.eqa (kBlock.ConvertToBlockMaxAbsFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆) (kBlock.ConvertToBlockMaxAbsFinite b₀ b₁ b₂ b₃ b₄ b₅ b₆)
    | eqa_computedBlock {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ : kFormat} {a₃ b₃ : kBlockProjSpec} {a₄ b₄ : MRat} {a₅ b₅ : kXSeq} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kBlockProjSpec.eqa a₃ b₃ → a₄ = b₄ → kXSeq.eqa a₅ b₅ → kBlock.eqa (kBlock.computedBlock a₀ a₁ a₂ a₃ a₄ a₅) (kBlock.computedBlock b₀ b₁ b₂ b₃ b₄ b₅)
    | eqa_BlockConvert {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockConvert a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockConvert b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockAbs {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockAbs a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockAbs b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockNegate {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockNegate a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockNegate b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockCopySign {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kBlockProjSpec.eqa a₇ b₇ → a₈ = b₈ → kCodeSeq.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqa (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockCopySign b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqa_BlockAdd {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kBlockProjSpec.eqa a₇ b₇ → a₈ = b₈ → kCodeSeq.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqa (kBlock.BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockAdd b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqa_BlockSubtract {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kBlockProjSpec.eqa a₇ b₇ → a₈ = b₈ → kCodeSeq.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqa (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockSubtract b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqa_BlockMultiply {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kBlockProjSpec.eqa a₇ b₇ → a₈ = b₈ → kCodeSeq.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqa (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMultiply b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqa_BlockDivide {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kBlockProjSpec.eqa a₇ b₇ → a₈ = b₈ → kCodeSeq.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqa (kBlock.BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockDivide b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqa_BlockFMA {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ a₇ b₇ a₈ b₈ : kFormat} {a₉ b₉ : kBlockProjSpec} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} {a₁₃ b₁₃ : kCodeSeq} {a₁₄ b₁₄ : MRat} {a₁₅ b₁₅ : kCodeSeq} {a₁₆ b₁₆ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kFormat.eqa a₇ b₇ → kFormat.eqa a₈ b₈ → kBlockProjSpec.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kCodeSeq.eqa a₁₃ b₁₃ → a₁₄ = b₁₄ → kCodeSeq.eqa a₁₅ b₁₅ → a₁₆ = b₁₆ → kBlock.eqa (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFMA b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃ b₁₄ b₁₅ b₁₆)
    | eqa_BlockFAA {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ a₇ b₇ a₈ b₈ : kFormat} {a₉ b₉ : kBlockProjSpec} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} {a₁₃ b₁₃ : kCodeSeq} {a₁₄ b₁₄ : MRat} {a₁₅ b₁₅ : kCodeSeq} {a₁₆ b₁₆ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kFormat.eqa a₇ b₇ → kFormat.eqa a₈ b₈ → kBlockProjSpec.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kCodeSeq.eqa a₁₃ b₁₃ → a₁₄ = b₁₄ → kCodeSeq.eqa a₁₅ b₁₅ → a₁₆ = b₁₆ → kBlock.eqa (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFAA b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃ b₁₄ b₁₅ b₁₆)
    | eqa_BlockRecip {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockRecip a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockRecip b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockMinimum {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kBlockProjSpec.eqa a₇ b₇ → a₈ = b₈ → kCodeSeq.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqa (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimum b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqa_BlockMaximum {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kBlockProjSpec.eqa a₇ b₇ → a₈ = b₈ → kCodeSeq.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqa (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximum b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqa_BlockMinimumNumber {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kBlockProjSpec.eqa a₇ b₇ → a₈ = b₈ → kCodeSeq.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqa (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumNumber b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqa_BlockMaximumNumber {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kBlockProjSpec.eqa a₇ b₇ → a₈ = b₈ → kCodeSeq.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqa (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumNumber b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqa_BlockMinimumMagnitude {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kBlockProjSpec.eqa a₇ b₇ → a₈ = b₈ → kCodeSeq.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqa (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitude b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqa_BlockMaximumMagnitude {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kBlockProjSpec.eqa a₇ b₇ → a₈ = b₈ → kCodeSeq.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqa (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitude b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqa_BlockMinimumMagnitudeNumber {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kBlockProjSpec.eqa a₇ b₇ → a₈ = b₈ → kCodeSeq.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqa (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitudeNumber b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqa_BlockMaximumMagnitudeNumber {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kBlockProjSpec.eqa a₇ b₇ → a₈ = b₈ → kCodeSeq.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqa (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitudeNumber b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqa_BlockMinimumFinite {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kBlockProjSpec.eqa a₇ b₇ → a₈ = b₈ → kCodeSeq.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqa (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumFinite b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqa_BlockMaximumFinite {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kBlockProjSpec.eqa a₇ b₇ → a₈ = b₈ → kCodeSeq.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqa (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumFinite b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqa_BlockClamp {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ a₇ b₇ a₈ b₈ : kFormat} {a₉ b₉ : kBlockProjSpec} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} {a₁₃ b₁₃ : kCodeSeq} {a₁₄ b₁₄ : MRat} {a₁₅ b₁₅ : kCodeSeq} {a₁₆ b₁₆ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kFormat.eqa a₇ b₇ → kFormat.eqa a₈ b₈ → kBlockProjSpec.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kCodeSeq.eqa a₁₃ b₁₃ → a₁₄ = b₁₄ → kCodeSeq.eqa a₁₅ b₁₅ → a₁₆ = b₁₆ → kBlock.eqa (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockClamp b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃ b₁₄ b₁₅ b₁₆)
    | eqa_BlockSqrt {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSqrt b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockRSqrt {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockRSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockRSqrt b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockExp {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockExp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockExp b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockExp2 {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockExp2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockExp2 b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockLog {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockLog a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockLog b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockLog2 {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockLog2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockLog2 b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockLogOnePlus {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockLogOnePlus a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockLogOnePlus b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockExpMinusOne {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockExpMinusOne a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockExpMinusOne b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockSin {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSin b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockCos {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockCos b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockTan {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockTan b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockArcSin {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockArcSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcSin b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockArcCos {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockArcCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcCos b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockArcTan {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockArcTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcTan b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockSinh {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSinh b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockCosh {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockCosh b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockTanh {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockTanh b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockArcSinh {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockArcSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcSinh b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockArcCosh {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockArcCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcCosh b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockArcTanh {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockArcTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcTanh b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockSinPi {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSinPi b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockCosPi {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockCosPi b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockTanPi {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockTanPi b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockArcSinPi {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockArcSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcSinPi b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockArcCosPi {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockArcCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcCosPi b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockArcTanPi {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockArcTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcTanPi b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockSoftplus {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kBlockProjSpec.eqa a₅ b₅ → a₆ = b₆ → kCodeSeq.eqa a₇ b₇ → a₈ = b₈ → kBlock.eqa (kBlock.BlockSoftplus a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSoftplus b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqa_BlockHypot {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kBlockProjSpec.eqa a₇ b₇ → a₈ = b₈ → kCodeSeq.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqa (kBlock.BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockHypot b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqa_BlockArcTan2 {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kBlockProjSpec.eqa a₇ b₇ → a₈ = b₈ → kCodeSeq.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqa (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2 b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqa_BlockArcTan2Pi {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → kFormat.eqa a₃ b₃ → kFormat.eqa a₄ b₄ → kFormat.eqa a₅ b₅ → kFormat.eqa a₆ b₆ → kBlockProjSpec.eqa a₇ b₇ → a₈ = b₈ → kCodeSeq.eqa a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqa a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqa (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2Pi b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)

  inductive kFormatSeq.eqa: kFormatSeq → kFormatSeq → Prop
    | refl {a} : kFormatSeq.eqa a a
    | symm {a b} : kFormatSeq.eqa a b → kFormatSeq.eqa b a
    | trans {a b c} : kFormatSeq.eqa a b → kFormatSeq.eqa b c → kFormatSeq.eqa a c
    -- Congruence axioms for each operator
    | eqa_fcons {a₀ b₀ : kFormat} {a₁ b₁ : kFormatSeq} : kFormat.eqa a₀ b₀ → kFormatSeq.eqa a₁ b₁ → kFormatSeq.eqa (kFormatSeq.fcons a₀ a₁) (kFormatSeq.fcons b₀ b₁)

  inductive kSpecialization.eqa: kSpecialization → kSpecialization → Prop
    | refl {a} : kSpecialization.eqa a a
    | symm {a b} : kSpecialization.eqa a b → kSpecialization.eqa b a
    | trans {a b c} : kSpecialization.eqa a b → kSpecialization.eqa b c → kSpecialization.eqa a c
    -- Congruence axioms for each operator
    | eqa_numeric {a₀ b₀ : MString} {a₁ b₁ : kFormatSeq} {a₂ b₂ : kProjSpec} : a₀ = b₀ → kFormatSeq.eqa a₁ b₁ → kProjSpec.eqa a₂ b₂ → kSpecialization.eqa (kSpecialization.numeric a₀ a₁ a₂) (kSpecialization.numeric b₀ b₁ b₂)
    | eqa_plain {a₀ b₀ : MString} {a₁ b₁ : kFormatSeq} : a₀ = b₀ → kFormatSeq.eqa a₁ b₁ → kSpecialization.eqa (kSpecialization.plain a₀ a₁) (kSpecialization.plain b₀ b₁)
    | eqa_blockElements {a₀ b₀ : MString} {a₁ b₁ : MRat} {a₂ b₂ : kFormatSeq} {a₃ b₃ : kBlockProjSpec} : a₀ = b₀ → a₁ = b₁ → kFormatSeq.eqa a₂ b₂ → kBlockProjSpec.eqa a₃ b₃ → kSpecialization.eqa (kSpecialization.blockElements a₀ a₁ a₂ a₃) (kSpecialization.blockElements b₀ b₁ b₂ b₃)
    | eqa_blockReduction {a₀ b₀ : MString} {a₁ b₁ : MRat} {a₂ b₂ : kFormatSeq} {a₃ b₃ : kProjSpec} : a₀ = b₀ → a₁ = b₁ → kFormatSeq.eqa a₂ b₂ → kProjSpec.eqa a₃ b₃ → kSpecialization.eqa (kSpecialization.blockReduction a₀ a₁ a₂ a₃) (kSpecialization.blockReduction b₀ b₁ b₂ b₃)
    | eqa_blockScale {a₀ b₀ : MString} {a₁ b₁ : MRat} {a₂ b₂ : kFormatSeq} {a₃ b₃ : kProjSpec} {a₄ b₄ : kBlockProjSpec} : a₀ = b₀ → a₁ = b₁ → kFormatSeq.eqa a₂ b₂ → kProjSpec.eqa a₃ b₃ → kBlockProjSpec.eqa a₄ b₄ → kSpecialization.eqa (kSpecialization.blockScale a₀ a₁ a₂ a₃ a₄) (kSpecialization.blockScale b₀ b₁ b₂ b₃ b₄)
    | eqa_at {a₀ b₀ : kSpecializationSeq} {a₁ b₁ : MRat} : kSpecializationSeq.eqa a₀ b₀ → a₁ = b₁ → kSpecialization.eqa (kSpecialization.«at» a₀ a₁) (kSpecialization.«at» b₀ b₁)
    | eqa_declaredIdentity {a b : kDeclaration} : kDeclaration.eqa a b → kSpecialization.eqa (kSpecialization.declaredIdentity a) (kSpecialization.declaredIdentity b)

  inductive kKappa.eqa: kKappa → kKappa → Prop
    | refl {a} : kKappa.eqa a a
    | symm {a b} : kKappa.eqa a b → kKappa.eqa b a
    | trans {a b c} : kKappa.eqa a b → kKappa.eqa b c → kKappa.eqa a c
    -- Congruence axioms for each operator
    | eqa_steps {a b : MRat} : a = b → kKappa.eqa (kKappa.steps a) (kKappa.steps b)
    | eqa_partBound {a b : kKappaPartSeq} : kKappaPartSeq.eqa a b → kKappa.eqa (kKappa.partBound a) (kKappa.partBound b)
    | eqa_declarationKappa {a b : kDeclaration} : kDeclaration.eqa a b → kKappa.eqa (kKappa.declarationKappa a) (kKappa.declarationKappa b)
    | eqa_observationKappa {a b : kObservation} : kObservation.eqa a b → kKappa.eqa (kKappa.observationKappa a) (kKappa.observationKappa b)
    | eqa_batchKappa {a b : kObservationSeq} : kObservationSeq.eqa a b → kKappa.eqa (kKappa.batchKappa a) (kKappa.batchKappa b)
    | eqa_mergeKappa {a₀ b₀ a₁ b₁ : kKappa} : kKappa.eqa a₀ b₀ → kKappa.eqa a₁ b₁ → kKappa.eqa (kKappa.mergeKappa a₀ a₁) (kKappa.mergeKappa b₀ b₁)

  inductive kObservation.eqa: kObservation → kObservation → Prop
    | refl {a} : kObservation.eqa a a
    | symm {a b} : kObservation.eqa a b → kObservation.eqa b a
    | trans {a b c} : kObservation.eqa a b → kObservation.eqa b c → kObservation.eqa a c
    -- Congruence axioms for each operator
    | eqa_observation {a₀ b₀ : MString} {a₁ b₁ : kCodeSeq} {a₂ b₂ : kFormat} {a₃ b₃ a₄ b₄ : MRat} : a₀ = b₀ → kCodeSeq.eqa a₁ b₁ → kFormat.eqa a₂ b₂ → a₃ = b₃ → a₄ = b₄ → kObservation.eqa (kObservation.observation a₀ a₁ a₂ a₃ a₄) (kObservation.observation b₀ b₁ b₂ b₃ b₄)
    | eqa_at {a₀ b₀ : kObservationSeq} {a₁ b₁ : MRat} : kObservationSeq.eqa a₀ b₀ → a₁ = b₁ → kObservation.eqa (kObservation.«at» a₀ a₁) (kObservation.«at» b₀ b₁)

  inductive kDeclaration.eqa: kDeclaration → kDeclaration → Prop
    | refl {a} : kDeclaration.eqa a a
    | symm {a b} : kDeclaration.eqa a b → kDeclaration.eqa b a
    | trans {a b c} : kDeclaration.eqa a b → kDeclaration.eqa b c → kDeclaration.eqa a c
    -- Congruence axioms for each operator
    | eqa_exact {a₀ b₀ : kSpecialization} {a₁ b₁ : MString} {a₂ b₂ : kEvidence} : kSpecialization.eqa a₀ b₀ → a₁ = b₁ → kEvidence.eqa a₂ b₂ → kDeclaration.eqa (kDeclaration.exact a₀ a₁ a₂) (kDeclaration.exact b₀ b₁ b₂)
    | eqa_approximate {a₀ b₀ : kSpecialization} {a₁ b₁ : MString} {a₂ b₂ : kKappa} {a₃ b₃ : kEvidence} : kSpecialization.eqa a₀ b₀ → a₁ = b₁ → kKappa.eqa a₂ b₂ → kEvidence.eqa a₃ b₃ → kDeclaration.eqa (kDeclaration.approximate a₀ a₁ a₂ a₃) (kDeclaration.approximate b₀ b₁ b₂ b₃)
    | eqa_at {a₀ b₀ : kDeclarationSeq} {a₁ b₁ : MRat} : kDeclarationSeq.eqa a₀ b₀ → a₁ = b₁ → kDeclaration.eqa (kDeclaration.«at» a₀ a₁) (kDeclaration.«at» b₀ b₁)
    | eqa_partitioned {a₀ b₀ : kSpecialization} {a₁ b₁ : MString} {a₂ b₂ : kCodeSeq} {a₃ b₃ : kKappaPartSeq} {a₄ b₄ : kEvidence} : kSpecialization.eqa a₀ b₀ → a₁ = b₁ → kCodeSeq.eqa a₂ b₂ → kKappaPartSeq.eqa a₃ b₃ → kEvidence.eqa a₄ b₄ → kDeclaration.eqa (kDeclaration.partitioned a₀ a₁ a₂ a₃ a₄) (kDeclaration.partitioned b₀ b₁ b₂ b₃ b₄)

  inductive kEvidence.eqa: kEvidence → kEvidence → Prop
    | refl {a} : kEvidence.eqa a a
    | symm {a b} : kEvidence.eqa a b → kEvidence.eqa b a
    | trans {a b c} : kEvidence.eqa a b → kEvidence.eqa b c → kEvidence.eqa a c
    -- Congruence axioms for each operator

  inductive kKappaPart.eqa: kKappaPart → kKappaPart → Prop
    | refl {a} : kKappaPart.eqa a a
    | symm {a b} : kKappaPart.eqa a b → kKappaPart.eqa b a
    | trans {a b c} : kKappaPart.eqa a b → kKappaPart.eqa b c → kKappaPart.eqa a c
    -- Congruence axioms for each operator
    | eqa_kappaPart {a₀ b₀ : kCodeSeq} {a₁ b₁ : kKappa} : kCodeSeq.eqa a₀ b₀ → kKappa.eqa a₁ b₁ → kKappaPart.eqa (kKappaPart.kappaPart a₀ a₁) (kKappaPart.kappaPart b₀ b₁)
    | eqa_at {a₀ b₀ : kKappaPartSeq} {a₁ b₁ : MRat} : kKappaPartSeq.eqa a₀ b₀ → a₁ = b₁ → kKappaPart.eqa (kKappaPart.«at» a₀ a₁) (kKappaPart.«at» b₀ b₁)

  inductive kArityEntry.eqa: kArityEntry → kArityEntry → Prop
    | refl {a} : kArityEntry.eqa a a
    | symm {a b} : kArityEntry.eqa a b → kArityEntry.eqa b a
    | trans {a b c} : kArityEntry.eqa a b → kArityEntry.eqa b c → kArityEntry.eqa a c
    -- Congruence axioms for each operator
    | eqa_entry {a₀ b₀ : MString} {a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kArityEntry.eqa (kArityEntry.entry a₀ a₁) (kArityEntry.entry b₀ b₁)
    | eqa_at {a₀ b₀ : kArityTable} {a₁ b₁ : MRat} : kArityTable.eqa a₀ b₀ → a₁ = b₁ → kArityEntry.eqa (kArityEntry.«at» a₀ a₁) (kArityEntry.«at» b₀ b₁)

  inductive kKappaPartSeq.eqa: kKappaPartSeq → kKappaPartSeq → Prop
    | refl {a} : kKappaPartSeq.eqa a a
    | symm {a b} : kKappaPartSeq.eqa a b → kKappaPartSeq.eqa b a
    | trans {a b c} : kKappaPartSeq.eqa a b → kKappaPartSeq.eqa b c → kKappaPartSeq.eqa a c
    -- Congruence axioms for each operator
    | eqa_kcons {a₀ b₀ : kKappaPart} {a₁ b₁ : kKappaPartSeq} : kKappaPart.eqa a₀ b₀ → kKappaPartSeq.eqa a₁ b₁ → kKappaPartSeq.eqa (kKappaPartSeq.kcons a₀ a₁) (kKappaPartSeq.kcons b₀ b₁)

  inductive kPartitionSeq.eqa: kPartitionSeq → kPartitionSeq → Prop
    | refl {a} : kPartitionSeq.eqa a a
    | symm {a b} : kPartitionSeq.eqa a b → kPartitionSeq.eqa b a
    | trans {a b c} : kPartitionSeq.eqa a b → kPartitionSeq.eqa b c → kPartitionSeq.eqa a c
    -- Congruence axioms for each operator
    | eqa_pcons {a₀ b₀ : kCodeSeq} {a₁ b₁ : kPartitionSeq} : kCodeSeq.eqa a₀ b₀ → kPartitionSeq.eqa a₁ b₁ → kPartitionSeq.eqa (kPartitionSeq.pcons a₀ a₁) (kPartitionSeq.pcons b₀ b₁)
    | eqa_partRegions {a b : kKappaPartSeq} : kKappaPartSeq.eqa a b → kPartitionSeq.eqa (kPartitionSeq.partRegions a) (kPartitionSeq.partRegions b)

  inductive kDeclarationSeq.eqa: kDeclarationSeq → kDeclarationSeq → Prop
    | refl {a} : kDeclarationSeq.eqa a a
    | symm {a b} : kDeclarationSeq.eqa a b → kDeclarationSeq.eqa b a
    | trans {a b c} : kDeclarationSeq.eqa a b → kDeclarationSeq.eqa b c → kDeclarationSeq.eqa a c
    -- Congruence axioms for each operator
    | eqa_dcons {a₀ b₀ : kDeclaration} {a₁ b₁ : kDeclarationSeq} : kDeclaration.eqa a₀ b₀ → kDeclarationSeq.eqa a₁ b₁ → kDeclarationSeq.eqa (kDeclarationSeq.dcons a₀ a₁) (kDeclarationSeq.dcons b₀ b₁)

  inductive kSpecializationSeq.eqa: kSpecializationSeq → kSpecializationSeq → Prop
    | refl {a} : kSpecializationSeq.eqa a a
    | symm {a b} : kSpecializationSeq.eqa a b → kSpecializationSeq.eqa b a
    | trans {a b c} : kSpecializationSeq.eqa a b → kSpecializationSeq.eqa b c → kSpecializationSeq.eqa a c
    -- Congruence axioms for each operator
    | eqa_scons {a₀ b₀ : kSpecialization} {a₁ b₁ : kSpecializationSeq} : kSpecialization.eqa a₀ b₀ → kSpecializationSeq.eqa a₁ b₁ → kSpecializationSeq.eqa (kSpecializationSeq.scons a₀ a₁) (kSpecializationSeq.scons b₀ b₁)

  inductive kClassEnum.eqa: kClassEnum → kClassEnum → Prop
    | refl {a} : kClassEnum.eqa a a
    | symm {a b} : kClassEnum.eqa a b → kClassEnum.eqa b a
    | trans {a b c} : kClassEnum.eqa a b → kClassEnum.eqa b c → kClassEnum.eqa a c
    -- Congruence axioms for each operator
    | eqa_Class {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqa a₀ b₀ → a₁ = b₁ → kClassEnum.eqa (kClassEnum.Class a₀ a₁) (kClassEnum.Class b₀ b₁)
    | eqa_ifthenelsefi {a₀ b₀ : kBool} {a₁ b₁ a₂ b₂ : kClassEnum} : kBool.eqa a₀ b₀ → kClassEnum.eqa a₁ b₁ → kClassEnum.eqa a₂ b₂ → kClassEnum.eqa (kClassEnum.ifthenelsefi a₀ a₁ a₂) (kClassEnum.ifthenelsefi b₀ b₁ b₂)

  inductive kObservationSeq.eqa: kObservationSeq → kObservationSeq → Prop
    | refl {a} : kObservationSeq.eqa a a
    | symm {a b} : kObservationSeq.eqa a b → kObservationSeq.eqa b a
    | trans {a b c} : kObservationSeq.eqa a b → kObservationSeq.eqa b c → kObservationSeq.eqa a c
    -- Congruence axioms for each operator
    | eqa_ocons {a₀ b₀ : kObservation} {a₁ b₁ : kObservationSeq} : kObservation.eqa a₀ b₀ → kObservationSeq.eqa a₁ b₁ → kObservationSeq.eqa (kObservationSeq.ocons a₀ a₁) (kObservationSeq.ocons b₀ b₁)

  inductive kArityTable.eqa: kArityTable → kArityTable → Prop
    | refl {a} : kArityTable.eqa a a
    | symm {a b} : kArityTable.eqa a b → kArityTable.eqa b a
    | trans {a b c} : kArityTable.eqa a b → kArityTable.eqa b c → kArityTable.eqa a c
    -- Congruence axioms for each operator
    | eqa_acons {a₀ b₀ : kArityEntry} {a₁ b₁ : kArityTable} : kArityEntry.eqa a₀ b₀ → kArityTable.eqa a₁ b₁ → kArityTable.eqa (kArityTable.acons a₀ a₁) (kArityTable.acons b₀ b₁)
end

end Maude
