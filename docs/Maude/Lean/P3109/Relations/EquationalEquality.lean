-- Extracted from ../spec2.lean, lines 1505-3334.
-- See PLAN.md and manifest.json for provenance.
import P3109.Relations.AxiomaticEquality

namespace Maude
-- Sort membership and equality modulo equations

mutual
  inductive kBool.has_sort: kBool → MSort → Prop
    | subsort {t a b} : subsort a b → kBool.has_sort t a → kBool.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | true_decl : kBool.has_sort kBool.true MSort.Bool
    | false_decl : kBool.has_sort kBool.false MSort.Bool
    | and_decl {a₀ a₁ : kBool} : kBool.has_sort a₀ MSort.Bool → kBool.has_sort a₁ MSort.Bool → kBool.has_sort (kBool.and a₀ a₁) MSort.Bool
    | or_decl {a₀ a₁ : kBool} : kBool.has_sort a₀ MSort.Bool → kBool.has_sort a₁ MSort.Bool → kBool.has_sort (kBool.or a₀ a₁) MSort.Bool
    | xor_decl {a₀ a₁ : kBool} : kBool.has_sort a₀ MSort.Bool → kBool.has_sort a₁ MSort.Bool → kBool.has_sort (kBool.xor a₀ a₁) MSort.Bool
    | not_decl {a : kBool} : kBool.has_sort a MSort.Bool → kBool.has_sort (kBool.not a) MSort.Bool
    | implies_decl {a₀ a₁ : kBool} : kBool.has_sort a₀ MSort.Bool → kBool.has_sort a₁ MSort.Bool → kBool.has_sort (kBool.implies a₀ a₁) MSort.Bool
    | lt₀_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Nat → kBool.has_sort (if a₀ < a₁ then kBool.true else kBool.false) MSort.Bool
    | lt₀_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → kBool.has_sort (if a₀ < a₁ then kBool.true else kBool.false) MSort.Bool
    | lt₀_decl₂ {a₀ a₁ : MRat} : kBool.has_sort (if a₀ < a₁ then kBool.true else kBool.false) MSort.Bool
    | lteq₀_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Nat → kBool.has_sort (if a₀ ≤ a₁ then kBool.true else kBool.false) MSort.Bool
    | lteq₀_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → kBool.has_sort (if a₀ ≤ a₁ then kBool.true else kBool.false) MSort.Bool
    | lteq₀_decl₂ {a₀ a₁ : MRat} : kBool.has_sort (if a₀ ≤ a₁ then kBool.true else kBool.false) MSort.Bool
    | gt₀_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Nat → kBool.has_sort (if a₁ < a₀ then kBool.true else kBool.false) MSort.Bool
    | gt₀_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → kBool.has_sort (if a₁ < a₀ then kBool.true else kBool.false) MSort.Bool
    | gt₀_decl₂ {a₀ a₁ : MRat} : kBool.has_sort (if a₁ < a₀ then kBool.true else kBool.false) MSort.Bool
    | gteq₀_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Nat → kBool.has_sort (if a₁ ≤ a₀ then kBool.true else kBool.false) MSort.Bool
    | gteq₀_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → kBool.has_sort (if a₁ ≤ a₀ then kBool.true else kBool.false) MSort.Bool
    | gteq₀_decl₂ {a₀ a₁ : MRat} : kBool.has_sort (if a₁ ≤ a₀ then kBool.true else kBool.false) MSort.Bool
    | divides_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzNat → MRat.has_sort a₁ MSort.Nat → kBool.has_sort (if a₁.num % a₀.num = 0 then kBool.true else kBool.false) MSort.Bool
    | divides_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzInt → MRat.has_sort a₁ MSort.Int → kBool.has_sort (if a₁.num % a₀.num = 0 then kBool.true else kBool.false) MSort.Bool
    | divides_decl₂ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzRat → kBool.has_sort (if a₁.num % a₀.num = 0 then kBool.true else kBool.false) MSort.Bool
    | even_decl {a : MRat} : MRat.has_sort a MSort.Int → kBool.has_sort (kBool.even a) MSort.Bool
    | validFormat_decl {a : kFormat} : kFormat.has_sort a MSort.Format → kBool.has_sort (kBool.validFormat a) MSort.Bool
    | internalFormat_decl {a : kFormat} : kFormat.has_sort a MSort.Format → kBool.has_sort (kBool.internalFormat a) MSort.Bool
    | validCode_decl {a₀ : kFormat} {a₁ : MRat} : kFormat.has_sort a₀ MSort.Format → MRat.has_sort a₁ MSort.Int → kBool.has_sort (kBool.validCode a₀ a₁) MSort.Bool
    | candidateDatum_decl {a₀ : kFormat} {a₁ a₂ : MRat} : kFormat.has_sort a₀ MSort.Format → MRat.has_sort a₂ MSort.Int → kBool.has_sort (kBool.candidateDatum a₀ a₁ a₂) MSort.Bool
    | randomInRange_decl {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → kBool.has_sort (kBool.randomInRange a₀ a₁) MSort.Bool
    | validRound_decl {a : kBlockRoundMode} : kBlockRoundMode.has_sort a MSort.RoundMode → kBool.has_sort (kBool.validRound a) MSort.Bool
    | validProjection_decl {a : kProjSpec} : kProjSpec.has_sort a MSort.ProjSpec → kBool.has_sort (kBool.validProjection a) MSort.Bool
    | validBlockProjection_decl {a₀ : kBlockProjSpec} {a₁ : MRat} : kBlockProjSpec.has_sort a₀ MSort.BlockProjSpec → MRat.has_sort a₁ MSort.Nat → kBool.has_sort (kBool.validBlockProjection a₀ a₁) MSort.Bool
    | validRandoms_decl {a₀ : MRat} {a₁ : kRandomSeq} : MRat.has_sort a₀ MSort.Int → kRandomSeq.has_sort a₁ MSort.RandomSeq → kBool.has_sort (kBool.validRandoms a₀ a₁) MSort.Bool
    | deterministic_decl {a : kBlockRoundMode} : kBlockRoundMode.has_sort a MSort.RoundMode → kBool.has_sort (kBool.deterministic a) MSort.Bool
    | roundAway_decl {a₀ : kBlockRoundMode} {a₁ a₂ : MRat} {a₃ : kBool} : kBlockRoundMode.has_sort a₀ MSort.RoundMode → kBool.has_sort a₃ MSort.Bool → kBool.has_sort (kBool.roundAway a₀ a₁ a₂ a₃) MSort.Bool
    | clipsHigh_decl {a : kBlockRoundMode} : kBlockRoundMode.has_sort a MSort.RoundMode → kBool.has_sort (kBool.clipsHigh a) MSort.Bool
    | clipsLow_decl {a : kBlockRoundMode} : kBlockRoundMode.has_sort a MSort.RoundMode → kBool.has_sort (kBool.clipsLow a) MSort.Bool
    | validCodes_decl {a₀ : kFormat} {a₁ : kCodeSeq} : kFormat.has_sort a₀ MSort.Format → kCodeSeq.has_sort a₁ MSort.CodeSeq → kBool.has_sort (kBool.validCodes a₀ a₁) MSort.Bool
    | validBlock_decl {a₀ : MRat} {a₁ a₂ : kFormat} {a₃ : MRat} {a₄ : kCodeSeq} : MRat.has_sort a₀ MSort.Nat → kFormat.has_sort a₁ MSort.Format → kFormat.has_sort a₂ MSort.Format → MRat.has_sort a₃ MSort.Int → kCodeSeq.has_sort a₄ MSort.CodeSeq → kBool.has_sort (kBool.validBlock a₀ a₁ a₂ a₃ a₄) MSort.Bool
    | lt₁_decl {a₀ a₁ : MString} : kBool.has_sort (if a₀ < a₁ then kBool.true else kBool.false) MSort.Bool
    | lteq₁_decl {a₀ a₁ : MString} : kBool.has_sort (if a₀ ≤ a₁ then kBool.true else kBool.false) MSort.Bool
    | gt₁_decl {a₀ a₁ : MString} : kBool.has_sort (if a₁ < a₀ then kBool.true else kBool.false) MSort.Bool
    | gteq₁_decl {a₀ a₁ : MString} : kBool.has_sort (if a₁ ≤ a₀ then kBool.true else kBool.false) MSort.Bool
    | inF4_decl {a : kFormat} : kFormat.has_sort a MSort.Format → kBool.has_sort (kBool.inF4 a) MSort.Bool
    | inF8_decl {a : kFormat} : kFormat.has_sort a MSort.Format → kBool.has_sort (kBool.inF8 a) MSort.Bool
    | inFs_decl {a : kFormat} : kFormat.has_sort a MSort.Format → kBool.has_sort (kBool.inFs a) MSort.Bool
    | allowedExternal_decl {a : kFormat} : kFormat.has_sort a MSort.Format → kBool.has_sort (kBool.allowedExternal a) MSort.Bool
    | containsFormat_decl {a₀ : kFormat} {a₁ : kFormatSeq} : kFormat.has_sort a₀ MSort.Format → kFormatSeq.has_sort a₁ MSort.FormatSeq → kBool.has_sort (kBool.containsFormat a₀ a₁) MSort.Bool
    | validFX_decl {a : kFormatSeq} : kFormatSeq.has_sort a MSort.FormatSeq → kBool.has_sort (kBool.validFX a) MSort.Bool
    | validFXTail_decl {a : kFormatSeq} : kFormatSeq.has_sort a MSort.FormatSeq → kBool.has_sort (kBool.validFXTail a) MSort.Bool
    | allFormats_decl {a : kFormatSeq} : kFormatSeq.has_sort a MSort.FormatSeq → kBool.has_sort (kBool.allFormats a) MSort.Bool
    | required_decl {a₀ : kSpecialization} {a₁ : kFormatSeq} : kSpecialization.has_sort a₀ MSort.Specialization → kFormatSeq.has_sort a₁ MSort.FormatSeq → kBool.has_sort (kBool.required a₀ a₁) MSort.Bool
    | requiredNumeric_decl {a₀ : MString} {a₁ a₂ : kFormatSeq} : kFormatSeq.has_sort a₁ MSort.FormatSeq → kFormatSeq.has_sort a₂ MSort.FormatSeq → kBool.has_sort (kBool.requiredNumeric a₀ a₁ a₂) MSort.Bool
    | requiredPlain_decl {a₀ : MString} {a₁ a₂ : kFormatSeq} : kFormatSeq.has_sort a₁ MSort.FormatSeq → kFormatSeq.has_sort a₂ MSort.FormatSeq → kBool.has_sort (kBool.requiredPlain a₀ a₁ a₂) MSort.Bool
    | minmaxName_decl {a : MString} : kBool.has_sort (kBool.minmaxName a) MSort.Bool
    | compareName_decl {a : MString} : kBool.has_sort (kBool.compareName a) MSort.Bool
    | predicateName_decl {a : MString} : kBool.has_sort (kBool.predicateName a) MSort.Bool
    | formatNameOp_decl {a : MString} : kBool.has_sort (kBool.formatNameOp a) MSort.Bool
    | numericPlainName_decl {a : MString} : kBool.has_sort (kBool.numericPlainName a) MSort.Bool
    | blockElementArity_decl {a₀ : MString} {a₁ : MRat} : MRat.has_sort a₁ MSort.Nat → kBool.has_sort (kBool.blockElementArity a₀ a₁) MSort.Bool
    | numericResult_decl {a : kSpecialization} : kSpecialization.has_sort a MSort.Specialization → kBool.has_sort (kBool.numericResult a) MSort.Bool
    | hasDeclaration_decl {a₀ : kSpecialization} {a₁ : kDeclarationSeq} : kSpecialization.has_sort a₀ MSort.Specialization → kDeclarationSeq.has_sort a₁ MSort.DeclarationSeq → kBool.has_sort (kBool.hasDeclaration a₀ a₁) MSort.Bool
    | declarationsCover_decl {a₀ : kSpecializationSeq} {a₁ : kDeclarationSeq} : kSpecializationSeq.has_sort a₀ MSort.SpecializationSeq → kDeclarationSeq.has_sort a₁ MSort.DeclarationSeq → kBool.has_sort (kBool.declarationsCover a₀ a₁) MSort.Bool
    | partition_decl {a₀ : kCodeSeq} {a₁ : kPartitionSeq} : kCodeSeq.has_sort a₀ MSort.CodeSeq → kPartitionSeq.has_sort a₁ MSort.PartitionSeq → kBool.has_sort (kBool.partition a₀ a₁) MSort.Bool
    | partitionDisjoint_decl {a : kPartitionSeq} : kPartitionSeq.has_sort a MSort.PartitionSeq → kBool.has_sort (kBool.partitionDisjoint a) MSort.Bool
    | validSpecialization_decl {a : kSpecialization} : kSpecialization.has_sort a MSort.Specialization → kBool.has_sort (kBool.validSpecialization a) MSort.Bool
    | numericArity_decl {a₀ : MString} {a₁ : MRat} : MRat.has_sort a₁ MSort.Nat → kBool.has_sort (kBool.numericArity a₀ a₁) MSort.Bool
    | plainArity_decl {a₀ : MString} {a₁ : MRat} : MRat.has_sort a₁ MSort.Nat → kBool.has_sort (kBool.plainArity a₀ a₁) MSort.Bool
    | wellFormedDeclaration_decl {a : kDeclaration} : kDeclaration.has_sort a MSort.Declaration → kBool.has_sort (kBool.wellFormedDeclaration a) MSort.Bool
    | evidenceComplete_decl {a : kEvidence} : kEvidence.has_sort a MSort.Evidence → kBool.has_sort (kBool.evidenceComplete a) MSort.Bool
    | memberCode_decl {a₀ : MRat} {a₁ : kCodeSeq} : MRat.has_sort a₀ MSort.Int → kCodeSeq.has_sort a₁ MSort.CodeSeq → kBool.has_sort (kBool.memberCode a₀ a₁) MSort.Bool
    | disjointCodes_decl {a₀ a₁ : kCodeSeq} : kCodeSeq.has_sort a₀ MSort.CodeSeq → kCodeSeq.has_sort a₁ MSort.CodeSeq → kBool.has_sort (kBool.disjointCodes a₀ a₁) MSort.Bool
    | uniqueCodes_decl {a : kCodeSeq} : kCodeSeq.has_sort a MSort.CodeSeq → kBool.has_sort (kBool.uniqueCodes a) MSort.Bool
    | subsetCodes_decl {a₀ a₁ : kCodeSeq} : kCodeSeq.has_sort a₀ MSort.CodeSeq → kCodeSeq.has_sort a₁ MSort.CodeSeq → kBool.has_sort (kBool.subsetCodes a₀ a₁) MSort.Bool
    | partition2_decl {a₀ a₁ a₂ : kCodeSeq} : kCodeSeq.has_sort a₀ MSort.CodeSeq → kCodeSeq.has_sort a₁ MSort.CodeSeq → kCodeSeq.has_sort a₂ MSort.CodeSeq → kBool.has_sort (kBool.partition2 a₀ a₁ a₂) MSort.Bool
    | inArityTable_decl {a₀ : MString} {a₁ : MRat} {a₂ : kArityTable} : MRat.has_sort a₁ MSort.Nat → kArityTable.has_sort a₂ MSort.ArityTable → kBool.has_sort (kBool.inArityTable a₀ a₁ a₂) MSort.Bool
    | eqeq₀_decl {a₀ a₁ : MRat} : kBool.has_sort (kBool.eqeq₀ a₀ a₁) MSort.Bool
    | ifthenelsefi_decl₁ {a₀ a₁ a₂ : kBool} : kBool.has_sort a₀ MSort.Bool → kBool.has_sort a₁ MSort.Bool → kBool.has_sort a₂ MSort.Bool → kBool.has_sort (kBool.ifthenelsefi a₀ a₁ a₂) MSort.Bool
    | eqeq₁_decl {a₀ a₁ : kSignedness} : kBool.has_sort (kBool.eqeq₁ a₀ a₁) MSort.Bool
    | eqeq₂_decl {a₀ a₁ : kDomain} : kBool.has_sort (kBool.eqeq₂ a₀ a₁) MSort.Bool
    | eqslasheq₀_decl {a₀ a₁ : MRat} : kBool.has_sort (kBool.eqslasheq₀ a₀ a₁) MSort.Bool
    | eqeq₃_decl {a₀ a₁ : kBlockRoundMode} : kBool.has_sort (kBool.eqeq₃ a₀ a₁) MSort.Bool
    | eqeq₄_decl {a₀ a₁ : kBool} : kBool.has_sort (kBool.eqeq₄ a₀ a₁) MSort.Bool
    | eqeq₅_decl {a₀ a₁ : MString} : kBool.has_sort (kBool.eqeq₅ a₀ a₁) MSort.Bool
    | eqeq₆_decl {a₀ a₁ : kFormat} : kBool.has_sort (kBool.eqeq₆ a₀ a₁) MSort.Bool
    | eqeq₇_decl {a₀ a₁ : kProjSpec} : kBool.has_sort (kBool.eqeq₇ a₀ a₁) MSort.Bool
    | eqslasheq₁_decl {a₀ a₁ : kBool} : kBool.has_sort (kBool.eqslasheq₁ a₀ a₁) MSort.Bool
    | eqslasheq₂_decl {a₀ a₁ : MString} : kBool.has_sort (kBool.eqslasheq₂ a₀ a₁) MSort.Bool
    | eqeq₈_decl {a₀ a₁ : kSpecialization} : kBool.has_sort (kBool.eqeq₈ a₀ a₁) MSort.Bool

  inductive kXReal.has_sort: kXReal → MSort → Prop
    | subsort {t a b} : subsort a b → kXReal.has_sort t a → kXReal.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | fin_decl {a : MRat} : kXReal.has_sort (kXReal.fin a) MSort.Real
    | posInf_decl : kXReal.has_sort kXReal.posInf MSort.Infinity
    | negInf_decl : kXReal.has_sort kXReal.negInf MSort.Infinity
    | nan_decl : kXReal.has_sort kXReal.nan MSort.XReal
    | overflow_decl {a₀ : kSignedness} {a₁ : kDomain} {a₂ : kBool} : kSignedness.has_sort a₀ MSort.Signedness → kDomain.has_sort a₁ MSort.Domain → kBool.has_sort a₂ MSort.Bool → kXReal.has_sort (kXReal.overflow a₀ a₁ a₂) MSort.XReal
    | realAdd_decl {a₀ a₁ : kXReal} : kXReal.has_sort a₀ MSort.Real → kXReal.has_sort a₁ MSort.Real → kXReal.has_sort (kXReal.realAdd a₀ a₁) MSort.Real
    | realMultiply_decl {a₀ a₁ : kXReal} : kXReal.has_sort a₀ MSort.Real → kXReal.has_sort a₁ MSort.Real → kXReal.has_sort (kXReal.realMultiply a₀ a₁) MSort.Real
    | realNegate_decl {a : kXReal} : kXReal.has_sort a MSort.Real → kXReal.has_sort (kXReal.realNegate a) MSort.Real
    | realAbs_decl {a : kXReal} : kXReal.has_sort a MSort.Real → kXReal.has_sort (kXReal.realAbs a) MSort.Real
    | piMultiple_decl {a : MRat} : kXReal.has_sort (kXReal.piMultiple a) MSort.Real
    | pi_decl : kXReal.has_sort kXReal.pi MSort.Real
    | exprExp_decl {a : kXReal} : kXReal.has_sort a MSort.Real → kXReal.has_sort (kXReal.exprExp a) MSort.Real
    | exprExp2_decl {a : kXReal} : kXReal.has_sort a MSort.Real → kXReal.has_sort (kXReal.exprExp2 a) MSort.Real
    | exprSin_decl {a : kXReal} : kXReal.has_sort a MSort.Real → kXReal.has_sort (kXReal.exprSin a) MSort.Real
    | exprCos_decl {a : kXReal} : kXReal.has_sort a MSort.Real → kXReal.has_sort (kXReal.exprCos a) MSort.Real
    | exprArcTan_decl {a : kXReal} : kXReal.has_sort a MSort.Real → kXReal.has_sort (kXReal.exprArcTan a) MSort.Real
    | exprSinh_decl {a : kXReal} : kXReal.has_sort a MSort.Real → kXReal.has_sort (kXReal.exprSinh a) MSort.Real
    | exprCosh_decl {a : kXReal} : kXReal.has_sort a MSort.Real → kXReal.has_sort (kXReal.exprCosh a) MSort.Real
    | exprTanh_decl {a : kXReal} : kXReal.has_sort a MSort.Real → kXReal.has_sort (kXReal.exprTanh a) MSort.Real
    | exprArcSinh_decl {a : kXReal} : kXReal.has_sort a MSort.Real → kXReal.has_sort (kXReal.exprArcSinh a) MSort.Real
    | ifthenelsefi_decl₁ {a₀ : kBool} {a₁ a₂ : kXReal} : kBool.has_sort a₀ MSort.Bool → kXReal.has_sort a₁ MSort.XReal → kXReal.has_sort a₂ MSort.XReal → kXReal.has_sort (kXReal.ifthenelsefi a₀ a₁ a₂) MSort.XReal
    | ifthenelsefi_decl₂ {a₀ : kBool} {a₁ a₂ : kXReal} : kBool.has_sort a₀ MSort.Bool → kXReal.has_sort a₁ MSort.Number → kXReal.has_sort a₂ MSort.Number → kXReal.has_sort (kXReal.ifthenelsefi a₀ a₁ a₂) MSort.Number
    | ifthenelsefi_decl₃ {a₀ : kBool} {a₁ a₂ : kXReal} : kBool.has_sort a₀ MSort.Bool → kXReal.has_sort a₁ MSort.Real → kXReal.has_sort a₂ MSort.Real → kXReal.has_sort (kXReal.ifthenelsefi a₀ a₁ a₂) MSort.Real
    | ifthenelsefi_decl₄ {a₀ : kBool} {a₁ a₂ : kXReal} : kBool.has_sort a₀ MSort.Bool → kXReal.has_sort a₁ MSort.Infinity → kXReal.has_sort a₂ MSort.Infinity → kXReal.has_sort (kXReal.ifthenelsefi a₀ a₁ a₂) MSort.Infinity
    -- Explicit membership axioms
    | mb_p31zero9_real_divide_domain {u v} : kXReal.has_sort u MSort.Real → kXReal.has_sort v MSort.Real → kBool.eqe (kBool.eqeq₄ (kBool.xEq v (kXReal.fin (0 : MRat))) kBool.false) kBool.true → kXReal.has_sort (kXReal.realDivide u v) MSort.Real
    | mb_p31zero9_expr_Sqrt_domain {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLe (kXReal.fin (0 : MRat)) u) kBool.true → kXReal.has_sort (kXReal.exprSqrt u) MSort.Real
    | mb_p31zero9_expr_Log_domain {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt (kXReal.fin (0 : MRat)) u) kBool.true → kXReal.has_sort (kXReal.exprLog u) MSort.Real
    | mb_p31zero9_expr_Log2_domain {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt (kXReal.fin (0 : MRat)) u) kBool.true → kXReal.has_sort (kXReal.exprLog2 u) MSort.Real
    | mb_p31zero9_expr_Tan_domain {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.eqeq₄ (kBool.xEq (kXReal.omegaCos u) (kXReal.fin (0 : MRat))) kBool.false) kBool.true → kXReal.has_sort (kXReal.exprTan u) MSort.Real
    | mb_p31zero9_expr_ArcSin_domain {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLe (kXReal.fin ((- 1) : MRat)) u) kBool.true → kBool.eqe (kBool.xLe u (kXReal.fin (1 : MRat))) kBool.true → kXReal.has_sort (kXReal.exprArcSin u) MSort.Real
    | mb_p31zero9_expr_ArcCos_domain {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLe (kXReal.fin ((- 1) : MRat)) u) kBool.true → kBool.eqe (kBool.xLe u (kXReal.fin (1 : MRat))) kBool.true → kXReal.has_sort (kXReal.exprArcCos u) MSort.Real
    | mb_p31zero9_expr_ArcCosh_domain {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLe (kXReal.fin (1 : MRat)) u) kBool.true → kXReal.has_sort (kXReal.exprArcCosh u) MSort.Real
    | mb_p31zero9_expr_ArcTanh_domain {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt (kXReal.fin ((- 1) : MRat)) u) kBool.true → kBool.eqe (kBool.xLt u (kXReal.fin (1 : MRat))) kBool.true → kXReal.has_sort (kXReal.exprArcTanh u) MSort.Real

  inductive kFormat.has_sort: kFormat → MSort → Prop
    | subsort {t a b} : subsort a b → kFormat.has_sort t a → kFormat.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | Binary_decl {a₀ a₁ : MRat} {a₂ : kSignedness} {a₃ : kDomain} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → kSignedness.has_sort a₂ MSort.Signedness → kDomain.has_sort a₃ MSort.Domain → kFormat.has_sort (kFormat.Binary a₀ a₁ a₂ a₃) MSort.Format
    | binary64_decl : kFormat.has_sort kFormat.binary64 MSort.Format
    | binary32_decl : kFormat.has_sort kFormat.binary32 MSort.Format
    | binary16_decl : kFormat.has_sort kFormat.binary16 MSort.Format
    | BFloat16_decl : kFormat.has_sort kFormat.BFloat16 MSort.Format

  inductive kSignedness.has_sort: kSignedness → MSort → Prop
    | subsort {t a b} : subsort a b → kSignedness.has_sort t a → kSignedness.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | Signed_decl : kSignedness.has_sort kSignedness.Signed MSort.Signedness
    | Unsigned_decl : kSignedness.has_sort kSignedness.Unsigned MSort.Signedness

  inductive kDomain.has_sort: kDomain → MSort → Prop
    | subsort {t a b} : subsort a b → kDomain.has_sort t a → kDomain.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | Finite_decl : kDomain.has_sort kDomain.Finite MSort.Domain
    | Extended_decl : kDomain.has_sort kDomain.Extended MSort.Domain

  inductive kBoundQuery.has_sort: kBoundQuery → MSort → Prop
    | subsort {t a b} : subsort a b → kBoundQuery.has_sort t a → kBoundQuery.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | maxFiniteQuery_decl : kBoundQuery.has_sort kBoundQuery.maxFiniteQuery MSort.BoundQuery
    | minFiniteQuery_decl : kBoundQuery.has_sort kBoundQuery.minFiniteQuery MSort.BoundQuery
    | minPositiveQuery_decl : kBoundQuery.has_sort kBoundQuery.minPositiveQuery MSort.BoundQuery
    | maxSubnormalQuery_decl : kBoundQuery.has_sort kBoundQuery.maxSubnormalQuery MSort.BoundQuery
    | minNormalQuery_decl : kBoundQuery.has_sort kBoundQuery.minNormalQuery MSort.BoundQuery

  inductive kRandomSeq.has_sort: kRandomSeq → MSort → Prop
    | subsort {t a b} : subsort a b → kRandomSeq.has_sort t a → kRandomSeq.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | rnil_decl : kRandomSeq.has_sort kRandomSeq.rnil MSort.RandomSeq
    | rcons_decl {a₀ : MRat} {a₁ : kRandomSeq} : MRat.has_sort a₀ MSort.Int → kRandomSeq.has_sort a₁ MSort.RandomSeq → kRandomSeq.has_sort (kRandomSeq.rcons a₀ a₁) MSort.RandomSeq

  inductive kBlockRoundMode.has_sort: kBlockRoundMode → MSort → Prop
    | subsort {t a b} : subsort a b → kBlockRoundMode.has_sort t a → kBlockRoundMode.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | NearestTiesToEven_decl : kBlockRoundMode.has_sort kBlockRoundMode.NearestTiesToEven MSort.RoundMode
    | NearestTiesToAway_decl : kBlockRoundMode.has_sort kBlockRoundMode.NearestTiesToAway MSort.RoundMode
    | TowardPositive_decl : kBlockRoundMode.has_sort kBlockRoundMode.TowardPositive MSort.RoundMode
    | TowardNegative_decl : kBlockRoundMode.has_sort kBlockRoundMode.TowardNegative MSort.RoundMode
    | TowardZero_decl : kBlockRoundMode.has_sort kBlockRoundMode.TowardZero MSort.RoundMode
    | ToOdd_decl : kBlockRoundMode.has_sort kBlockRoundMode.ToOdd MSort.RoundMode
    | StochasticA_decl {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → kBlockRoundMode.has_sort (kBlockRoundMode.StochasticA a₀ a₁) MSort.RoundMode
    | StochasticB_decl {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → kBlockRoundMode.has_sort (kBlockRoundMode.StochasticB a₀ a₁) MSort.RoundMode
    | StochasticC_decl {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → kBlockRoundMode.has_sort (kBlockRoundMode.StochasticC a₀ a₁) MSort.RoundMode
    | BlockStochasticA_decl {a₀ : MRat} {a₁ : kRandomSeq} : MRat.has_sort a₀ MSort.Int → kRandomSeq.has_sort a₁ MSort.RandomSeq → kBlockRoundMode.has_sort (kBlockRoundMode.BlockStochasticA a₀ a₁) MSort.BlockRoundMode
    | BlockStochasticB_decl {a₀ : MRat} {a₁ : kRandomSeq} : MRat.has_sort a₀ MSort.Int → kRandomSeq.has_sort a₁ MSort.RandomSeq → kBlockRoundMode.has_sort (kBlockRoundMode.BlockStochasticB a₀ a₁) MSort.BlockRoundMode
    | BlockStochasticC_decl {a₀ : MRat} {a₁ : kRandomSeq} : MRat.has_sort a₀ MSort.Int → kRandomSeq.has_sort a₁ MSort.RandomSeq → kBlockRoundMode.has_sort (kBlockRoundMode.BlockStochasticC a₀ a₁) MSort.BlockRoundMode

  inductive kSatMode.has_sort: kSatMode → MSort → Prop
    | subsort {t a b} : subsort a b → kSatMode.has_sort t a → kSatMode.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | SatNone_decl : kSatMode.has_sort kSatMode.SatNone MSort.SatMode
    | SatFinite_decl : kSatMode.has_sort kSatMode.SatFinite MSort.SatMode
    | SatPropagate_decl : kSatMode.has_sort kSatMode.SatPropagate MSort.SatMode

  inductive kProjSpec.has_sort: kProjSpec → MSort → Prop
    | subsort {t a b} : subsort a b → kProjSpec.has_sort t a → kProjSpec.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | proj_decl {a₀ : kBlockRoundMode} {a₁ : kSatMode} : kBlockRoundMode.has_sort a₀ MSort.RoundMode → kSatMode.has_sort a₁ MSort.SatMode → kProjSpec.has_sort (kProjSpec.proj a₀ a₁) MSort.ProjSpec

  inductive kBlockProjSpec.has_sort: kBlockProjSpec → MSort → Prop
    | subsort {t a b} : subsort a b → kBlockProjSpec.has_sort t a → kBlockProjSpec.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | bproj_decl {a₀ : kBlockRoundMode} {a₁ : kSatMode} : kBlockRoundMode.has_sort a₀ MSort.BlockRoundMode → kSatMode.has_sort a₁ MSort.SatMode → kBlockProjSpec.has_sort (kBlockProjSpec.bproj a₀ a₁) MSort.BlockProjSpec

  inductive kXSeq.has_sort: kXSeq → MSort → Prop
    | subsort {t a b} : subsort a b → kXSeq.has_sort t a → kXSeq.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | xnil_decl : kXSeq.has_sort kXSeq.xnil MSort.XSeq
    | xcons_decl {a₀ : kXReal} {a₁ : kXSeq} : kXReal.has_sort a₀ MSort.XReal → kXSeq.has_sort a₁ MSort.XSeq → kXSeq.has_sort (kXSeq.xcons a₀ a₁) MSort.XSeq

  inductive kCodeSeq.has_sort: kCodeSeq → MSort → Prop
    | subsort {t a b} : subsort a b → kCodeSeq.has_sort t a → kCodeSeq.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | cnil_decl : kCodeSeq.has_sort kCodeSeq.cnil MSort.CodeSeq
    | ccons_decl {a₀ : MRat} {a₁ : kCodeSeq} : MRat.has_sort a₀ MSort.Int → kCodeSeq.has_sort a₁ MSort.CodeSeq → kCodeSeq.has_sort (kCodeSeq.ccons a₀ a₁) MSort.CodeSeq
    | partitionUnion_decl {a : kPartitionSeq} : kPartitionSeq.has_sort a MSort.PartitionSeq → kCodeSeq.has_sort (kCodeSeq.partitionUnion a) MSort.CodeSeq
    | appendCodes_decl {a₀ a₁ : kCodeSeq} : kCodeSeq.has_sort a₀ MSort.CodeSeq → kCodeSeq.has_sort a₁ MSort.CodeSeq → kCodeSeq.has_sort (kCodeSeq.appendCodes a₀ a₁) MSort.CodeSeq

  inductive kBlock.has_sort: kBlock → MSort → Prop
    | subsort {t a b} : subsort a b → kBlock.has_sort t a → kBlock.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | block_decl {a₀ : MRat} {a₁ : kCodeSeq} : MRat.has_sort a₀ MSort.Int → kCodeSeq.has_sort a₁ MSort.CodeSeq → kBlock.has_sort (kBlock.block a₀ a₁) MSort.Block

  inductive kFormatSeq.has_sort: kFormatSeq → MSort → Prop
    | subsort {t a b} : subsort a b → kFormatSeq.has_sort t a → kFormatSeq.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | fnil_decl : kFormatSeq.has_sort kFormatSeq.fnil MSort.FormatSeq
    | fcons_decl {a₀ : kFormat} {a₁ : kFormatSeq} : kFormat.has_sort a₀ MSort.Format → kFormatSeq.has_sort a₁ MSort.FormatSeq → kFormatSeq.has_sort (kFormatSeq.fcons a₀ a₁) MSort.FormatSeq

  inductive kSpecialization.has_sort: kSpecialization → MSort → Prop
    | subsort {t a b} : subsort a b → kSpecialization.has_sort t a → kSpecialization.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | numeric_decl {a₀ : MString} {a₁ : kFormatSeq} {a₂ : kProjSpec} : kFormatSeq.has_sort a₁ MSort.FormatSeq → kProjSpec.has_sort a₂ MSort.ProjSpec → kSpecialization.has_sort (kSpecialization.numeric a₀ a₁ a₂) MSort.Specialization
    | plain_decl {a₀ : MString} {a₁ : kFormatSeq} : kFormatSeq.has_sort a₁ MSort.FormatSeq → kSpecialization.has_sort (kSpecialization.plain a₀ a₁) MSort.Specialization
    | blockElements_decl {a₀ : MString} {a₁ : MRat} {a₂ : kFormatSeq} {a₃ : kBlockProjSpec} : MRat.has_sort a₁ MSort.Nat → kFormatSeq.has_sort a₂ MSort.FormatSeq → kBlockProjSpec.has_sort a₃ MSort.BlockProjSpec → kSpecialization.has_sort (kSpecialization.blockElements a₀ a₁ a₂ a₃) MSort.Specialization
    | blockReduction_decl {a₀ : MString} {a₁ : MRat} {a₂ : kFormatSeq} {a₃ : kProjSpec} : MRat.has_sort a₁ MSort.Nat → kFormatSeq.has_sort a₂ MSort.FormatSeq → kProjSpec.has_sort a₃ MSort.ProjSpec → kSpecialization.has_sort (kSpecialization.blockReduction a₀ a₁ a₂ a₃) MSort.Specialization
    | blockScale_decl {a₀ : MString} {a₁ : MRat} {a₂ : kFormatSeq} {a₃ : kProjSpec} {a₄ : kBlockProjSpec} : MRat.has_sort a₁ MSort.Nat → kFormatSeq.has_sort a₂ MSort.FormatSeq → kProjSpec.has_sort a₃ MSort.ProjSpec → kBlockProjSpec.has_sort a₄ MSort.BlockProjSpec → kSpecialization.has_sort (kSpecialization.blockScale a₀ a₁ a₂ a₃ a₄) MSort.Specialization
    | declaredIdentity_decl {a : kDeclaration} : kDeclaration.has_sort a MSort.Declaration → kSpecialization.has_sort (kSpecialization.declaredIdentity a) MSort.Specialization

  inductive kKappa.has_sort: kKappa → MSort → Prop
    | subsort {t a b} : subsort a b → kKappa.has_sort t a → kKappa.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | steps_decl {a : MRat} : MRat.has_sort a MSort.Nat → kKappa.has_sort (kKappa.steps a) MSort.Kappa
    | kNaN_decl : kKappa.has_sort kKappa.kNaN MSort.Kappa
    | kInfinity_decl : kKappa.has_sort kKappa.kInfinity MSort.Kappa
    | partBound_decl {a : kKappaPartSeq} : kKappaPartSeq.has_sort a MSort.KappaPartSeq → kKappa.has_sort (kKappa.partBound a) MSort.Kappa
    | mergeKappa_decl {a₀ a₁ : kKappa} : kKappa.has_sort a₀ MSort.Kappa → kKappa.has_sort a₁ MSort.Kappa → kKappa.has_sort (kKappa.mergeKappa a₀ a₁) MSort.Kappa

  inductive kObservation.has_sort: kObservation → MSort → Prop
    | subsort {t a b} : subsort a b → kObservation.has_sort t a → kObservation.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | observation_decl {a₀ : MString} {a₁ : kCodeSeq} {a₂ : kFormat} {a₃ a₄ : MRat} : kCodeSeq.has_sort a₁ MSort.CodeSeq → kFormat.has_sort a₂ MSort.Format → MRat.has_sort a₃ MSort.Int → MRat.has_sort a₄ MSort.Int → kObservation.has_sort (kObservation.observation a₀ a₁ a₂ a₃ a₄) MSort.Observation

  inductive kDeclaration.has_sort: kDeclaration → MSort → Prop
    | subsort {t a b} : subsort a b → kDeclaration.has_sort t a → kDeclaration.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | exact_decl {a₀ : kSpecialization} {a₁ : MString} {a₂ : kEvidence} : kSpecialization.has_sort a₀ MSort.Specialization → kEvidence.has_sort a₂ MSort.Evidence → kDeclaration.has_sort (kDeclaration.exact a₀ a₁ a₂) MSort.Declaration
    | approximate_decl {a₀ : kSpecialization} {a₁ : MString} {a₂ : kKappa} {a₃ : kEvidence} : kSpecialization.has_sort a₀ MSort.Specialization → kKappa.has_sort a₂ MSort.Kappa → kEvidence.has_sort a₃ MSort.Evidence → kDeclaration.has_sort (kDeclaration.approximate a₀ a₁ a₂ a₃) MSort.Declaration
    | partitioned_decl {a₀ : kSpecialization} {a₁ : MString} {a₂ : kCodeSeq} {a₃ : kKappaPartSeq} {a₄ : kEvidence} : kSpecialization.has_sort a₀ MSort.Specialization → kCodeSeq.has_sort a₂ MSort.CodeSeq → kKappaPartSeq.has_sort a₃ MSort.KappaPartSeq → kEvidence.has_sort a₄ MSort.Evidence → kDeclaration.has_sort (kDeclaration.partitioned a₀ a₁ a₂ a₃ a₄) MSort.Declaration

  inductive kEvidence.has_sort: kEvidence → MSort → Prop
    | subsort {t a b} : subsort a b → kEvidence.has_sort t a → kEvidence.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | pendingEvidence_decl : kEvidence.has_sort kEvidence.pendingEvidence MSort.Evidence
    | sampleEvidence_decl : kEvidence.has_sort kEvidence.sampleEvidence MSort.Evidence
    | exhaustiveEvidence_decl : kEvidence.has_sort kEvidence.exhaustiveEvidence MSort.Evidence
    | proofEvidence_decl : kEvidence.has_sort kEvidence.proofEvidence MSort.Evidence

  inductive kKappaPart.has_sort: kKappaPart → MSort → Prop
    | subsort {t a b} : subsort a b → kKappaPart.has_sort t a → kKappaPart.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | kappaPart_decl {a₀ : kCodeSeq} {a₁ : kKappa} : kCodeSeq.has_sort a₀ MSort.CodeSeq → kKappa.has_sort a₁ MSort.Kappa → kKappaPart.has_sort (kKappaPart.kappaPart a₀ a₁) MSort.KappaPart

  inductive kArityEntry.has_sort: kArityEntry → MSort → Prop
    | subsort {t a b} : subsort a b → kArityEntry.has_sort t a → kArityEntry.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | entry_decl {a₀ : MString} {a₁ : MRat} : MRat.has_sort a₁ MSort.Nat → kArityEntry.has_sort (kArityEntry.entry a₀ a₁) MSort.ArityEntry

  inductive kKappaPartSeq.has_sort: kKappaPartSeq → MSort → Prop
    | subsort {t a b} : subsort a b → kKappaPartSeq.has_sort t a → kKappaPartSeq.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | knil_decl : kKappaPartSeq.has_sort kKappaPartSeq.knil MSort.KappaPartSeq
    | kcons_decl {a₀ : kKappaPart} {a₁ : kKappaPartSeq} : kKappaPart.has_sort a₀ MSort.KappaPart → kKappaPartSeq.has_sort a₁ MSort.KappaPartSeq → kKappaPartSeq.has_sort (kKappaPartSeq.kcons a₀ a₁) MSort.KappaPartSeq

  inductive kPartitionSeq.has_sort: kPartitionSeq → MSort → Prop
    | subsort {t a b} : subsort a b → kPartitionSeq.has_sort t a → kPartitionSeq.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | pnil_decl : kPartitionSeq.has_sort kPartitionSeq.pnil MSort.PartitionSeq
    | pcons_decl {a₀ : kCodeSeq} {a₁ : kPartitionSeq} : kCodeSeq.has_sort a₀ MSort.CodeSeq → kPartitionSeq.has_sort a₁ MSort.PartitionSeq → kPartitionSeq.has_sort (kPartitionSeq.pcons a₀ a₁) MSort.PartitionSeq
    | partRegions_decl {a : kKappaPartSeq} : kKappaPartSeq.has_sort a MSort.KappaPartSeq → kPartitionSeq.has_sort (kPartitionSeq.partRegions a) MSort.PartitionSeq

  inductive kDeclarationSeq.has_sort: kDeclarationSeq → MSort → Prop
    | subsort {t a b} : subsort a b → kDeclarationSeq.has_sort t a → kDeclarationSeq.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | dnil_decl : kDeclarationSeq.has_sort kDeclarationSeq.dnil MSort.DeclarationSeq
    | dcons_decl {a₀ : kDeclaration} {a₁ : kDeclarationSeq} : kDeclaration.has_sort a₀ MSort.Declaration → kDeclarationSeq.has_sort a₁ MSort.DeclarationSeq → kDeclarationSeq.has_sort (kDeclarationSeq.dcons a₀ a₁) MSort.DeclarationSeq

  inductive kSpecializationSeq.has_sort: kSpecializationSeq → MSort → Prop
    | subsort {t a b} : subsort a b → kSpecializationSeq.has_sort t a → kSpecializationSeq.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | snil_decl : kSpecializationSeq.has_sort kSpecializationSeq.snil MSort.SpecializationSeq
    | scons_decl {a₀ : kSpecialization} {a₁ : kSpecializationSeq} : kSpecialization.has_sort a₀ MSort.Specialization → kSpecializationSeq.has_sort a₁ MSort.SpecializationSeq → kSpecializationSeq.has_sort (kSpecializationSeq.scons a₀ a₁) MSort.SpecializationSeq

  inductive kClassEnum.has_sort: kClassEnum → MSort → Prop
    | subsort {t a b} : subsort a b → kClassEnum.has_sort t a → kClassEnum.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | ClsNaN_decl : kClassEnum.has_sort kClassEnum.ClsNaN MSort.ClassEnum
    | ClsNegativeInfinity_decl : kClassEnum.has_sort kClassEnum.ClsNegativeInfinity MSort.ClassEnum
    | ClsNegativeNormal_decl : kClassEnum.has_sort kClassEnum.ClsNegativeNormal MSort.ClassEnum
    | ClsNegativeSubnormal_decl : kClassEnum.has_sort kClassEnum.ClsNegativeSubnormal MSort.ClassEnum
    | ClsZero_decl : kClassEnum.has_sort kClassEnum.ClsZero MSort.ClassEnum
    | ClsPositiveSubnormal_decl : kClassEnum.has_sort kClassEnum.ClsPositiveSubnormal MSort.ClassEnum
    | ClsPositiveNormal_decl : kClassEnum.has_sort kClassEnum.ClsPositiveNormal MSort.ClassEnum
    | ClsPositiveInfinity_decl : kClassEnum.has_sort kClassEnum.ClsPositiveInfinity MSort.ClassEnum
    | ifthenelsefi_decl₁ {a₀ : kBool} {a₁ a₂ : kClassEnum} : kBool.has_sort a₀ MSort.Bool → kClassEnum.has_sort a₁ MSort.ClassEnum → kClassEnum.has_sort a₂ MSort.ClassEnum → kClassEnum.has_sort (kClassEnum.ifthenelsefi a₀ a₁ a₂) MSort.ClassEnum

  inductive kObservationSeq.has_sort: kObservationSeq → MSort → Prop
    | subsort {t a b} : subsort a b → kObservationSeq.has_sort t a → kObservationSeq.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | onil_decl : kObservationSeq.has_sort kObservationSeq.onil MSort.ObservationSeq
    | ocons_decl {a₀ : kObservation} {a₁ : kObservationSeq} : kObservation.has_sort a₀ MSort.Observation → kObservationSeq.has_sort a₁ MSort.ObservationSeq → kObservationSeq.has_sort (kObservationSeq.ocons a₀ a₁) MSort.ObservationSeq

  inductive kArityTable.has_sort: kArityTable → MSort → Prop
    | subsort {t a b} : subsort a b → kArityTable.has_sort t a → kArityTable.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | anil_decl : kArityTable.has_sort kArityTable.anil MSort.ArityTable
    | acons_decl {a₀ : kArityEntry} {a₁ : kArityTable} : kArityEntry.has_sort a₀ MSort.ArityEntry → kArityTable.has_sort a₁ MSort.ArityTable → kArityTable.has_sort (kArityTable.acons a₀ a₁) MSort.ArityTable
    | numericArityTable_decl : kArityTable.has_sort kArityTable.numericArityTable MSort.ArityTable
    | plainArityTable_decl : kArityTable.has_sort kArityTable.plainArityTable MSort.ArityTable
    | blockElementArityTable_decl : kArityTable.has_sort kArityTable.blockElementArityTable MSort.ArityTable

  inductive MRat.has_sort: MRat → MSort → Prop
    | subsort {t a b} : subsort a b → MRat.has_sort t a → MRat.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | trunc_decl₀ {a : MRat} : MRat.has_sort a MSort.PosRat → MRat.has_sort (MRat.trunc a) MSort.Nat
    | trunc_decl₁ {a : MRat} : MRat.has_sort (MRat.trunc a) MSort.Int
    | frac_decl {a : MRat} : MRat.has_sort (MRat.frac a) MSort.Rat
    | floor_decl₀ {a : MRat} : MRat.has_sort a MSort.PosRat → MRat.has_sort (MRat.floor a) MSort.Nat
    | floor_decl₁ {a : MRat} : MRat.has_sort (MRat.floor a) MSort.Int
    | ceiling_decl₀ {a : MRat} : MRat.has_sort a MSort.PosRat → MRat.has_sort (MRat.ceiling a) MSort.NzNat
    | ceiling_decl₁ {a : MRat} : MRat.has_sort (MRat.ceiling a) MSort.Int
    | pow2_decl {a : MRat} : MRat.has_sort a MSort.Int → MRat.has_sort (MRat.pow2 a) MSort.Rat
    | nearestEvenInteger_decl {a : MRat} : MRat.has_sort (MRat.nearestEvenInteger a) MSort.Int
    | integerSqrt_decl {a : MRat} : MRat.has_sort a MSort.Nat → MRat.has_sort (MRat.integerSqrt a) MSort.Nat
    | sqrtSearch_decl {a₀ a₁ a₂ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort a₂ MSort.Nat → MRat.has_sort (MRat.sqrtSearch a₀ a₁ a₂) MSort.Nat
    | length₀_decl {a : kRandomSeq} : kRandomSeq.has_sort a MSort.RandomSeq → MRat.has_sort (MRat.length₀ a) MSort.Nat
    | roundScaled_decl {a₀ a₁ : MRat} {a₂ : kBlockRoundMode} {a₃ a₄ a₅ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → kBlockRoundMode.has_sort a₂ MSort.RoundMode → MRat.has_sort a₄ MSort.Int → MRat.has_sort (MRat.roundScaled a₀ a₁ a₂ a₃ a₄ a₅) MSort.Rat
    | length₁_decl {a : kXSeq} : kXSeq.has_sort a MSort.XSeq → MRat.has_sort (MRat.length₁ a) MSort.Nat
    | length₂_decl {a : kCodeSeq} : kCodeSeq.has_sort a MSort.CodeSeq → MRat.has_sort (MRat.length₂ a) MSort.Nat
    | notFound_decl : MRat.has_sort MRat.notFound MSort.FindResult
    | ascii_decl {a : MString} : MString.has_sort a MSort.Char → MRat.has_sort (MRat.ascii a) MSort.Nat
    | find_decl {a₀ a₁ : MString} {a₂ : MRat} : MRat.has_sort a₂ MSort.Nat → MRat.has_sort (MRat.find a₀ a₁ a₂) MSort.FindResult
    | rfind_decl {a₀ a₁ : MString} {a₂ : MRat} : MRat.has_sort a₂ MSort.Nat → MRat.has_sort (MRat.rfind a₀ a₁ a₂) MSort.FindResult
    | length₄_decl {a : kFormatSeq} : kFormatSeq.has_sort a MSort.FormatSeq → MRat.has_sort (MRat.length₄ a) MSort.Nat
    | length₅_decl {a : kKappaPartSeq} : kKappaPartSeq.has_sort a MSort.KappaPartSeq → MRat.has_sort (MRat.length₅ a) MSort.Nat
    | length₆_decl {a : kPartitionSeq} : kPartitionSeq.has_sort a MSort.PartitionSeq → MRat.has_sort (MRat.length₆ a) MSort.Nat
    | length₇_decl {a : kDeclarationSeq} : kDeclarationSeq.has_sort a MSort.DeclarationSeq → MRat.has_sort (MRat.length₇ a) MSort.Nat
    | length₈_decl {a : kSpecializationSeq} : kSpecializationSeq.has_sort a MSort.SpecializationSeq → MRat.has_sort (MRat.length₈ a) MSort.Nat
    | length₉_decl {a : kObservationSeq} : kObservationSeq.has_sort a MSort.ObservationSeq → MRat.has_sort (MRat.length₉ a) MSort.Nat
    | length₁₀_decl {a : kArityTable} : kArityTable.has_sort a MSort.ArityTable → MRat.has_sort (MRat.length₁₀ a) MSort.Nat
    | numeratorOf_decl {a : MRat} : MRat.has_sort (MRat.numeratorOf a) MSort.Int
    | denominatorOf_decl {a : MRat} : MRat.has_sort (MRat.denominatorOf a) MSort.Nat
    | ifthenelsefi_decl₁ {a₀ : kBool} {a₁ a₂ : MRat} : kBool.has_sort a₀ MSort.Bool → MRat.has_sort (MRat.ifthenelsefi a₀ a₁ a₂) MSort.Rat
    | ifthenelsefi_decl₂ {a₀ : kBool} {a₁ a₂ : MRat} : kBool.has_sort a₀ MSort.Bool → MRat.has_sort a₁ MSort.FindResult → MRat.has_sort a₂ MSort.FindResult → MRat.has_sort (MRat.ifthenelsefi a₀ a₁ a₂) MSort.FindResult
    | ifthenelsefi_decl₃ {a₀ : kBool} {a₁ a₂ : MRat} : kBool.has_sort a₀ MSort.Bool → MRat.has_sort a₁ MSort.NzRat → MRat.has_sort a₂ MSort.NzRat → MRat.has_sort (MRat.ifthenelsefi a₀ a₁ a₂) MSort.NzRat
    | ifthenelsefi_decl₄ {a₀ : kBool} {a₁ a₂ : MRat} : kBool.has_sort a₀ MSort.Bool → MRat.has_sort a₁ MSort.Int → MRat.has_sort a₂ MSort.Int → MRat.has_sort (MRat.ifthenelsefi a₀ a₁ a₂) MSort.Int
    | ifthenelsefi_decl₅ {a₀ : kBool} {a₁ a₂ : MRat} : kBool.has_sort a₀ MSort.Bool → MRat.has_sort a₁ MSort.PosRat → MRat.has_sort a₂ MSort.PosRat → MRat.has_sort (MRat.ifthenelsefi a₀ a₁ a₂) MSort.PosRat
    | ifthenelsefi_decl₆ {a₀ : kBool} {a₁ a₂ : MRat} : kBool.has_sort a₀ MSort.Bool → MRat.has_sort a₁ MSort.Nat → MRat.has_sort a₂ MSort.Nat → MRat.has_sort (MRat.ifthenelsefi a₀ a₁ a₂) MSort.Nat
    | ifthenelsefi_decl₇ {a₀ : kBool} {a₁ a₂ : MRat} : kBool.has_sort a₀ MSort.Bool → MRat.has_sort a₁ MSort.NzInt → MRat.has_sort a₂ MSort.NzInt → MRat.has_sort (MRat.ifthenelsefi a₀ a₁ a₂) MSort.NzInt
    | ifthenelsefi_decl₈ {a₀ : kBool} {a₁ a₂ : MRat} : kBool.has_sort a₀ MSort.Bool → MRat.has_sort a₁ MSort.Zero → MRat.has_sort a₂ MSort.Zero → MRat.has_sort (MRat.ifthenelsefi a₀ a₁ a₂) MSort.Zero
    | ifthenelsefi_decl₉ {a₀ : kBool} {a₁ a₂ : MRat} : kBool.has_sort a₀ MSort.Bool → MRat.has_sort a₁ MSort.NzNat → MRat.has_sort a₂ MSort.NzNat → MRat.has_sort (MRat.ifthenelsefi a₀ a₁ a₂) MSort.NzNat
    | s_decl {a : MRat} : MRat.has_sort a MSort.Nat → MRat.has_sort (a + 1) MSort.NzNat
    | sum_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzNat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (a₀ + a₁) MSort.NzNat
    | sum_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (a₀ + a₁) MSort.Nat
    | sum_decl₂ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → MRat.has_sort (a₀ + a₁) MSort.Int
    | sum_decl₃ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.PosRat → MRat.has_sort a₁ MSort.PosRat → MRat.has_sort (a₀ + a₁) MSort.PosRat
    | sum_decl₄ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.PosRat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (a₀ + a₁) MSort.PosRat
    | sum_decl₅ {a₀ a₁ : MRat} : MRat.has_sort (a₀ + a₁) MSort.Rat
    | sum_decl₆ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.NzNat → MRat.has_sort (a₀ + a₁) MSort.NzNat
    | sum_decl₇ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.PosRat → MRat.has_sort (a₀ + a₁) MSort.PosRat
    | sd_decl {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (if a₀ ≤ a₁ then a₁ - a₀ else a₀ - a₁) MSort.Nat
    | mul_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzNat → MRat.has_sort a₁ MSort.NzNat → MRat.has_sort (a₀ * a₁) MSort.NzNat
    | mul_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (a₀ * a₁) MSort.Nat
    | mul_decl₂ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzInt → MRat.has_sort a₁ MSort.NzInt → MRat.has_sort (a₀ * a₁) MSort.NzInt
    | mul_decl₃ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → MRat.has_sort (a₀ * a₁) MSort.Int
    | mul_decl₄ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.PosRat → MRat.has_sort a₁ MSort.PosRat → MRat.has_sort (a₀ * a₁) MSort.PosRat
    | mul_decl₅ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzRat → MRat.has_sort a₁ MSort.NzRat → MRat.has_sort (a₀ * a₁) MSort.NzRat
    | mul_decl₆ {a₀ a₁ : MRat} : MRat.has_sort (a₀ * a₁) MSort.Rat
    | quo_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.NzNat → MRat.has_sort (((Int.tdiv a₀.num a₁.num : Int) : Rat)) MSort.Nat
    | quo_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.NzInt → MRat.has_sort (((Int.tdiv a₀.num a₁.num : Int) : Rat)) MSort.Int
    | quo_decl₂ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.PosRat → MRat.has_sort a₁ MSort.PosRat → MRat.has_sort (((Int.tdiv a₀.num a₁.num : Int) : Rat)) MSort.Nat
    | quo_decl₃ {a₀ a₁ : MRat} : MRat.has_sort a₁ MSort.NzRat → MRat.has_sort (((Int.tdiv a₀.num a₁.num : Int) : Rat)) MSort.Int
    | rem_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.NzNat → MRat.has_sort (((Int.tmod a₀.num a₁.num : Int) : Rat)) MSort.Nat
    | rem_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.NzInt → MRat.has_sort (((Int.tmod a₀.num a₁.num : Int) : Rat)) MSort.Int
    | rem_decl₂ {a₀ a₁ : MRat} : MRat.has_sort a₁ MSort.NzRat → MRat.has_sort (((Int.tmod a₀.num a₁.num : Int) : Rat)) MSort.Rat
    | pow_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (a₀ ^ a₁.num.toNat) MSort.Nat
    | pow_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzNat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (a₀ ^ a₁.num.toNat) MSort.NzNat
    | pow_decl₂ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (a₀ ^ a₁.num.toNat) MSort.Int
    | pow_decl₃ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzInt → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (a₀ ^ a₁.num.toNat) MSort.NzInt
    | pow_decl₄ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.PosRat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (a₀ ^ a₁.num.toNat) MSort.PosRat
    | pow_decl₅ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzRat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (a₀ ^ a₁.num.toNat) MSort.NzRat
    | pow_decl₆ {a₀ a₁ : MRat} : MRat.has_sort a₁ MSort.Nat → MRat.has_sort (a₀ ^ a₁.num.toNat) MSort.Rat
    | gcd_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzNat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (((Int.gcd a₀.num a₁.num : Nat) : Rat)) MSort.NzNat
    | gcd_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (((Int.gcd a₀.num a₁.num : Nat) : Rat)) MSort.Nat
    | gcd_decl₂ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzInt → MRat.has_sort a₁ MSort.Int → MRat.has_sort (((Int.gcd a₀.num a₁.num : Nat) : Rat)) MSort.NzNat
    | gcd_decl₃ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → MRat.has_sort (((Int.gcd a₀.num a₁.num : Nat) : Rat)) MSort.Nat
    | gcd_decl₄ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzRat → MRat.has_sort (((Int.gcd a₀.num a₁.num : Nat) : Rat)) MSort.PosRat
    | gcd_decl₅ {a₀ a₁ : MRat} : MRat.has_sort (((Int.gcd a₀.num a₁.num : Nat) : Rat)) MSort.Rat
    | gcd_decl₆ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.NzNat → MRat.has_sort (((Int.gcd a₀.num a₁.num : Nat) : Rat)) MSort.NzNat
    | gcd_decl₇ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.NzInt → MRat.has_sort (((Int.gcd a₀.num a₁.num : Nat) : Rat)) MSort.NzNat
    | gcd_decl₈ {a₀ a₁ : MRat} : MRat.has_sort a₁ MSort.NzRat → MRat.has_sort (((Int.gcd a₀.num a₁.num : Nat) : Rat)) MSort.PosRat
    | lcm_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzNat → MRat.has_sort a₁ MSort.NzNat → MRat.has_sort (((Int.lcm a₀.num a₁.num : Nat) : Rat)) MSort.NzNat
    | lcm_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (((Int.lcm a₀.num a₁.num : Nat) : Rat)) MSort.Nat
    | lcm_decl₂ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzInt → MRat.has_sort a₁ MSort.NzInt → MRat.has_sort (((Int.lcm a₀.num a₁.num : Nat) : Rat)) MSort.NzNat
    | lcm_decl₃ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → MRat.has_sort (((Int.lcm a₀.num a₁.num : Nat) : Rat)) MSort.Nat
    | lcm_decl₄ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzRat → MRat.has_sort a₁ MSort.NzRat → MRat.has_sort (((Int.lcm a₀.num a₁.num : Nat) : Rat)) MSort.PosRat
    | lcm_decl₅ {a₀ a₁ : MRat} : MRat.has_sort (((Int.lcm a₀.num a₁.num : Nat) : Rat)) MSort.Rat
    | min_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzNat → MRat.has_sort a₁ MSort.NzNat → MRat.has_sort (min a₀ a₁) MSort.NzNat
    | min_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (min a₀ a₁) MSort.Nat
    | min_decl₂ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzInt → MRat.has_sort a₁ MSort.NzInt → MRat.has_sort (min a₀ a₁) MSort.NzInt
    | min_decl₃ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → MRat.has_sort (min a₀ a₁) MSort.Int
    | min_decl₄ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.PosRat → MRat.has_sort a₁ MSort.PosRat → MRat.has_sort (min a₀ a₁) MSort.PosRat
    | min_decl₅ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzRat → MRat.has_sort a₁ MSort.NzRat → MRat.has_sort (min a₀ a₁) MSort.NzRat
    | min_decl₆ {a₀ a₁ : MRat} : MRat.has_sort (min a₀ a₁) MSort.Rat
    | max_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzNat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (max a₀ a₁) MSort.NzNat
    | max_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (max a₀ a₁) MSort.Nat
    | max_decl₂ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzInt → MRat.has_sort a₁ MSort.NzInt → MRat.has_sort (max a₀ a₁) MSort.NzInt
    | max_decl₃ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → MRat.has_sort (max a₀ a₁) MSort.Int
    | max_decl₄ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzNat → MRat.has_sort a₁ MSort.Int → MRat.has_sort (max a₀ a₁) MSort.NzNat
    | max_decl₅ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Int → MRat.has_sort (max a₀ a₁) MSort.Nat
    | max_decl₆ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.PosRat → MRat.has_sort (max a₀ a₁) MSort.PosRat
    | max_decl₇ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzRat → MRat.has_sort a₁ MSort.NzRat → MRat.has_sort (max a₀ a₁) MSort.NzRat
    | max_decl₈ {a₀ a₁ : MRat} : MRat.has_sort (max a₀ a₁) MSort.Rat
    | max_decl₉ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.NzNat → MRat.has_sort (max a₀ a₁) MSort.NzNat
    | max_decl₁₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.NzNat → MRat.has_sort (max a₀ a₁) MSort.NzNat
    | max_decl₁₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (max a₀ a₁) MSort.Nat
    | max_decl₁₂ {a₀ a₁ : MRat} : MRat.has_sort a₁ MSort.PosRat → MRat.has_sort (max a₀ a₁) MSort.PosRat
    | xor_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (((a₀.num.toNat ^^^ a₁.num.toNat : Nat) : Rat)) MSort.Nat
    | xor_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → MRat.has_sort (((a₀.num.toNat ^^^ a₁.num.toNat : Nat) : Rat)) MSort.Int
    | amp_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (((a₀.num.toNat &&& a₁.num.toNat : Nat) : Rat)) MSort.Nat
    | amp_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Int → MRat.has_sort (((a₀.num.toNat &&& a₁.num.toNat : Nat) : Rat)) MSort.Nat
    | amp_decl₂ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → MRat.has_sort (((a₀.num.toNat &&& a₁.num.toNat : Nat) : Rat)) MSort.Int
    | amp_decl₃ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (((a₀.num.toNat &&& a₁.num.toNat : Nat) : Rat)) MSort.Nat
    | bar_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzNat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (((a₀.num.toNat ||| a₁.num.toNat : Nat) : Rat)) MSort.NzNat
    | bar_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (((a₀.num.toNat ||| a₁.num.toNat : Nat) : Rat)) MSort.Nat
    | bar_decl₂ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzInt → MRat.has_sort a₁ MSort.Int → MRat.has_sort (((a₀.num.toNat ||| a₁.num.toNat : Nat) : Rat)) MSort.NzInt
    | bar_decl₃ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → MRat.has_sort (((a₀.num.toNat ||| a₁.num.toNat : Nat) : Rat)) MSort.Int
    | bar_decl₄ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.NzNat → MRat.has_sort (((a₀.num.toNat ||| a₁.num.toNat : Nat) : Rat)) MSort.NzNat
    | bar_decl₅ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.NzInt → MRat.has_sort (((a₀.num.toNat ||| a₁.num.toNat : Nat) : Rat)) MSort.NzInt
    | gtgt_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (((a₀.num.toNat >>> a₁.num.toNat : Nat) : Rat)) MSort.Nat
    | gtgt_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (((a₀.num.toNat >>> a₁.num.toNat : Nat) : Rat)) MSort.Int
    | ltlt_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Nat → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (((a₀.num.toNat <<< a₁.num.toNat : Nat) : Rat)) MSort.Nat
    | ltlt_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Nat → MRat.has_sort (((a₀.num.toNat <<< a₁.num.toNat : Nat) : Rat)) MSort.Int
    | sub₀_decl₀ {a : MRat} : MRat.has_sort a MSort.NzNat → MRat.has_sort (- a) MSort.NzInt
    | sub₀_decl₁ {a : MRat} : MRat.has_sort a MSort.NzInt → MRat.has_sort (- a) MSort.NzInt
    | sub₀_decl₂ {a : MRat} : MRat.has_sort a MSort.Int → MRat.has_sort (- a) MSort.Int
    | sub₀_decl₃ {a : MRat} : MRat.has_sort a MSort.NzRat → MRat.has_sort (- a) MSort.NzRat
    | sub₀_decl₄ {a : MRat} : MRat.has_sort (- a) MSort.Rat
    | sub₁_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.Int → MRat.has_sort a₁ MSort.Int → MRat.has_sort (a₀ - a₁) MSort.Int
    | sub₁_decl₁ {a₀ a₁ : MRat} : MRat.has_sort (a₀ - a₁) MSort.Rat
    | abs_decl₀ {a : MRat} : MRat.has_sort a MSort.NzInt → MRat.has_sort (if a < 0 then - a else a) MSort.NzNat
    | abs_decl₁ {a : MRat} : MRat.has_sort a MSort.Int → MRat.has_sort (if a < 0 then - a else a) MSort.Nat
    | abs_decl₂ {a : MRat} : MRat.has_sort a MSort.NzRat → MRat.has_sort (if a < 0 then - a else a) MSort.PosRat
    | abs_decl₃ {a : MRat} : MRat.has_sort (if a < 0 then - a else a) MSort.Rat
    | «~_decl» {a : MRat} : MRat.has_sort a MSort.Int → MRat.has_sort (- a - 1) MSort.Int
    | slash_decl₀ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzInt → MRat.has_sort a₁ MSort.NzNat → MRat.has_sort (a₀ / a₁) MSort.NzRat
    | slash_decl₁ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzNat → MRat.has_sort a₁ MSort.NzNat → MRat.has_sort (a₀ / a₁) MSort.PosRat
    | slash_decl₂ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.PosRat → MRat.has_sort a₁ MSort.PosRat → MRat.has_sort (a₀ / a₁) MSort.PosRat
    | slash_decl₃ {a₀ a₁ : MRat} : MRat.has_sort a₀ MSort.NzRat → MRat.has_sort a₁ MSort.NzRat → MRat.has_sort (a₀ / a₁) MSort.NzRat
    | slash_decl₄ {a₀ a₁ : MRat} : MRat.has_sort a₁ MSort.NzRat → MRat.has_sort (a₀ / a₁) MSort.Rat
    | length₃_decl {a : MString} : MRat.has_sort (((a.length : Nat) : Rat)) MSort.Nat
    -- Membership of the values of the builtin type in its sorts
    | builtin_nzrat {v : MRat} : v.num ≠ 0 → MRat.has_sort v MSort.NzRat
    | builtin_int {v : MRat} : v.den = 1 → MRat.has_sort v MSort.Int
    | builtin_posrat {v : MRat} : 0 < v.num → MRat.has_sort v MSort.PosRat
    | builtin_nat {v : MRat} : v.den = 1 → 0 ≤ v.num → MRat.has_sort v MSort.Nat
    | builtin_nzint {v : MRat} : v.den = 1 → v.num ≠ 0 → MRat.has_sort v MSort.NzInt
    | builtin_zero {v : MRat} : v = 0 → MRat.has_sort v MSort.Zero
    | builtin_nznat {v : MRat} : v.den = 1 → 0 < v.num → MRat.has_sort v MSort.NzNat

  inductive MString.has_sort: MString → MSort → Prop
    | subsort {t a b} : subsort a b → MString.has_sort t a → MString.has_sort t b
    -- Implicit membership axioms (operator declarations)
    | specializationName_decl {a : kSpecialization} : kSpecialization.has_sort a MSort.Specialization → MString.has_sort (MString.specializationName a) MSort.String
    | sum_decl {a₀ a₁ : MString} : MString.has_sort (a₀ ++ a₁) MSort.String
    | substr_decl {a₀ : MString} {a₁ a₂ : MRat} : MRat.has_sort a₁ MSort.Nat → MRat.has_sort a₂ MSort.Nat → MString.has_sort (((a₀.drop a₁.num.toNat).take a₂.num.toNat).toString) MSort.String
    | upperCase_decl {a : MString} : MString.has_sort (a.toUpper) MSort.String
    | lowerCase_decl {a : MString} : MString.has_sort (a.toLower) MSort.String
    -- Membership of the values of the builtin type in its sorts
    | builtin_char {v : MString} : v.length = 1 → MString.has_sort v MSort.Char

  inductive kBool.eqe: kBool → kBool → Prop
    | from_eqa {a b} : kBool.eqa a b → kBool.eqe a b
    | symm {a b} : kBool.eqe a b → kBool.eqe b a
    | trans {a b c} : kBool.eqe a b → kBool.eqe b c → kBool.eqe a c
    -- Congruence axioms for each operator
    | eqe_and {a₀ b₀ a₁ b₁ : kBool} : kBool.eqe a₀ b₀ → kBool.eqe a₁ b₁ → kBool.eqe (kBool.and a₀ a₁) (kBool.and b₀ b₁)
    | eqe_or {a₀ b₀ a₁ b₁ : kBool} : kBool.eqe a₀ b₀ → kBool.eqe a₁ b₁ → kBool.eqe (kBool.or a₀ a₁) (kBool.or b₀ b₁)
    | eqe_xor {a₀ b₀ a₁ b₁ : kBool} : kBool.eqe a₀ b₀ → kBool.eqe a₁ b₁ → kBool.eqe (kBool.xor a₀ a₁) (kBool.xor b₀ b₁)
    | eqe_not {a b : kBool} : kBool.eqe a b → kBool.eqe (kBool.not a) (kBool.not b)
    | eqe_implies {a₀ b₀ a₁ b₁ : kBool} : kBool.eqe a₀ b₀ → kBool.eqe a₁ b₁ → kBool.eqe (kBool.implies a₀ a₁) (kBool.implies b₀ b₁)
    | eqe_lt₀ {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqe (kBool.lt₀ a₀ a₁) (kBool.lt₀ b₀ b₁)
    | eqe_lteq₀ {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqe (kBool.lteq₀ a₀ a₁) (kBool.lteq₀ b₀ b₁)
    | eqe_gt₀ {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqe (kBool.gt₀ a₀ a₁) (kBool.gt₀ b₀ b₁)
    | eqe_gteq₀ {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqe (kBool.gteq₀ a₀ a₁) (kBool.gteq₀ b₀ b₁)
    | eqe_divides {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqe (kBool.divides a₀ a₁) (kBool.divides b₀ b₁)
    | eqe_xNaN {a b : kXReal} : kXReal.eqe a b → kBool.eqe (kBool.xNaN a) (kBool.xNaN b)
    | eqe_xInfinite {a b : kXReal} : kXReal.eqe a b → kBool.eqe (kBool.xInfinite a) (kBool.xInfinite b)
    | eqe_xFinite {a b : kXReal} : kXReal.eqe a b → kBool.eqe (kBool.xFinite a) (kBool.xFinite b)
    | eqe_xMinus {a b : kXReal} : kXReal.eqe a b → kBool.eqe (kBool.xMinus a) (kBool.xMinus b)
    | eqe_xLt {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kBool.eqe (kBool.xLt a₀ a₁) (kBool.xLt b₀ b₁)
    | eqe_xLe {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kBool.eqe (kBool.xLe a₀ a₁) (kBool.xLe b₀ b₁)
    | eqe_xEq {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kBool.eqe (kBool.xEq a₀ a₁) (kBool.xEq b₀ b₁)
    | eqe_even {a b : MRat} : a = b → kBool.eqe (kBool.even a) (kBool.even b)
    | eqe_validFormat {a b : kFormat} : kFormat.eqe a b → kBool.eqe (kBool.validFormat a) (kBool.validFormat b)
    | eqe_internalFormat {a b : kFormat} : kFormat.eqe a b → kBool.eqe (kBool.internalFormat a) (kBool.internalFormat b)
    | eqe_externalDatum {a₀ b₀ : kFormat} {a₁ b₁ : kXReal} : kFormat.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kBool.eqe (kBool.externalDatum a₀ a₁) (kBool.externalDatum b₀ b₁)
    | eqe_validCode {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqe a₀ b₀ → a₁ = b₁ → kBool.eqe (kBool.validCode a₀ a₁) (kBool.validCode b₀ b₁)
    | eqe_datum {a₀ b₀ : kFormat} {a₁ b₁ : kXReal} : kFormat.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kBool.eqe (kBool.datum a₀ a₁) (kBool.datum b₀ b₁)
    | eqe_candidateDatum {a₀ b₀ : kFormat} {a₁ b₁ a₂ b₂ : MRat} : kFormat.eqe a₀ b₀ → a₁ = b₁ → a₂ = b₂ → kBool.eqe (kBool.candidateDatum a₀ a₁ a₂) (kBool.candidateDatum b₀ b₁ b₂)
    | eqe_randomInRange {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqe (kBool.randomInRange a₀ a₁) (kBool.randomInRange b₀ b₁)
    | eqe_validRound {a b : kBlockRoundMode} : kBlockRoundMode.eqe a b → kBool.eqe (kBool.validRound a) (kBool.validRound b)
    | eqe_validProjection {a b : kProjSpec} : kProjSpec.eqe a b → kBool.eqe (kBool.validProjection a) (kBool.validProjection b)
    | eqe_validBlockProjection {a₀ b₀ : kBlockProjSpec} {a₁ b₁ : MRat} : kBlockProjSpec.eqe a₀ b₀ → a₁ = b₁ → kBool.eqe (kBool.validBlockProjection a₀ a₁) (kBool.validBlockProjection b₀ b₁)
    | eqe_validRandoms {a₀ b₀ : MRat} {a₁ b₁ : kRandomSeq} : a₀ = b₀ → kRandomSeq.eqe a₁ b₁ → kBool.eqe (kBool.validRandoms a₀ a₁) (kBool.validRandoms b₀ b₁)
    | eqe_deterministic {a b : kBlockRoundMode} : kBlockRoundMode.eqe a b → kBool.eqe (kBool.deterministic a) (kBool.deterministic b)
    | eqe_roundAway {a₀ b₀ : kBlockRoundMode} {a₁ b₁ a₂ b₂ : MRat} {a₃ b₃ : kBool} : kBlockRoundMode.eqe a₀ b₀ → a₁ = b₁ → a₂ = b₂ → kBool.eqe a₃ b₃ → kBool.eqe (kBool.roundAway a₀ a₁ a₂ a₃) (kBool.roundAway b₀ b₁ b₂ b₃)
    | eqe_clipsHigh {a b : kBlockRoundMode} : kBlockRoundMode.eqe a b → kBool.eqe (kBool.clipsHigh a) (kBool.clipsHigh b)
    | eqe_clipsLow {a b : kBlockRoundMode} : kBlockRoundMode.eqe a b → kBool.eqe (kBool.clipsLow a) (kBool.clipsLow b)
    | eqe_validCodes {a₀ b₀ : kFormat} {a₁ b₁ : kCodeSeq} : kFormat.eqe a₀ b₀ → kCodeSeq.eqe a₁ b₁ → kBool.eqe (kBool.validCodes a₀ a₁) (kBool.validCodes b₀ b₁)
    | eqe_validBlock {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ : kFormat} {a₃ b₃ : MRat} {a₄ b₄ : kCodeSeq} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → a₃ = b₃ → kCodeSeq.eqe a₄ b₄ → kBool.eqe (kBool.validBlock a₀ a₁ a₂ a₃ a₄) (kBool.validBlock b₀ b₁ b₂ b₃ b₄)
    | eqe_lt₁ {a₀ b₀ a₁ b₁ : MString} : a₀ = b₀ → a₁ = b₁ → kBool.eqe (kBool.lt₁ a₀ a₁) (kBool.lt₁ b₀ b₁)
    | eqe_lteq₁ {a₀ b₀ a₁ b₁ : MString} : a₀ = b₀ → a₁ = b₁ → kBool.eqe (kBool.lteq₁ a₀ a₁) (kBool.lteq₁ b₀ b₁)
    | eqe_gt₁ {a₀ b₀ a₁ b₁ : MString} : a₀ = b₀ → a₁ = b₁ → kBool.eqe (kBool.gt₁ a₀ a₁) (kBool.gt₁ b₀ b₁)
    | eqe_gteq₁ {a₀ b₀ a₁ b₁ : MString} : a₀ = b₀ → a₁ = b₁ → kBool.eqe (kBool.gteq₁ a₀ a₁) (kBool.gteq₁ b₀ b₁)
    | eqe_CompareLess {a₀ b₀ a₁ b₁ : kFormat} {a₂ b₂ a₃ b₃ : MRat} : kFormat.eqe a₀ b₀ → kFormat.eqe a₁ b₁ → a₂ = b₂ → a₃ = b₃ → kBool.eqe (kBool.CompareLess a₀ a₁ a₂ a₃) (kBool.CompareLess b₀ b₁ b₂ b₃)
    | eqe_CompareLessEqual {a₀ b₀ a₁ b₁ : kFormat} {a₂ b₂ a₃ b₃ : MRat} : kFormat.eqe a₀ b₀ → kFormat.eqe a₁ b₁ → a₂ = b₂ → a₃ = b₃ → kBool.eqe (kBool.CompareLessEqual a₀ a₁ a₂ a₃) (kBool.CompareLessEqual b₀ b₁ b₂ b₃)
    | eqe_CompareEqual {a₀ b₀ a₁ b₁ : kFormat} {a₂ b₂ a₃ b₃ : MRat} : kFormat.eqe a₀ b₀ → kFormat.eqe a₁ b₁ → a₂ = b₂ → a₃ = b₃ → kBool.eqe (kBool.CompareEqual a₀ a₁ a₂ a₃) (kBool.CompareEqual b₀ b₁ b₂ b₃)
    | eqe_CompareGreaterEqual {a₀ b₀ a₁ b₁ : kFormat} {a₂ b₂ a₃ b₃ : MRat} : kFormat.eqe a₀ b₀ → kFormat.eqe a₁ b₁ → a₂ = b₂ → a₃ = b₃ → kBool.eqe (kBool.CompareGreaterEqual a₀ a₁ a₂ a₃) (kBool.CompareGreaterEqual b₀ b₁ b₂ b₃)
    | eqe_CompareGreater {a₀ b₀ a₁ b₁ : kFormat} {a₂ b₂ a₃ b₃ : MRat} : kFormat.eqe a₀ b₀ → kFormat.eqe a₁ b₁ → a₂ = b₂ → a₃ = b₃ → kBool.eqe (kBool.CompareGreater a₀ a₁ a₂ a₃) (kBool.CompareGreater b₀ b₁ b₂ b₃)
    | eqe_IsZero {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqe a₀ b₀ → a₁ = b₁ → kBool.eqe (kBool.IsZero a₀ a₁) (kBool.IsZero b₀ b₁)
    | eqe_IsOne {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqe a₀ b₀ → a₁ = b₁ → kBool.eqe (kBool.IsOne a₀ a₁) (kBool.IsOne b₀ b₁)
    | eqe_IsNaN {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqe a₀ b₀ → a₁ = b₁ → kBool.eqe (kBool.IsNaN a₀ a₁) (kBool.IsNaN b₀ b₁)
    | eqe_IsInfinite {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqe a₀ b₀ → a₁ = b₁ → kBool.eqe (kBool.IsInfinite a₀ a₁) (kBool.IsInfinite b₀ b₁)
    | eqe_IsFinite {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqe a₀ b₀ → a₁ = b₁ → kBool.eqe (kBool.IsFinite a₀ a₁) (kBool.IsFinite b₀ b₁)
    | eqe_IsSignMinus {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqe a₀ b₀ → a₁ = b₁ → kBool.eqe (kBool.IsSignMinus a₀ a₁) (kBool.IsSignMinus b₀ b₁)
    | eqe_IsNormal {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqe a₀ b₀ → a₁ = b₁ → kBool.eqe (kBool.IsNormal a₀ a₁) (kBool.IsNormal b₀ b₁)
    | eqe_IsSubnormal {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqe a₀ b₀ → a₁ = b₁ → kBool.eqe (kBool.IsSubnormal a₀ a₁) (kBool.IsSubnormal b₀ b₁)
    | eqe_inF4 {a b : kFormat} : kFormat.eqe a b → kBool.eqe (kBool.inF4 a) (kBool.inF4 b)
    | eqe_inF8 {a b : kFormat} : kFormat.eqe a b → kBool.eqe (kBool.inF8 a) (kBool.inF8 b)
    | eqe_inFs {a b : kFormat} : kFormat.eqe a b → kBool.eqe (kBool.inFs a) (kBool.inFs b)
    | eqe_allowedExternal {a b : kFormat} : kFormat.eqe a b → kBool.eqe (kBool.allowedExternal a) (kBool.allowedExternal b)
    | eqe_containsFormat {a₀ b₀ : kFormat} {a₁ b₁ : kFormatSeq} : kFormat.eqe a₀ b₀ → kFormatSeq.eqe a₁ b₁ → kBool.eqe (kBool.containsFormat a₀ a₁) (kBool.containsFormat b₀ b₁)
    | eqe_validFX {a b : kFormatSeq} : kFormatSeq.eqe a b → kBool.eqe (kBool.validFX a) (kBool.validFX b)
    | eqe_validFXTail {a b : kFormatSeq} : kFormatSeq.eqe a b → kBool.eqe (kBool.validFXTail a) (kBool.validFXTail b)
    | eqe_allFormats {a b : kFormatSeq} : kFormatSeq.eqe a b → kBool.eqe (kBool.allFormats a) (kBool.allFormats b)
    | eqe_required {a₀ b₀ : kSpecialization} {a₁ b₁ : kFormatSeq} : kSpecialization.eqe a₀ b₀ → kFormatSeq.eqe a₁ b₁ → kBool.eqe (kBool.required a₀ a₁) (kBool.required b₀ b₁)
    | eqe_requiredNumeric {a₀ b₀ : MString} {a₁ b₁ a₂ b₂ : kFormatSeq} : a₀ = b₀ → kFormatSeq.eqe a₁ b₁ → kFormatSeq.eqe a₂ b₂ → kBool.eqe (kBool.requiredNumeric a₀ a₁ a₂) (kBool.requiredNumeric b₀ b₁ b₂)
    | eqe_requiredPlain {a₀ b₀ : MString} {a₁ b₁ a₂ b₂ : kFormatSeq} : a₀ = b₀ → kFormatSeq.eqe a₁ b₁ → kFormatSeq.eqe a₂ b₂ → kBool.eqe (kBool.requiredPlain a₀ a₁ a₂) (kBool.requiredPlain b₀ b₁ b₂)
    | eqe_minmaxName {a b : MString} : a = b → kBool.eqe (kBool.minmaxName a) (kBool.minmaxName b)
    | eqe_compareName {a b : MString} : a = b → kBool.eqe (kBool.compareName a) (kBool.compareName b)
    | eqe_predicateName {a b : MString} : a = b → kBool.eqe (kBool.predicateName a) (kBool.predicateName b)
    | eqe_formatNameOp {a b : MString} : a = b → kBool.eqe (kBool.formatNameOp a) (kBool.formatNameOp b)
    | eqe_numericPlainName {a b : MString} : a = b → kBool.eqe (kBool.numericPlainName a) (kBool.numericPlainName b)
    | eqe_blockElementArity {a₀ b₀ : MString} {a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqe (kBool.blockElementArity a₀ a₁) (kBool.blockElementArity b₀ b₁)
    | eqe_numericResult {a b : kSpecialization} : kSpecialization.eqe a b → kBool.eqe (kBool.numericResult a) (kBool.numericResult b)
    | eqe_hasDeclaration {a₀ b₀ : kSpecialization} {a₁ b₁ : kDeclarationSeq} : kSpecialization.eqe a₀ b₀ → kDeclarationSeq.eqe a₁ b₁ → kBool.eqe (kBool.hasDeclaration a₀ a₁) (kBool.hasDeclaration b₀ b₁)
    | eqe_declarationsCover {a₀ b₀ : kSpecializationSeq} {a₁ b₁ : kDeclarationSeq} : kSpecializationSeq.eqe a₀ b₀ → kDeclarationSeq.eqe a₁ b₁ → kBool.eqe (kBool.declarationsCover a₀ a₁) (kBool.declarationsCover b₀ b₁)
    | eqe_partition {a₀ b₀ : kCodeSeq} {a₁ b₁ : kPartitionSeq} : kCodeSeq.eqe a₀ b₀ → kPartitionSeq.eqe a₁ b₁ → kBool.eqe (kBool.partition a₀ a₁) (kBool.partition b₀ b₁)
    | eqe_partitionDisjoint {a b : kPartitionSeq} : kPartitionSeq.eqe a b → kBool.eqe (kBool.partitionDisjoint a) (kBool.partitionDisjoint b)
    | eqe_validSpecialization {a b : kSpecialization} : kSpecialization.eqe a b → kBool.eqe (kBool.validSpecialization a) (kBool.validSpecialization b)
    | eqe_numericArity {a₀ b₀ : MString} {a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqe (kBool.numericArity a₀ a₁) (kBool.numericArity b₀ b₁)
    | eqe_plainArity {a₀ b₀ : MString} {a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqe (kBool.plainArity a₀ a₁) (kBool.plainArity b₀ b₁)
    | eqe_wellFormedDeclaration {a b : kDeclaration} : kDeclaration.eqe a b → kBool.eqe (kBool.wellFormedDeclaration a) (kBool.wellFormedDeclaration b)
    | eqe_evidenceComplete {a b : kEvidence} : kEvidence.eqe a b → kBool.eqe (kBool.evidenceComplete a) (kBool.evidenceComplete b)
    | eqe_memberCode {a₀ b₀ : MRat} {a₁ b₁ : kCodeSeq} : a₀ = b₀ → kCodeSeq.eqe a₁ b₁ → kBool.eqe (kBool.memberCode a₀ a₁) (kBool.memberCode b₀ b₁)
    | eqe_disjointCodes {a₀ b₀ a₁ b₁ : kCodeSeq} : kCodeSeq.eqe a₀ b₀ → kCodeSeq.eqe a₁ b₁ → kBool.eqe (kBool.disjointCodes a₀ a₁) (kBool.disjointCodes b₀ b₁)
    | eqe_uniqueCodes {a b : kCodeSeq} : kCodeSeq.eqe a b → kBool.eqe (kBool.uniqueCodes a) (kBool.uniqueCodes b)
    | eqe_subsetCodes {a₀ b₀ a₁ b₁ : kCodeSeq} : kCodeSeq.eqe a₀ b₀ → kCodeSeq.eqe a₁ b₁ → kBool.eqe (kBool.subsetCodes a₀ a₁) (kBool.subsetCodes b₀ b₁)
    | eqe_partition2 {a₀ b₀ a₁ b₁ a₂ b₂ : kCodeSeq} : kCodeSeq.eqe a₀ b₀ → kCodeSeq.eqe a₁ b₁ → kCodeSeq.eqe a₂ b₂ → kBool.eqe (kBool.partition2 a₀ a₁ a₂) (kBool.partition2 b₀ b₁ b₂)
    | eqe_inArityTable {a₀ b₀ : MString} {a₁ b₁ : MRat} {a₂ b₂ : kArityTable} : a₀ = b₀ → a₁ = b₁ → kArityTable.eqe a₂ b₂ → kBool.eqe (kBool.inArityTable a₀ a₁ a₂) (kBool.inArityTable b₀ b₁ b₂)
    | eqe_TotalOrder {a₀ b₀ a₁ b₁ : kFormat} {a₂ b₂ a₃ b₃ : MRat} : kFormat.eqe a₀ b₀ → kFormat.eqe a₁ b₁ → a₂ = b₂ → a₃ = b₃ → kBool.eqe (kBool.TotalOrder a₀ a₁ a₂ a₃) (kBool.TotalOrder b₀ b₁ b₂ b₃)
    | eqe_eqeq₀ {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqe (kBool.eqeq₀ a₀ a₁) (kBool.eqeq₀ b₀ b₁)
    | eqe_ifthenelsefi {a₀ b₀ a₁ b₁ a₂ b₂ : kBool} : kBool.eqe a₀ b₀ → kBool.eqe a₁ b₁ → kBool.eqe a₂ b₂ → kBool.eqe (kBool.ifthenelsefi a₀ a₁ a₂) (kBool.ifthenelsefi b₀ b₁ b₂)
    | eqe_eqeq₁ {a₀ b₀ a₁ b₁ : kSignedness} : kSignedness.eqe a₀ b₀ → kSignedness.eqe a₁ b₁ → kBool.eqe (kBool.eqeq₁ a₀ a₁) (kBool.eqeq₁ b₀ b₁)
    | eqe_eqeq₂ {a₀ b₀ a₁ b₁ : kDomain} : kDomain.eqe a₀ b₀ → kDomain.eqe a₁ b₁ → kBool.eqe (kBool.eqeq₂ a₀ a₁) (kBool.eqeq₂ b₀ b₁)
    | eqe_eqslasheq₀ {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBool.eqe (kBool.eqslasheq₀ a₀ a₁) (kBool.eqslasheq₀ b₀ b₁)
    | eqe_eqeq₃ {a₀ b₀ a₁ b₁ : kBlockRoundMode} : kBlockRoundMode.eqe a₀ b₀ → kBlockRoundMode.eqe a₁ b₁ → kBool.eqe (kBool.eqeq₃ a₀ a₁) (kBool.eqeq₃ b₀ b₁)
    | eqe_eqeq₄ {a₀ b₀ a₁ b₁ : kBool} : kBool.eqe a₀ b₀ → kBool.eqe a₁ b₁ → kBool.eqe (kBool.eqeq₄ a₀ a₁) (kBool.eqeq₄ b₀ b₁)
    | eqe_eqeq₅ {a₀ b₀ a₁ b₁ : MString} : a₀ = b₀ → a₁ = b₁ → kBool.eqe (kBool.eqeq₅ a₀ a₁) (kBool.eqeq₅ b₀ b₁)
    | eqe_eqeq₆ {a₀ b₀ a₁ b₁ : kFormat} : kFormat.eqe a₀ b₀ → kFormat.eqe a₁ b₁ → kBool.eqe (kBool.eqeq₆ a₀ a₁) (kBool.eqeq₆ b₀ b₁)
    | eqe_eqeq₇ {a₀ b₀ a₁ b₁ : kProjSpec} : kProjSpec.eqe a₀ b₀ → kProjSpec.eqe a₁ b₁ → kBool.eqe (kBool.eqeq₇ a₀ a₁) (kBool.eqeq₇ b₀ b₁)
    | eqe_eqslasheq₁ {a₀ b₀ a₁ b₁ : kBool} : kBool.eqe a₀ b₀ → kBool.eqe a₁ b₁ → kBool.eqe (kBool.eqslasheq₁ a₀ a₁) (kBool.eqslasheq₁ b₀ b₁)
    | eqe_eqslasheq₂ {a₀ b₀ a₁ b₁ : MString} : a₀ = b₀ → a₁ = b₁ → kBool.eqe (kBool.eqslasheq₂ a₀ a₁) (kBool.eqslasheq₂ b₀ b₁)
    | eqe_eqeq₈ {a₀ b₀ a₁ b₁ : kSpecialization} : kSpecialization.eqe a₀ b₀ → kSpecialization.eqe a₁ b₁ → kBool.eqe (kBool.eqeq₈ a₀ a₁) (kBool.eqeq₈ b₀ b₁)
    -- Equations
    | eq_and₀ {a} : kBool.has_sort a MSort.Bool → kBool.eqe (kBool.and kBool.true a) a
    | eq_and₁ {a} : kBool.has_sort a MSort.Bool → kBool.eqe (kBool.and kBool.false a) kBool.false
    | eq_and₂ {a} : kBool.has_sort a MSort.Bool → kBool.eqe (kBool.and a a) a
    | eq_xor₀ {a} : kBool.has_sort a MSort.Bool → kBool.eqe (kBool.xor kBool.false a) a
    | eq_xor₁ {a} : kBool.has_sort a MSort.Bool → kBool.eqe (kBool.xor a a) kBool.false
    | eq_and₃ {a b c} : kBool.has_sort a MSort.Bool → kBool.has_sort b MSort.Bool → kBool.has_sort c MSort.Bool → kBool.eqe (kBool.and a (kBool.xor b c)) (kBool.xor (kBool.and a b) (kBool.and a c))
    | eq_not {a} : kBool.has_sort a MSort.Bool → kBool.eqe (kBool.not a) (kBool.xor kBool.true a)
    | eq_or {a b} : kBool.has_sort a MSort.Bool → kBool.has_sort b MSort.Bool → kBool.eqe (kBool.or a b) (kBool.xor (kBool.and a b) (kBool.xor a b))
    | eq_implies {a b} : kBool.has_sort a MSort.Bool → kBool.has_sort b MSort.Bool → kBool.eqe (kBool.implies a b) (kBool.not (kBool.xor a (kBool.and a b)))
    | eq_lt₀₀ {i n j m} : MRat.has_sort i MSort.NzInt → MRat.has_sort n MSort.NzNat → MRat.has_sort j MSort.NzInt → MRat.has_sort m MSort.NzNat → kBool.eqe (if (i / n) < (j / m) then kBool.true else kBool.false) (if (i * m) < (j * n) then kBool.true else kBool.false)
    | eq_lt₀₁ {i n k} : MRat.has_sort i MSort.NzInt → MRat.has_sort n MSort.NzNat → MRat.has_sort k MSort.Int → kBool.eqe (if (i / n) < k then kBool.true else kBool.false) (if i < (n * k) then kBool.true else kBool.false)
    | eq_lt₀₂ {k j m} : MRat.has_sort k MSort.Int → MRat.has_sort j MSort.NzInt → MRat.has_sort m MSort.NzNat → kBool.eqe (if k < (j / m) then kBool.true else kBool.false) (if (m * k) < j then kBool.true else kBool.false)
    | eq_lteq₀₀ {i n j m} : MRat.has_sort i MSort.NzInt → MRat.has_sort n MSort.NzNat → MRat.has_sort j MSort.NzInt → MRat.has_sort m MSort.NzNat → kBool.eqe (if (i / n) ≤ (j / m) then kBool.true else kBool.false) (if (i * m) ≤ (j * n) then kBool.true else kBool.false)
    | eq_lteq₀₁ {i n k} : MRat.has_sort i MSort.NzInt → MRat.has_sort n MSort.NzNat → MRat.has_sort k MSort.Int → kBool.eqe (if (i / n) ≤ k then kBool.true else kBool.false) (if i ≤ (n * k) then kBool.true else kBool.false)
    | eq_lteq₀₂ {k j m} : MRat.has_sort k MSort.Int → MRat.has_sort j MSort.NzInt → MRat.has_sort m MSort.NzNat → kBool.eqe (if k ≤ (j / m) then kBool.true else kBool.false) (if (m * k) ≤ j then kBool.true else kBool.false)
    | eq_gt₀₀ {i n j m} : MRat.has_sort i MSort.NzInt → MRat.has_sort n MSort.NzNat → MRat.has_sort j MSort.NzInt → MRat.has_sort m MSort.NzNat → kBool.eqe (if (j / m) < (i / n) then kBool.true else kBool.false) (if (j * n) < (i * m) then kBool.true else kBool.false)
    | eq_gt₀₁ {i n k} : MRat.has_sort i MSort.NzInt → MRat.has_sort n MSort.NzNat → MRat.has_sort k MSort.Int → kBool.eqe (if k < (i / n) then kBool.true else kBool.false) (if (n * k) < i then kBool.true else kBool.false)
    | eq_gt₀₂ {k j m} : MRat.has_sort k MSort.Int → MRat.has_sort j MSort.NzInt → MRat.has_sort m MSort.NzNat → kBool.eqe (if (j / m) < k then kBool.true else kBool.false) (if j < (m * k) then kBool.true else kBool.false)
    | eq_gteq₀₀ {i n j m} : MRat.has_sort i MSort.NzInt → MRat.has_sort n MSort.NzNat → MRat.has_sort j MSort.NzInt → MRat.has_sort m MSort.NzNat → kBool.eqe (if (j / m) ≤ (i / n) then kBool.true else kBool.false) (if (j * n) ≤ (i * m) then kBool.true else kBool.false)
    | eq_gteq₀₁ {i n k} : MRat.has_sort i MSort.NzInt → MRat.has_sort n MSort.NzNat → MRat.has_sort k MSort.Int → kBool.eqe (if k ≤ (i / n) then kBool.true else kBool.false) (if (n * k) ≤ i then kBool.true else kBool.false)
    | eq_gteq₀₂ {k j m} : MRat.has_sort k MSort.Int → MRat.has_sort j MSort.NzInt → MRat.has_sort m MSort.NzNat → kBool.eqe (if (j / m) ≤ k then kBool.true else kBool.false) (if j ≤ (m * k) then kBool.true else kBool.false)
    | eq_divides₀ {i n k} : MRat.has_sort i MSort.NzInt → MRat.has_sort n MSort.NzNat → MRat.has_sort k MSort.Int → kBool.eqe (if k.num % (i / n).num = 0 then kBool.true else kBool.false) (if (n * k).num % i.num = 0 then kBool.true else kBool.false)
    | eq_divides₁ {q j m} : MRat.has_sort q MSort.NzRat → MRat.has_sort j MSort.NzInt → MRat.has_sort m MSort.NzNat → kBool.eqe (if (j / m).num % q.num = 0 then kBool.true else kBool.false) (if j.num % (q * m).num = 0 then kBool.true else kBool.false)
    | eq_p31zero9_xreal_zerozero1 : kBool.eqe (kBool.xNaN kXReal.nan) kBool.true
    | eq_p31zero9_xreal_zerozero2 {a} : kXReal.has_sort a MSort.Number → kBool.eqe (kBool.xNaN a) kBool.false
    | eq_p31zero9_xreal_zerozero3 : kBool.eqe (kBool.xInfinite kXReal.nan) kBool.false
    | eq_p31zero9_xreal_zerozero4 {i} : kXReal.has_sort i MSort.Infinity → kBool.eqe (kBool.xInfinite i) kBool.true
    | eq_p31zero9_xreal_zerozero5 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xInfinite u) kBool.false
    | eq_p31zero9_xreal_zerozero6 : kBool.eqe (kBool.xFinite kXReal.nan) kBool.false
    | eq_p31zero9_xreal_zerozero7 {i} : kXReal.has_sort i MSort.Infinity → kBool.eqe (kBool.xFinite i) kBool.false
    | eq_p31zero9_xreal_zerozero8 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xFinite u) kBool.true
    | eq_p31zero9_xreal_zerozero9 : kBool.eqe (kBool.xMinus kXReal.nan) kBool.false
    | eq_p31zero9_xreal_zero1zero : kBool.eqe (kBool.xMinus kXReal.posInf) kBool.false
    | eq_p31zero9_xreal_zero11 : kBool.eqe (kBool.xMinus kXReal.negInf) kBool.true
    | eq_p31zero9_xreal_zero12 {r} : kBool.eqe (kBool.xMinus (kXReal.fin r)) (if r < (0 : MRat) then kBool.true else kBool.false)
    | eq_p31zero9_xreal_zero13 {x} : kXReal.has_sort x MSort.XReal → kBool.eqe (kBool.xLt kXReal.nan x) kBool.false
    | eq_p31zero9_xreal_zero14 {a} : kXReal.has_sort a MSort.Number → kBool.eqe (kBool.xLt a kXReal.nan) kBool.false
    | eq_p31zero9_xreal_zero15 : kBool.eqe (kBool.xLt kXReal.negInf kXReal.posInf) kBool.true
    | eq_p31zero9_xreal_zero16 : kBool.eqe (kBool.xLt kXReal.posInf kXReal.negInf) kBool.false
    | eq_p31zero9_xreal_zero17 {i} : kXReal.has_sort i MSort.Infinity → kBool.eqe (kBool.xLt i i) kBool.false
    | eq_p31zero9_xreal_zero18 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt kXReal.negInf u) kBool.true
    | eq_p31zero9_xreal_zero19 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt u kXReal.posInf) kBool.true
    | eq_p31zero9_xreal_zero2zero {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt kXReal.posInf u) kBool.false
    | eq_p31zero9_xreal_zero21 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt u kXReal.negInf) kBool.false
    | eq_p31zero9_xreal_zero22 {r s₁} : kBool.eqe (kBool.xLt (kXReal.fin r) (kXReal.fin s₁)) (if r < s₁ then kBool.true else kBool.false)
    | eq_p31zero9_xreal_zero23 {x} : kXReal.has_sort x MSort.XReal → kBool.eqe (kBool.xEq kXReal.nan x) kBool.false
    | eq_p31zero9_xreal_zero24 {a} : kXReal.has_sort a MSort.Number → kBool.eqe (kBool.xEq a kXReal.nan) kBool.false
    | eq_p31zero9_xreal_zero25 {i} : kXReal.has_sort i MSort.Infinity → kBool.eqe (kBool.xEq i i) kBool.true
    | eq_p31zero9_xreal_zero26 : kBool.eqe (kBool.xEq kXReal.posInf kXReal.negInf) kBool.false
    | eq_p31zero9_xreal_zero27 : kBool.eqe (kBool.xEq kXReal.negInf kXReal.posInf) kBool.false
    | eq_p31zero9_xreal_zero28 {i u} : kXReal.has_sort i MSort.Infinity → kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xEq i u) kBool.false
    | eq_p31zero9_xreal_zero29 {u i} : kXReal.has_sort u MSort.Real → kXReal.has_sort i MSort.Infinity → kBool.eqe (kBool.xEq u i) kBool.false
    | eq_p31zero9_xreal_zero3zero {r s₁} : kBool.eqe (kBool.xEq (kXReal.fin r) (kXReal.fin s₁)) (kBool.eqeq₀ r s₁)
    | eq_p31zero9_xreal_zero31 {x y} : kXReal.has_sort x MSort.XReal → kXReal.has_sort y MSort.XReal → kBool.eqe (kBool.xLe x y) (kBool.or (kBool.xLt x y) (kBool.xEq x y))
    | eq_p31zero9_rational_math_zerozero5 {i} : MRat.has_sort i MSort.Int → kBool.eqe (kBool.even i) (kBool.eqeq₀ (((Int.tmod i.num (2 : MRat).num : Int) : Rat)) (0 : MRat))
    | eq_p31zero9_format_core_zerozero1 {k p s₁ d} : MRat.has_sort k MSort.Int → MRat.has_sort p MSort.Int → kSignedness.has_sort s₁ MSort.Signedness → kDomain.has_sort d MSort.Domain → kBool.eqe (kBool.validFormat (kFormat.Binary k p s₁ d)) (kBool.and (kBool.and (if (0 : MRat) < p then kBool.true else kBool.false) (kBool.ifthenelsefi (kBool.eqeq₁ s₁ kSignedness.Signed) (if p < k then kBool.true else kBool.false) (if p ≤ k then kBool.true else kBool.false))) (if (2 : MRat) < k then kBool.true else kBool.false))
    | eq_p31zero9_format_core_zerozero2 {k p s₁ d} : MRat.has_sort k MSort.Int → MRat.has_sort p MSort.Int → kSignedness.has_sort s₁ MSort.Signedness → kDomain.has_sort d MSort.Domain → kBool.eqe (kBool.internalFormat (kFormat.Binary k p s₁ d)) kBool.true
    | eq_p31zero9_format_core_zero15 : kBool.eqe (kBool.validFormat kFormat.binary64) kBool.true
    | eq_p31zero9_format_core_zero16 : kBool.eqe (kBool.internalFormat kFormat.binary64) kBool.false
    | eq_p31zero9_format_core_zero23 : kBool.eqe (kBool.validFormat kFormat.binary32) kBool.true
    | eq_p31zero9_format_core_zero24 : kBool.eqe (kBool.internalFormat kFormat.binary32) kBool.false
    | eq_p31zero9_format_core_zero31 : kBool.eqe (kBool.validFormat kFormat.binary16) kBool.true
    | eq_p31zero9_format_core_zero32 : kBool.eqe (kBool.internalFormat kFormat.binary16) kBool.false
    | eq_p31zero9_format_core_zero39 : kBool.eqe (kBool.validFormat kFormat.BFloat16) kBool.true
    | eq_p31zero9_format_core_zero4zero : kBool.eqe (kBool.internalFormat kFormat.BFloat16) kBool.false
    | eq_p31zero9_code_invalid_format {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.not (kBool.validFormat f)) kBool.true → kBool.eqe (kBool.validCode f c) kBool.false
    | eq_p31zero9_codec_zerozero1 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validFormat f) kBool.true → kBool.eqe (kBool.validCode f c) (kBool.and (if c < ((2 : MRat) ^ (MRat.BitwidthOf f).num.toNat) then kBool.true else kBool.false) (if (0 : MRat) ≤ c then kBool.true else kBool.false))
    | eq_p31zero9_codec_zero12 {f x} : kFormat.has_sort f MSort.Format → kXReal.has_sort x MSort.XReal → kBool.eqe (kBool.not (kBool.validFormat f)) kBool.true → kBool.eqe (kBool.datum f x) kBool.false
    | eq_p31zero9_codec_zero13 {f x} : kFormat.has_sort f MSort.Format → kXReal.has_sort x MSort.XReal → kBool.eqe (kBool.validFormat f) kBool.true → kBool.eqe (kBool.not (kBool.internalFormat f)) kBool.true → kBool.eqe (kBool.datum f x) (kBool.externalDatum f x)
    | eq_p31zero9_codec_zero14 {f} : kFormat.has_sort f MSort.Format → kBool.eqe (kBool.validFormat f) kBool.true → kBool.eqe (kBool.internalFormat f) kBool.true → kBool.eqe (kBool.datum f kXReal.nan) kBool.true
    | eq_p31zero9_codec_zero15 {f} : kFormat.has_sort f MSort.Format → kBool.eqe (kBool.validFormat f) kBool.true → kBool.eqe (kBool.internalFormat f) kBool.true → kBool.eqe (kBool.datum f kXReal.posInf) (kBool.eqeq₂ (kDomain.DomainOf f) kDomain.Extended)
    | eq_p31zero9_codec_zero16 {f} : kFormat.has_sort f MSort.Format → kBool.eqe (kBool.validFormat f) kBool.true → kBool.eqe (kBool.internalFormat f) kBool.true → kBool.eqe (kBool.datum f kXReal.negInf) (kBool.and (kBool.eqeq₁ (kSignedness.SignednessOf f) kSignedness.Signed) (kBool.eqeq₂ (kDomain.DomainOf f) kDomain.Extended))
    | eq_p31zero9_codec_zero17 {f r} : kFormat.has_sort f MSort.Format → kBool.eqe (kBool.validFormat f) kBool.true → kBool.eqe (kBool.internalFormat f) kBool.true → kBool.eqe (if r < (0 : MRat) then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.eqeq₁ (kSignedness.SignednessOf f) kSignedness.Unsigned) kBool.true → kBool.eqe (kBool.datum f (kXReal.fin r)) kBool.false
    | eq_p31zero9_codec_zero18 {f} : kFormat.has_sort f MSort.Format → kBool.eqe (kBool.validFormat f) kBool.true → kBool.eqe (kBool.internalFormat f) kBool.true → kBool.eqe (kBool.datum f (kXReal.fin (0 : MRat))) kBool.true
    | eq_p31zero9_codec_zero19 {f r} : kFormat.has_sort f MSort.Format → kBool.eqe (kBool.validFormat f) kBool.true → kBool.eqe (kBool.internalFormat f) kBool.true → kBool.eqe (kBool.eqslasheq₀ r (0 : MRat)) kBool.true → kBool.eqe (kBool.or (if (0 : MRat) < r then kBool.true else kBool.false) (kBool.eqeq₁ (kSignedness.SignednessOf f) kSignedness.Signed)) kBool.true → kBool.eqe (kBool.datum f (kXReal.fin r)) (kBool.candidateDatum f (if r < 0 then - r else r) (MRat.magnitudeCode f (if r < 0 then - r else r)))
    | eq_p31zero9_codec_zero21 {f r c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.or (kBool.or (kBool.and (kBool.eqeq₀ c (MRat.positiveLimit f)) (kBool.eqeq₂ (kDomain.DomainOf f) kDomain.Extended)) (if (MRat.positiveLimit f) < c then kBool.true else kBool.false)) (if c < (0 : MRat) then kBool.true else kBool.false)) kBool.true → kBool.eqe (kBool.candidateDatum f r c) kBool.false
    | eq_p31zero9_codec_zero22 {f r c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (if (0 : MRat) ≤ c then kBool.true else kBool.false) kBool.true → kBool.eqe (if c ≤ (MRat.positiveLimit f) then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.or (if c < (MRat.positiveLimit f) then kBool.true else kBool.false) (kBool.eqeq₂ (kDomain.DomainOf f) kDomain.Finite)) kBool.true → kBool.eqe (kBool.candidateDatum f r c) (kBool.xEq (kXReal.decode f c) (kXReal.fin r))
    | eq_p31zero9_random_negative_bits {n r} : MRat.has_sort n MSort.Int → MRat.has_sort r MSort.Int → kBool.eqe (if n < (0 : MRat) then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.randomInRange n r) kBool.false
    | eq_p31zero9_random_range {n r} : MRat.has_sort n MSort.Int → MRat.has_sort r MSort.Int → kBool.eqe (if (0 : MRat) ≤ n then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.randomInRange n r) (kBool.and (if r < ((2 : MRat) ^ n.num.toNat) then kBool.true else kBool.false) (if (0 : MRat) ≤ r then kBool.true else kBool.false))
    | eq_p31zero9_projection_spec_zerozero1 : kBool.eqe (kBool.validRound kBlockRoundMode.NearestTiesToEven) kBool.true
    | eq_p31zero9_projection_spec_zerozero2 : kBool.eqe (kBool.deterministic kBlockRoundMode.NearestTiesToEven) kBool.true
    | eq_p31zero9_projection_spec_zerozero3 : kBool.eqe (kBool.validRound kBlockRoundMode.NearestTiesToAway) kBool.true
    | eq_p31zero9_projection_spec_zerozero4 : kBool.eqe (kBool.deterministic kBlockRoundMode.NearestTiesToAway) kBool.true
    | eq_p31zero9_projection_spec_zerozero5 : kBool.eqe (kBool.validRound kBlockRoundMode.TowardPositive) kBool.true
    | eq_p31zero9_projection_spec_zerozero6 : kBool.eqe (kBool.deterministic kBlockRoundMode.TowardPositive) kBool.true
    | eq_p31zero9_projection_spec_zerozero7 : kBool.eqe (kBool.validRound kBlockRoundMode.TowardNegative) kBool.true
    | eq_p31zero9_projection_spec_zerozero8 : kBool.eqe (kBool.deterministic kBlockRoundMode.TowardNegative) kBool.true
    | eq_p31zero9_projection_spec_zerozero9 : kBool.eqe (kBool.validRound kBlockRoundMode.TowardZero) kBool.true
    | eq_p31zero9_projection_spec_zero1zero : kBool.eqe (kBool.deterministic kBlockRoundMode.TowardZero) kBool.true
    | eq_p31zero9_projection_spec_zero11 : kBool.eqe (kBool.validRound kBlockRoundMode.ToOdd) kBool.true
    | eq_p31zero9_projection_spec_zero12 : kBool.eqe (kBool.deterministic kBlockRoundMode.ToOdd) kBool.true
    | eq_p31zero9_projection_spec_zero13 {n r} : MRat.has_sort n MSort.Int → MRat.has_sort r MSort.Int → kBool.eqe (kBool.validRound (kBlockRoundMode.StochasticA n r)) (kBool.randomInRange n r)
    | eq_p31zero9_projection_spec_zero14 {n r} : MRat.has_sort n MSort.Int → MRat.has_sort r MSort.Int → kBool.eqe (kBool.deterministic (kBlockRoundMode.StochasticA n r)) kBool.false
    | eq_p31zero9_projection_spec_zero15 {n rs s₁ b} : MRat.has_sort n MSort.Int → kRandomSeq.has_sort rs MSort.RandomSeq → kSatMode.has_sort s₁ MSort.SatMode → MRat.has_sort b MSort.Nat → kBool.eqe (kBool.validBlockProjection (kBlockProjSpec.bproj (kBlockRoundMode.BlockStochasticA n rs) s₁) b) (kBool.and (kBool.and (kBool.validRandoms n rs) (kBool.eqeq₀ (MRat.length₀ rs) b)) (if (1 : MRat) ≤ b then kBool.true else kBool.false))
    | eq_p31zero9_projection_spec_zero18 {n r} : MRat.has_sort n MSort.Int → MRat.has_sort r MSort.Int → kBool.eqe (kBool.validRound (kBlockRoundMode.StochasticB n r)) (kBool.randomInRange n r)
    | eq_p31zero9_projection_spec_zero19 {n r} : MRat.has_sort n MSort.Int → MRat.has_sort r MSort.Int → kBool.eqe (kBool.deterministic (kBlockRoundMode.StochasticB n r)) kBool.false
    | eq_p31zero9_projection_spec_zero2zero {n rs s₁ b} : MRat.has_sort n MSort.Int → kRandomSeq.has_sort rs MSort.RandomSeq → kSatMode.has_sort s₁ MSort.SatMode → MRat.has_sort b MSort.Nat → kBool.eqe (kBool.validBlockProjection (kBlockProjSpec.bproj (kBlockRoundMode.BlockStochasticB n rs) s₁) b) (kBool.and (kBool.and (kBool.validRandoms n rs) (kBool.eqeq₀ (MRat.length₀ rs) b)) (if (1 : MRat) ≤ b then kBool.true else kBool.false))
    | eq_p31zero9_projection_spec_zero23 {n r} : MRat.has_sort n MSort.Int → MRat.has_sort r MSort.Int → kBool.eqe (kBool.validRound (kBlockRoundMode.StochasticC n r)) (kBool.randomInRange n r)
    | eq_p31zero9_projection_spec_zero24 {n r} : MRat.has_sort n MSort.Int → MRat.has_sort r MSort.Int → kBool.eqe (kBool.deterministic (kBlockRoundMode.StochasticC n r)) kBool.false
    | eq_p31zero9_projection_spec_zero25 {n rs s₁ b} : MRat.has_sort n MSort.Int → kRandomSeq.has_sort rs MSort.RandomSeq → kSatMode.has_sort s₁ MSort.SatMode → MRat.has_sort b MSort.Nat → kBool.eqe (kBool.validBlockProjection (kBlockProjSpec.bproj (kBlockRoundMode.BlockStochasticC n rs) s₁) b) (kBool.and (kBool.and (kBool.validRandoms n rs) (kBool.eqeq₀ (MRat.length₀ rs) b)) (if (1 : MRat) ≤ b then kBool.true else kBool.false))
    | eq_p31zero9_projection_spec_zero28 {m s₁} : kBlockRoundMode.has_sort m MSort.RoundMode → kSatMode.has_sort s₁ MSort.SatMode → kBool.eqe (kBool.validProjection (kProjSpec.proj m s₁)) (kBool.validRound m)
    | eq_p31zero9_projection_spec_zero31 {n} : MRat.has_sort n MSort.Int → kBool.eqe (kBool.validRandoms n kRandomSeq.rnil) (if (0 : MRat) ≤ n then kBool.true else kBool.false)
    | eq_p31zero9_projection_spec_zero32 {n r rs} : MRat.has_sort n MSort.Int → MRat.has_sort r MSort.Int → kRandomSeq.has_sort rs MSort.RandomSeq → kBool.eqe (kBool.validRandoms n (kRandomSeq.rcons r rs)) (kBool.and (kBool.randomInRange n r) (kBool.validRandoms n rs))
    | eq_p31zero9_projection_spec_zero33 {m s₁ b} : kBlockRoundMode.has_sort m MSort.RoundMode → kSatMode.has_sort s₁ MSort.SatMode → MRat.has_sort b MSort.Nat → kBool.eqe (kBool.validBlockProjection (kBlockProjSpec.bproj m s₁) b) (kBool.and (kBool.and (kBool.validRound m) (kBool.deterministic m)) (if (1 : MRat) ≤ b then kBool.true else kBool.false))
    | eq_p31zero9_rounding_zerozero6 {x v e} : kBool.has_sort e MSort.Bool → kBool.eqe (kBool.roundAway kBlockRoundMode.TowardZero x v e) kBool.false
    | eq_p31zero9_rounding_zerozero7 {x v e} : kBool.has_sort e MSort.Bool → kBool.eqe (kBool.roundAway kBlockRoundMode.TowardPositive x v e) (kBool.and (if (0 : MRat) < x then kBool.true else kBool.false) (if (0 : MRat) < v then kBool.true else kBool.false))
    | eq_p31zero9_rounding_zerozero8 {x v e} : kBool.has_sort e MSort.Bool → kBool.eqe (kBool.roundAway kBlockRoundMode.TowardNegative x v e) (kBool.and (if x < (0 : MRat) then kBool.true else kBool.false) (if (0 : MRat) < v then kBool.true else kBool.false))
    | eq_p31zero9_rounding_zerozero9 {x v e} : kBool.has_sort e MSort.Bool → kBool.eqe (kBool.roundAway kBlockRoundMode.NearestTiesToAway x v e) (if ((1 / 2) : MRat) ≤ v then kBool.true else kBool.false)
    | eq_p31zero9_rounding_zero1zero {x v e} : kBool.has_sort e MSort.Bool → kBool.eqe (kBool.roundAway kBlockRoundMode.NearestTiesToEven x v e) (kBool.or (kBool.and (kBool.not e) (kBool.eqeq₀ v ((1 / 2) : MRat))) (if ((1 / 2) : MRat) < v then kBool.true else kBool.false))
    | eq_p31zero9_rounding_zero11 {x v e} : kBool.has_sort e MSort.Bool → kBool.eqe (kBool.roundAway kBlockRoundMode.ToOdd x v e) (kBool.and e (if (0 : MRat) < v then kBool.true else kBool.false))
    | eq_p31zero9_rounding_zero12 {n r x v e} : MRat.has_sort n MSort.Int → MRat.has_sort r MSort.Int → kBool.has_sort e MSort.Bool → kBool.eqe (kBool.roundAway (kBlockRoundMode.StochasticA n r) x v e) (if (MRat.pow2 n) ≤ (r + (MRat.floor (v * (MRat.pow2 n)))) then kBool.true else kBool.false)
    | eq_p31zero9_rounding_zero13 {n r x v e} : MRat.has_sort n MSort.Int → MRat.has_sort r MSort.Int → kBool.has_sort e MSort.Bool → kBool.eqe (kBool.roundAway (kBlockRoundMode.StochasticB n r) x v e) (if (MRat.pow2 (n + (1 : MRat))) ≤ ((MRat.floor (v * (MRat.pow2 (n + (1 : MRat))))) + ((1 : MRat) + (r * (2 : MRat)))) then kBool.true else kBool.false)
    | eq_p31zero9_rounding_zero14 {n r x v e} : MRat.has_sort n MSort.Int → MRat.has_sort r MSort.Int → kBool.has_sort e MSort.Bool → kBool.eqe (kBool.roundAway (kBlockRoundMode.StochasticC n r) x v e) (if (MRat.pow2 n) ≤ (r + (MRat.nearestEvenInteger (v * (MRat.pow2 n)))) then kBool.true else kBool.false)
    | eq_p31zero9_saturation_zerozero1 {m} : kBlockRoundMode.has_sort m MSort.RoundMode → kBool.eqe (kBool.clipsHigh m) (kBool.or (kBool.eqeq₃ m kBlockRoundMode.TowardNegative) (kBool.eqeq₃ m kBlockRoundMode.TowardZero))
    | eq_p31zero9_saturation_zerozero2 {m} : kBlockRoundMode.has_sort m MSort.RoundMode → kBool.eqe (kBool.clipsLow m) (kBool.or (kBool.eqeq₃ m kBlockRoundMode.TowardPositive) (kBool.eqeq₃ m kBlockRoundMode.TowardZero))
    | eq_p31zero9_block_core_zerozero1 {fx} : kFormat.has_sort fx MSort.Format → kBool.eqe (kBool.validCodes fx kCodeSeq.cnil) (kBool.validFormat fx)
    | eq_p31zero9_block_core_zerozero2 {fx c cs} : kFormat.has_sort fx MSort.Format → MRat.has_sort c MSort.Int → kCodeSeq.has_sort cs MSort.CodeSeq → kBool.eqe (kBool.validCodes fx (kCodeSeq.ccons c cs)) (kBool.and (kBool.validCode fx c) (kBool.validCodes fx cs))
    | eq_p31zero9_block_core_zerozero3 {b fs fx s₁ cs} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs MSort.Format → kFormat.has_sort fx MSort.Format → MRat.has_sort s₁ MSort.Int → kCodeSeq.has_sort cs MSort.CodeSeq → kBool.eqe (kBool.validBlock b fs fx s₁ cs) (kBool.and (kBool.and (kBool.and (kBool.validCode fs s₁) (kBool.validCodes fx cs)) (kBool.eqeq₀ (MRat.length₂ cs) b)) (if (1 : MRat) ≤ b then kBool.true else kBool.false))
    | eq_p31zero9_predicates_zerozero1 {f g c d} : kFormat.has_sort f MSort.Format → kFormat.has_sort g MSort.Format → MRat.has_sort c MSort.Int → MRat.has_sort d MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.validCode g d) kBool.true → kBool.eqe (kBool.CompareLess f g c d) (kBool.xLt (kXReal.decode f c) (kXReal.decode g d))
    | eq_p31zero9_predicates_zerozero2 {f g c d} : kFormat.has_sort f MSort.Format → kFormat.has_sort g MSort.Format → MRat.has_sort c MSort.Int → MRat.has_sort d MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.validCode g d) kBool.true → kBool.eqe (kBool.CompareLessEqual f g c d) (kBool.xLe (kXReal.decode f c) (kXReal.decode g d))
    | eq_p31zero9_predicates_zerozero3 {f g c d} : kFormat.has_sort f MSort.Format → kFormat.has_sort g MSort.Format → MRat.has_sort c MSort.Int → MRat.has_sort d MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.validCode g d) kBool.true → kBool.eqe (kBool.CompareEqual f g c d) (kBool.xEq (kXReal.decode f c) (kXReal.decode g d))
    | eq_p31zero9_predicates_zerozero4 {f g c d} : kFormat.has_sort f MSort.Format → kFormat.has_sort g MSort.Format → MRat.has_sort c MSort.Int → MRat.has_sort d MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.validCode g d) kBool.true → kBool.eqe (kBool.CompareGreaterEqual f g c d) (kBool.xLe (kXReal.decode g d) (kXReal.decode f c))
    | eq_p31zero9_predicates_zerozero5 {f g c d} : kFormat.has_sort f MSort.Format → kFormat.has_sort g MSort.Format → MRat.has_sort c MSort.Int → MRat.has_sort d MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.validCode g d) kBool.true → kBool.eqe (kBool.CompareGreater f g c d) (kBool.xLt (kXReal.decode g d) (kXReal.decode f c))
    | eq_p31zero9_predicates_zerozero6 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.IsZero f c) (kBool.xEq (kXReal.decode f c) (kXReal.fin (0 : MRat)))
    | eq_p31zero9_predicates_zerozero7 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.IsOne f c) (kBool.xEq (kXReal.decode f c) (kXReal.fin (1 : MRat)))
    | eq_p31zero9_predicates_zerozero8 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.IsNaN f c) (kBool.xNaN (kXReal.decode f c))
    | eq_p31zero9_predicates_zerozero9 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.IsInfinite f c) (kBool.xInfinite (kXReal.decode f c))
    | eq_p31zero9_predicates_zero1zero {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.IsFinite f c) (kBool.xFinite (kXReal.decode f c))
    | eq_p31zero9_predicates_zero11 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.IsSignMinus f c) (kBool.xMinus (kXReal.decode f c))
    | eq_p31zero9_predicates_zero12 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.or (kBool.or (kBool.IsNaN f c) (kBool.IsInfinite f c)) (kBool.IsZero f c)) kBool.true → kBool.eqe (kBool.IsNormal f c) kBool.false
    | eq_p31zero9_predicates_zero13 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.IsFinite f c) kBool.true → kBool.eqe (kBool.not (kBool.IsZero f c)) kBool.true → kBool.eqe (kBool.IsNormal f c) (kBool.xLe (kXReal.decode f (MRat.MinNormalOf f)) (kXReal.omegaAbs (kXReal.decode f c)))
    | eq_p31zero9_predicates_zero14 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.IsSubnormal f c) (kBool.and (kBool.and (kBool.not (kBool.IsZero f c)) (kBool.not (kBool.IsNormal f c))) (kBool.IsFinite f c))
    | eq_p31zero9_arity_table_nil {n a} : MRat.has_sort a MSort.Nat → kBool.eqe (kBool.inArityTable n a kArityTable.anil) kBool.false
    | eq_p31zero9_arity_table_cons {n a name b at₂} : MRat.has_sort a MSort.Nat → MRat.has_sort b MSort.Nat → kArityTable.has_sort at₂ MSort.ArityTable → kBool.eqe (kBool.inArityTable n a (kArityTable.acons (kArityEntry.entry name b) at₂)) (kBool.or (kBool.and (kBool.eqeq₀ a b) (kBool.eqeq₅ n name)) (kBool.inArityTable n a at₂))
    | eq_p31zero9_conformance_zerozero1 {f} : kFormat.has_sort f MSort.Format → kBool.eqe (kBool.inF4 f) (kBool.eqeq₆ f (kFormat.Binary (4 : MRat) (2 : MRat) kSignedness.Signed kDomain.Finite))
    | eq_p31zero9_conformance_zerozero2 {f} : kFormat.has_sort f MSort.Format → kBool.eqe (kBool.inF8 f) (kBool.or (kBool.eqeq₆ f (kFormat.Binary (8 : MRat) (3 : MRat) kSignedness.Signed kDomain.Extended)) (kBool.eqeq₆ f (kFormat.Binary (8 : MRat) (4 : MRat) kSignedness.Signed kDomain.Extended)))
    | eq_p31zero9_conformance_zerozero3 {f} : kFormat.has_sort f MSort.Format → kBool.eqe (kBool.inFs f) (kBool.eqeq₆ f (kFormat.Binary (8 : MRat) (1 : MRat) kSignedness.Unsigned kDomain.Finite))
    | eq_p31zero9_conformance_zerozero4 {f} : kFormat.has_sort f MSort.Format → kBool.eqe (kBool.allowedExternal f) (kBool.or (kBool.or (kBool.eqeq₆ f kFormat.binary16) (kBool.eqeq₆ f kFormat.BFloat16)) (kBool.eqeq₆ f kFormat.binary32))
    | eq_p31zero9_conformance_zerozero5 {f} : kFormat.has_sort f MSort.Format → kBool.eqe (kBool.containsFormat f kFormatSeq.fnil) kBool.false
    | eq_p31zero9_conformance_zerozero6 {f g fs} : kFormat.has_sort f MSort.Format → kFormat.has_sort g MSort.Format → kFormatSeq.has_sort fs MSort.FormatSeq → kBool.eqe (kBool.containsFormat f (kFormatSeq.fcons g fs)) (kBool.or (kBool.containsFormat f fs) (kBool.eqeq₆ f g))
    | eq_p31zero9_conformance_zerozero7 : kBool.eqe (kBool.validFX kFormatSeq.fnil) kBool.false
    | eq_p31zero9_conformance_zerozero8 {f fs} : kFormat.has_sort f MSort.Format → kFormatSeq.has_sort fs MSort.FormatSeq → kBool.eqe (kBool.validFX (kFormatSeq.fcons f fs)) (kBool.and (kBool.allowedExternal f) (kBool.and (kBool.not (kBool.containsFormat f fs)) (kBool.validFXTail fs)))
    | eq_p31zero9_conformance_zerozero9 : kBool.eqe (kBool.validFXTail kFormatSeq.fnil) kBool.true
    | eq_p31zero9_conformance_zero1zero {f fs} : kFormat.has_sort f MSort.Format → kFormatSeq.has_sort fs MSort.FormatSeq → kBool.eqe (kBool.validFXTail (kFormatSeq.fcons f fs)) (kBool.and (kBool.allowedExternal f) (kBool.and (kBool.not (kBool.containsFormat f fs)) (kBool.validFXTail fs)))
    | eq_p31zero9_conformance_zero11 : kBool.eqe (kBool.allFormats kFormatSeq.fnil) kBool.true
    | eq_p31zero9_conformance_zero12 {f fs} : kFormat.has_sort f MSort.Format → kFormatSeq.has_sort fs MSort.FormatSeq → kBool.eqe (kBool.allFormats (kFormatSeq.fcons f fs)) (kBool.and (kBool.validFormat f) (kBool.allFormats fs))
    | eq_p31zero9_conformance_zero13 {n fs ps fx} : kFormatSeq.has_sort fs MSort.FormatSeq → kProjSpec.has_sort ps MSort.ProjSpec → kFormatSeq.has_sort fx MSort.FormatSeq → kBool.eqe (kBool.required (kSpecialization.numeric n fs ps) fx) (kBool.and (kBool.validFX fx) (kBool.and (kBool.eqeq₇ ps (kProjSpec.proj kBlockRoundMode.NearestTiesToEven kSatMode.SatNone)) (kBool.requiredNumeric n fs fx)))
    | eq_p31zero9_conformance_zero14 {n fs fx} : kFormatSeq.has_sort fs MSort.FormatSeq → kFormatSeq.has_sort fx MSort.FormatSeq → kBool.eqe (kBool.required (kSpecialization.plain n fs) fx) (kBool.and (kBool.validFX fx) (kBool.requiredPlain n fs fx))
    | eq_p31zero9_conformance_zero15 {n f g fx} : kFormat.has_sort f MSort.Format → kFormat.has_sort g MSort.Format → kFormatSeq.has_sort fx MSort.FormatSeq → kBool.eqe (kBool.requiredNumeric n (kFormatSeq.fcons f (kFormatSeq.fcons g kFormatSeq.fnil)) fx) (kBool.or (kBool.and (kBool.and (kBool.or (kBool.inF4 f) (kBool.inF8 f)) (kBool.eqeq₆ f g)) (kBool.or (kBool.eqeq₅ n ("Abs" : MString)) (kBool.eqeq₅ n ("Negate" : MString)))) (kBool.and (kBool.and (kBool.or (kBool.inF4 f) (kBool.or (kBool.inF8 f) (kBool.containsFormat f fx))) (kBool.or (kBool.inF4 g) (kBool.or (kBool.inF8 g) (kBool.containsFormat g fx)))) (kBool.or (kBool.eqeq₅ n ("Convert" : MString)) (kBool.eqeq₅ n ("Recip" : MString)))))
    | eq_p31zero9_conformance_zero16 {n f g h fx} : kFormat.has_sort f MSort.Format → kFormat.has_sort g MSort.Format → kFormat.has_sort h MSort.Format → kFormatSeq.has_sort fx MSort.FormatSeq → kBool.eqe (kBool.requiredNumeric n (kFormatSeq.fcons f (kFormatSeq.fcons g (kFormatSeq.fcons h kFormatSeq.fnil))) fx) (kBool.or (kBool.and (kBool.minmaxName n) (kBool.and (kBool.and (kBool.or (kBool.inF4 f) (kBool.inF8 f)) (kBool.eqeq₆ g h)) (kBool.eqeq₆ f g))) (kBool.and (kBool.and (kBool.and (kBool.or (kBool.inF4 g) (kBool.inF8 g)) (kBool.or (kBool.inF8 h) (kBool.containsFormat h fx))) (kBool.or (kBool.inF4 f) (kBool.inF8 f))) (kBool.or (kBool.or (kBool.eqeq₅ n ("Multiply" : MString)) (kBool.eqeq₅ n ("Subtract" : MString))) (kBool.eqeq₅ n ("Add" : MString)))))
    | eq_p31zero9_conformance_zero17 {n f g h j fx} : kFormat.has_sort f MSort.Format → kFormat.has_sort g MSort.Format → kFormat.has_sort h MSort.Format → kFormat.has_sort j MSort.Format → kFormatSeq.has_sort fx MSort.FormatSeq → kBool.eqe (kBool.requiredNumeric n (kFormatSeq.fcons f (kFormatSeq.fcons g (kFormatSeq.fcons h (kFormatSeq.fcons j kFormatSeq.fnil)))) fx) (kBool.and (kBool.and (kBool.and (kBool.and (kBool.containsFormat h fx) (kBool.eqeq₆ h j)) (kBool.or (kBool.inF4 g) (kBool.inF8 g))) (kBool.or (kBool.inF4 f) (kBool.inF8 f))) (kBool.or (kBool.eqeq₅ n ("FAA" : MString)) (kBool.eqeq₅ n ("FMA" : MString))))
    | eq_p31zero9_conformance_zero18 {n f g h j l fx} : kFormat.has_sort f MSort.Format → kFormat.has_sort g MSort.Format → kFormat.has_sort h MSort.Format → kFormat.has_sort j MSort.Format → kFormat.has_sort l MSort.Format → kFormatSeq.has_sort fx MSort.FormatSeq → kBool.eqe (kBool.requiredNumeric n (kFormatSeq.fcons f (kFormatSeq.fcons g (kFormatSeq.fcons h (kFormatSeq.fcons j (kFormatSeq.fcons l kFormatSeq.fnil))))) fx) (kBool.and (kBool.and (kBool.inFs f) (kBool.and (kBool.and (kBool.and (kBool.or (kBool.inF4 j) (kBool.inF8 j)) (kBool.or (kBool.inF8 l) (kBool.containsFormat l fx))) (kBool.or (kBool.inF4 g) (kBool.inF8 g))) (kBool.eqeq₆ f h))) (kBool.or (kBool.or (kBool.eqeq₅ n ("ScaledMultiply" : MString)) (kBool.eqeq₅ n ("ScaledSubtract" : MString))) (kBool.eqeq₅ n ("ScaledAdd" : MString))))
    | eq_p31zero9_conformance_zero19 {n fs fx} : kFormatSeq.has_sort fs MSort.FormatSeq → kFormatSeq.has_sort fx MSort.FormatSeq → kBool.eqe (kBool.or (if (MRat.length₄ fs) < (2 : MRat) then kBool.true else kBool.false) (if (5 : MRat) < (MRat.length₄ fs) then kBool.true else kBool.false)) kBool.true → kBool.eqe (kBool.requiredNumeric n fs fx) kBool.false
    | eq_p31zero9_conformance_zero2zero {n f fx} : kFormat.has_sort f MSort.Format → kFormatSeq.has_sort fx MSort.FormatSeq → kBool.eqe (kBool.requiredPlain n (kFormatSeq.fcons f kFormatSeq.fnil) fx) (kBool.or (kBool.and (kBool.predicateName n) (kBool.or (kBool.inF4 f) (kBool.inF8 f))) (kBool.and (kBool.formatNameOp n) (kBool.or (kBool.inF4 f) (kBool.or (kBool.inF8 f) (kBool.containsFormat f fx)))))
    | eq_p31zero9_conformance_zero21 {n f g fx} : kFormat.has_sort f MSort.Format → kFormat.has_sort g MSort.Format → kFormatSeq.has_sort fx MSort.FormatSeq → kBool.eqe (kBool.requiredPlain n (kFormatSeq.fcons f (kFormatSeq.fcons g kFormatSeq.fnil)) fx) (kBool.and (kBool.compareName n) (kBool.and (kBool.or (kBool.inF4 f) (kBool.inF8 f)) (kBool.eqeq₆ f g)))
    | eq_p31zero9_conformance_zero22 {n fs fx} : kFormatSeq.has_sort fs MSort.FormatSeq → kFormatSeq.has_sort fx MSort.FormatSeq → kBool.eqe (kBool.or (if (MRat.length₄ fs) < (1 : MRat) then kBool.true else kBool.false) (if (2 : MRat) < (MRat.length₄ fs) then kBool.true else kBool.false)) kBool.true → kBool.eqe (kBool.requiredPlain n fs fx) kBool.false
    | eq_p31zero9_conformance_zero23 {n} : kBool.eqe (kBool.minmaxName n) (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.eqeq₅ n ("MaximumFinite" : MString)) (kBool.eqeq₅ n ("MinimumFinite" : MString))) (kBool.eqeq₅ n ("MaximumMagnitudeNumber" : MString))) (kBool.eqeq₅ n ("MinimumMagnitudeNumber" : MString))) (kBool.eqeq₅ n ("MaximumMagnitude" : MString))) (kBool.eqeq₅ n ("MinimumMagnitude" : MString))) (kBool.eqeq₅ n ("MaximumNumber" : MString))) (kBool.eqeq₅ n ("MinimumNumber" : MString))) (kBool.eqeq₅ n ("Maximum" : MString))) (kBool.eqeq₅ n ("Minimum" : MString)))
    | eq_p31zero9_conformance_zero24 {n} : kBool.eqe (kBool.compareName n) (kBool.or (kBool.or (kBool.or (kBool.or (kBool.eqeq₅ n ("CompareGreater" : MString)) (kBool.eqeq₅ n ("CompareGreaterEqual" : MString))) (kBool.eqeq₅ n ("CompareEqual" : MString))) (kBool.eqeq₅ n ("CompareLessEqual" : MString))) (kBool.eqeq₅ n ("CompareLess" : MString)))
    | eq_p31zero9_conformance_zero25 {n} : kBool.eqe (kBool.predicateName n) (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.eqeq₅ n ("NextGreaterThan" : MString)) (kBool.eqeq₅ n ("NextLessThan" : MString))) (kBool.eqeq₅ n ("IsSubnormal" : MString))) (kBool.eqeq₅ n ("IsNormal" : MString))) (kBool.eqeq₅ n ("IsSignMinus" : MString))) (kBool.eqeq₅ n ("IsFinite" : MString))) (kBool.eqeq₅ n ("IsInfinite" : MString))) (kBool.eqeq₅ n ("IsNaN" : MString))) (kBool.eqeq₅ n ("IsOne" : MString))) (kBool.eqeq₅ n ("IsZero" : MString)))
    | eq_p31zero9_conformance_zero26 {n} : kBool.eqe (kBool.formatNameOp n) (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.eqeq₅ n ("MaxSubnormalOf" : MString)) (kBool.eqeq₅ n ("MinNormalOf" : MString))) (kBool.eqeq₅ n ("MinPositiveOf" : MString))) (kBool.eqeq₅ n ("MinFiniteOf" : MString))) (kBool.eqeq₅ n ("MaxFiniteOf" : MString))) (kBool.eqeq₅ n ("ExponentBiasOf" : MString))) (kBool.eqeq₅ n ("TrailingSignificandBitwidthOf" : MString))) (kBool.eqeq₅ n ("ExponentBitwidthOf" : MString))) (kBool.eqeq₅ n ("DomainOf" : MString))) (kBool.eqeq₅ n ("SignednessOf" : MString))) (kBool.eqeq₅ n ("PrecisionOf" : MString))) (kBool.eqeq₅ n ("BitwidthOf" : MString)))
    | eq_p31zero9_conformance_zero33 : kBool.eqe (kBool.evidenceComplete kEvidence.pendingEvidence) kBool.false
    | eq_p31zero9_conformance_zero34 : kBool.eqe (kBool.evidenceComplete kEvidence.sampleEvidence) kBool.false
    | eq_p31zero9_conformance_zero35 : kBool.eqe (kBool.evidenceComplete kEvidence.exhaustiveEvidence) kBool.true
    | eq_p31zero9_conformance_zero36 : kBool.eqe (kBool.evidenceComplete kEvidence.proofEvidence) kBool.true
    | eq_p31zero9_conformance_zero54 {c} : MRat.has_sort c MSort.Int → kBool.eqe (kBool.memberCode c kCodeSeq.cnil) kBool.false
    | eq_p31zero9_conformance_zero55 {c d cs} : MRat.has_sort c MSort.Int → MRat.has_sort d MSort.Int → kCodeSeq.has_sort cs MSort.CodeSeq → kBool.eqe (kBool.memberCode c (kCodeSeq.ccons d cs)) (kBool.or (kBool.memberCode c cs) (kBool.eqeq₀ c d))
    | eq_p31zero9_conformance_zero56 {cs} : kCodeSeq.has_sort cs MSort.CodeSeq → kBool.eqe (kBool.disjointCodes kCodeSeq.cnil cs) kBool.true
    | eq_p31zero9_conformance_zero57 {c cs ds} : MRat.has_sort c MSort.Int → kCodeSeq.has_sort cs MSort.CodeSeq → kCodeSeq.has_sort ds MSort.CodeSeq → kBool.eqe (kBool.disjointCodes (kCodeSeq.ccons c cs) ds) (kBool.and (kBool.not (kBool.memberCode c ds)) (kBool.disjointCodes cs ds))
    | eq_p31zero9_conformance_zero58 : kBool.eqe (kBool.uniqueCodes kCodeSeq.cnil) kBool.true
    | eq_p31zero9_conformance_zero59 {c cs} : MRat.has_sort c MSort.Int → kCodeSeq.has_sort cs MSort.CodeSeq → kBool.eqe (kBool.uniqueCodes (kCodeSeq.ccons c cs)) (kBool.and (kBool.not (kBool.memberCode c cs)) (kBool.uniqueCodes cs))
    | eq_p31zero9_conformance_zero62 {cs} : kCodeSeq.has_sort cs MSort.CodeSeq → kBool.eqe (kBool.subsetCodes kCodeSeq.cnil cs) kBool.true
    | eq_p31zero9_conformance_zero63 {c cs ds} : MRat.has_sort c MSort.Int → kCodeSeq.has_sort cs MSort.CodeSeq → kCodeSeq.has_sort ds MSort.CodeSeq → kBool.eqe (kBool.subsetCodes (kCodeSeq.ccons c cs) ds) (kBool.and (kBool.memberCode c ds) (kBool.subsetCodes cs ds))
    | eq_p31zero9_conformance_zero64 {cs ds es} : kCodeSeq.has_sort cs MSort.CodeSeq → kCodeSeq.has_sort ds MSort.CodeSeq → kCodeSeq.has_sort es MSort.CodeSeq → kBool.eqe (kBool.partition2 cs ds es) (kBool.and (kBool.uniqueCodes cs) (kBool.and (kBool.uniqueCodes ds) (kBool.and (kBool.uniqueCodes es) (kBool.and (kBool.and (kBool.subsetCodes cs (kCodeSeq.appendCodes ds es)) (kBool.subsetCodes (kCodeSeq.appendCodes ds es) cs)) (kBool.disjointCodes ds es)))))
    | eq_p31zero9_decl_numeric {n a} : MRat.has_sort a MSort.Nat → kBool.eqe (kBool.numericArity n a) (kBool.inArityTable n a kArityTable.numericArityTable)
    | eq_p31zero9_decl_plain {n a} : MRat.has_sort a MSort.Nat → kBool.eqe (kBool.plainArity n a) (kBool.inArityTable n a kArityTable.plainArityTable)
    | eq_p31zero9_decl_specialization_numeric {n fs ps} : kFormatSeq.has_sort fs MSort.FormatSeq → kProjSpec.has_sort ps MSort.ProjSpec → kBool.eqe (kBool.validSpecialization (kSpecialization.numeric n fs ps)) (kBool.and (kBool.and (kBool.validProjection ps) (kBool.allFormats fs)) (kBool.numericArity n (MRat.length₄ fs)))
    | eq_p31zero9_decl_specialization_plain {n fs} : kFormatSeq.has_sort fs MSort.FormatSeq → kBool.eqe (kBool.validSpecialization (kSpecialization.plain n fs)) (kBool.and (kBool.allFormats fs) (kBool.plainArity n (MRat.length₄ fs)))
    | eq_p31zero9_decl_numeric_plain {n} : kBool.eqe (kBool.numericPlainName n) (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.or (kBool.eqeq₅ n ("MaxSubnormalOf" : MString)) (kBool.eqeq₅ n ("MinNormalOf" : MString))) (kBool.eqeq₅ n ("MinPositiveOf" : MString))) (kBool.eqeq₅ n ("MinFiniteOf" : MString))) (kBool.eqeq₅ n ("MaxFiniteOf" : MString))) (kBool.eqeq₅ n ("NextLessThan" : MString))) (kBool.eqeq₅ n ("NextGreaterThan" : MString)))
    | eq_p31zero9_decl_exact {s₁ name e} : kSpecialization.has_sort s₁ MSort.Specialization → kEvidence.has_sort e MSort.Evidence → kBool.eqe (kBool.wellFormedDeclaration (kDeclaration.exact s₁ name e)) (kBool.and (kBool.validSpecialization s₁) (kBool.eqslasheq₂ name ("" : MString)))
    | eq_p31zero9_decl_approximate {s₁ name k e} : kSpecialization.has_sort s₁ MSort.Specialization → kKappa.has_sort k MSort.Kappa → kEvidence.has_sort e MSort.Evidence → kBool.eqe (kBool.wellFormedDeclaration (kDeclaration.approximate s₁ name k e)) (kBool.and (kBool.and (kBool.and (kBool.numericResult s₁) (kBool.validSpecialization s₁)) (kBool.eqslasheq₂ name (MString.specializationName s₁))) (kBool.eqslasheq₂ name ("" : MString)))
    | eq_p31zero9_block_elements_valid {n a fs bp} : MRat.has_sort a MSort.Nat → kFormatSeq.has_sort fs MSort.FormatSeq → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → kBool.eqe (kBool.validSpecialization (kSpecialization.blockElements n a fs bp)) (kBool.and (kBool.and (kBool.allFormats fs) (kBool.and (kBool.validBlockProjection bp a) (kBool.blockElementArity n (MRat.length₄ fs)))) (if (1 : MRat) ≤ a then kBool.true else kBool.false))
    | eq_p31zero9_block_reduction_valid {n a fs ps} : MRat.has_sort a MSort.Nat → kFormatSeq.has_sort fs MSort.FormatSeq → kProjSpec.has_sort ps MSort.ProjSpec → kBool.eqe (kBool.validSpecialization (kSpecialization.blockReduction n a fs ps)) (kBool.and (kBool.and (kBool.allFormats fs) (kBool.and (kBool.validProjection ps) (kBool.or (kBool.and (kBool.or (kBool.eqeq₅ n ("BlockReduceAdd" : MString)) (kBool.eqeq₅ n ("BlockReduceMultiply" : MString))) (kBool.eqeq₀ (MRat.length₄ fs) (3 : MRat))) (kBool.and (kBool.eqeq₀ (MRat.length₄ fs) (5 : MRat)) (kBool.eqeq₅ n ("BlockDotProduct" : MString)))))) (if (1 : MRat) ≤ a then kBool.true else kBool.false))
    | eq_p31zero9_block_scale_valid {n a fs ps bp} : MRat.has_sort a MSort.Nat → kFormatSeq.has_sort fs MSort.FormatSeq → kProjSpec.has_sort ps MSort.ProjSpec → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → kBool.eqe (kBool.validSpecialization (kSpecialization.blockScale n a fs ps bp)) (kBool.and (kBool.and (kBool.and (kBool.and (kBool.allFormats fs) (kBool.and (kBool.validProjection ps) (kBool.validBlockProjection bp a))) (kBool.eqeq₀ (MRat.length₄ fs) (3 : MRat))) (if (1 : MRat) ≤ a then kBool.true else kBool.false)) (kBool.eqeq₅ n ("ConvertToBlockMaxAbsFinite" : MString)))
    | eq_p31zero9_block_elements_not_required {n a fs bp fx} : MRat.has_sort a MSort.Nat → kFormatSeq.has_sort fs MSort.FormatSeq → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → kFormatSeq.has_sort fx MSort.FormatSeq → kBool.eqe (kBool.required (kSpecialization.blockElements n a fs bp) fx) kBool.false
    | eq_p31zero9_block_reduction_not_required {n a fs ps fx} : MRat.has_sort a MSort.Nat → kFormatSeq.has_sort fs MSort.FormatSeq → kProjSpec.has_sort ps MSort.ProjSpec → kFormatSeq.has_sort fx MSort.FormatSeq → kBool.eqe (kBool.required (kSpecialization.blockReduction n a fs ps) fx) kBool.false
    | eq_p31zero9_block_scale_not_required {n a fs ps bp fx} : MRat.has_sort a MSort.Nat → kFormatSeq.has_sort fs MSort.FormatSeq → kProjSpec.has_sort ps MSort.ProjSpec → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → kFormatSeq.has_sort fx MSort.FormatSeq → kBool.eqe (kBool.required (kSpecialization.blockScale n a fs ps bp) fx) kBool.false
    | eq_p31zero9_result_projected_numeric {n fs ps} : kFormatSeq.has_sort fs MSort.FormatSeq → kProjSpec.has_sort ps MSort.ProjSpec → kBool.eqe (kBool.numericResult (kSpecialization.numeric n fs ps)) kBool.true
    | eq_p31zero9_result_plain_numeric {n fs} : kFormatSeq.has_sort fs MSort.FormatSeq → kBool.eqe (kBool.numericResult (kSpecialization.plain n fs)) (kBool.numericPlainName n)
    | eq_p31zero9_result_block_elements_numeric {n a fs bp} : MRat.has_sort a MSort.Nat → kFormatSeq.has_sort fs MSort.FormatSeq → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → kBool.eqe (kBool.numericResult (kSpecialization.blockElements n a fs bp)) kBool.true
    | eq_p31zero9_result_block_reduction_numeric {n a fs ps} : MRat.has_sort a MSort.Nat → kFormatSeq.has_sort fs MSort.FormatSeq → kProjSpec.has_sort ps MSort.ProjSpec → kBool.eqe (kBool.numericResult (kSpecialization.blockReduction n a fs ps)) kBool.true
    | eq_p31zero9_result_block_scale_numeric {n a fs ps bp} : MRat.has_sort a MSort.Nat → kFormatSeq.has_sort fs MSort.FormatSeq → kProjSpec.has_sort ps MSort.ProjSpec → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → kBool.eqe (kBool.numericResult (kSpecialization.blockScale n a fs ps bp)) kBool.true
    | eq_p31zero9_declared_empty {s₁} : kSpecialization.has_sort s₁ MSort.Specialization → kBool.eqe (kBool.hasDeclaration s₁ kDeclarationSeq.dnil) kBool.false
    | eq_p31zero9_declared_member {s₁ dec decs} : kSpecialization.has_sort s₁ MSort.Specialization → kDeclaration.has_sort dec MSort.Declaration → kDeclarationSeq.has_sort decs MSort.DeclarationSeq → kBool.eqe (kBool.hasDeclaration s₁ (kDeclarationSeq.dcons dec decs)) (kBool.or (kBool.and (kBool.wellFormedDeclaration dec) (kBool.eqeq₈ (kSpecialization.declaredIdentity dec) s₁)) (kBool.hasDeclaration s₁ decs))
    | eq_p31zero9_declarations_cover_empty {decs} : kDeclarationSeq.has_sort decs MSort.DeclarationSeq → kBool.eqe (kBool.declarationsCover kSpecializationSeq.snil decs) kBool.true
    | eq_p31zero9_declarations_cover_cons {s₁ specs decs} : kSpecialization.has_sort s₁ MSort.Specialization → kSpecializationSeq.has_sort specs MSort.SpecializationSeq → kDeclarationSeq.has_sort decs MSort.DeclarationSeq → kBool.eqe (kBool.declarationsCover (kSpecializationSeq.scons s₁ specs) decs) (kBool.and (kBool.hasDeclaration s₁ decs) (kBool.declarationsCover specs decs))
    | eq_p31zero9_partition_disjoint_empty : kBool.eqe (kBool.partitionDisjoint kPartitionSeq.pnil) kBool.true
    | eq_p31zero9_partition_disjoint_cons {cs parts} : kCodeSeq.has_sort cs MSort.CodeSeq → kPartitionSeq.has_sort parts MSort.PartitionSeq → kBool.eqe (kBool.partitionDisjoint (kPartitionSeq.pcons cs parts)) (kBool.and (kBool.uniqueCodes cs) (kBool.and (kBool.partitionDisjoint parts) (kBool.disjointCodes cs (kCodeSeq.partitionUnion parts))))
    | eq_p31zero9_partition_general {cs parts} : kCodeSeq.has_sort cs MSort.CodeSeq → kPartitionSeq.has_sort parts MSort.PartitionSeq → kBool.eqe (kBool.partition cs parts) (kBool.and (kBool.uniqueCodes cs) (kBool.and (kBool.partitionDisjoint parts) (kBool.and (kBool.subsetCodes cs (kCodeSeq.partitionUnion parts)) (kBool.subsetCodes (kCodeSeq.partitionUnion parts) cs))))
    | eq_p31zero9_block_element_arity {n a} : MRat.has_sort a MSort.Nat → kBool.eqe (kBool.blockElementArity n a) (kBool.inArityTable n a kArityTable.blockElementArityTable)
    | eq_p31zero9_decl_partitioned_valid {s₁ name cs kp e} : kSpecialization.has_sort s₁ MSort.Specialization → kCodeSeq.has_sort cs MSort.CodeSeq → kKappaPartSeq.has_sort kp MSort.KappaPartSeq → kEvidence.has_sort e MSort.Evidence → kBool.eqe (kBool.wellFormedDeclaration (kDeclaration.partitioned s₁ name cs kp e)) (kBool.and (kBool.and (kBool.and (kBool.numericResult s₁) (kBool.and (kBool.validSpecialization s₁) (kBool.partition cs (kPartitionSeq.partRegions kp)))) (kBool.eqslasheq₂ name (MString.specializationName s₁))) (kBool.eqslasheq₂ name ("" : MString)))
    | eq_p31zero9_order_next_zerozero1 {f g c d} : kFormat.has_sort f MSort.Format → kFormat.has_sort g MSort.Format → MRat.has_sort c MSort.Int → MRat.has_sort d MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.validCode g d) kBool.true → kBool.eqe (kBool.internalFormat f) kBool.true → kBool.eqe (kBool.internalFormat g) kBool.true → kBool.eqe (kBool.IsNaN f c) kBool.true → kBool.eqe (kBool.TotalOrder f g c d) kBool.true
    | eq_p31zero9_order_next_zerozero2 {f g c d} : kFormat.has_sort f MSort.Format → kFormat.has_sort g MSort.Format → MRat.has_sort c MSort.Int → MRat.has_sort d MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.validCode g d) kBool.true → kBool.eqe (kBool.internalFormat f) kBool.true → kBool.eqe (kBool.internalFormat g) kBool.true → kBool.eqe (kBool.not (kBool.IsNaN f c)) kBool.true → kBool.eqe (kBool.IsNaN g d) kBool.true → kBool.eqe (kBool.TotalOrder f g c d) kBool.false
    | eq_p31zero9_order_next_zerozero3 {f g c d} : kFormat.has_sort f MSort.Format → kFormat.has_sort g MSort.Format → MRat.has_sort c MSort.Int → MRat.has_sort d MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.validCode g d) kBool.true → kBool.eqe (kBool.internalFormat f) kBool.true → kBool.eqe (kBool.internalFormat g) kBool.true → kBool.eqe (kBool.not (kBool.IsNaN f c)) kBool.true → kBool.eqe (kBool.not (kBool.IsNaN g d)) kBool.true → kBool.eqe (kBool.TotalOrder f g c d) (kBool.CompareLessEqual f g c d)
    | eq_p31zero9_real_expressions_zero31 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xEq u u) kBool.true
    | eq_p31zero9_real_expressions_zero32 {r s₁} : kBool.eqe (kBool.xEq (kXReal.piMultiple r) (kXReal.piMultiple s₁)) (kBool.eqeq₀ r s₁)
    | eq_p31zero9_real_expressions_zero33 {r} : kBool.eqe (kBool.xEq (kXReal.piMultiple r) (kXReal.fin (0 : MRat))) (kBool.eqeq₀ r (0 : MRat))
    | eq_p31zero9_real_expressions_zero34 {r} : kBool.eqe (kBool.xEq (kXReal.fin (0 : MRat)) (kXReal.piMultiple r)) (kBool.eqeq₀ r (0 : MRat))
    | eq_p31zero9_real_expressions_zero35 {r s₁} : kBool.eqe (kBool.xLt (kXReal.piMultiple r) (kXReal.piMultiple s₁)) (if r < s₁ then kBool.true else kBool.false)
    | eq_p31zero9_real_expressions_zero36 {r} : kBool.eqe (kBool.xLt (kXReal.piMultiple r) (kXReal.fin (0 : MRat))) (if r < (0 : MRat) then kBool.true else kBool.false)
    | eq_p31zero9_real_expressions_zero37 {r} : kBool.eqe (kBool.xLt (kXReal.fin (0 : MRat)) (kXReal.piMultiple r)) (if (0 : MRat) < r then kBool.true else kBool.false)
    | eq_p31zero9_real_expressions_zero38 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xMinus u) (kBool.xLt u (kXReal.fin (0 : MRat)))
    | eq_p31zero9_omega_elementary_128 {r} : kBool.eqe (kBool.eqslasheq₀ r (0 : MRat)) kBool.true → kBool.eqe (kBool.xEq (kXReal.exprCos (kXReal.fin r)) (kXReal.fin (0 : MRat))) kBool.false
    | eq_p31zero9_omega_elementary_129 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt (kXReal.fin (0 : MRat)) (kXReal.exprExp u)) kBool.true
    | eq_p31zero9_omega_elementary_13zero {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xEq (kXReal.exprExp u) (kXReal.fin (0 : MRat))) kBool.false
    | eq_p31zero9_omega_elementary_131 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt (kXReal.exprExp u) (kXReal.fin (0 : MRat))) kBool.false
    | eq_p31zero9_omega_elementary_132 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt (kXReal.fin (0 : MRat)) (kXReal.exprExp2 u)) kBool.true
    | eq_p31zero9_omega_elementary_133 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xEq (kXReal.exprExp2 u) (kXReal.fin (0 : MRat))) kBool.false
    | eq_p31zero9_omega_elementary_134 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt (kXReal.exprExp2 u) (kXReal.fin (0 : MRat))) kBool.false
    | eq_p31zero9_omega_elementary_135 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt (kXReal.fin (0 : MRat)) u) kBool.true → kBool.eqe (kBool.xLt (kXReal.fin (0 : MRat)) (kXReal.exprSqrt u)) kBool.true
    | eq_p31zero9_omega_elementary_136 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt (kXReal.fin (0 : MRat)) u) kBool.true → kBool.eqe (kBool.xEq (kXReal.exprSqrt u) (kXReal.fin (0 : MRat))) kBool.false
    | eq_p31zero9_omega_elementary_137 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLe (kXReal.fin (0 : MRat)) u) kBool.true → kBool.eqe (kBool.xLt (kXReal.exprSqrt u) (kXReal.fin (0 : MRat))) kBool.false
    | eq_eqeq₀ {l r} : l = r → kBool.eqe (kBool.eqeq₀ l r) kBool.true
    | eq_itet {l r} : kBool.eqe (kBool.ifthenelsefi kBool.true l r) l
    | eq_itef {l r} : kBool.eqe (kBool.ifthenelsefi kBool.false l r) r
    | eq_eqeq₁ {l r} : kSignedness.eqe l r → kBool.eqe (kBool.eqeq₁ l r) kBool.true
    | eq_eqeq₂ {l r} : kDomain.eqe l r → kBool.eqe (kBool.eqeq₂ l r) kBool.true
    | eq_eqslasheq₀ {l r} : l = r → kBool.eqe (kBool.eqslasheq₀ l r) kBool.false
    | eq_eqeq₃ {l r} : kBlockRoundMode.eqe l r → kBool.eqe (kBool.eqeq₃ l r) kBool.true
    | eq_eqeq₄ {l r} : kBool.eqe l r → kBool.eqe (kBool.eqeq₄ l r) kBool.true
    | eq_eqeq₅ {l r} : l = r → kBool.eqe (kBool.eqeq₅ l r) kBool.true
    | eq_eqeq₆ {l r} : kFormat.eqe l r → kBool.eqe (kBool.eqeq₆ l r) kBool.true
    | eq_eqeq₇ {l r} : kProjSpec.eqe l r → kBool.eqe (kBool.eqeq₇ l r) kBool.true
    | eq_eqslasheq₁ {l r} : kBool.eqe l r → kBool.eqe (kBool.eqslasheq₁ l r) kBool.false
    | eq_eqslasheq₂ {l r} : l = r → kBool.eqe (kBool.eqslasheq₂ l r) kBool.false
    | eq_eqeq₈ {l r} : kSpecialization.eqe l r → kBool.eqe (kBool.eqeq₈ l r) kBool.true

  inductive kXReal.eqe: kXReal → kXReal → Prop
    | from_eqa {a b} : kXReal.eqa a b → kXReal.eqe a b
    | symm {a b} : kXReal.eqe a b → kXReal.eqe b a
    | trans {a b c} : kXReal.eqe a b → kXReal.eqe b c → kXReal.eqe a c
    -- Congruence axioms for each operator
    | eqe_fin {a b : MRat} : a = b → kXReal.eqe (kXReal.fin a) (kXReal.fin b)
    | eqe_externalDecode {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqe a₀ b₀ → a₁ = b₁ → kXReal.eqe (kXReal.externalDecode a₀ a₁) (kXReal.externalDecode b₀ b₁)
    | eqe_decode {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqe a₀ b₀ → a₁ = b₁ → kXReal.eqe (kXReal.decode a₀ a₁) (kXReal.decode b₀ b₁)
    | eqe_roundToPrecision {a₀ b₀ a₁ b₁ : MRat} {a₂ b₂ : kBlockRoundMode} {a₃ b₃ : kXReal} : a₀ = b₀ → a₁ = b₁ → kBlockRoundMode.eqe a₂ b₂ → kXReal.eqe a₃ b₃ → kXReal.eqe (kXReal.roundToPrecision a₀ a₁ a₂ a₃) (kXReal.roundToPrecision b₀ b₁ b₂ b₃)
    | eqe_saturate {a₀ b₀ a₁ b₁ : MRat} {a₂ b₂ : kSatMode} {a₃ b₃ : kBlockRoundMode} {a₄ b₄ : kXReal} {a₅ b₅ : kSignedness} {a₆ b₆ : kDomain} : a₀ = b₀ → a₁ = b₁ → kSatMode.eqe a₂ b₂ → kBlockRoundMode.eqe a₃ b₃ → kXReal.eqe a₄ b₄ → kSignedness.eqe a₅ b₅ → kDomain.eqe a₆ b₆ → kXReal.eqe (kXReal.saturate a₀ a₁ a₂ a₃ a₄ a₅ a₆) (kXReal.saturate b₀ b₁ b₂ b₃ b₄ b₅ b₆)
    | eqe_overflow {a₀ b₀ : kSignedness} {a₁ b₁ : kDomain} {a₂ b₂ : kBool} : kSignedness.eqe a₀ b₀ → kDomain.eqe a₁ b₁ → kBool.eqe a₂ b₂ → kXReal.eqe (kXReal.overflow a₀ a₁ a₂) (kXReal.overflow b₀ b₁ b₂)
    | eqe_omegaConvert {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaConvert a) (kXReal.omegaConvert b)
    | eqe_omegaAbs {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaAbs a) (kXReal.omegaAbs b)
    | eqe_omegaNegate {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaNegate a) (kXReal.omegaNegate b)
    | eqe_omegaRecip {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaRecip a) (kXReal.omegaRecip b)
    | eqe_omegaCopySign {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.omegaCopySign a₀ a₁) (kXReal.omegaCopySign b₀ b₁)
    | eqe_omegaAdd {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.omegaAdd a₀ a₁) (kXReal.omegaAdd b₀ b₁)
    | eqe_omegaSubtract {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.omegaSubtract a₀ a₁) (kXReal.omegaSubtract b₀ b₁)
    | eqe_omegaMultiply {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.omegaMultiply a₀ a₁) (kXReal.omegaMultiply b₀ b₁)
    | eqe_omegaDivide {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.omegaDivide a₀ a₁) (kXReal.omegaDivide b₀ b₁)
    | eqe_omegaFMA {a₀ b₀ a₁ b₁ a₂ b₂ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe a₂ b₂ → kXReal.eqe (kXReal.omegaFMA a₀ a₁ a₂) (kXReal.omegaFMA b₀ b₁ b₂)
    | eqe_omegaFAA {a₀ b₀ a₁ b₁ a₂ b₂ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe a₂ b₂ → kXReal.eqe (kXReal.omegaFAA a₀ a₁ a₂) (kXReal.omegaFAA b₀ b₁ b₂)
    | eqe_at {a₀ b₀ : kXSeq} {a₁ b₁ : MRat} : kXSeq.eqe a₀ b₀ → a₁ = b₁ → kXReal.eqe (kXReal.«at» a₀ a₁) (kXReal.«at» b₀ b₁)
    | eqe_normalizeElement {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.normalizeElement a₀ a₁) (kXReal.normalizeElement b₀ b₁)
    | eqe_omegaMinimum {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.omegaMinimum a₀ a₁) (kXReal.omegaMinimum b₀ b₁)
    | eqe_omegaMaximum {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.omegaMaximum a₀ a₁) (kXReal.omegaMaximum b₀ b₁)
    | eqe_omegaMinimumNumber {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.omegaMinimumNumber a₀ a₁) (kXReal.omegaMinimumNumber b₀ b₁)
    | eqe_omegaMaximumNumber {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.omegaMaximumNumber a₀ a₁) (kXReal.omegaMaximumNumber b₀ b₁)
    | eqe_omegaMinimumMagnitude {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.omegaMinimumMagnitude a₀ a₁) (kXReal.omegaMinimumMagnitude b₀ b₁)
    | eqe_omegaMaximumMagnitude {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.omegaMaximumMagnitude a₀ a₁) (kXReal.omegaMaximumMagnitude b₀ b₁)
    | eqe_omegaMinimumMagnitudeNumber {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.omegaMinimumMagnitudeNumber a₀ a₁) (kXReal.omegaMinimumMagnitudeNumber b₀ b₁)
    | eqe_omegaMaximumMagnitudeNumber {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.omegaMaximumMagnitudeNumber a₀ a₁) (kXReal.omegaMaximumMagnitudeNumber b₀ b₁)
    | eqe_omegaMinimumFinite {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.omegaMinimumFinite a₀ a₁) (kXReal.omegaMinimumFinite b₀ b₁)
    | eqe_omegaMaximumFinite {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.omegaMaximumFinite a₀ a₁) (kXReal.omegaMaximumFinite b₀ b₁)
    | eqe_omegaClamp {a₀ b₀ a₁ b₁ a₂ b₂ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe a₂ b₂ → kXReal.eqe (kXReal.omegaClamp a₀ a₁ a₂) (kXReal.omegaClamp b₀ b₁ b₂)
    | eqe_foldAdd {a₀ b₀ : kXReal} {a₁ b₁ : kXSeq} : kXReal.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXReal.eqe (kXReal.foldAdd a₀ a₁) (kXReal.foldAdd b₀ b₁)
    | eqe_foldMultiply {a₀ b₀ : kXReal} {a₁ b₁ : kXSeq} : kXReal.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXReal.eqe (kXReal.foldMultiply a₀ a₁) (kXReal.foldMultiply b₀ b₁)
    | eqe_foldMaximumFinite {a₀ b₀ : kXReal} {a₁ b₁ : kXSeq} : kXReal.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXReal.eqe (kXReal.foldMaximumFinite a₀ a₁) (kXReal.foldMaximumFinite b₀ b₁)
    | eqe_realAdd {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.realAdd a₀ a₁) (kXReal.realAdd b₀ b₁)
    | eqe_realMultiply {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.realMultiply a₀ a₁) (kXReal.realMultiply b₀ b₁)
    | eqe_realNegate {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.realNegate a) (kXReal.realNegate b)
    | eqe_realAbs {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.realAbs a) (kXReal.realAbs b)
    | eqe_realDivide {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.realDivide a₀ a₁) (kXReal.realDivide b₀ b₁)
    | eqe_piMultiple {a b : MRat} : a = b → kXReal.eqe (kXReal.piMultiple a) (kXReal.piMultiple b)
    | eqe_omegaHypot {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.omegaHypot a₀ a₁) (kXReal.omegaHypot b₀ b₁)
    | eqe_omegaArcTan2 {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.omegaArcTan2 a₀ a₁) (kXReal.omegaArcTan2 b₀ b₁)
    | eqe_omegaArcTan2Pi {a₀ b₀ a₁ b₁ : kXReal} : kXReal.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe (kXReal.omegaArcTan2Pi a₀ a₁) (kXReal.omegaArcTan2Pi b₀ b₁)
    | eqe_omegaSqrt {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaSqrt a) (kXReal.omegaSqrt b)
    | eqe_omegaRSqrt {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaRSqrt a) (kXReal.omegaRSqrt b)
    | eqe_omegaExp {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaExp a) (kXReal.omegaExp b)
    | eqe_omegaExp2 {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaExp2 a) (kXReal.omegaExp2 b)
    | eqe_omegaLog {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaLog a) (kXReal.omegaLog b)
    | eqe_omegaLog2 {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaLog2 a) (kXReal.omegaLog2 b)
    | eqe_omegaLogOnePlus {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaLogOnePlus a) (kXReal.omegaLogOnePlus b)
    | eqe_omegaExpMinusOne {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaExpMinusOne a) (kXReal.omegaExpMinusOne b)
    | eqe_omegaSin {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaSin a) (kXReal.omegaSin b)
    | eqe_omegaCos {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaCos a) (kXReal.omegaCos b)
    | eqe_omegaTan {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaTan a) (kXReal.omegaTan b)
    | eqe_omegaArcSin {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaArcSin a) (kXReal.omegaArcSin b)
    | eqe_omegaArcCos {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaArcCos a) (kXReal.omegaArcCos b)
    | eqe_omegaArcTan {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaArcTan a) (kXReal.omegaArcTan b)
    | eqe_omegaSinh {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaSinh a) (kXReal.omegaSinh b)
    | eqe_omegaCosh {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaCosh a) (kXReal.omegaCosh b)
    | eqe_omegaTanh {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaTanh a) (kXReal.omegaTanh b)
    | eqe_omegaArcSinh {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaArcSinh a) (kXReal.omegaArcSinh b)
    | eqe_omegaArcCosh {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaArcCosh a) (kXReal.omegaArcCosh b)
    | eqe_omegaArcTanh {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaArcTanh a) (kXReal.omegaArcTanh b)
    | eqe_omegaSinPi {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaSinPi a) (kXReal.omegaSinPi b)
    | eqe_omegaCosPi {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaCosPi a) (kXReal.omegaCosPi b)
    | eqe_omegaTanPi {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaTanPi a) (kXReal.omegaTanPi b)
    | eqe_omegaArcSinPi {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaArcSinPi a) (kXReal.omegaArcSinPi b)
    | eqe_omegaArcCosPi {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaArcCosPi a) (kXReal.omegaArcCosPi b)
    | eqe_omegaArcTanPi {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaArcTanPi a) (kXReal.omegaArcTanPi b)
    | eqe_omegaSoftplus {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.omegaSoftplus a) (kXReal.omegaSoftplus b)
    | eqe_exprSqrt {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.exprSqrt a) (kXReal.exprSqrt b)
    | eqe_exprExp {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.exprExp a) (kXReal.exprExp b)
    | eqe_exprExp2 {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.exprExp2 a) (kXReal.exprExp2 b)
    | eqe_exprLog {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.exprLog a) (kXReal.exprLog b)
    | eqe_exprLog2 {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.exprLog2 a) (kXReal.exprLog2 b)
    | eqe_exprSin {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.exprSin a) (kXReal.exprSin b)
    | eqe_exprCos {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.exprCos a) (kXReal.exprCos b)
    | eqe_exprTan {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.exprTan a) (kXReal.exprTan b)
    | eqe_exprArcSin {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.exprArcSin a) (kXReal.exprArcSin b)
    | eqe_exprArcCos {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.exprArcCos a) (kXReal.exprArcCos b)
    | eqe_exprArcTan {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.exprArcTan a) (kXReal.exprArcTan b)
    | eqe_exprSinh {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.exprSinh a) (kXReal.exprSinh b)
    | eqe_exprCosh {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.exprCosh a) (kXReal.exprCosh b)
    | eqe_exprTanh {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.exprTanh a) (kXReal.exprTanh b)
    | eqe_exprArcSinh {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.exprArcSinh a) (kXReal.exprArcSinh b)
    | eqe_exprArcCosh {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.exprArcCosh a) (kXReal.exprArcCosh b)
    | eqe_exprArcTanh {a b : kXReal} : kXReal.eqe a b → kXReal.eqe (kXReal.exprArcTanh a) (kXReal.exprArcTanh b)
    | eqe_ifthenelsefi {a₀ b₀ : kBool} {a₁ b₁ a₂ b₂ : kXReal} : kBool.eqe a₀ b₀ → kXReal.eqe a₁ b₁ → kXReal.eqe a₂ b₂ → kXReal.eqe (kXReal.ifthenelsefi a₀ a₁ a₂) (kXReal.ifthenelsefi b₀ b₁ b₂)
    -- Equations
    | eq_p31zero9_codec_zerozero4 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.not (kBool.internalFormat f)) kBool.true → kXReal.eqe (kXReal.decode f c) (kXReal.externalDecode f c)
    | eq_p31zero9_codec_zerozero5 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.internalFormat f) kBool.true → kBool.eqe (kBool.eqeq₀ c (MRat.nanCode f)) kBool.true → kXReal.eqe (kXReal.decode f c) kXReal.nan
    | eq_p31zero9_codec_zerozero6 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.internalFormat f) kBool.true → kBool.eqe (kBool.eqeq₂ (kDomain.DomainOf f) kDomain.Extended) kBool.true → kBool.eqe (kBool.eqeq₀ c (MRat.positiveLimit f)) kBool.true → kXReal.eqe (kXReal.decode f c) kXReal.posInf
    | eq_p31zero9_codec_zerozero7 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.internalFormat f) kBool.true → kBool.eqe (kBool.eqeq₁ (kSignedness.SignednessOf f) kSignedness.Signed) kBool.true → kBool.eqe (kBool.eqeq₂ (kDomain.DomainOf f) kDomain.Extended) kBool.true → kBool.eqe (kBool.eqeq₀ c (((2 : MRat) ^ (MRat.BitwidthOf f).num.toNat) - (1 : MRat))) kBool.true → kXReal.eqe (kXReal.decode f c) kXReal.negInf
    | eq_p31zero9_codec_zerozero8 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.internalFormat f) kBool.true → kBool.eqe (kBool.eqeq₁ (kSignedness.SignednessOf f) kSignedness.Signed) kBool.true → kBool.eqe (if (MRat.nanCode f) < c then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.or (if c < (((2 : MRat) ^ (MRat.BitwidthOf f).num.toNat) - (1 : MRat)) then kBool.true else kBool.false) (kBool.eqeq₂ (kDomain.DomainOf f) kDomain.Finite)) kBool.true → kXReal.eqe (kXReal.decode f c) (kXReal.fin (- (MRat.decodePositive f (c - ((2 : MRat) ^ ((MRat.BitwidthOf f) - (1 : MRat)).num.toNat)))))
    | eq_p31zero9_codec_zerozero9 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.internalFormat f) kBool.true → kBool.eqe (if c < (MRat.nanCode f) then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.or (if c < (MRat.positiveLimit f) then kBool.true else kBool.false) (kBool.eqeq₂ (kDomain.DomainOf f) kDomain.Finite)) kBool.true → kXReal.eqe (kXReal.decode f c) (kXReal.fin (MRat.decodePositive f c))
    | eq_p31zero9_rounding_zerozero1 {p b m} : MRat.has_sort p MSort.Int → MRat.has_sort b MSort.Int → kBlockRoundMode.has_sort m MSort.RoundMode → kBool.eqe (if (1 : MRat) ≤ p then kBool.true else kBool.false) kBool.true → kBool.eqe (if (1 : MRat) ≤ b then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.validRound m) kBool.true → kXReal.eqe (kXReal.roundToPrecision p b m kXReal.nan) kXReal.nan
    | eq_p31zero9_rounding_zerozero2 {p b m i} : MRat.has_sort p MSort.Int → MRat.has_sort b MSort.Int → kBlockRoundMode.has_sort m MSort.RoundMode → kXReal.has_sort i MSort.Infinity → kBool.eqe (if (1 : MRat) ≤ p then kBool.true else kBool.false) kBool.true → kBool.eqe (if (1 : MRat) ≤ b then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.validRound m) kBool.true → kXReal.eqe (kXReal.roundToPrecision p b m i) i
    | eq_p31zero9_rounding_zerozero3 {p b m} : MRat.has_sort p MSort.Int → MRat.has_sort b MSort.Int → kBlockRoundMode.has_sort m MSort.RoundMode → kBool.eqe (if (1 : MRat) ≤ p then kBool.true else kBool.false) kBool.true → kBool.eqe (if (1 : MRat) ≤ b then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.validRound m) kBool.true → kXReal.eqe (kXReal.roundToPrecision p b m (kXReal.fin (0 : MRat))) (kXReal.fin (0 : MRat))
    | eq_p31zero9_rounding_zerozero4 {p b m x q} : MRat.has_sort p MSort.Int → MRat.has_sort b MSort.Int → kBlockRoundMode.has_sort m MSort.RoundMode → MRat.has_sort q MSort.Int → kBool.eqe (if (1 : MRat) ≤ p then kBool.true else kBool.false) kBool.true → kBool.eqe (if (1 : MRat) ≤ b then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.validRound m) kBool.true → kBool.eqe (kBool.eqslasheq₀ x (0 : MRat)) kBool.true → q = ((1 : MRat) + ((max (MRat.floorLog2 (if x < 0 then - x else x)) ((1 : MRat) - b)) - p)) → kXReal.eqe (kXReal.roundToPrecision p b m (kXReal.fin x)) (kXReal.fin (MRat.roundScaled p b m x q ((if x < 0 then - x else x) * (MRat.pow2 (- q)))))
    | eq_p31zero9_saturation_zerozero3 {sg} : kSignedness.has_sort sg MSort.Signedness → kXReal.eqe (kXReal.overflow sg kDomain.Finite kBool.true) kXReal.nan
    | eq_p31zero9_saturation_zerozero4 {sg} : kSignedness.has_sort sg MSort.Signedness → kXReal.eqe (kXReal.overflow sg kDomain.Finite kBool.false) kXReal.nan
    | eq_p31zero9_saturation_zerozero5 {sg} : kSignedness.has_sort sg MSort.Signedness → kXReal.eqe (kXReal.overflow sg kDomain.Extended kBool.true) kXReal.posInf
    | eq_p31zero9_saturation_zerozero6 : kXReal.eqe (kXReal.overflow kSignedness.Signed kDomain.Extended kBool.false) kXReal.negInf
    | eq_p31zero9_saturation_zerozero7 : kXReal.eqe (kXReal.overflow kSignedness.Unsigned kDomain.Extended kBool.false) kXReal.nan
    | eq_p31zero9_saturation_zerozero8 {l h s₁ m sg d} : kSatMode.has_sort s₁ MSort.SatMode → kBlockRoundMode.has_sort m MSort.RoundMode → kSignedness.has_sort sg MSort.Signedness → kDomain.has_sort d MSort.Domain → kBool.eqe (if l ≤ h then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.validRound m) kBool.true → kXReal.eqe (kXReal.saturate l h s₁ m kXReal.nan sg d) kXReal.nan
    | eq_p31zero9_saturation_zerozero9 {l h s₁ m r sg d} : kSatMode.has_sort s₁ MSort.SatMode → kBlockRoundMode.has_sort m MSort.RoundMode → kSignedness.has_sort sg MSort.Signedness → kDomain.has_sort d MSort.Domain → kBool.eqe (if l ≤ r then kBool.true else kBool.false) kBool.true → kBool.eqe (if r ≤ h then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.validRound m) kBool.true → kXReal.eqe (kXReal.saturate l h s₁ m (kXReal.fin r) sg d) (kXReal.fin r)
    | eq_p31zero9_saturation_zero1zero {l h m x sg d} : kBlockRoundMode.has_sort m MSort.RoundMode → kXReal.has_sort x MSort.XReal → kSignedness.has_sort sg MSort.Signedness → kDomain.has_sort d MSort.Domain → kBool.eqe (if l ≤ h then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.validRound m) kBool.true → kBool.eqe (kBool.xLt x (kXReal.fin l)) kBool.true → kXReal.eqe (kXReal.saturate l h kSatMode.SatFinite m x sg d) (kXReal.fin l)
    | eq_p31zero9_saturation_zero11 {l h m x sg d} : kBlockRoundMode.has_sort m MSort.RoundMode → kXReal.has_sort x MSort.XReal → kSignedness.has_sort sg MSort.Signedness → kDomain.has_sort d MSort.Domain → kBool.eqe (if l ≤ h then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.validRound m) kBool.true → kBool.eqe (kBool.xLt (kXReal.fin h) x) kBool.true → kXReal.eqe (kXReal.saturate l h kSatMode.SatFinite m x sg d) (kXReal.fin h)
    | eq_p31zero9_saturation_zero12 {l h m sg d} : kBlockRoundMode.has_sort m MSort.RoundMode → kSignedness.has_sort sg MSort.Signedness → kDomain.has_sort d MSort.Domain → kBool.eqe (if l ≤ h then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.validRound m) kBool.true → kXReal.eqe (kXReal.saturate l h kSatMode.SatPropagate m kXReal.posInf sg d) (kXReal.ifthenelsefi (kBool.eqeq₂ d kDomain.Extended) kXReal.posInf (kXReal.fin h))
    | eq_p31zero9_saturation_zero13 {l h m sg d} : kBlockRoundMode.has_sort m MSort.RoundMode → kSignedness.has_sort sg MSort.Signedness → kDomain.has_sort d MSort.Domain → kBool.eqe (if l ≤ h then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.validRound m) kBool.true → kXReal.eqe (kXReal.saturate l h kSatMode.SatPropagate m kXReal.negInf sg d) (kXReal.ifthenelsefi (kBool.and (kBool.eqeq₁ sg kSignedness.Signed) (kBool.eqeq₂ d kDomain.Extended)) kXReal.negInf (kXReal.fin l))
    | eq_p31zero9_saturation_zero14 {l h m r sg d} : kBlockRoundMode.has_sort m MSort.RoundMode → kSignedness.has_sort sg MSort.Signedness → kDomain.has_sort d MSort.Domain → kBool.eqe (if l ≤ h then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.validRound m) kBool.true → kBool.eqe (if r < l then kBool.true else kBool.false) kBool.true → kXReal.eqe (kXReal.saturate l h kSatMode.SatPropagate m (kXReal.fin r) sg d) (kXReal.fin l)
    | eq_p31zero9_saturation_zero15 {l h m r sg d} : kBlockRoundMode.has_sort m MSort.RoundMode → kSignedness.has_sort sg MSort.Signedness → kDomain.has_sort d MSort.Domain → kBool.eqe (if l ≤ h then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.validRound m) kBool.true → kBool.eqe (if h < r then kBool.true else kBool.false) kBool.true → kXReal.eqe (kXReal.saturate l h kSatMode.SatPropagate m (kXReal.fin r) sg d) (kXReal.fin h)
    | eq_p31zero9_saturation_zero16 {l h m r sg d} : kBlockRoundMode.has_sort m MSort.RoundMode → kSignedness.has_sort sg MSort.Signedness → kDomain.has_sort d MSort.Domain → kBool.eqe (if l ≤ h then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.validRound m) kBool.true → kBool.eqe (if h < r then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.clipsHigh m) kBool.true → kXReal.eqe (kXReal.saturate l h kSatMode.SatNone m (kXReal.fin r) sg d) (kXReal.fin h)
    | eq_p31zero9_saturation_zero17 {l h m r sg d} : kBlockRoundMode.has_sort m MSort.RoundMode → kSignedness.has_sort sg MSort.Signedness → kDomain.has_sort d MSort.Domain → kBool.eqe (if l ≤ h then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.validRound m) kBool.true → kBool.eqe (if r < l then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.clipsLow m) kBool.true → kXReal.eqe (kXReal.saturate l h kSatMode.SatNone m (kXReal.fin r) sg d) (kXReal.fin l)
    | eq_p31zero9_saturation_zero18 {l h m sg d} : kBlockRoundMode.has_sort m MSort.RoundMode → kSignedness.has_sort sg MSort.Signedness → kDomain.has_sort d MSort.Domain → kBool.eqe (if l ≤ h then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.validRound m) kBool.true → kXReal.eqe (kXReal.saturate l h kSatMode.SatNone m kXReal.posInf sg d) (kXReal.overflow sg d kBool.true)
    | eq_p31zero9_saturation_zero19 {l h m sg d} : kBlockRoundMode.has_sort m MSort.RoundMode → kSignedness.has_sort sg MSort.Signedness → kDomain.has_sort d MSort.Domain → kBool.eqe (if l ≤ h then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.validRound m) kBool.true → kXReal.eqe (kXReal.saturate l h kSatMode.SatNone m kXReal.negInf sg d) (kXReal.overflow sg d kBool.false)
    | eq_p31zero9_saturation_zero2zero {l h m r sg d} : kBlockRoundMode.has_sort m MSort.RoundMode → kSignedness.has_sort sg MSort.Signedness → kDomain.has_sort d MSort.Domain → kBool.eqe (if l ≤ h then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.validRound m) kBool.true → kBool.eqe (if r < l then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.not (kBool.clipsLow m)) kBool.true → kXReal.eqe (kXReal.saturate l h kSatMode.SatNone m (kXReal.fin r) sg d) (kXReal.overflow sg d kBool.false)
    | eq_p31zero9_saturation_zero21 {l h m r sg d} : kBlockRoundMode.has_sort m MSort.RoundMode → kSignedness.has_sort sg MSort.Signedness → kDomain.has_sort d MSort.Domain → kBool.eqe (if l ≤ h then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.validRound m) kBool.true → kBool.eqe (if h < r then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.not (kBool.clipsHigh m)) kBool.true → kXReal.eqe (kXReal.saturate l h kSatMode.SatNone m (kXReal.fin r) sg d) (kXReal.overflow sg d kBool.true)
    | eq_p31zero9_omega_arithmetic_zerozero1 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaConvert x) x
    | eq_p31zero9_omega_arithmetic_zerozero2 : kXReal.eqe (kXReal.omegaAbs kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_arithmetic_zerozero3 {i} : kXReal.has_sort i MSort.Infinity → kXReal.eqe (kXReal.omegaAbs i) kXReal.posInf
    | eq_p31zero9_omega_arithmetic_zerozero4 {r} : kXReal.eqe (kXReal.omegaAbs (kXReal.fin r)) (kXReal.fin (if r < 0 then - r else r))
    | eq_p31zero9_omega_arithmetic_zerozero5 : kXReal.eqe (kXReal.omegaNegate kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_arithmetic_zerozero6 : kXReal.eqe (kXReal.omegaNegate kXReal.posInf) kXReal.negInf
    | eq_p31zero9_omega_arithmetic_zerozero7 : kXReal.eqe (kXReal.omegaNegate kXReal.negInf) kXReal.posInf
    | eq_p31zero9_omega_arithmetic_zerozero8 {r} : kXReal.eqe (kXReal.omegaNegate (kXReal.fin r)) (kXReal.fin (- r))
    | eq_p31zero9_omega_arithmetic_zerozero9 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaCopySign kXReal.nan x) kXReal.nan
    | eq_p31zero9_omega_arithmetic_zero1zero {a} : kXReal.has_sort a MSort.Number → kXReal.eqe (kXReal.omegaCopySign a kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_arithmetic_zero11 {a b} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kBool.eqe (kBool.xMinus b) kBool.true → kXReal.eqe (kXReal.omegaCopySign a b) (kXReal.omegaNegate (kXReal.omegaAbs a))
    | eq_p31zero9_omega_arithmetic_zero12 {a b} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kBool.eqe (kBool.eqeq₄ (kBool.xMinus b) kBool.false) kBool.true → kXReal.eqe (kXReal.omegaCopySign a b) (kXReal.omegaAbs a)
    | eq_p31zero9_omega_arithmetic_zero13 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaAdd kXReal.nan x) kXReal.nan
    | eq_p31zero9_omega_arithmetic_zero14 {a} : kXReal.has_sort a MSort.Number → kXReal.eqe (kXReal.omegaAdd a kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_arithmetic_zero15 : kXReal.eqe (kXReal.omegaAdd kXReal.posInf kXReal.negInf) kXReal.nan
    | eq_p31zero9_omega_arithmetic_zero16 : kXReal.eqe (kXReal.omegaAdd kXReal.negInf kXReal.posInf) kXReal.nan
    | eq_p31zero9_omega_arithmetic_zero17 {i} : kXReal.has_sort i MSort.Infinity → kXReal.eqe (kXReal.omegaAdd i i) i
    | eq_p31zero9_omega_arithmetic_zero18 {i u} : kXReal.has_sort i MSort.Infinity → kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.omegaAdd i u) i
    | eq_p31zero9_omega_arithmetic_zero19 {u i} : kXReal.has_sort u MSort.Real → kXReal.has_sort i MSort.Infinity → kXReal.eqe (kXReal.omegaAdd u i) i
    | eq_p31zero9_omega_arithmetic_zero2zero {r s₁} : kXReal.eqe (kXReal.omegaAdd (kXReal.fin r) (kXReal.fin s₁)) (kXReal.fin (r + s₁))
    | eq_p31zero9_omega_arithmetic_zero21 {x y} : kXReal.has_sort x MSort.XReal → kXReal.has_sort y MSort.XReal → kXReal.eqe (kXReal.omegaSubtract x y) (kXReal.omegaAdd x (kXReal.omegaNegate y))
    | eq_p31zero9_omega_arithmetic_zero22 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaMultiply kXReal.nan x) kXReal.nan
    | eq_p31zero9_omega_arithmetic_zero23 {a} : kXReal.has_sort a MSort.Number → kXReal.eqe (kXReal.omegaMultiply a kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_arithmetic_zero24 {i j} : kXReal.has_sort i MSort.Infinity → kXReal.has_sort j MSort.Infinity → kXReal.eqe (kXReal.omegaMultiply i j) (kXReal.ifthenelsefi (kBool.eqeq₄ (kBool.xMinus i) (kBool.xMinus j)) kXReal.posInf kXReal.negInf)
    | eq_p31zero9_omega_arithmetic_zero25 {i} : kXReal.has_sort i MSort.Infinity → kXReal.eqe (kXReal.omegaMultiply i (kXReal.fin (0 : MRat))) kXReal.nan
    | eq_p31zero9_omega_arithmetic_zero26 {i r} : kXReal.has_sort i MSort.Infinity → kBool.eqe (kBool.eqslasheq₀ r (0 : MRat)) kBool.true → kXReal.eqe (kXReal.omegaMultiply i (kXReal.fin r)) (kXReal.ifthenelsefi (kBool.eqeq₄ (kBool.xMinus i) (if r < (0 : MRat) then kBool.true else kBool.false)) kXReal.posInf kXReal.negInf)
    | eq_p31zero9_omega_arithmetic_zero27 {u i} : kXReal.has_sort u MSort.Real → kXReal.has_sort i MSort.Infinity → kXReal.eqe (kXReal.omegaMultiply u i) (kXReal.omegaMultiply i u)
    | eq_p31zero9_omega_arithmetic_zero28 {r s₁} : kXReal.eqe (kXReal.omegaMultiply (kXReal.fin r) (kXReal.fin s₁)) (kXReal.fin (r * s₁))
    | eq_p31zero9_omega_arithmetic_zero29 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaDivide kXReal.nan x) kXReal.nan
    | eq_p31zero9_omega_arithmetic_zero3zero {a} : kXReal.has_sort a MSort.Number → kXReal.eqe (kXReal.omegaDivide a kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_arithmetic_zero31 {i j} : kXReal.has_sort i MSort.Infinity → kXReal.has_sort j MSort.Infinity → kXReal.eqe (kXReal.omegaDivide i j) kXReal.nan
    | eq_p31zero9_omega_arithmetic_zero32 {a} : kXReal.has_sort a MSort.Number → kXReal.eqe (kXReal.omegaDivide a (kXReal.fin (0 : MRat))) kXReal.nan
    | eq_p31zero9_omega_arithmetic_zero33 {i r} : kXReal.has_sort i MSort.Infinity → kBool.eqe (kBool.eqslasheq₀ r (0 : MRat)) kBool.true → kXReal.eqe (kXReal.omegaDivide i (kXReal.fin r)) (kXReal.ifthenelsefi (kBool.eqeq₄ (kBool.xMinus i) (if r < (0 : MRat) then kBool.true else kBool.false)) kXReal.posInf kXReal.negInf)
    | eq_p31zero9_omega_arithmetic_zero34 {u i} : kXReal.has_sort u MSort.Real → kXReal.has_sort i MSort.Infinity → kXReal.eqe (kXReal.omegaDivide u i) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_arithmetic_zero35 {r s₁} : kBool.eqe (kBool.eqslasheq₀ s₁ (0 : MRat)) kBool.true → kXReal.eqe (kXReal.omegaDivide (kXReal.fin r) (kXReal.fin s₁)) (kXReal.fin (r / s₁))
    | eq_p31zero9_omega_arithmetic_zero36 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaRecip x) (kXReal.omegaDivide (kXReal.fin (1 : MRat)) x)
    | eq_p31zero9_omega_arithmetic_zero37 {x y z} : kXReal.has_sort x MSort.XReal → kXReal.has_sort y MSort.XReal → kXReal.has_sort z MSort.XReal → kXReal.eqe (kXReal.omegaFMA x y z) (kXReal.omegaAdd (kXReal.omegaMultiply x y) z)
    | eq_p31zero9_omega_arithmetic_zero38 {x y z} : kXReal.has_sort x MSort.XReal → kXReal.has_sort y MSort.XReal → kXReal.has_sort z MSort.XReal → kXReal.eqe (kXReal.omegaFAA x y z) (kXReal.omegaAdd (kXReal.omegaAdd x y) z)
    | eq_p31zero9_sequences_zerozero3 {x xs} : kXReal.has_sort x MSort.XReal → kXSeq.has_sort xs MSort.XSeq → kXReal.eqe (kXReal.«at» (kXSeq.xcons x xs) (0 : MRat)) x
    | eq_p31zero9_sequences_zerozero4 {x xs n} : kXReal.has_sort x MSort.XReal → kXSeq.has_sort xs MSort.XSeq → MRat.has_sort n MSort.Nat → kBool.eqe (if (0 : MRat) < n then kBool.true else kBool.false) kBool.true → kXReal.eqe (kXReal.«at» (kXSeq.xcons x xs) n) (kXReal.«at» xs (if n ≤ (1 : MRat) then (1 : MRat) - n else n - (1 : MRat)))
    | eq_p31zero9_block_core_zerozero9 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.normalizeElement kXReal.nan x) kXReal.nan
    | eq_p31zero9_block_core_zero1zero {a} : kXReal.has_sort a MSort.Number → kXReal.eqe (kXReal.normalizeElement a kXReal.nan) kXReal.nan
    | eq_p31zero9_block_core_zero11 {v} : kXReal.has_sort v MSort.Number → kXReal.eqe (kXReal.normalizeElement (kXReal.fin (0 : MRat)) v) (kXReal.fin (0 : MRat))
    | eq_p31zero9_block_core_zero12 {i v} : kXReal.has_sort i MSort.Infinity → kXReal.has_sort v MSort.Number → kXReal.eqe (kXReal.normalizeElement i v) (kXReal.fin ((MRat.xSign v) * (MRat.xSign i)))
    | eq_p31zero9_block_core_zero13 {r v} : kXReal.has_sort v MSort.Number → kBool.eqe (kBool.eqslasheq₀ r (0 : MRat)) kBool.true → kXReal.eqe (kXReal.normalizeElement (kXReal.fin r) v) (kXReal.omegaDivide v (kXReal.fin r))
    | eq_p31zero9_omega_extrema_zerozero1 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaMinimum kXReal.nan x) kXReal.nan
    | eq_p31zero9_omega_extrema_zerozero2 {a} : kXReal.has_sort a MSort.Number → kXReal.eqe (kXReal.omegaMinimum a kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_extrema_zerozero3 {a b} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kBool.eqe (kBool.xLt a b) kBool.true → kXReal.eqe (kXReal.omegaMinimum a b) a
    | eq_p31zero9_omega_extrema_zerozero4 {a b} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kBool.eqe (kBool.xLe b a) kBool.true → kXReal.eqe (kXReal.omegaMinimum a b) b
    | eq_p31zero9_omega_extrema_zerozero5 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaMinimumNumber kXReal.nan x) x
    | eq_p31zero9_omega_extrema_zerozero6 {a} : kXReal.has_sort a MSort.Number → kXReal.eqe (kXReal.omegaMinimumNumber a kXReal.nan) a
    | eq_p31zero9_omega_extrema_zerozero7 {a b} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kXReal.eqe (kXReal.omegaMinimumNumber a b) (kXReal.omegaMinimum a b)
    | eq_p31zero9_omega_extrema_zerozero8 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaMinimumMagnitude kXReal.nan x) kXReal.nan
    | eq_p31zero9_omega_extrema_zerozero9 {a} : kXReal.has_sort a MSort.Number → kXReal.eqe (kXReal.omegaMinimumMagnitude a kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_extrema_zero1zero {a b} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kBool.eqe (kBool.xLt (kXReal.omegaAbs a) (kXReal.omegaAbs b)) kBool.true → kXReal.eqe (kXReal.omegaMinimumMagnitude a b) a
    | eq_p31zero9_omega_extrema_zero11 {a b} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kBool.eqe (kBool.xLt (kXReal.omegaAbs b) (kXReal.omegaAbs a)) kBool.true → kXReal.eqe (kXReal.omegaMinimumMagnitude a b) b
    | eq_p31zero9_omega_extrema_zero12 {a b} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kBool.eqe (kBool.xEq (kXReal.omegaAbs a) (kXReal.omegaAbs b)) kBool.true → kXReal.eqe (kXReal.omegaMinimumMagnitude a b) (kXReal.omegaMinimum a b)
    | eq_p31zero9_omega_extrema_zero13 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaMinimumMagnitudeNumber kXReal.nan x) x
    | eq_p31zero9_omega_extrema_zero14 {a} : kXReal.has_sort a MSort.Number → kXReal.eqe (kXReal.omegaMinimumMagnitudeNumber a kXReal.nan) a
    | eq_p31zero9_omega_extrema_zero15 {a b} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kXReal.eqe (kXReal.omegaMinimumMagnitudeNumber a b) (kXReal.omegaMinimumMagnitude a b)
    | eq_p31zero9_omega_extrema_zero16 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaMinimumFinite kXReal.nan x) x
    | eq_p31zero9_omega_extrema_zero17 {a} : kXReal.has_sort a MSort.Number → kXReal.eqe (kXReal.omegaMinimumFinite a kXReal.nan) a
    | eq_p31zero9_omega_extrema_zero18 {i j} : kXReal.has_sort i MSort.Infinity → kXReal.has_sort j MSort.Infinity → kXReal.eqe (kXReal.omegaMinimumFinite i j) (kXReal.omegaMinimum i j)
    | eq_p31zero9_omega_extrema_zero19 {i u} : kXReal.has_sort i MSort.Infinity → kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.omegaMinimumFinite i u) u
    | eq_p31zero9_omega_extrema_zero2zero {u i} : kXReal.has_sort u MSort.Real → kXReal.has_sort i MSort.Infinity → kXReal.eqe (kXReal.omegaMinimumFinite u i) u
    | eq_p31zero9_omega_extrema_zero21 {u v} : kXReal.has_sort u MSort.Real → kXReal.has_sort v MSort.Real → kXReal.eqe (kXReal.omegaMinimumFinite u v) (kXReal.omegaMinimum u v)
    | eq_p31zero9_omega_extrema_zero22 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaMaximum kXReal.nan x) kXReal.nan
    | eq_p31zero9_omega_extrema_zero23 {a} : kXReal.has_sort a MSort.Number → kXReal.eqe (kXReal.omegaMaximum a kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_extrema_zero24 {a b} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kBool.eqe (kBool.xLt a b) kBool.true → kXReal.eqe (kXReal.omegaMaximum a b) b
    | eq_p31zero9_omega_extrema_zero25 {a b} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kBool.eqe (kBool.xLe b a) kBool.true → kXReal.eqe (kXReal.omegaMaximum a b) a
    | eq_p31zero9_omega_extrema_zero26 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaMaximumNumber kXReal.nan x) x
    | eq_p31zero9_omega_extrema_zero27 {a} : kXReal.has_sort a MSort.Number → kXReal.eqe (kXReal.omegaMaximumNumber a kXReal.nan) a
    | eq_p31zero9_omega_extrema_zero28 {a b} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kXReal.eqe (kXReal.omegaMaximumNumber a b) (kXReal.omegaMaximum a b)
    | eq_p31zero9_omega_extrema_zero29 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaMaximumMagnitude kXReal.nan x) kXReal.nan
    | eq_p31zero9_omega_extrema_zero3zero {a} : kXReal.has_sort a MSort.Number → kXReal.eqe (kXReal.omegaMaximumMagnitude a kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_extrema_zero31 {a b} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kBool.eqe (kBool.xLt (kXReal.omegaAbs a) (kXReal.omegaAbs b)) kBool.true → kXReal.eqe (kXReal.omegaMaximumMagnitude a b) b
    | eq_p31zero9_omega_extrema_zero32 {a b} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kBool.eqe (kBool.xLt (kXReal.omegaAbs b) (kXReal.omegaAbs a)) kBool.true → kXReal.eqe (kXReal.omegaMaximumMagnitude a b) a
    | eq_p31zero9_omega_extrema_zero33 {a b} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kBool.eqe (kBool.xEq (kXReal.omegaAbs a) (kXReal.omegaAbs b)) kBool.true → kXReal.eqe (kXReal.omegaMaximumMagnitude a b) (kXReal.omegaMaximum a b)
    | eq_p31zero9_omega_extrema_zero34 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaMaximumMagnitudeNumber kXReal.nan x) x
    | eq_p31zero9_omega_extrema_zero35 {a} : kXReal.has_sort a MSort.Number → kXReal.eqe (kXReal.omegaMaximumMagnitudeNumber a kXReal.nan) a
    | eq_p31zero9_omega_extrema_zero36 {a b} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kXReal.eqe (kXReal.omegaMaximumMagnitudeNumber a b) (kXReal.omegaMaximumMagnitude a b)
    | eq_p31zero9_omega_extrema_zero37 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaMaximumFinite kXReal.nan x) x
    | eq_p31zero9_omega_extrema_zero38 {a} : kXReal.has_sort a MSort.Number → kXReal.eqe (kXReal.omegaMaximumFinite a kXReal.nan) a
    | eq_p31zero9_omega_extrema_zero39 {i j} : kXReal.has_sort i MSort.Infinity → kXReal.has_sort j MSort.Infinity → kXReal.eqe (kXReal.omegaMaximumFinite i j) (kXReal.omegaMaximum i j)
    | eq_p31zero9_omega_extrema_zero4zero {i u} : kXReal.has_sort i MSort.Infinity → kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.omegaMaximumFinite i u) u
    | eq_p31zero9_omega_extrema_zero41 {u i} : kXReal.has_sort u MSort.Real → kXReal.has_sort i MSort.Infinity → kXReal.eqe (kXReal.omegaMaximumFinite u i) u
    | eq_p31zero9_omega_extrema_zero42 {u v} : kXReal.has_sort u MSort.Real → kXReal.has_sort v MSort.Real → kXReal.eqe (kXReal.omegaMaximumFinite u v) (kXReal.omegaMaximum u v)
    | eq_p31zero9_omega_extrema_zero43 {x y} : kXReal.has_sort x MSort.XReal → kXReal.has_sort y MSort.XReal → kXReal.eqe (kXReal.omegaClamp kXReal.nan x y) kXReal.nan
    | eq_p31zero9_omega_extrema_zero44 {a x} : kXReal.has_sort a MSort.Number → kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaClamp a kXReal.nan x) kXReal.nan
    | eq_p31zero9_omega_extrema_zero45 {a b} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kXReal.eqe (kXReal.omegaClamp a b kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_extrema_zero46 {a b c} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kXReal.has_sort c MSort.Number → kBool.eqe (kBool.xLt c b) kBool.true → kXReal.eqe (kXReal.omegaClamp a b c) kXReal.nan
    | eq_p31zero9_omega_extrema_zero47 {a b c} : kXReal.has_sort a MSort.Number → kXReal.has_sort b MSort.Number → kXReal.has_sort c MSort.Number → kBool.eqe (kBool.xLe b c) kBool.true → kXReal.eqe (kXReal.omegaClamp a b c) (kXReal.omegaMinimum (kXReal.omegaMaximum a b) c)
    | eq_p31zero9_block_ops_zerozero1 {a} : kXReal.has_sort a MSort.XReal → kXReal.eqe (kXReal.foldAdd a kXSeq.xnil) a
    | eq_p31zero9_block_ops_zerozero2 {a x xs} : kXReal.has_sort a MSort.XReal → kXReal.has_sort x MSort.XReal → kXSeq.has_sort xs MSort.XSeq → kXReal.eqe (kXReal.foldAdd a (kXSeq.xcons x xs)) (kXReal.foldAdd (kXReal.omegaAdd a x) xs)
    | eq_p31zero9_block_ops_zerozero3 {a} : kXReal.has_sort a MSort.XReal → kXReal.eqe (kXReal.foldMultiply a kXSeq.xnil) a
    | eq_p31zero9_block_ops_zerozero4 {a x xs} : kXReal.has_sort a MSort.XReal → kXReal.has_sort x MSort.XReal → kXSeq.has_sort xs MSort.XSeq → kXReal.eqe (kXReal.foldMultiply a (kXSeq.xcons x xs)) (kXReal.foldMultiply (kXReal.omegaMultiply a x) xs)
    | eq_p31zero9_block_ops_zerozero5 {a} : kXReal.has_sort a MSort.XReal → kXReal.eqe (kXReal.foldMaximumFinite a kXSeq.xnil) a
    | eq_p31zero9_block_ops_zerozero6 {a x xs} : kXReal.has_sort a MSort.XReal → kXReal.has_sort x MSort.XReal → kXSeq.has_sort xs MSort.XSeq → kXReal.eqe (kXReal.foldMaximumFinite a (kXSeq.xcons x xs)) (kXReal.foldMaximumFinite (kXReal.omegaMaximumFinite a x) xs)
    | eq_p31zero9_real_expressions_zerozero1 : kXReal.eqe kXReal.pi (kXReal.piMultiple (1 : MRat))
    | eq_p31zero9_real_expressions_zerozero2 : kXReal.eqe (kXReal.piMultiple (0 : MRat)) (kXReal.fin (0 : MRat))
    | eq_p31zero9_real_expressions_zerozero3 {r s₁} : kXReal.eqe (kXReal.realAdd (kXReal.fin r) (kXReal.fin s₁)) (kXReal.fin (r + s₁))
    | eq_p31zero9_real_expressions_zerozero4 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.realAdd (kXReal.fin (0 : MRat)) u) u
    | eq_p31zero9_real_expressions_zerozero5 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.realAdd u (kXReal.fin (0 : MRat))) u
    | eq_p31zero9_real_expressions_zerozero6 {r s₁} : kXReal.eqe (kXReal.realAdd (kXReal.piMultiple r) (kXReal.piMultiple s₁)) (kXReal.piMultiple (r + s₁))
    | eq_p31zero9_real_expressions_zerozero7 {r s₁} : kXReal.eqe (kXReal.realMultiply (kXReal.fin r) (kXReal.fin s₁)) (kXReal.fin (r * s₁))
    | eq_p31zero9_real_expressions_zerozero8 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.realMultiply (kXReal.fin (0 : MRat)) u) (kXReal.fin (0 : MRat))
    | eq_p31zero9_real_expressions_zerozero9 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.realMultiply u (kXReal.fin (0 : MRat))) (kXReal.fin (0 : MRat))
    | eq_p31zero9_real_expressions_zero1zero {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.realMultiply (kXReal.fin (1 : MRat)) u) u
    | eq_p31zero9_real_expressions_zero11 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.realMultiply u (kXReal.fin (1 : MRat))) u
    | eq_p31zero9_real_expressions_zero12 {r s₁} : kXReal.eqe (kXReal.realMultiply (kXReal.fin r) (kXReal.piMultiple s₁)) (kXReal.piMultiple (r * s₁))
    | eq_p31zero9_real_expressions_zero13 {s₁ r} : kXReal.eqe (kXReal.realMultiply (kXReal.piMultiple s₁) (kXReal.fin r)) (kXReal.piMultiple (r * s₁))
    | eq_p31zero9_real_expressions_zero14 {r} : kXReal.eqe (kXReal.realNegate (kXReal.fin r)) (kXReal.fin (- r))
    | eq_p31zero9_real_expressions_zero15 {r} : kXReal.eqe (kXReal.realNegate (kXReal.piMultiple r)) (kXReal.piMultiple (- r))
    | eq_p31zero9_real_expressions_zero16 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.realNegate (kXReal.realNegate u)) u
    | eq_p31zero9_real_expressions_zero17 {r} : kXReal.eqe (kXReal.realAbs (kXReal.fin r)) (kXReal.fin (if r < 0 then - r else r))
    | eq_p31zero9_real_expressions_zero18 {r} : kXReal.eqe (kXReal.realAbs (kXReal.piMultiple r)) (kXReal.piMultiple (if r < 0 then - r else r))
    | eq_p31zero9_real_expressions_zero19 {r s₁} : kBool.eqe (kBool.eqslasheq₀ s₁ (0 : MRat)) kBool.true → kXReal.eqe (kXReal.realDivide (kXReal.fin r) (kXReal.fin s₁)) (kXReal.fin (r / s₁))
    | eq_p31zero9_real_expressions_zero2zero {r s₁} : kBool.eqe (kBool.eqslasheq₀ s₁ (0 : MRat)) kBool.true → kXReal.eqe (kXReal.realDivide (kXReal.piMultiple r) (kXReal.piMultiple s₁)) (kXReal.fin (r / s₁))
    | eq_p31zero9_real_expressions_zero21 {r s₁} : kBool.eqe (kBool.eqslasheq₀ s₁ (0 : MRat)) kBool.true → kXReal.eqe (kXReal.realDivide (kXReal.piMultiple r) (kXReal.fin s₁)) (kXReal.piMultiple (r / s₁))
    | eq_p31zero9_real_expressions_zero22 {u v} : kXReal.has_sort u MSort.Real → kXReal.has_sort v MSort.Real → kXReal.eqe (kXReal.omegaAdd u v) (kXReal.realAdd u v)
    | eq_p31zero9_real_expressions_zero23 {u v} : kXReal.has_sort u MSort.Real → kXReal.has_sort v MSort.Real → kXReal.eqe (kXReal.omegaMultiply u v) (kXReal.realMultiply u v)
    | eq_p31zero9_real_expressions_zero24 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.omegaNegate u) (kXReal.realNegate u)
    | eq_p31zero9_real_expressions_zero25 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.omegaAbs u) (kXReal.realAbs u)
    | eq_p31zero9_real_expressions_zero26 {u v} : kXReal.has_sort u MSort.Real → kXReal.has_sort v MSort.Real → kBool.eqe (kBool.xEq v (kXReal.fin (0 : MRat))) kBool.true → kXReal.eqe (kXReal.omegaDivide u v) kXReal.nan
    | eq_p31zero9_real_expressions_zero27 {u v} : kXReal.has_sort u MSort.Real → kXReal.has_sort v MSort.Real → kBool.eqe (kBool.eqeq₄ (kBool.xEq v (kXReal.fin (0 : MRat))) kBool.false) kBool.true → kXReal.eqe (kXReal.omegaDivide u v) (kXReal.realDivide u v)
    | eq_p31zero9_real_expressions_zero28 {i u} : kXReal.has_sort i MSort.Infinity → kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xEq u (kXReal.fin (0 : MRat))) kBool.true → kXReal.eqe (kXReal.omegaMultiply i u) kXReal.nan
    | eq_p31zero9_real_expressions_zero29 {i u} : kXReal.has_sort i MSort.Infinity → kXReal.has_sort u MSort.Real → kBool.eqe (kBool.eqeq₄ (kBool.xEq u (kXReal.fin (0 : MRat))) kBool.false) kBool.true → kXReal.eqe (kXReal.omegaMultiply i u) (kXReal.ifthenelsefi (kBool.eqeq₄ (kBool.xMinus i) (kBool.xMinus u)) kXReal.posInf kXReal.negInf)
    | eq_p31zero9_real_expressions_zero3zero {i u} : kXReal.has_sort i MSort.Infinity → kXReal.has_sort u MSort.Real → kBool.eqe (kBool.eqeq₄ (kBool.xEq u (kXReal.fin (0 : MRat))) kBool.false) kBool.true → kXReal.eqe (kXReal.omegaDivide i u) (kXReal.ifthenelsefi (kBool.eqeq₄ (kBool.xMinus i) (kBool.xMinus u)) kXReal.posInf kXReal.negInf)
    | eq_p31zero9_real_zero_divide {v} : kXReal.has_sort v MSort.Real → kBool.eqe (kBool.eqeq₄ (kBool.xEq v (kXReal.fin (0 : MRat))) kBool.false) kBool.true → kXReal.eqe (kXReal.realDivide (kXReal.fin (0 : MRat)) v) (kXReal.fin (0 : MRat))
    | eq_p31zero9_real_unit_divide {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.realDivide u (kXReal.fin (1 : MRat))) u
    | eq_p31zero9_omega_elementary_zerozero1 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLe (kXReal.fin (0 : MRat)) u) kBool.true → kXReal.eqe (kXReal.omegaSqrt u) (kXReal.exprSqrt u)
    | eq_p31zero9_omega_elementary_zerozero2 : kXReal.eqe (kXReal.omegaSqrt kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_zerozero3 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.omegaExp u) (kXReal.exprExp u)
    | eq_p31zero9_omega_elementary_zerozero4 : kXReal.eqe (kXReal.omegaExp kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_zerozero5 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.omegaExp2 u) (kXReal.exprExp2 u)
    | eq_p31zero9_omega_elementary_zerozero6 : kXReal.eqe (kXReal.omegaExp2 kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_zerozero7 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt (kXReal.fin (0 : MRat)) u) kBool.true → kXReal.eqe (kXReal.omegaLog u) (kXReal.exprLog u)
    | eq_p31zero9_omega_elementary_zerozero8 : kXReal.eqe (kXReal.omegaLog kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_zerozero9 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt (kXReal.fin (0 : MRat)) u) kBool.true → kXReal.eqe (kXReal.omegaLog2 u) (kXReal.exprLog2 u)
    | eq_p31zero9_omega_elementary_zero1zero : kXReal.eqe (kXReal.omegaLog2 kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_zero11 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.omegaSin u) (kXReal.exprSin u)
    | eq_p31zero9_omega_elementary_zero12 : kXReal.eqe (kXReal.omegaSin kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_zero13 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.omegaCos u) (kXReal.exprCos u)
    | eq_p31zero9_omega_elementary_zero14 : kXReal.eqe (kXReal.omegaCos kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_zero15 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.eqeq₄ (kBool.xEq (kXReal.omegaCos u) (kXReal.fin (0 : MRat))) kBool.false) kBool.true → kXReal.eqe (kXReal.omegaTan u) (kXReal.exprTan u)
    | eq_p31zero9_omega_elementary_zero16 : kXReal.eqe (kXReal.omegaTan kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_zero17 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLe (kXReal.fin ((- 1) : MRat)) u) kBool.true → kBool.eqe (kBool.xLe u (kXReal.fin (1 : MRat))) kBool.true → kXReal.eqe (kXReal.omegaArcSin u) (kXReal.exprArcSin u)
    | eq_p31zero9_omega_elementary_zero18 : kXReal.eqe (kXReal.omegaArcSin kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_zero19 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLe (kXReal.fin ((- 1) : MRat)) u) kBool.true → kBool.eqe (kBool.xLe u (kXReal.fin (1 : MRat))) kBool.true → kXReal.eqe (kXReal.omegaArcCos u) (kXReal.exprArcCos u)
    | eq_p31zero9_omega_elementary_zero2zero : kXReal.eqe (kXReal.omegaArcCos kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_zero21 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.omegaArcTan u) (kXReal.exprArcTan u)
    | eq_p31zero9_omega_elementary_zero22 : kXReal.eqe (kXReal.omegaArcTan kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_zero23 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.omegaSinh u) (kXReal.exprSinh u)
    | eq_p31zero9_omega_elementary_zero24 : kXReal.eqe (kXReal.omegaSinh kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_zero25 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.omegaCosh u) (kXReal.exprCosh u)
    | eq_p31zero9_omega_elementary_zero26 : kXReal.eqe (kXReal.omegaCosh kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_zero27 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.omegaTanh u) (kXReal.exprTanh u)
    | eq_p31zero9_omega_elementary_zero28 : kXReal.eqe (kXReal.omegaTanh kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_zero29 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.omegaArcSinh u) (kXReal.exprArcSinh u)
    | eq_p31zero9_omega_elementary_zero3zero : kXReal.eqe (kXReal.omegaArcSinh kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_zero31 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLe (kXReal.fin (1 : MRat)) u) kBool.true → kXReal.eqe (kXReal.omegaArcCosh u) (kXReal.exprArcCosh u)
    | eq_p31zero9_omega_elementary_zero32 : kXReal.eqe (kXReal.omegaArcCosh kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_zero33 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt (kXReal.fin ((- 1) : MRat)) u) kBool.true → kBool.eqe (kBool.xLt u (kXReal.fin (1 : MRat))) kBool.true → kXReal.eqe (kXReal.omegaArcTanh u) (kXReal.exprArcTanh u)
    | eq_p31zero9_omega_elementary_zero34 : kXReal.eqe (kXReal.omegaArcTanh kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_zero35 : kXReal.eqe (kXReal.omegaSqrt kXReal.posInf) kXReal.posInf
    | eq_p31zero9_omega_elementary_zero36 : kXReal.eqe (kXReal.omegaSqrt kXReal.negInf) kXReal.nan
    | eq_p31zero9_omega_elementary_zero37 : kXReal.eqe (kXReal.omegaExp kXReal.posInf) kXReal.posInf
    | eq_p31zero9_omega_elementary_zero38 : kXReal.eqe (kXReal.omegaExp kXReal.negInf) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_zero39 : kXReal.eqe (kXReal.omegaExp2 kXReal.posInf) kXReal.posInf
    | eq_p31zero9_omega_elementary_zero4zero : kXReal.eqe (kXReal.omegaExp2 kXReal.negInf) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_zero41 : kXReal.eqe (kXReal.omegaLog kXReal.posInf) kXReal.posInf
    | eq_p31zero9_omega_elementary_zero42 : kXReal.eqe (kXReal.omegaLog kXReal.negInf) kXReal.nan
    | eq_p31zero9_omega_elementary_zero43 : kXReal.eqe (kXReal.omegaLog2 kXReal.posInf) kXReal.posInf
    | eq_p31zero9_omega_elementary_zero44 : kXReal.eqe (kXReal.omegaLog2 kXReal.negInf) kXReal.nan
    | eq_p31zero9_omega_elementary_zero45 : kXReal.eqe (kXReal.omegaSin kXReal.posInf) kXReal.nan
    | eq_p31zero9_omega_elementary_zero46 : kXReal.eqe (kXReal.omegaSin kXReal.negInf) kXReal.nan
    | eq_p31zero9_omega_elementary_zero47 : kXReal.eqe (kXReal.omegaCos kXReal.posInf) kXReal.nan
    | eq_p31zero9_omega_elementary_zero48 : kXReal.eqe (kXReal.omegaCos kXReal.negInf) kXReal.nan
    | eq_p31zero9_omega_elementary_zero49 : kXReal.eqe (kXReal.omegaTan kXReal.posInf) kXReal.nan
    | eq_p31zero9_omega_elementary_zero5zero : kXReal.eqe (kXReal.omegaTan kXReal.negInf) kXReal.nan
    | eq_p31zero9_omega_elementary_zero51 : kXReal.eqe (kXReal.omegaArcSin kXReal.posInf) kXReal.nan
    | eq_p31zero9_omega_elementary_zero52 : kXReal.eqe (kXReal.omegaArcSin kXReal.negInf) kXReal.nan
    | eq_p31zero9_omega_elementary_zero53 : kXReal.eqe (kXReal.omegaArcCos kXReal.posInf) kXReal.nan
    | eq_p31zero9_omega_elementary_zero54 : kXReal.eqe (kXReal.omegaArcCos kXReal.negInf) kXReal.nan
    | eq_p31zero9_omega_elementary_zero55 : kXReal.eqe (kXReal.omegaArcTan kXReal.posInf) (kXReal.piMultiple ((1 / 2) : MRat))
    | eq_p31zero9_omega_elementary_zero56 : kXReal.eqe (kXReal.omegaArcTan kXReal.negInf) (kXReal.piMultiple (((- 1) / 2) : MRat))
    | eq_p31zero9_omega_elementary_zero57 : kXReal.eqe (kXReal.omegaSinh kXReal.posInf) kXReal.posInf
    | eq_p31zero9_omega_elementary_zero58 : kXReal.eqe (kXReal.omegaSinh kXReal.negInf) kXReal.negInf
    | eq_p31zero9_omega_elementary_zero59 : kXReal.eqe (kXReal.omegaCosh kXReal.posInf) kXReal.posInf
    | eq_p31zero9_omega_elementary_zero6zero : kXReal.eqe (kXReal.omegaCosh kXReal.negInf) kXReal.posInf
    | eq_p31zero9_omega_elementary_zero61 : kXReal.eqe (kXReal.omegaTanh kXReal.posInf) (kXReal.fin (1 : MRat))
    | eq_p31zero9_omega_elementary_zero62 : kXReal.eqe (kXReal.omegaTanh kXReal.negInf) (kXReal.fin ((- 1) : MRat))
    | eq_p31zero9_omega_elementary_zero63 : kXReal.eqe (kXReal.omegaArcSinh kXReal.posInf) kXReal.posInf
    | eq_p31zero9_omega_elementary_zero64 : kXReal.eqe (kXReal.omegaArcSinh kXReal.negInf) kXReal.negInf
    | eq_p31zero9_omega_elementary_zero65 : kXReal.eqe (kXReal.omegaArcCosh kXReal.posInf) kXReal.posInf
    | eq_p31zero9_omega_elementary_zero66 : kXReal.eqe (kXReal.omegaArcCosh kXReal.negInf) kXReal.nan
    | eq_p31zero9_omega_elementary_zero67 : kXReal.eqe (kXReal.omegaArcTanh kXReal.posInf) kXReal.nan
    | eq_p31zero9_omega_elementary_zero68 : kXReal.eqe (kXReal.omegaArcTanh kXReal.negInf) kXReal.nan
    | eq_p31zero9_omega_elementary_zero69 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt u (kXReal.fin (0 : MRat))) kBool.true → kXReal.eqe (kXReal.omegaSqrt u) kXReal.nan
    | eq_p31zero9_omega_elementary_zero7zero {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt u (kXReal.fin (0 : MRat))) kBool.true → kXReal.eqe (kXReal.omegaLog u) kXReal.nan
    | eq_p31zero9_omega_elementary_zero71 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt u (kXReal.fin (0 : MRat))) kBool.true → kXReal.eqe (kXReal.omegaLog2 u) kXReal.nan
    | eq_p31zero9_omega_elementary_zero72 : kXReal.eqe (kXReal.omegaLog (kXReal.fin (0 : MRat))) kXReal.negInf
    | eq_p31zero9_omega_elementary_zero73 : kXReal.eqe (kXReal.omegaLog2 (kXReal.fin (0 : MRat))) kXReal.negInf
    | eq_p31zero9_omega_elementary_zero74 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.or (kBool.xLt u (kXReal.fin ((- 1) : MRat))) (kBool.xLt (kXReal.fin (1 : MRat)) u)) kBool.true → kXReal.eqe (kXReal.omegaArcSin u) kXReal.nan
    | eq_p31zero9_omega_elementary_zero75 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.or (kBool.xLt u (kXReal.fin ((- 1) : MRat))) (kBool.xLt (kXReal.fin (1 : MRat)) u)) kBool.true → kXReal.eqe (kXReal.omegaArcCos u) kXReal.nan
    | eq_p31zero9_omega_elementary_zero76 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.or (kBool.xLt u (kXReal.fin ((- 1) : MRat))) (kBool.xLt (kXReal.fin (1 : MRat)) u)) kBool.true → kXReal.eqe (kXReal.omegaArcTanh u) kXReal.nan
    | eq_p31zero9_omega_elementary_zero77 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt u (kXReal.fin (1 : MRat))) kBool.true → kXReal.eqe (kXReal.omegaArcCosh u) kXReal.nan
    | eq_p31zero9_omega_elementary_zero78 : kXReal.eqe (kXReal.omegaArcTanh (kXReal.fin (1 : MRat))) kXReal.posInf
    | eq_p31zero9_omega_elementary_zero79 : kXReal.eqe (kXReal.omegaArcTanh (kXReal.fin ((- 1) : MRat))) kXReal.negInf
    | eq_p31zero9_omega_elementary_zero8zero : kXReal.eqe (kXReal.omegaRSqrt kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_zero81 : kXReal.eqe (kXReal.omegaRSqrt kXReal.negInf) kXReal.nan
    | eq_p31zero9_omega_elementary_zero82 : kXReal.eqe (kXReal.omegaRSqrt kXReal.posInf) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_zero83 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLe u (kXReal.fin (0 : MRat))) kBool.true → kXReal.eqe (kXReal.omegaRSqrt u) kXReal.nan
    | eq_p31zero9_omega_elementary_zero84 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt (kXReal.fin (0 : MRat)) u) kBool.true → kXReal.eqe (kXReal.omegaRSqrt u) (kXReal.omegaRecip (kXReal.omegaSqrt u))
    | eq_p31zero9_omega_elementary_zero85 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaLogOnePlus x) (kXReal.omegaLog (kXReal.omegaAdd (kXReal.fin (1 : MRat)) x))
    | eq_p31zero9_omega_elementary_zero86 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaExpMinusOne x) (kXReal.omegaSubtract (kXReal.omegaExp x) (kXReal.fin (1 : MRat)))
    | eq_p31zero9_omega_elementary_zero87 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaSoftplus x) (kXReal.omegaLog (kXReal.omegaAdd (kXReal.fin (1 : MRat)) (kXReal.omegaExp x)))
    | eq_p31zero9_omega_elementary_zero88 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaSinPi x) (kXReal.omegaSin (kXReal.omegaMultiply x kXReal.pi))
    | eq_p31zero9_omega_elementary_zero89 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaCosPi x) (kXReal.omegaCos (kXReal.omegaMultiply x kXReal.pi))
    | eq_p31zero9_omega_elementary_zero9zero {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaTanPi x) (kXReal.omegaTan (kXReal.omegaMultiply x kXReal.pi))
    | eq_p31zero9_omega_elementary_zero91 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaArcSinPi x) (kXReal.omegaDivide (kXReal.omegaArcSin x) kXReal.pi)
    | eq_p31zero9_omega_elementary_zero92 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaArcCosPi x) (kXReal.omegaDivide (kXReal.omegaArcCos x) kXReal.pi)
    | eq_p31zero9_omega_elementary_zero93 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaArcTanPi x) (kXReal.omegaDivide (kXReal.omegaArcTan x) kXReal.pi)
    | eq_p31zero9_omega_elementary_zero94 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xEq (kXReal.omegaCos u) (kXReal.fin (0 : MRat))) kBool.true → kBool.eqe (kBool.xLt (kXReal.fin (0 : MRat)) (kXReal.omegaSin u)) kBool.true → kXReal.eqe (kXReal.omegaTan u) kXReal.posInf
    | eq_p31zero9_omega_elementary_zero95 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xEq (kXReal.omegaCos u) (kXReal.fin (0 : MRat))) kBool.true → kBool.eqe (kBool.xLt (kXReal.omegaSin u) (kXReal.fin (0 : MRat))) kBool.true → kXReal.eqe (kXReal.omegaTan u) kXReal.negInf
    | eq_p31zero9_omega_elementary_1zerozero {r ns ds n d} : MRat.has_sort ns MSort.Nat → MRat.has_sort ds MSort.Nat → MRat.has_sort n MSort.Nat → MRat.has_sort d MSort.Nat → kBool.eqe (if (0 : MRat) ≤ r then kBool.true else kBool.false) kBool.true → n = (MRat.numeratorOf r) → d = (MRat.denominatorOf r) → ns = (MRat.integerSqrt n) → ds = (MRat.integerSqrt d) → kBool.eqe (kBool.eqeq₀ (ns * ns) n) kBool.true → kBool.eqe (kBool.eqeq₀ (ds * ds) d) kBool.true → kXReal.eqe (kXReal.exprSqrt (kXReal.fin r)) (kXReal.fin (ns / ds))
    | eq_p31zero9_omega_elementary_1zero1 : kXReal.eqe (kXReal.exprExp (kXReal.fin (0 : MRat))) (kXReal.fin (1 : MRat))
    | eq_p31zero9_omega_elementary_1zero2 {k} : MRat.has_sort k MSort.Int → kXReal.eqe (kXReal.exprExp2 (kXReal.fin k)) (kXReal.fin (MRat.pow2 k))
    | eq_p31zero9_omega_elementary_1zero3 : kXReal.eqe (kXReal.exprLog (kXReal.fin (1 : MRat))) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_1zero4 {r k} : MRat.has_sort k MSort.Int → kBool.eqe (if (0 : MRat) < r then kBool.true else kBool.false) kBool.true → k = (MRat.floorLog2 r) → kBool.eqe (kBool.eqeq₀ r (MRat.pow2 k)) kBool.true → kXReal.eqe (kXReal.exprLog2 (kXReal.fin r)) (kXReal.fin k)
    | eq_p31zero9_omega_elementary_1zero5 : kXReal.eqe (kXReal.exprSin (kXReal.fin (0 : MRat))) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_1zero6 : kXReal.eqe (kXReal.exprCos (kXReal.fin (0 : MRat))) (kXReal.fin (1 : MRat))
    | eq_p31zero9_omega_elementary_1zero7 : kXReal.eqe (kXReal.exprTan (kXReal.fin (0 : MRat))) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_1zero8 : kXReal.eqe (kXReal.exprArcSin (kXReal.fin (0 : MRat))) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_1zero9 : kXReal.eqe (kXReal.exprArcSin (kXReal.fin (1 : MRat))) (kXReal.piMultiple ((1 / 2) : MRat))
    | eq_p31zero9_omega_elementary_11zero : kXReal.eqe (kXReal.exprArcSin (kXReal.fin ((- 1) : MRat))) (kXReal.piMultiple (((- 1) / 2) : MRat))
    | eq_p31zero9_omega_elementary_111 : kXReal.eqe (kXReal.exprArcCos (kXReal.fin (0 : MRat))) (kXReal.piMultiple ((1 / 2) : MRat))
    | eq_p31zero9_omega_elementary_112 : kXReal.eqe (kXReal.exprArcCos (kXReal.fin (1 : MRat))) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_113 : kXReal.eqe (kXReal.exprArcCos (kXReal.fin ((- 1) : MRat))) kXReal.pi
    | eq_p31zero9_omega_elementary_114 : kXReal.eqe (kXReal.exprArcTan (kXReal.fin (0 : MRat))) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_115 : kXReal.eqe (kXReal.exprArcTan (kXReal.fin (1 : MRat))) (kXReal.piMultiple ((1 / 4) : MRat))
    | eq_p31zero9_omega_elementary_116 : kXReal.eqe (kXReal.exprArcTan (kXReal.fin ((- 1) : MRat))) (kXReal.piMultiple (((- 1) / 4) : MRat))
    | eq_p31zero9_omega_elementary_117 : kXReal.eqe (kXReal.exprSinh (kXReal.fin (0 : MRat))) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_118 : kXReal.eqe (kXReal.exprCosh (kXReal.fin (0 : MRat))) (kXReal.fin (1 : MRat))
    | eq_p31zero9_omega_elementary_119 : kXReal.eqe (kXReal.exprTanh (kXReal.fin (0 : MRat))) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_12zero : kXReal.eqe (kXReal.exprArcSinh (kXReal.fin (0 : MRat))) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_121 : kXReal.eqe (kXReal.exprArcCosh (kXReal.fin (1 : MRat))) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_122 : kXReal.eqe (kXReal.exprArcTanh (kXReal.fin (0 : MRat))) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_123 {r} : kBool.eqe (kBool.eqeq₀ r (MRat.floor r)) kBool.true → kXReal.eqe (kXReal.exprSin (kXReal.piMultiple r)) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_124 {r} : kBool.eqe (kBool.eqeq₀ (r - (MRat.floor r)) ((1 / 2) : MRat)) kBool.true → kXReal.eqe (kXReal.exprSin (kXReal.piMultiple r)) (kXReal.ifthenelsefi (kBool.even (MRat.floor r)) (kXReal.fin (1 : MRat)) (kXReal.fin ((- 1) : MRat)))
    | eq_p31zero9_omega_elementary_125 {r} : kBool.eqe (kBool.eqeq₀ r (MRat.floor r)) kBool.true → kXReal.eqe (kXReal.exprCos (kXReal.piMultiple r)) (kXReal.ifthenelsefi (kBool.even (MRat.floor r)) (kXReal.fin (1 : MRat)) (kXReal.fin ((- 1) : MRat)))
    | eq_p31zero9_omega_elementary_126 {r} : kBool.eqe (kBool.eqeq₀ (r - (MRat.floor r)) ((1 / 2) : MRat)) kBool.true → kXReal.eqe (kXReal.exprCos (kXReal.piMultiple r)) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_127 {r} : kBool.eqe (kBool.eqeq₀ r (MRat.floor r)) kBool.true → kXReal.eqe (kXReal.exprTan (kXReal.piMultiple r)) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_138 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaHypot kXReal.nan x) kXReal.nan
    | eq_p31zero9_omega_elementary_139 {a} : kXReal.has_sort a MSort.Number → kXReal.eqe (kXReal.omegaHypot a kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_14zero {a i} : kXReal.has_sort a MSort.Number → kXReal.has_sort i MSort.Infinity → kXReal.eqe (kXReal.omegaHypot a i) kXReal.posInf
    | eq_p31zero9_omega_elementary_141 {i u} : kXReal.has_sort i MSort.Infinity → kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.omegaHypot i u) kXReal.posInf
    | eq_p31zero9_omega_elementary_142 {u v} : kXReal.has_sort u MSort.Real → kXReal.has_sort v MSort.Real → kXReal.eqe (kXReal.omegaHypot u v) (kXReal.omegaSqrt (kXReal.realAdd (kXReal.realMultiply u u) (kXReal.realMultiply v v)))
    | eq_p31zero9_omega_elementary_143 {x} : kXReal.has_sort x MSort.XReal → kXReal.eqe (kXReal.omegaArcTan2 kXReal.nan x) kXReal.nan
    | eq_p31zero9_omega_elementary_144 {a} : kXReal.has_sort a MSort.Number → kXReal.eqe (kXReal.omegaArcTan2 a kXReal.nan) kXReal.nan
    | eq_p31zero9_omega_elementary_145 : kXReal.eqe (kXReal.omegaArcTan2 (kXReal.fin (0 : MRat)) (kXReal.fin (0 : MRat))) kXReal.nan
    | eq_p31zero9_omega_elementary_146 {i j} : kXReal.has_sort i MSort.Infinity → kXReal.has_sort j MSort.Infinity → kXReal.eqe (kXReal.omegaArcTan2 i j) kXReal.nan
    | eq_p31zero9_omega_elementary_147 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.omegaArcTan2 u kXReal.posInf) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_148 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt (kXReal.fin (0 : MRat)) u) kBool.true → kXReal.eqe (kXReal.omegaArcTan2 (kXReal.fin (0 : MRat)) u) (kXReal.fin (0 : MRat))
    | eq_p31zero9_omega_elementary_149 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.omegaArcTan2 kXReal.posInf u) (kXReal.piMultiple ((1 / 2) : MRat))
    | eq_p31zero9_omega_elementary_15zero {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt (kXReal.fin (0 : MRat)) u) kBool.true → kXReal.eqe (kXReal.omegaArcTan2 u (kXReal.fin (0 : MRat))) (kXReal.piMultiple ((1 / 2) : MRat))
    | eq_p31zero9_omega_elementary_151 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLe (kXReal.fin (0 : MRat)) u) kBool.true → kXReal.eqe (kXReal.omegaArcTan2 u kXReal.negInf) kXReal.pi
    | eq_p31zero9_omega_elementary_152 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt u (kXReal.fin (0 : MRat))) kBool.true → kXReal.eqe (kXReal.omegaArcTan2 u kXReal.negInf) (kXReal.piMultiple ((- 1) : MRat))
    | eq_p31zero9_omega_elementary_153 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt u (kXReal.fin (0 : MRat))) kBool.true → kXReal.eqe (kXReal.omegaArcTan2 (kXReal.fin (0 : MRat)) u) kXReal.pi
    | eq_p31zero9_omega_elementary_154 {u} : kXReal.has_sort u MSort.Real → kXReal.eqe (kXReal.omegaArcTan2 kXReal.negInf u) (kXReal.piMultiple (((- 1) / 2) : MRat))
    | eq_p31zero9_omega_elementary_155 {u} : kXReal.has_sort u MSort.Real → kBool.eqe (kBool.xLt u (kXReal.fin (0 : MRat))) kBool.true → kXReal.eqe (kXReal.omegaArcTan2 u (kXReal.fin (0 : MRat))) (kXReal.piMultiple (((- 1) / 2) : MRat))
    | eq_p31zero9_omega_elementary_156 {u v} : kXReal.has_sort u MSort.Real → kXReal.has_sort v MSort.Real → kBool.eqe (kBool.xLt (kXReal.fin (0 : MRat)) v) kBool.true → kBool.eqe (kBool.eqeq₄ (kBool.xEq u (kXReal.fin (0 : MRat))) kBool.false) kBool.true → kXReal.eqe (kXReal.omegaArcTan2 u v) (kXReal.omegaArcTan (kXReal.omegaDivide u v))
    | eq_p31zero9_omega_elementary_157 {u v} : kXReal.has_sort u MSort.Real → kXReal.has_sort v MSort.Real → kBool.eqe (kBool.xLt (kXReal.fin (0 : MRat)) u) kBool.true → kBool.eqe (kBool.xLt v (kXReal.fin (0 : MRat))) kBool.true → kXReal.eqe (kXReal.omegaArcTan2 u v) (kXReal.omegaAdd (kXReal.omegaArcTan (kXReal.omegaDivide u v)) kXReal.pi)
    | eq_p31zero9_omega_elementary_158 {u v} : kXReal.has_sort u MSort.Real → kXReal.has_sort v MSort.Real → kBool.eqe (kBool.xLt u (kXReal.fin (0 : MRat))) kBool.true → kBool.eqe (kBool.xLt v (kXReal.fin (0 : MRat))) kBool.true → kXReal.eqe (kXReal.omegaArcTan2 u v) (kXReal.omegaSubtract (kXReal.omegaArcTan (kXReal.omegaDivide u v)) kXReal.pi)
    | eq_p31zero9_omega_elementary_159 {x y} : kXReal.has_sort x MSort.XReal → kXReal.has_sort y MSort.XReal → kXReal.eqe (kXReal.omegaArcTan2Pi x y) (kXReal.omegaDivide (kXReal.omegaArcTan2 x y) kXReal.pi)
    | eq_itet {l r} : kXReal.eqe (kXReal.ifthenelsefi kBool.true l r) l
    | eq_itef {l r} : kXReal.eqe (kXReal.ifthenelsefi kBool.false l r) r

  inductive kFormat.eqe: kFormat → kFormat → Prop
    | from_eqa {a b} : kFormat.eqa a b → kFormat.eqe a b
    | symm {a b} : kFormat.eqe a b → kFormat.eqe b a
    | trans {a b c} : kFormat.eqe a b → kFormat.eqe b c → kFormat.eqe a c
    -- Congruence axioms for each operator
    | eqe_Binary {a₀ b₀ a₁ b₁ : MRat} {a₂ b₂ : kSignedness} {a₃ b₃ : kDomain} : a₀ = b₀ → a₁ = b₁ → kSignedness.eqe a₂ b₂ → kDomain.eqe a₃ b₃ → kFormat.eqe (kFormat.Binary a₀ a₁ a₂ a₃) (kFormat.Binary b₀ b₁ b₂ b₃)
    | eqe_at {a₀ b₀ : kFormatSeq} {a₁ b₁ : MRat} : kFormatSeq.eqe a₀ b₀ → a₁ = b₁ → kFormat.eqe (kFormat.«at» a₀ a₁) (kFormat.«at» b₀ b₁)
    -- Equations
    | eq_p31zero9_sequences_zerozero3 {x xs} : kFormat.has_sort x MSort.Format → kFormatSeq.has_sort xs MSort.FormatSeq → kFormat.eqe (kFormat.«at» (kFormatSeq.fcons x xs) (0 : MRat)) x
    | eq_p31zero9_sequences_zerozero4 {x xs n} : kFormat.has_sort x MSort.Format → kFormatSeq.has_sort xs MSort.FormatSeq → MRat.has_sort n MSort.Nat → kBool.eqe (if (0 : MRat) < n then kBool.true else kBool.false) kBool.true → kFormat.eqe (kFormat.«at» (kFormatSeq.fcons x xs) n) (kFormat.«at» xs (if n ≤ (1 : MRat) then (1 : MRat) - n else n - (1 : MRat)))

  inductive kSignedness.eqe: kSignedness → kSignedness → Prop
    | from_eqa {a b} : kSignedness.eqa a b → kSignedness.eqe a b
    | symm {a b} : kSignedness.eqe a b → kSignedness.eqe b a
    | trans {a b c} : kSignedness.eqe a b → kSignedness.eqe b c → kSignedness.eqe a c
    -- Congruence axioms for each operator
    | eqe_SignednessOf {a b : kFormat} : kFormat.eqe a b → kSignedness.eqe (kSignedness.SignednessOf a) (kSignedness.SignednessOf b)
    -- Equations
    | eq_p31zero9_format_core_zerozero5 {k p s₁ d} : MRat.has_sort k MSort.Int → MRat.has_sort p MSort.Int → kSignedness.has_sort s₁ MSort.Signedness → kDomain.has_sort d MSort.Domain → kBool.eqe (kBool.validFormat (kFormat.Binary k p s₁ d)) kBool.true → kSignedness.eqe (kSignedness.SignednessOf (kFormat.Binary k p s₁ d)) s₁
    | eq_p31zero9_format_core_zero2zero : kSignedness.eqe (kSignedness.SignednessOf kFormat.binary64) kSignedness.Signed
    | eq_p31zero9_format_core_zero28 : kSignedness.eqe (kSignedness.SignednessOf kFormat.binary32) kSignedness.Signed
    | eq_p31zero9_format_core_zero36 : kSignedness.eqe (kSignedness.SignednessOf kFormat.binary16) kSignedness.Signed
    | eq_p31zero9_format_core_zero44 : kSignedness.eqe (kSignedness.SignednessOf kFormat.BFloat16) kSignedness.Signed

  inductive kDomain.eqe: kDomain → kDomain → Prop
    | from_eqa {a b} : kDomain.eqa a b → kDomain.eqe a b
    | symm {a b} : kDomain.eqe a b → kDomain.eqe b a
    | trans {a b c} : kDomain.eqe a b → kDomain.eqe b c → kDomain.eqe a c
    -- Congruence axioms for each operator
    | eqe_DomainOf {a b : kFormat} : kFormat.eqe a b → kDomain.eqe (kDomain.DomainOf a) (kDomain.DomainOf b)
    -- Equations
    | eq_p31zero9_format_core_zerozero6 {k p s₁ d} : MRat.has_sort k MSort.Int → MRat.has_sort p MSort.Int → kSignedness.has_sort s₁ MSort.Signedness → kDomain.has_sort d MSort.Domain → kBool.eqe (kBool.validFormat (kFormat.Binary k p s₁ d)) kBool.true → kDomain.eqe (kDomain.DomainOf (kFormat.Binary k p s₁ d)) d
    | eq_p31zero9_format_core_zero21 : kDomain.eqe (kDomain.DomainOf kFormat.binary64) kDomain.Extended
    | eq_p31zero9_format_core_zero29 : kDomain.eqe (kDomain.DomainOf kFormat.binary32) kDomain.Extended
    | eq_p31zero9_format_core_zero37 : kDomain.eqe (kDomain.DomainOf kFormat.binary16) kDomain.Extended
    | eq_p31zero9_format_core_zero45 : kDomain.eqe (kDomain.DomainOf kFormat.BFloat16) kDomain.Extended

  inductive kBoundQuery.eqe: kBoundQuery → kBoundQuery → Prop
    | from_eqa {a b} : kBoundQuery.eqa a b → kBoundQuery.eqe a b
    | symm {a b} : kBoundQuery.eqe a b → kBoundQuery.eqe b a
    | trans {a b c} : kBoundQuery.eqe a b → kBoundQuery.eqe b c → kBoundQuery.eqe a c
    -- Congruence axioms for each operator

  inductive kRandomSeq.eqe: kRandomSeq → kRandomSeq → Prop
    | from_eqa {a b} : kRandomSeq.eqa a b → kRandomSeq.eqe a b
    | symm {a b} : kRandomSeq.eqe a b → kRandomSeq.eqe b a
    | trans {a b c} : kRandomSeq.eqe a b → kRandomSeq.eqe b c → kRandomSeq.eqe a c
    -- Congruence axioms for each operator
    | eqe_rcons {a₀ b₀ : MRat} {a₁ b₁ : kRandomSeq} : a₀ = b₀ → kRandomSeq.eqe a₁ b₁ → kRandomSeq.eqe (kRandomSeq.rcons a₀ a₁) (kRandomSeq.rcons b₀ b₁)

  inductive kBlockRoundMode.eqe: kBlockRoundMode → kBlockRoundMode → Prop
    | from_eqa {a b} : kBlockRoundMode.eqa a b → kBlockRoundMode.eqe a b
    | symm {a b} : kBlockRoundMode.eqe a b → kBlockRoundMode.eqe b a
    | trans {a b c} : kBlockRoundMode.eqe a b → kBlockRoundMode.eqe b c → kBlockRoundMode.eqe a c
    -- Congruence axioms for each operator
    | eqe_StochasticA {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBlockRoundMode.eqe (kBlockRoundMode.StochasticA a₀ a₁) (kBlockRoundMode.StochasticA b₀ b₁)
    | eqe_StochasticB {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBlockRoundMode.eqe (kBlockRoundMode.StochasticB a₀ a₁) (kBlockRoundMode.StochasticB b₀ b₁)
    | eqe_StochasticC {a₀ b₀ a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kBlockRoundMode.eqe (kBlockRoundMode.StochasticC a₀ a₁) (kBlockRoundMode.StochasticC b₀ b₁)
    | eqe_BlockStochasticA {a₀ b₀ : MRat} {a₁ b₁ : kRandomSeq} : a₀ = b₀ → kRandomSeq.eqe a₁ b₁ → kBlockRoundMode.eqe (kBlockRoundMode.BlockStochasticA a₀ a₁) (kBlockRoundMode.BlockStochasticA b₀ b₁)
    | eqe_BlockStochasticB {a₀ b₀ : MRat} {a₁ b₁ : kRandomSeq} : a₀ = b₀ → kRandomSeq.eqe a₁ b₁ → kBlockRoundMode.eqe (kBlockRoundMode.BlockStochasticB a₀ a₁) (kBlockRoundMode.BlockStochasticB b₀ b₁)
    | eqe_BlockStochasticC {a₀ b₀ : MRat} {a₁ b₁ : kRandomSeq} : a₀ = b₀ → kRandomSeq.eqe a₁ b₁ → kBlockRoundMode.eqe (kBlockRoundMode.BlockStochasticC a₀ a₁) (kBlockRoundMode.BlockStochasticC b₀ b₁)
    | eqe_RoundOf {a b : kProjSpec} : kProjSpec.eqe a b → kBlockRoundMode.eqe (kBlockRoundMode.RoundOf a) (kBlockRoundMode.RoundOf b)
    -- Equations
    | eq_p31zero9_projection_spec_zero29 {m s₁} : kBlockRoundMode.has_sort m MSort.RoundMode → kSatMode.has_sort s₁ MSort.SatMode → kBool.eqe (kBool.validProjection (kProjSpec.proj m s₁)) kBool.true → kBlockRoundMode.eqe (kBlockRoundMode.RoundOf (kProjSpec.proj m s₁)) m

  inductive kSatMode.eqe: kSatMode → kSatMode → Prop
    | from_eqa {a b} : kSatMode.eqa a b → kSatMode.eqe a b
    | symm {a b} : kSatMode.eqe a b → kSatMode.eqe b a
    | trans {a b c} : kSatMode.eqe a b → kSatMode.eqe b c → kSatMode.eqe a c
    -- Congruence axioms for each operator
    | eqe_SatOf {a b : kProjSpec} : kProjSpec.eqe a b → kSatMode.eqe (kSatMode.SatOf a) (kSatMode.SatOf b)
    -- Equations
    | eq_p31zero9_projection_spec_zero3zero {m s₁} : kBlockRoundMode.has_sort m MSort.RoundMode → kSatMode.has_sort s₁ MSort.SatMode → kBool.eqe (kBool.validProjection (kProjSpec.proj m s₁)) kBool.true → kSatMode.eqe (kSatMode.SatOf (kProjSpec.proj m s₁)) s₁

  inductive kProjSpec.eqe: kProjSpec → kProjSpec → Prop
    | from_eqa {a b} : kProjSpec.eqa a b → kProjSpec.eqe a b
    | symm {a b} : kProjSpec.eqe a b → kProjSpec.eqe b a
    | trans {a b c} : kProjSpec.eqe a b → kProjSpec.eqe b c → kProjSpec.eqe a c
    -- Congruence axioms for each operator
    | eqe_proj {a₀ b₀ : kBlockRoundMode} {a₁ b₁ : kSatMode} : kBlockRoundMode.eqe a₀ b₀ → kSatMode.eqe a₁ b₁ → kProjSpec.eqe (kProjSpec.proj a₀ a₁) (kProjSpec.proj b₀ b₁)
    | eqe_projectionAt {a₀ b₀ : kBlockProjSpec} {a₁ b₁ : MRat} : kBlockProjSpec.eqe a₀ b₀ → a₁ = b₁ → kProjSpec.eqe (kProjSpec.projectionAt a₀ a₁) (kProjSpec.projectionAt b₀ b₁)
    -- Equations
    | eq_p31zero9_projection_spec_zero16 {n rs s₁ j} : MRat.has_sort n MSort.Int → kRandomSeq.has_sort rs MSort.RandomSeq → kSatMode.has_sort s₁ MSort.SatMode → MRat.has_sort j MSort.Nat → kBool.eqe (kBool.validRandoms n rs) kBool.true → kBool.eqe (if j < (MRat.length₀ rs) then kBool.true else kBool.false) kBool.true → kProjSpec.eqe (kProjSpec.projectionAt (kBlockProjSpec.bproj (kBlockRoundMode.BlockStochasticA n rs) s₁) j) (kProjSpec.proj (kBlockRoundMode.StochasticA n (MRat.at₀ rs j)) s₁)
    | eq_p31zero9_projection_spec_zero21 {n rs s₁ j} : MRat.has_sort n MSort.Int → kRandomSeq.has_sort rs MSort.RandomSeq → kSatMode.has_sort s₁ MSort.SatMode → MRat.has_sort j MSort.Nat → kBool.eqe (kBool.validRandoms n rs) kBool.true → kBool.eqe (if j < (MRat.length₀ rs) then kBool.true else kBool.false) kBool.true → kProjSpec.eqe (kProjSpec.projectionAt (kBlockProjSpec.bproj (kBlockRoundMode.BlockStochasticB n rs) s₁) j) (kProjSpec.proj (kBlockRoundMode.StochasticB n (MRat.at₀ rs j)) s₁)
    | eq_p31zero9_projection_spec_zero26 {n rs s₁ j} : MRat.has_sort n MSort.Int → kRandomSeq.has_sort rs MSort.RandomSeq → kSatMode.has_sort s₁ MSort.SatMode → MRat.has_sort j MSort.Nat → kBool.eqe (kBool.validRandoms n rs) kBool.true → kBool.eqe (if j < (MRat.length₀ rs) then kBool.true else kBool.false) kBool.true → kProjSpec.eqe (kProjSpec.projectionAt (kBlockProjSpec.bproj (kBlockRoundMode.BlockStochasticC n rs) s₁) j) (kProjSpec.proj (kBlockRoundMode.StochasticC n (MRat.at₀ rs j)) s₁)
    | eq_p31zero9_projection_spec_zero34 {m s₁ j} : kBlockRoundMode.has_sort m MSort.RoundMode → kSatMode.has_sort s₁ MSort.SatMode → MRat.has_sort j MSort.Nat → kBool.eqe (kBool.validRound m) kBool.true → kBool.eqe (kBool.deterministic m) kBool.true → kProjSpec.eqe (kProjSpec.projectionAt (kBlockProjSpec.bproj m s₁) j) (kProjSpec.proj m s₁)

  inductive kBlockProjSpec.eqe: kBlockProjSpec → kBlockProjSpec → Prop
    | from_eqa {a b} : kBlockProjSpec.eqa a b → kBlockProjSpec.eqe a b
    | symm {a b} : kBlockProjSpec.eqe a b → kBlockProjSpec.eqe b a
    | trans {a b c} : kBlockProjSpec.eqe a b → kBlockProjSpec.eqe b c → kBlockProjSpec.eqe a c
    -- Congruence axioms for each operator
    | eqe_bproj {a₀ b₀ : kBlockRoundMode} {a₁ b₁ : kSatMode} : kBlockRoundMode.eqe a₀ b₀ → kSatMode.eqe a₁ b₁ → kBlockProjSpec.eqe (kBlockProjSpec.bproj a₀ a₁) (kBlockProjSpec.bproj b₀ b₁)
    | eqe_singletonLift {a b : kProjSpec} : kProjSpec.eqe a b → kBlockProjSpec.eqe (kBlockProjSpec.singletonLift a) (kBlockProjSpec.singletonLift b)
    -- Equations
    | eq_p31zero9_projection_spec_zero17 {n r s₁} : MRat.has_sort n MSort.Int → MRat.has_sort r MSort.Int → kSatMode.has_sort s₁ MSort.SatMode → kBool.eqe (kBool.validRound (kBlockRoundMode.StochasticA n r)) kBool.true → kBlockProjSpec.eqe (kBlockProjSpec.singletonLift (kProjSpec.proj (kBlockRoundMode.StochasticA n r) s₁)) (kBlockProjSpec.bproj (kBlockRoundMode.BlockStochasticA n (kRandomSeq.rcons r kRandomSeq.rnil)) s₁)
    | eq_p31zero9_projection_spec_zero22 {n r s₁} : MRat.has_sort n MSort.Int → MRat.has_sort r MSort.Int → kSatMode.has_sort s₁ MSort.SatMode → kBool.eqe (kBool.validRound (kBlockRoundMode.StochasticB n r)) kBool.true → kBlockProjSpec.eqe (kBlockProjSpec.singletonLift (kProjSpec.proj (kBlockRoundMode.StochasticB n r) s₁)) (kBlockProjSpec.bproj (kBlockRoundMode.BlockStochasticB n (kRandomSeq.rcons r kRandomSeq.rnil)) s₁)
    | eq_p31zero9_projection_spec_zero27 {n r s₁} : MRat.has_sort n MSort.Int → MRat.has_sort r MSort.Int → kSatMode.has_sort s₁ MSort.SatMode → kBool.eqe (kBool.validRound (kBlockRoundMode.StochasticC n r)) kBool.true → kBlockProjSpec.eqe (kBlockProjSpec.singletonLift (kProjSpec.proj (kBlockRoundMode.StochasticC n r) s₁)) (kBlockProjSpec.bproj (kBlockRoundMode.BlockStochasticC n (kRandomSeq.rcons r kRandomSeq.rnil)) s₁)
    | eq_p31zero9_projection_spec_zero35 {m s₁} : kBlockRoundMode.has_sort m MSort.RoundMode → kSatMode.has_sort s₁ MSort.SatMode → kBool.eqe (kBool.validRound m) kBool.true → kBool.eqe (kBool.deterministic m) kBool.true → kBlockProjSpec.eqe (kBlockProjSpec.singletonLift (kProjSpec.proj m s₁)) (kBlockProjSpec.bproj m s₁)

  inductive kXSeq.eqe: kXSeq → kXSeq → Prop
    | from_eqa {a b} : kXSeq.eqa a b → kXSeq.eqe a b
    | symm {a b} : kXSeq.eqe a b → kXSeq.eqe b a
    | trans {a b c} : kXSeq.eqe a b → kXSeq.eqe b c → kXSeq.eqe a c
    -- Congruence axioms for each operator
    | eqe_xcons {a₀ b₀ : kXReal} {a₁ b₁ : kXSeq} : kXReal.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.xcons a₀ a₁) (kXSeq.xcons b₀ b₁)
    | eqe_decodeElements {a₀ b₀ : kFormat} {a₁ b₁ : kCodeSeq} : kFormat.eqe a₀ b₀ → kCodeSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.decodeElements a₀ a₁) (kXSeq.decodeElements b₀ b₁)
    | eqe_multiplyElements {a₀ b₀ : kXReal} {a₁ b₁ : kXSeq} : kXReal.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.multiplyElements a₀ a₁) (kXSeq.multiplyElements b₀ b₁)
    | eqe_blockDecode {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ : kFormat} {a₃ b₃ : MRat} {a₄ b₄ : kCodeSeq} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → a₃ = b₃ → kCodeSeq.eqe a₄ b₄ → kXSeq.eqe (kXSeq.blockDecode a₀ a₁ a₂ a₃ a₄) (kXSeq.blockDecode b₀ b₁ b₂ b₃ b₄)
    | eqe_absElements {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.absElements a) (kXSeq.absElements b)
    | eqe_pairProducts {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.pairProducts a₀ a₁) (kXSeq.pairProducts b₀ b₁)
    | eqe_mapConvert {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapConvert a) (kXSeq.mapConvert b)
    | eqe_mapAbs {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapAbs a) (kXSeq.mapAbs b)
    | eqe_mapNegate {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapNegate a) (kXSeq.mapNegate b)
    | eqe_mapCopySign {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.mapCopySign a₀ a₁) (kXSeq.mapCopySign b₀ b₁)
    | eqe_mapAdd {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.mapAdd a₀ a₁) (kXSeq.mapAdd b₀ b₁)
    | eqe_mapSubtract {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.mapSubtract a₀ a₁) (kXSeq.mapSubtract b₀ b₁)
    | eqe_mapMultiply {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.mapMultiply a₀ a₁) (kXSeq.mapMultiply b₀ b₁)
    | eqe_mapDivide {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.mapDivide a₀ a₁) (kXSeq.mapDivide b₀ b₁)
    | eqe_mapFMA {a₀ b₀ a₁ b₁ a₂ b₂ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe a₂ b₂ → kXSeq.eqe (kXSeq.mapFMA a₀ a₁ a₂) (kXSeq.mapFMA b₀ b₁ b₂)
    | eqe_mapFAA {a₀ b₀ a₁ b₁ a₂ b₂ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe a₂ b₂ → kXSeq.eqe (kXSeq.mapFAA a₀ a₁ a₂) (kXSeq.mapFAA b₀ b₁ b₂)
    | eqe_mapRecip {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapRecip a) (kXSeq.mapRecip b)
    | eqe_mapMinimum {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.mapMinimum a₀ a₁) (kXSeq.mapMinimum b₀ b₁)
    | eqe_mapMaximum {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.mapMaximum a₀ a₁) (kXSeq.mapMaximum b₀ b₁)
    | eqe_mapMinimumNumber {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.mapMinimumNumber a₀ a₁) (kXSeq.mapMinimumNumber b₀ b₁)
    | eqe_mapMaximumNumber {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.mapMaximumNumber a₀ a₁) (kXSeq.mapMaximumNumber b₀ b₁)
    | eqe_mapMinimumMagnitude {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.mapMinimumMagnitude a₀ a₁) (kXSeq.mapMinimumMagnitude b₀ b₁)
    | eqe_mapMaximumMagnitude {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.mapMaximumMagnitude a₀ a₁) (kXSeq.mapMaximumMagnitude b₀ b₁)
    | eqe_mapMinimumMagnitudeNumber {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.mapMinimumMagnitudeNumber a₀ a₁) (kXSeq.mapMinimumMagnitudeNumber b₀ b₁)
    | eqe_mapMaximumMagnitudeNumber {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.mapMaximumMagnitudeNumber a₀ a₁) (kXSeq.mapMaximumMagnitudeNumber b₀ b₁)
    | eqe_mapMinimumFinite {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.mapMinimumFinite a₀ a₁) (kXSeq.mapMinimumFinite b₀ b₁)
    | eqe_mapMaximumFinite {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.mapMaximumFinite a₀ a₁) (kXSeq.mapMaximumFinite b₀ b₁)
    | eqe_mapClamp {a₀ b₀ a₁ b₁ a₂ b₂ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe a₂ b₂ → kXSeq.eqe (kXSeq.mapClamp a₀ a₁ a₂) (kXSeq.mapClamp b₀ b₁ b₂)
    | eqe_mapSqrt {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapSqrt a) (kXSeq.mapSqrt b)
    | eqe_mapRSqrt {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapRSqrt a) (kXSeq.mapRSqrt b)
    | eqe_mapExp {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapExp a) (kXSeq.mapExp b)
    | eqe_mapExp2 {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapExp2 a) (kXSeq.mapExp2 b)
    | eqe_mapLog {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapLog a) (kXSeq.mapLog b)
    | eqe_mapLog2 {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapLog2 a) (kXSeq.mapLog2 b)
    | eqe_mapLogOnePlus {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapLogOnePlus a) (kXSeq.mapLogOnePlus b)
    | eqe_mapExpMinusOne {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapExpMinusOne a) (kXSeq.mapExpMinusOne b)
    | eqe_mapSin {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapSin a) (kXSeq.mapSin b)
    | eqe_mapCos {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapCos a) (kXSeq.mapCos b)
    | eqe_mapTan {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapTan a) (kXSeq.mapTan b)
    | eqe_mapArcSin {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapArcSin a) (kXSeq.mapArcSin b)
    | eqe_mapArcCos {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapArcCos a) (kXSeq.mapArcCos b)
    | eqe_mapArcTan {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapArcTan a) (kXSeq.mapArcTan b)
    | eqe_mapSinh {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapSinh a) (kXSeq.mapSinh b)
    | eqe_mapCosh {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapCosh a) (kXSeq.mapCosh b)
    | eqe_mapTanh {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapTanh a) (kXSeq.mapTanh b)
    | eqe_mapArcSinh {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapArcSinh a) (kXSeq.mapArcSinh b)
    | eqe_mapArcCosh {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapArcCosh a) (kXSeq.mapArcCosh b)
    | eqe_mapArcTanh {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapArcTanh a) (kXSeq.mapArcTanh b)
    | eqe_mapSinPi {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapSinPi a) (kXSeq.mapSinPi b)
    | eqe_mapCosPi {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapCosPi a) (kXSeq.mapCosPi b)
    | eqe_mapTanPi {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapTanPi a) (kXSeq.mapTanPi b)
    | eqe_mapArcSinPi {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapArcSinPi a) (kXSeq.mapArcSinPi b)
    | eqe_mapArcCosPi {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapArcCosPi a) (kXSeq.mapArcCosPi b)
    | eqe_mapArcTanPi {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapArcTanPi a) (kXSeq.mapArcTanPi b)
    | eqe_mapSoftplus {a b : kXSeq} : kXSeq.eqe a b → kXSeq.eqe (kXSeq.mapSoftplus a) (kXSeq.mapSoftplus b)
    | eqe_mapHypot {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.mapHypot a₀ a₁) (kXSeq.mapHypot b₀ b₁)
    | eqe_mapArcTan2 {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.mapArcTan2 a₀ a₁) (kXSeq.mapArcTan2 b₀ b₁)
    | eqe_mapArcTan2Pi {a₀ b₀ a₁ b₁ : kXSeq} : kXSeq.eqe a₀ b₀ → kXSeq.eqe a₁ b₁ → kXSeq.eqe (kXSeq.mapArcTan2Pi a₀ a₁) (kXSeq.mapArcTan2Pi b₀ b₁)
    -- Equations
    | eq_p31zero9_block_core_zerozero4 {fx} : kFormat.has_sort fx MSort.Format → kBool.eqe (kBool.validFormat fx) kBool.true → kXSeq.eqe (kXSeq.decodeElements fx kCodeSeq.cnil) kXSeq.xnil
    | eq_p31zero9_block_core_zerozero5 {fx c cs} : kFormat.has_sort fx MSort.Format → MRat.has_sort c MSort.Int → kCodeSeq.has_sort cs MSort.CodeSeq → kBool.eqe (kBool.validCodes fx (kCodeSeq.ccons c cs)) kBool.true → kXSeq.eqe (kXSeq.decodeElements fx (kCodeSeq.ccons c cs)) (kXSeq.xcons (kXReal.decode fx c) (kXSeq.decodeElements fx cs))
    | eq_p31zero9_block_core_zerozero6 {x} : kXReal.has_sort x MSort.XReal → kXSeq.eqe (kXSeq.multiplyElements x kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_block_core_zerozero7 {x y xs} : kXReal.has_sort x MSort.XReal → kXReal.has_sort y MSort.XReal → kXSeq.has_sort xs MSort.XSeq → kXSeq.eqe (kXSeq.multiplyElements x (kXSeq.xcons y xs)) (kXSeq.xcons (kXReal.omegaMultiply x y) (kXSeq.multiplyElements x xs))
    | eq_p31zero9_block_core_zerozero8 {b fs fx s₁ cs} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs MSort.Format → kFormat.has_sort fx MSort.Format → MRat.has_sort s₁ MSort.Int → kCodeSeq.has_sort cs MSort.CodeSeq → kBool.eqe (kBool.validBlock b fs fx s₁ cs) kBool.true → kXSeq.eqe (kXSeq.blockDecode b fs fx s₁ cs) (kXSeq.multiplyElements (kXReal.decode fs s₁) (kXSeq.decodeElements fx cs))
    | eq_p31zero9_block_ops_zerozero7 : kXSeq.eqe (kXSeq.absElements kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_block_ops_zerozero8 {x xs} : kXReal.has_sort x MSort.XReal → kXSeq.has_sort xs MSort.XSeq → kXSeq.eqe (kXSeq.absElements (kXSeq.xcons x xs)) (kXSeq.xcons (kXReal.omegaAbs x) (kXSeq.absElements xs))
    | eq_p31zero9_block_ops_zerozero9 : kXSeq.eqe (kXSeq.pairProducts kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_block_ops_zero1zero {x xs y ys} : kXReal.has_sort x MSort.XReal → kXSeq.has_sort xs MSort.XSeq → kXReal.has_sort y MSort.XReal → kXSeq.has_sort ys MSort.XSeq → kXSeq.eqe (kXSeq.pairProducts (kXSeq.xcons x xs) (kXSeq.xcons y ys)) (kXSeq.xcons (kXReal.omegaMultiply x y) (kXSeq.pairProducts xs ys))
    | eq_p31zero9_map_Convert_nil : kXSeq.eqe (kXSeq.mapConvert kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Convert_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapConvert (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaConvert x1) (kXSeq.mapConvert xs1))
    | eq_p31zero9_map_Abs_nil : kXSeq.eqe (kXSeq.mapAbs kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Abs_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapAbs (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaAbs x1) (kXSeq.mapAbs xs1))
    | eq_p31zero9_map_Negate_nil : kXSeq.eqe (kXSeq.mapNegate kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Negate_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapNegate (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaNegate x1) (kXSeq.mapNegate xs1))
    | eq_p31zero9_map_CopySign_nil : kXSeq.eqe (kXSeq.mapCopySign kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_CopySign_cons {x1 xs1 x2 xs2} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXSeq.eqe (kXSeq.mapCopySign (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2)) (kXSeq.xcons (kXReal.omegaCopySign x1 x2) (kXSeq.mapCopySign xs1 xs2))
    | eq_p31zero9_map_Add_nil : kXSeq.eqe (kXSeq.mapAdd kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Add_cons {x1 xs1 x2 xs2} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXSeq.eqe (kXSeq.mapAdd (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2)) (kXSeq.xcons (kXReal.omegaAdd x1 x2) (kXSeq.mapAdd xs1 xs2))
    | eq_p31zero9_map_Subtract_nil : kXSeq.eqe (kXSeq.mapSubtract kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Subtract_cons {x1 xs1 x2 xs2} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXSeq.eqe (kXSeq.mapSubtract (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2)) (kXSeq.xcons (kXReal.omegaSubtract x1 x2) (kXSeq.mapSubtract xs1 xs2))
    | eq_p31zero9_map_Multiply_nil : kXSeq.eqe (kXSeq.mapMultiply kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Multiply_cons {x1 xs1 x2 xs2} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXSeq.eqe (kXSeq.mapMultiply (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2)) (kXSeq.xcons (kXReal.omegaMultiply x1 x2) (kXSeq.mapMultiply xs1 xs2))
    | eq_p31zero9_map_Divide_nil : kXSeq.eqe (kXSeq.mapDivide kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Divide_cons {x1 xs1 x2 xs2} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXSeq.eqe (kXSeq.mapDivide (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2)) (kXSeq.xcons (kXReal.omegaDivide x1 x2) (kXSeq.mapDivide xs1 xs2))
    | eq_p31zero9_map_FMA_nil : kXSeq.eqe (kXSeq.mapFMA kXSeq.xnil kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_FMA_cons {x1 xs1 x2 xs2 x3 xs3} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXReal.has_sort x3 MSort.XReal → kXSeq.has_sort xs3 MSort.XSeq → kXSeq.eqe (kXSeq.mapFMA (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2) (kXSeq.xcons x3 xs3)) (kXSeq.xcons (kXReal.omegaFMA x1 x2 x3) (kXSeq.mapFMA xs1 xs2 xs3))
    | eq_p31zero9_map_FAA_nil : kXSeq.eqe (kXSeq.mapFAA kXSeq.xnil kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_FAA_cons {x1 xs1 x2 xs2 x3 xs3} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXReal.has_sort x3 MSort.XReal → kXSeq.has_sort xs3 MSort.XSeq → kXSeq.eqe (kXSeq.mapFAA (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2) (kXSeq.xcons x3 xs3)) (kXSeq.xcons (kXReal.omegaFAA x1 x2 x3) (kXSeq.mapFAA xs1 xs2 xs3))
    | eq_p31zero9_map_Recip_nil : kXSeq.eqe (kXSeq.mapRecip kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Recip_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapRecip (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaRecip x1) (kXSeq.mapRecip xs1))
    | eq_p31zero9_map_Minimum_nil : kXSeq.eqe (kXSeq.mapMinimum kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Minimum_cons {x1 xs1 x2 xs2} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXSeq.eqe (kXSeq.mapMinimum (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2)) (kXSeq.xcons (kXReal.omegaMinimum x1 x2) (kXSeq.mapMinimum xs1 xs2))
    | eq_p31zero9_map_Maximum_nil : kXSeq.eqe (kXSeq.mapMaximum kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Maximum_cons {x1 xs1 x2 xs2} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXSeq.eqe (kXSeq.mapMaximum (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2)) (kXSeq.xcons (kXReal.omegaMaximum x1 x2) (kXSeq.mapMaximum xs1 xs2))
    | eq_p31zero9_map_MinimumNumber_nil : kXSeq.eqe (kXSeq.mapMinimumNumber kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_MinimumNumber_cons {x1 xs1 x2 xs2} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXSeq.eqe (kXSeq.mapMinimumNumber (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2)) (kXSeq.xcons (kXReal.omegaMinimumNumber x1 x2) (kXSeq.mapMinimumNumber xs1 xs2))
    | eq_p31zero9_map_MaximumNumber_nil : kXSeq.eqe (kXSeq.mapMaximumNumber kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_MaximumNumber_cons {x1 xs1 x2 xs2} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXSeq.eqe (kXSeq.mapMaximumNumber (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2)) (kXSeq.xcons (kXReal.omegaMaximumNumber x1 x2) (kXSeq.mapMaximumNumber xs1 xs2))
    | eq_p31zero9_map_MinimumMagnitude_nil : kXSeq.eqe (kXSeq.mapMinimumMagnitude kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_MinimumMagnitude_cons {x1 xs1 x2 xs2} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXSeq.eqe (kXSeq.mapMinimumMagnitude (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2)) (kXSeq.xcons (kXReal.omegaMinimumMagnitude x1 x2) (kXSeq.mapMinimumMagnitude xs1 xs2))
    | eq_p31zero9_map_MaximumMagnitude_nil : kXSeq.eqe (kXSeq.mapMaximumMagnitude kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_MaximumMagnitude_cons {x1 xs1 x2 xs2} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXSeq.eqe (kXSeq.mapMaximumMagnitude (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2)) (kXSeq.xcons (kXReal.omegaMaximumMagnitude x1 x2) (kXSeq.mapMaximumMagnitude xs1 xs2))
    | eq_p31zero9_map_MinimumMagnitudeNumber_nil : kXSeq.eqe (kXSeq.mapMinimumMagnitudeNumber kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_MinimumMagnitudeNumber_cons {x1 xs1 x2 xs2} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXSeq.eqe (kXSeq.mapMinimumMagnitudeNumber (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2)) (kXSeq.xcons (kXReal.omegaMinimumMagnitudeNumber x1 x2) (kXSeq.mapMinimumMagnitudeNumber xs1 xs2))
    | eq_p31zero9_map_MaximumMagnitudeNumber_nil : kXSeq.eqe (kXSeq.mapMaximumMagnitudeNumber kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_MaximumMagnitudeNumber_cons {x1 xs1 x2 xs2} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXSeq.eqe (kXSeq.mapMaximumMagnitudeNumber (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2)) (kXSeq.xcons (kXReal.omegaMaximumMagnitudeNumber x1 x2) (kXSeq.mapMaximumMagnitudeNumber xs1 xs2))
    | eq_p31zero9_map_MinimumFinite_nil : kXSeq.eqe (kXSeq.mapMinimumFinite kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_MinimumFinite_cons {x1 xs1 x2 xs2} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXSeq.eqe (kXSeq.mapMinimumFinite (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2)) (kXSeq.xcons (kXReal.omegaMinimumFinite x1 x2) (kXSeq.mapMinimumFinite xs1 xs2))
    | eq_p31zero9_map_MaximumFinite_nil : kXSeq.eqe (kXSeq.mapMaximumFinite kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_MaximumFinite_cons {x1 xs1 x2 xs2} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXSeq.eqe (kXSeq.mapMaximumFinite (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2)) (kXSeq.xcons (kXReal.omegaMaximumFinite x1 x2) (kXSeq.mapMaximumFinite xs1 xs2))
    | eq_p31zero9_map_Clamp_nil : kXSeq.eqe (kXSeq.mapClamp kXSeq.xnil kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Clamp_cons {x1 xs1 x2 xs2 x3 xs3} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXReal.has_sort x3 MSort.XReal → kXSeq.has_sort xs3 MSort.XSeq → kXSeq.eqe (kXSeq.mapClamp (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2) (kXSeq.xcons x3 xs3)) (kXSeq.xcons (kXReal.omegaClamp x1 x2 x3) (kXSeq.mapClamp xs1 xs2 xs3))
    | eq_p31zero9_map_Sqrt_nil : kXSeq.eqe (kXSeq.mapSqrt kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Sqrt_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapSqrt (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaSqrt x1) (kXSeq.mapSqrt xs1))
    | eq_p31zero9_map_RSqrt_nil : kXSeq.eqe (kXSeq.mapRSqrt kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_RSqrt_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapRSqrt (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaRSqrt x1) (kXSeq.mapRSqrt xs1))
    | eq_p31zero9_map_Exp_nil : kXSeq.eqe (kXSeq.mapExp kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Exp_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapExp (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaExp x1) (kXSeq.mapExp xs1))
    | eq_p31zero9_map_Exp2_nil : kXSeq.eqe (kXSeq.mapExp2 kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Exp2_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapExp2 (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaExp2 x1) (kXSeq.mapExp2 xs1))
    | eq_p31zero9_map_Log_nil : kXSeq.eqe (kXSeq.mapLog kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Log_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapLog (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaLog x1) (kXSeq.mapLog xs1))
    | eq_p31zero9_map_Log2_nil : kXSeq.eqe (kXSeq.mapLog2 kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Log2_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapLog2 (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaLog2 x1) (kXSeq.mapLog2 xs1))
    | eq_p31zero9_map_LogOnePlus_nil : kXSeq.eqe (kXSeq.mapLogOnePlus kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_LogOnePlus_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapLogOnePlus (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaLogOnePlus x1) (kXSeq.mapLogOnePlus xs1))
    | eq_p31zero9_map_ExpMinusOne_nil : kXSeq.eqe (kXSeq.mapExpMinusOne kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_ExpMinusOne_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapExpMinusOne (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaExpMinusOne x1) (kXSeq.mapExpMinusOne xs1))
    | eq_p31zero9_map_Sin_nil : kXSeq.eqe (kXSeq.mapSin kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Sin_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapSin (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaSin x1) (kXSeq.mapSin xs1))
    | eq_p31zero9_map_Cos_nil : kXSeq.eqe (kXSeq.mapCos kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Cos_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapCos (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaCos x1) (kXSeq.mapCos xs1))
    | eq_p31zero9_map_Tan_nil : kXSeq.eqe (kXSeq.mapTan kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Tan_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapTan (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaTan x1) (kXSeq.mapTan xs1))
    | eq_p31zero9_map_ArcSin_nil : kXSeq.eqe (kXSeq.mapArcSin kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_ArcSin_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapArcSin (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaArcSin x1) (kXSeq.mapArcSin xs1))
    | eq_p31zero9_map_ArcCos_nil : kXSeq.eqe (kXSeq.mapArcCos kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_ArcCos_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapArcCos (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaArcCos x1) (kXSeq.mapArcCos xs1))
    | eq_p31zero9_map_ArcTan_nil : kXSeq.eqe (kXSeq.mapArcTan kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_ArcTan_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapArcTan (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaArcTan x1) (kXSeq.mapArcTan xs1))
    | eq_p31zero9_map_Sinh_nil : kXSeq.eqe (kXSeq.mapSinh kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Sinh_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapSinh (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaSinh x1) (kXSeq.mapSinh xs1))
    | eq_p31zero9_map_Cosh_nil : kXSeq.eqe (kXSeq.mapCosh kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Cosh_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapCosh (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaCosh x1) (kXSeq.mapCosh xs1))
    | eq_p31zero9_map_Tanh_nil : kXSeq.eqe (kXSeq.mapTanh kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Tanh_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapTanh (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaTanh x1) (kXSeq.mapTanh xs1))
    | eq_p31zero9_map_ArcSinh_nil : kXSeq.eqe (kXSeq.mapArcSinh kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_ArcSinh_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapArcSinh (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaArcSinh x1) (kXSeq.mapArcSinh xs1))
    | eq_p31zero9_map_ArcCosh_nil : kXSeq.eqe (kXSeq.mapArcCosh kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_ArcCosh_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapArcCosh (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaArcCosh x1) (kXSeq.mapArcCosh xs1))
    | eq_p31zero9_map_ArcTanh_nil : kXSeq.eqe (kXSeq.mapArcTanh kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_ArcTanh_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapArcTanh (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaArcTanh x1) (kXSeq.mapArcTanh xs1))
    | eq_p31zero9_map_SinPi_nil : kXSeq.eqe (kXSeq.mapSinPi kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_SinPi_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapSinPi (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaSinPi x1) (kXSeq.mapSinPi xs1))
    | eq_p31zero9_map_CosPi_nil : kXSeq.eqe (kXSeq.mapCosPi kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_CosPi_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapCosPi (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaCosPi x1) (kXSeq.mapCosPi xs1))
    | eq_p31zero9_map_TanPi_nil : kXSeq.eqe (kXSeq.mapTanPi kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_TanPi_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapTanPi (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaTanPi x1) (kXSeq.mapTanPi xs1))
    | eq_p31zero9_map_ArcSinPi_nil : kXSeq.eqe (kXSeq.mapArcSinPi kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_ArcSinPi_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapArcSinPi (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaArcSinPi x1) (kXSeq.mapArcSinPi xs1))
    | eq_p31zero9_map_ArcCosPi_nil : kXSeq.eqe (kXSeq.mapArcCosPi kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_ArcCosPi_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapArcCosPi (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaArcCosPi x1) (kXSeq.mapArcCosPi xs1))
    | eq_p31zero9_map_ArcTanPi_nil : kXSeq.eqe (kXSeq.mapArcTanPi kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_ArcTanPi_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapArcTanPi (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaArcTanPi x1) (kXSeq.mapArcTanPi xs1))
    | eq_p31zero9_map_Softplus_nil : kXSeq.eqe (kXSeq.mapSoftplus kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Softplus_cons {x1 xs1} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXSeq.eqe (kXSeq.mapSoftplus (kXSeq.xcons x1 xs1)) (kXSeq.xcons (kXReal.omegaSoftplus x1) (kXSeq.mapSoftplus xs1))
    | eq_p31zero9_map_Hypot_nil : kXSeq.eqe (kXSeq.mapHypot kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_Hypot_cons {x1 xs1 x2 xs2} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXSeq.eqe (kXSeq.mapHypot (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2)) (kXSeq.xcons (kXReal.omegaHypot x1 x2) (kXSeq.mapHypot xs1 xs2))
    | eq_p31zero9_map_ArcTan2_nil : kXSeq.eqe (kXSeq.mapArcTan2 kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_ArcTan2_cons {x1 xs1 x2 xs2} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXSeq.eqe (kXSeq.mapArcTan2 (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2)) (kXSeq.xcons (kXReal.omegaArcTan2 x1 x2) (kXSeq.mapArcTan2 xs1 xs2))
    | eq_p31zero9_map_ArcTan2Pi_nil : kXSeq.eqe (kXSeq.mapArcTan2Pi kXSeq.xnil kXSeq.xnil) kXSeq.xnil
    | eq_p31zero9_map_ArcTan2Pi_cons {x1 xs1 x2 xs2} : kXReal.has_sort x1 MSort.XReal → kXSeq.has_sort xs1 MSort.XSeq → kXReal.has_sort x2 MSort.XReal → kXSeq.has_sort xs2 MSort.XSeq → kXSeq.eqe (kXSeq.mapArcTan2Pi (kXSeq.xcons x1 xs1) (kXSeq.xcons x2 xs2)) (kXSeq.xcons (kXReal.omegaArcTan2Pi x1 x2) (kXSeq.mapArcTan2Pi xs1 xs2))

  inductive kCodeSeq.eqe: kCodeSeq → kCodeSeq → Prop
    | from_eqa {a b} : kCodeSeq.eqa a b → kCodeSeq.eqe a b
    | symm {a b} : kCodeSeq.eqe a b → kCodeSeq.eqe b a
    | trans {a b c} : kCodeSeq.eqe a b → kCodeSeq.eqe b c → kCodeSeq.eqe a c
    -- Congruence axioms for each operator
    | eqe_ccons {a₀ b₀ : MRat} {a₁ b₁ : kCodeSeq} : a₀ = b₀ → kCodeSeq.eqe a₁ b₁ → kCodeSeq.eqe (kCodeSeq.ccons a₀ a₁) (kCodeSeq.ccons b₀ b₁)
    | eqe_blockProject {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ : kFormat} {a₃ b₃ : kBlockProjSpec} {a₄ b₄ : MRat} {a₅ b₅ : kXSeq} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kBlockProjSpec.eqe a₃ b₃ → a₄ = b₄ → kXSeq.eqe a₅ b₅ → kCodeSeq.eqe (kCodeSeq.blockProject a₀ a₁ a₂ a₃ a₄ a₅) (kCodeSeq.blockProject b₀ b₁ b₂ b₃ b₄ b₅)
    | eqe_projectElements {a₀ b₀ : kFormat} {a₁ b₁ : kBlockProjSpec} {a₂ b₂ : kXReal} {a₃ b₃ : kXSeq} {a₄ b₄ : MRat} : kFormat.eqe a₀ b₀ → kBlockProjSpec.eqe a₁ b₁ → kXReal.eqe a₂ b₂ → kXSeq.eqe a₃ b₃ → a₄ = b₄ → kCodeSeq.eqe (kCodeSeq.projectElements a₀ a₁ a₂ a₃ a₄) (kCodeSeq.projectElements b₀ b₁ b₂ b₃ b₄)
    | eqe_projectUnscaled {a₀ b₀ : kFormat} {a₁ b₁ : kBlockProjSpec} {a₂ b₂ : kXSeq} {a₃ b₃ : MRat} : kFormat.eqe a₀ b₀ → kBlockProjSpec.eqe a₁ b₁ → kXSeq.eqe a₂ b₂ → a₃ = b₃ → kCodeSeq.eqe (kCodeSeq.projectUnscaled a₀ a₁ a₂ a₃) (kCodeSeq.projectUnscaled b₀ b₁ b₂ b₃)
    | eqe_at {a₀ b₀ : kPartitionSeq} {a₁ b₁ : MRat} : kPartitionSeq.eqe a₀ b₀ → a₁ = b₁ → kCodeSeq.eqe (kCodeSeq.«at» a₀ a₁) (kCodeSeq.«at» b₀ b₁)
    | eqe_partitionUnion {a b : kPartitionSeq} : kPartitionSeq.eqe a b → kCodeSeq.eqe (kCodeSeq.partitionUnion a) (kCodeSeq.partitionUnion b)
    | eqe_appendCodes {a₀ b₀ a₁ b₁ : kCodeSeq} : kCodeSeq.eqe a₀ b₀ → kCodeSeq.eqe a₁ b₁ → kCodeSeq.eqe (kCodeSeq.appendCodes a₀ a₁) (kCodeSeq.appendCodes b₀ b₁)
    | eqe_ConvertFromBlock {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ : kFormat} {a₄ b₄ : kBlockProjSpec} {a₅ b₅ : MRat} {a₆ b₆ : kCodeSeq} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kBlockProjSpec.eqe a₄ b₄ → a₅ = b₅ → kCodeSeq.eqe a₆ b₆ → kCodeSeq.eqe (kCodeSeq.ConvertFromBlock a₀ a₁ a₂ a₃ a₄ a₅ a₆) (kCodeSeq.ConvertFromBlock b₀ b₁ b₂ b₃ b₄ b₅ b₆)
    | eqe_ConvertToBlock {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ : kFormat} {a₄ b₄ : kBlockProjSpec} {a₅ b₅ : kCodeSeq} {a₆ b₆ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kBlockProjSpec.eqe a₄ b₄ → kCodeSeq.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe (kCodeSeq.ConvertToBlock a₀ a₁ a₂ a₃ a₄ a₅ a₆) (kCodeSeq.ConvertToBlock b₀ b₁ b₂ b₃ b₄ b₅ b₆)
    -- Equations
    | eq_p31zero9_block_core_zero14 {b fs fr bp s₁ xs} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s₁ MSort.Int → kXSeq.has_sort xs MSort.XSeq → kBool.eqe (if (1 : MRat) ≤ b then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.eqeq₀ (MRat.length₁ xs) b) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kCodeSeq.eqe (kCodeSeq.blockProject b fs fr bp s₁ xs) (kCodeSeq.projectElements fr bp (kXReal.decode fs s₁) xs (0 : MRat))
    | eq_p31zero9_block_core_zero15 {fr bp x j} : kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → kXReal.has_sort x MSort.XReal → MRat.has_sort j MSort.Nat → kCodeSeq.eqe (kCodeSeq.projectElements fr bp x kXSeq.xnil j) kCodeSeq.cnil
    | eq_p31zero9_block_core_zero16 {fr bp x y xs j} : kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → kXReal.has_sort x MSort.XReal → kXReal.has_sort y MSort.XReal → kXSeq.has_sort xs MSort.XSeq → MRat.has_sort j MSort.Nat → kCodeSeq.eqe (kCodeSeq.projectElements fr bp x (kXSeq.xcons y xs) j) (kCodeSeq.ccons (MRat.project fr (kProjSpec.projectionAt bp j) (kXReal.normalizeElement x y)) (kCodeSeq.projectElements fr bp x xs (j + (1 : MRat))))
    | eq_p31zero9_block_core_zero17 {fr bp j} : kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort j MSort.Nat → kCodeSeq.eqe (kCodeSeq.projectUnscaled fr bp kXSeq.xnil j) kCodeSeq.cnil
    | eq_p31zero9_block_core_zero18 {fr bp y xs j} : kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → kXReal.has_sort y MSort.XReal → kXSeq.has_sort xs MSort.XSeq → MRat.has_sort j MSort.Nat → kCodeSeq.eqe (kCodeSeq.projectUnscaled fr bp (kXSeq.xcons y xs) j) (kCodeSeq.ccons (MRat.project fr (kProjSpec.projectionAt bp j) y) (kCodeSeq.projectUnscaled fr bp xs (j + (1 : MRat))))
    | eq_p31zero9_sequences_zerozero3 {x xs} : kCodeSeq.has_sort x MSort.CodeSeq → kPartitionSeq.has_sort xs MSort.PartitionSeq → kCodeSeq.eqe (kCodeSeq.«at» (kPartitionSeq.pcons x xs) (0 : MRat)) x
    | eq_p31zero9_sequences_zerozero4 {x xs n} : kCodeSeq.has_sort x MSort.CodeSeq → kPartitionSeq.has_sort xs MSort.PartitionSeq → MRat.has_sort n MSort.Nat → kBool.eqe (if (0 : MRat) < n then kBool.true else kBool.false) kBool.true → kCodeSeq.eqe (kCodeSeq.«at» (kPartitionSeq.pcons x xs) n) (kCodeSeq.«at» xs (if n ≤ (1 : MRat) then (1 : MRat) - n else n - (1 : MRat)))
    | eq_p31zero9_conformance_zero6zero {cs} : kCodeSeq.has_sort cs MSort.CodeSeq → kCodeSeq.eqe (kCodeSeq.appendCodes kCodeSeq.cnil cs) cs
    | eq_p31zero9_conformance_zero61 {c cs ds} : MRat.has_sort c MSort.Int → kCodeSeq.has_sort cs MSort.CodeSeq → kCodeSeq.has_sort ds MSort.CodeSeq → kCodeSeq.eqe (kCodeSeq.appendCodes (kCodeSeq.ccons c cs) ds) (kCodeSeq.ccons c (kCodeSeq.appendCodes cs ds))
    | eq_p31zero9_partition_union_empty : kCodeSeq.eqe (kCodeSeq.partitionUnion kPartitionSeq.pnil) kCodeSeq.cnil
    | eq_p31zero9_partition_union_cons {cs parts} : kCodeSeq.has_sort cs MSort.CodeSeq → kPartitionSeq.has_sort parts MSort.PartitionSeq → kCodeSeq.eqe (kCodeSeq.partitionUnion (kPartitionSeq.pcons cs parts)) (kCodeSeq.appendCodes cs (kCodeSeq.partitionUnion parts))
    | eq_p31zero9_block_ops_zero11 {b fs fx fr bp s₁ cs} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs MSort.Format → kFormat.has_sort fx MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s₁ MSort.Int → kCodeSeq.has_sort cs MSort.CodeSeq → kBool.eqe (kBool.validBlock b fs fx s₁ cs) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kCodeSeq.eqe (kCodeSeq.ConvertFromBlock b fs fx fr bp s₁ cs) (kCodeSeq.projectUnscaled fr bp (kXSeq.blockDecode b fs fx s₁ cs) (0 : MRat))
    | eq_p31zero9_block_ops_zero12 {b fx fs fr bp cs s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fx MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → kCodeSeq.has_sort cs MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (if (1 : MRat) ≤ b then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.eqeq₀ (MRat.length₂ cs) b) kBool.true → kBool.eqe (kBool.validCodes fx cs) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kCodeSeq.eqe (kCodeSeq.ConvertToBlock b fx fs fr bp cs s₁) (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.decodeElements fx cs))

  inductive kBlock.eqe: kBlock → kBlock → Prop
    | from_eqa {a b} : kBlock.eqa a b → kBlock.eqe a b
    | symm {a b} : kBlock.eqe a b → kBlock.eqe b a
    | trans {a b c} : kBlock.eqe a b → kBlock.eqe b c → kBlock.eqe a c
    -- Congruence axioms for each operator
    | eqe_block {a₀ b₀ : MRat} {a₁ b₁ : kCodeSeq} : a₀ = b₀ → kCodeSeq.eqe a₁ b₁ → kBlock.eqe (kBlock.block a₀ a₁) (kBlock.block b₀ b₁)
    | eqe_ConvertToBlockMaxAbsFinite {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ : kFormat} {a₄ b₄ : kProjSpec} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : kCodeSeq} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kProjSpec.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → kCodeSeq.eqe a₆ b₆ → kBlock.eqe (kBlock.ConvertToBlockMaxAbsFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆) (kBlock.ConvertToBlockMaxAbsFinite b₀ b₁ b₂ b₃ b₄ b₅ b₆)
    | eqe_computedBlock {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ : kFormat} {a₃ b₃ : kBlockProjSpec} {a₄ b₄ : MRat} {a₅ b₅ : kXSeq} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kBlockProjSpec.eqe a₃ b₃ → a₄ = b₄ → kXSeq.eqe a₅ b₅ → kBlock.eqe (kBlock.computedBlock a₀ a₁ a₂ a₃ a₄ a₅) (kBlock.computedBlock b₀ b₁ b₂ b₃ b₄ b₅)
    | eqe_BlockConvert {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockConvert a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockConvert b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockAbs {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockAbs a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockAbs b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockNegate {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockNegate a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockNegate b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockCopySign {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kBlockProjSpec.eqe a₇ b₇ → a₈ = b₈ → kCodeSeq.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqe (kBlock.BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockCopySign b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqe_BlockAdd {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kBlockProjSpec.eqe a₇ b₇ → a₈ = b₈ → kCodeSeq.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqe (kBlock.BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockAdd b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqe_BlockSubtract {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kBlockProjSpec.eqe a₇ b₇ → a₈ = b₈ → kCodeSeq.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqe (kBlock.BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockSubtract b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqe_BlockMultiply {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kBlockProjSpec.eqe a₇ b₇ → a₈ = b₈ → kCodeSeq.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqe (kBlock.BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMultiply b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqe_BlockDivide {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kBlockProjSpec.eqe a₇ b₇ → a₈ = b₈ → kCodeSeq.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqe (kBlock.BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockDivide b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqe_BlockFMA {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ a₇ b₇ a₈ b₈ : kFormat} {a₉ b₉ : kBlockProjSpec} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} {a₁₃ b₁₃ : kCodeSeq} {a₁₄ b₁₄ : MRat} {a₁₅ b₁₅ : kCodeSeq} {a₁₆ b₁₆ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kFormat.eqe a₇ b₇ → kFormat.eqe a₈ b₈ → kBlockProjSpec.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kCodeSeq.eqe a₁₃ b₁₃ → a₁₄ = b₁₄ → kCodeSeq.eqe a₁₅ b₁₅ → a₁₆ = b₁₆ → kBlock.eqe (kBlock.BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFMA b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃ b₁₄ b₁₅ b₁₆)
    | eqe_BlockFAA {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ a₇ b₇ a₈ b₈ : kFormat} {a₉ b₉ : kBlockProjSpec} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} {a₁₃ b₁₃ : kCodeSeq} {a₁₄ b₁₄ : MRat} {a₁₅ b₁₅ : kCodeSeq} {a₁₆ b₁₆ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kFormat.eqe a₇ b₇ → kFormat.eqe a₈ b₈ → kBlockProjSpec.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kCodeSeq.eqe a₁₃ b₁₃ → a₁₄ = b₁₄ → kCodeSeq.eqe a₁₅ b₁₅ → a₁₆ = b₁₆ → kBlock.eqe (kBlock.BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockFAA b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃ b₁₄ b₁₅ b₁₆)
    | eqe_BlockRecip {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockRecip a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockRecip b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockMinimum {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kBlockProjSpec.eqe a₇ b₇ → a₈ = b₈ → kCodeSeq.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqe (kBlock.BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimum b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqe_BlockMaximum {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kBlockProjSpec.eqe a₇ b₇ → a₈ = b₈ → kCodeSeq.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqe (kBlock.BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximum b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqe_BlockMinimumNumber {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kBlockProjSpec.eqe a₇ b₇ → a₈ = b₈ → kCodeSeq.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqe (kBlock.BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumNumber b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqe_BlockMaximumNumber {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kBlockProjSpec.eqe a₇ b₇ → a₈ = b₈ → kCodeSeq.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqe (kBlock.BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumNumber b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqe_BlockMinimumMagnitude {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kBlockProjSpec.eqe a₇ b₇ → a₈ = b₈ → kCodeSeq.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqe (kBlock.BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitude b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqe_BlockMaximumMagnitude {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kBlockProjSpec.eqe a₇ b₇ → a₈ = b₈ → kCodeSeq.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqe (kBlock.BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitude b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqe_BlockMinimumMagnitudeNumber {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kBlockProjSpec.eqe a₇ b₇ → a₈ = b₈ → kCodeSeq.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqe (kBlock.BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumMagnitudeNumber b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqe_BlockMaximumMagnitudeNumber {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kBlockProjSpec.eqe a₇ b₇ → a₈ = b₈ → kCodeSeq.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqe (kBlock.BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumMagnitudeNumber b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqe_BlockMinimumFinite {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kBlockProjSpec.eqe a₇ b₇ → a₈ = b₈ → kCodeSeq.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqe (kBlock.BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMinimumFinite b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqe_BlockMaximumFinite {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kBlockProjSpec.eqe a₇ b₇ → a₈ = b₈ → kCodeSeq.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqe (kBlock.BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockMaximumFinite b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqe_BlockClamp {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ a₇ b₇ a₈ b₈ : kFormat} {a₉ b₉ : kBlockProjSpec} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} {a₁₃ b₁₃ : kCodeSeq} {a₁₄ b₁₄ : MRat} {a₁₅ b₁₅ : kCodeSeq} {a₁₆ b₁₆ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kFormat.eqe a₇ b₇ → kFormat.eqe a₈ b₈ → kBlockProjSpec.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kCodeSeq.eqe a₁₃ b₁₃ → a₁₄ = b₁₄ → kCodeSeq.eqe a₁₅ b₁₅ → a₁₆ = b₁₆ → kBlock.eqe (kBlock.BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆) (kBlock.BlockClamp b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃ b₁₄ b₁₅ b₁₆)
    | eqe_BlockSqrt {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSqrt b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockRSqrt {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockRSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockRSqrt b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockExp {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockExp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockExp b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockExp2 {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockExp2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockExp2 b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockLog {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockLog a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockLog b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockLog2 {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockLog2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockLog2 b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockLogOnePlus {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockLogOnePlus a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockLogOnePlus b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockExpMinusOne {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockExpMinusOne a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockExpMinusOne b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockSin {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSin b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockCos {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockCos b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockTan {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockTan b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockArcSin {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockArcSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcSin b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockArcCos {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockArcCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcCos b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockArcTan {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockArcTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcTan b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockSinh {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSinh b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockCosh {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockCosh b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockTanh {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockTanh b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockArcSinh {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockArcSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcSinh b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockArcCosh {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockArcCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcCosh b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockArcTanh {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockArcTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcTanh b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockSinPi {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSinPi b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockCosPi {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockCosPi b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockTanPi {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockTanPi b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockArcSinPi {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockArcSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcSinPi b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockArcCosPi {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockArcCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcCosPi b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockArcTanPi {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockArcTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockArcTanPi b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockSoftplus {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : kFormat} {a₅ b₅ : kBlockProjSpec} {a₆ b₆ : MRat} {a₇ b₇ : kCodeSeq} {a₈ b₈ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kBlockProjSpec.eqe a₅ b₅ → a₆ = b₆ → kCodeSeq.eqe a₇ b₇ → a₈ = b₈ → kBlock.eqe (kBlock.BlockSoftplus a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) (kBlock.BlockSoftplus b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈)
    | eqe_BlockHypot {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kBlockProjSpec.eqe a₇ b₇ → a₈ = b₈ → kCodeSeq.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqe (kBlock.BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockHypot b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqe_BlockArcTan2 {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kBlockProjSpec.eqe a₇ b₇ → a₈ = b₈ → kCodeSeq.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqe (kBlock.BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2 b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    | eqe_BlockArcTan2Pi {a₀ b₀ : MRat} {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆ : kFormat} {a₇ b₇ : kBlockProjSpec} {a₈ b₈ : MRat} {a₉ b₉ : kCodeSeq} {a₁₀ b₁₀ : MRat} {a₁₁ b₁₁ : kCodeSeq} {a₁₂ b₁₂ : MRat} : a₀ = b₀ → kFormat.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → kFormat.eqe a₃ b₃ → kFormat.eqe a₄ b₄ → kFormat.eqe a₅ b₅ → kFormat.eqe a₆ b₆ → kBlockProjSpec.eqe a₇ b₇ → a₈ = b₈ → kCodeSeq.eqe a₉ b₉ → a₁₀ = b₁₀ → kCodeSeq.eqe a₁₁ b₁₁ → a₁₂ = b₁₂ → kBlock.eqe (kBlock.BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂) (kBlock.BlockArcTan2Pi b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂)
    -- Equations
    | eq_p31zero9_block_ops_zero13 {b fx fs fr ps bp cs} : MRat.has_sort b MSort.Nat → kFormat.has_sort fx MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kProjSpec.has_sort ps MSort.ProjSpec → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → kCodeSeq.has_sort cs MSort.CodeSeq → kBool.eqe (if (1 : MRat) ≤ b then kBool.true else kBool.false) kBool.true → kBool.eqe (kBool.eqeq₀ (MRat.length₂ cs) b) kBool.true → kBool.eqe (kBool.validCodes fx cs) kBool.true → kBool.eqe (kBool.validFormat fs) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validProjection ps) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.ConvertToBlockMaxAbsFinite b fx fs fr ps bp cs) (kBlock.computedBlock b fs fr bp (MRat.project fs ps (kXReal.foldMaximumFinite kXReal.nan (kXSeq.absElements (kXSeq.decodeElements fx cs)))) (kXSeq.decodeElements fx cs))
    | eq_p31zero9_block_ops_zero14 {b fs fr bp s₁ xs} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s₁ MSort.Int → kXSeq.has_sort xs MSort.XSeq → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBlock.eqe (kBlock.computedBlock b fs fr bp s₁ xs) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ xs))
    | eq_p31zero9_block_Convert {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockConvert b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapConvert (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_Abs {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockAbs b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapAbs (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_Negate {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockNegate b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapNegate (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_CopySign {b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockCopySign b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapCopySign (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2))))
    | eq_p31zero9_block_Add {b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockAdd b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapAdd (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2))))
    | eq_p31zero9_block_Subtract {b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockSubtract b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapSubtract (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2))))
    | eq_p31zero9_block_Multiply {b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockMultiply b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapMultiply (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2))))
    | eq_p31zero9_block_Divide {b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockDivide b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapDivide (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2))))
    | eq_p31zero9_block_FMA {b fs1 f1 fs2 f2 fs3 f3 fs fr bp s1 cs1 s2 cs2 s3 cs3 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs3 MSort.Format → kFormat.has_sort f3 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s3 MSort.Int → kCodeSeq.has_sort cs3 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validBlock b fs3 f3 s3 cs3) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockFMA b fs1 f1 fs2 f2 fs3 f3 fs fr bp s1 cs1 s2 cs2 s3 cs3 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapFMA (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2) (kXSeq.blockDecode b fs3 f3 s3 cs3))))
    | eq_p31zero9_block_FAA {b fs1 f1 fs2 f2 fs3 f3 fs fr bp s1 cs1 s2 cs2 s3 cs3 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs3 MSort.Format → kFormat.has_sort f3 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s3 MSort.Int → kCodeSeq.has_sort cs3 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validBlock b fs3 f3 s3 cs3) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockFAA b fs1 f1 fs2 f2 fs3 f3 fs fr bp s1 cs1 s2 cs2 s3 cs3 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapFAA (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2) (kXSeq.blockDecode b fs3 f3 s3 cs3))))
    | eq_p31zero9_block_Recip {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockRecip b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapRecip (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_Minimum {b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockMinimum b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapMinimum (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2))))
    | eq_p31zero9_block_Maximum {b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockMaximum b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapMaximum (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2))))
    | eq_p31zero9_block_MinimumNumber {b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockMinimumNumber b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapMinimumNumber (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2))))
    | eq_p31zero9_block_MaximumNumber {b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockMaximumNumber b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapMaximumNumber (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2))))
    | eq_p31zero9_block_MinimumMagnitude {b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockMinimumMagnitude b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapMinimumMagnitude (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2))))
    | eq_p31zero9_block_MaximumMagnitude {b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockMaximumMagnitude b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapMaximumMagnitude (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2))))
    | eq_p31zero9_block_MinimumMagnitudeNumber {b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockMinimumMagnitudeNumber b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapMinimumMagnitudeNumber (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2))))
    | eq_p31zero9_block_MaximumMagnitudeNumber {b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockMaximumMagnitudeNumber b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapMaximumMagnitudeNumber (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2))))
    | eq_p31zero9_block_MinimumFinite {b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockMinimumFinite b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapMinimumFinite (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2))))
    | eq_p31zero9_block_MaximumFinite {b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockMaximumFinite b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapMaximumFinite (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2))))
    | eq_p31zero9_block_Clamp {b fs1 f1 fs2 f2 fs3 f3 fs fr bp s1 cs1 s2 cs2 s3 cs3 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs3 MSort.Format → kFormat.has_sort f3 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s3 MSort.Int → kCodeSeq.has_sort cs3 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validBlock b fs3 f3 s3 cs3) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockClamp b fs1 f1 fs2 f2 fs3 f3 fs fr bp s1 cs1 s2 cs2 s3 cs3 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapClamp (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2) (kXSeq.blockDecode b fs3 f3 s3 cs3))))
    | eq_p31zero9_block_Sqrt {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockSqrt b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapSqrt (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_RSqrt {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockRSqrt b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapRSqrt (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_Exp {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockExp b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapExp (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_Exp2 {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockExp2 b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapExp2 (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_Log {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockLog b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapLog (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_Log2 {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockLog2 b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapLog2 (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_LogOnePlus {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockLogOnePlus b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapLogOnePlus (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_ExpMinusOne {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockExpMinusOne b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapExpMinusOne (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_Sin {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockSin b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapSin (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_Cos {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockCos b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapCos (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_Tan {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockTan b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapTan (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_ArcSin {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockArcSin b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapArcSin (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_ArcCos {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockArcCos b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapArcCos (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_ArcTan {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockArcTan b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapArcTan (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_Sinh {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockSinh b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapSinh (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_Cosh {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockCosh b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapCosh (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_Tanh {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockTanh b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapTanh (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_ArcSinh {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockArcSinh b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapArcSinh (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_ArcCosh {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockArcCosh b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapArcCosh (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_ArcTanh {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockArcTanh b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapArcTanh (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_SinPi {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockSinPi b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapSinPi (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_CosPi {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockCosPi b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapCosPi (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_TanPi {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockTanPi b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapTanPi (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_ArcSinPi {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockArcSinPi b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapArcSinPi (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_ArcCosPi {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockArcCosPi b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapArcCosPi (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_ArcTanPi {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockArcTanPi b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapArcTanPi (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_Softplus {b fs1 f1 fs fr bp s1 cs1 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockSoftplus b fs1 f1 fs fr bp s1 cs1 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapSoftplus (kXSeq.blockDecode b fs1 f1 s1 cs1))))
    | eq_p31zero9_block_Hypot {b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockHypot b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapHypot (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2))))
    | eq_p31zero9_block_ArcTan2 {b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockArcTan2 b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapArcTan2 (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2))))
    | eq_p31zero9_block_ArcTan2Pi {b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁} : MRat.has_sort b MSort.Nat → kFormat.has_sort fs1 MSort.Format → kFormat.has_sort f1 MSort.Format → kFormat.has_sort fs2 MSort.Format → kFormat.has_sort f2 MSort.Format → kFormat.has_sort fs MSort.Format → kFormat.has_sort fr MSort.Format → kBlockProjSpec.has_sort bp MSort.BlockProjSpec → MRat.has_sort s1 MSort.Int → kCodeSeq.has_sort cs1 MSort.CodeSeq → MRat.has_sort s2 MSort.Int → kCodeSeq.has_sort cs2 MSort.CodeSeq → MRat.has_sort s₁ MSort.Int → kBool.eqe (kBool.validBlock b fs1 f1 s1 cs1) kBool.true → kBool.eqe (kBool.validBlock b fs2 f2 s2 cs2) kBool.true → kBool.eqe (kBool.validCode fs s₁) kBool.true → kBool.eqe (kBool.validFormat fr) kBool.true → kBool.eqe (kBool.validBlockProjection bp b) kBool.true → kBlock.eqe (kBlock.BlockArcTan2Pi b fs1 f1 fs2 f2 fs fr bp s1 cs1 s2 cs2 s₁) (kBlock.block s₁ (kCodeSeq.blockProject b fs fr bp s₁ (kXSeq.mapArcTan2Pi (kXSeq.blockDecode b fs1 f1 s1 cs1) (kXSeq.blockDecode b fs2 f2 s2 cs2))))

  inductive kFormatSeq.eqe: kFormatSeq → kFormatSeq → Prop
    | from_eqa {a b} : kFormatSeq.eqa a b → kFormatSeq.eqe a b
    | symm {a b} : kFormatSeq.eqe a b → kFormatSeq.eqe b a
    | trans {a b c} : kFormatSeq.eqe a b → kFormatSeq.eqe b c → kFormatSeq.eqe a c
    -- Congruence axioms for each operator
    | eqe_fcons {a₀ b₀ : kFormat} {a₁ b₁ : kFormatSeq} : kFormat.eqe a₀ b₀ → kFormatSeq.eqe a₁ b₁ → kFormatSeq.eqe (kFormatSeq.fcons a₀ a₁) (kFormatSeq.fcons b₀ b₁)

  inductive kSpecialization.eqe: kSpecialization → kSpecialization → Prop
    | from_eqa {a b} : kSpecialization.eqa a b → kSpecialization.eqe a b
    | symm {a b} : kSpecialization.eqe a b → kSpecialization.eqe b a
    | trans {a b c} : kSpecialization.eqe a b → kSpecialization.eqe b c → kSpecialization.eqe a c
    -- Congruence axioms for each operator
    | eqe_numeric {a₀ b₀ : MString} {a₁ b₁ : kFormatSeq} {a₂ b₂ : kProjSpec} : a₀ = b₀ → kFormatSeq.eqe a₁ b₁ → kProjSpec.eqe a₂ b₂ → kSpecialization.eqe (kSpecialization.numeric a₀ a₁ a₂) (kSpecialization.numeric b₀ b₁ b₂)
    | eqe_plain {a₀ b₀ : MString} {a₁ b₁ : kFormatSeq} : a₀ = b₀ → kFormatSeq.eqe a₁ b₁ → kSpecialization.eqe (kSpecialization.plain a₀ a₁) (kSpecialization.plain b₀ b₁)
    | eqe_blockElements {a₀ b₀ : MString} {a₁ b₁ : MRat} {a₂ b₂ : kFormatSeq} {a₃ b₃ : kBlockProjSpec} : a₀ = b₀ → a₁ = b₁ → kFormatSeq.eqe a₂ b₂ → kBlockProjSpec.eqe a₃ b₃ → kSpecialization.eqe (kSpecialization.blockElements a₀ a₁ a₂ a₃) (kSpecialization.blockElements b₀ b₁ b₂ b₃)
    | eqe_blockReduction {a₀ b₀ : MString} {a₁ b₁ : MRat} {a₂ b₂ : kFormatSeq} {a₃ b₃ : kProjSpec} : a₀ = b₀ → a₁ = b₁ → kFormatSeq.eqe a₂ b₂ → kProjSpec.eqe a₃ b₃ → kSpecialization.eqe (kSpecialization.blockReduction a₀ a₁ a₂ a₃) (kSpecialization.blockReduction b₀ b₁ b₂ b₃)
    | eqe_blockScale {a₀ b₀ : MString} {a₁ b₁ : MRat} {a₂ b₂ : kFormatSeq} {a₃ b₃ : kProjSpec} {a₄ b₄ : kBlockProjSpec} : a₀ = b₀ → a₁ = b₁ → kFormatSeq.eqe a₂ b₂ → kProjSpec.eqe a₃ b₃ → kBlockProjSpec.eqe a₄ b₄ → kSpecialization.eqe (kSpecialization.blockScale a₀ a₁ a₂ a₃ a₄) (kSpecialization.blockScale b₀ b₁ b₂ b₃ b₄)
    | eqe_at {a₀ b₀ : kSpecializationSeq} {a₁ b₁ : MRat} : kSpecializationSeq.eqe a₀ b₀ → a₁ = b₁ → kSpecialization.eqe (kSpecialization.«at» a₀ a₁) (kSpecialization.«at» b₀ b₁)
    | eqe_declaredIdentity {a b : kDeclaration} : kDeclaration.eqe a b → kSpecialization.eqe (kSpecialization.declaredIdentity a) (kSpecialization.declaredIdentity b)
    -- Equations
    | eq_p31zero9_sequences_zerozero3 {x xs} : kSpecialization.has_sort x MSort.Specialization → kSpecializationSeq.has_sort xs MSort.SpecializationSeq → kSpecialization.eqe (kSpecialization.«at» (kSpecializationSeq.scons x xs) (0 : MRat)) x
    | eq_p31zero9_sequences_zerozero4 {x xs n} : kSpecialization.has_sort x MSort.Specialization → kSpecializationSeq.has_sort xs MSort.SpecializationSeq → MRat.has_sort n MSort.Nat → kBool.eqe (if (0 : MRat) < n then kBool.true else kBool.false) kBool.true → kSpecialization.eqe (kSpecialization.«at» (kSpecializationSeq.scons x xs) n) (kSpecialization.«at» xs (if n ≤ (1 : MRat) then (1 : MRat) - n else n - (1 : MRat)))
    | eq_p31zero9_declared_exact {s₁ name e} : kSpecialization.has_sort s₁ MSort.Specialization → kEvidence.has_sort e MSort.Evidence → kSpecialization.eqe (kSpecialization.declaredIdentity (kDeclaration.exact s₁ name e)) s₁
    | eq_p31zero9_declared_approximate {s₁ name k e} : kSpecialization.has_sort s₁ MSort.Specialization → kKappa.has_sort k MSort.Kappa → kEvidence.has_sort e MSort.Evidence → kSpecialization.eqe (kSpecialization.declaredIdentity (kDeclaration.approximate s₁ name k e)) s₁
    | eq_p31zero9_decl_partitioned_identity {s₁ name cs kp e} : kSpecialization.has_sort s₁ MSort.Specialization → kCodeSeq.has_sort cs MSort.CodeSeq → kKappaPartSeq.has_sort kp MSort.KappaPartSeq → kEvidence.has_sort e MSort.Evidence → kSpecialization.eqe (kSpecialization.declaredIdentity (kDeclaration.partitioned s₁ name cs kp e)) s₁

  inductive kKappa.eqe: kKappa → kKappa → Prop
    | from_eqa {a b} : kKappa.eqa a b → kKappa.eqe a b
    | symm {a b} : kKappa.eqe a b → kKappa.eqe b a
    | trans {a b c} : kKappa.eqe a b → kKappa.eqe b c → kKappa.eqe a c
    -- Congruence axioms for each operator
    | eqe_steps {a b : MRat} : a = b → kKappa.eqe (kKappa.steps a) (kKappa.steps b)
    | eqe_partBound {a b : kKappaPartSeq} : kKappaPartSeq.eqe a b → kKappa.eqe (kKappa.partBound a) (kKappa.partBound b)
    | eqe_declarationKappa {a b : kDeclaration} : kDeclaration.eqe a b → kKappa.eqe (kKappa.declarationKappa a) (kKappa.declarationKappa b)
    | eqe_observationKappa {a b : kObservation} : kObservation.eqe a b → kKappa.eqe (kKappa.observationKappa a) (kKappa.observationKappa b)
    | eqe_batchKappa {a b : kObservationSeq} : kObservationSeq.eqe a b → kKappa.eqe (kKappa.batchKappa a) (kKappa.batchKappa b)
    | eqe_mergeKappa {a₀ b₀ a₁ b₁ : kKappa} : kKappa.eqe a₀ b₀ → kKappa.eqe a₁ b₁ → kKappa.eqe (kKappa.mergeKappa a₀ a₁) (kKappa.mergeKappa b₀ b₁)
    -- Equations
    | eq_p31zero9_conformance_zero4zero {n cs f c d} : kCodeSeq.has_sort cs MSort.CodeSeq → kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → MRat.has_sort d MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.validCode f d) kBool.true → kBool.eqe (kBool.eqslasheq₁ (kBool.IsNaN f c) (kBool.IsNaN f d)) kBool.true → kKappa.eqe (kKappa.observationKappa (kObservation.observation n cs f c d)) kKappa.kNaN
    | eq_p31zero9_conformance_zero41 {n cs f c d} : kCodeSeq.has_sort cs MSort.CodeSeq → kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → MRat.has_sort d MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.validCode f d) kBool.true → kBool.eqe (kBool.IsNaN f c) kBool.true → kBool.eqe (kBool.IsNaN f d) kBool.true → kKappa.eqe (kKappa.observationKappa (kObservation.observation n cs f c d)) (kKappa.steps (0 : MRat))
    | eq_p31zero9_conformance_zero42 {n cs f c d} : kCodeSeq.has_sort cs MSort.CodeSeq → kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → MRat.has_sort d MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.validCode f d) kBool.true → kBool.eqe (kBool.IsInfinite f c) kBool.true → kBool.eqe (kBool.IsInfinite f d) kBool.true → kBool.eqe (kBool.eqeq₄ (kBool.IsSignMinus f c) (kBool.IsSignMinus f d)) kBool.true → kKappa.eqe (kKappa.observationKappa (kObservation.observation n cs f c d)) (kKappa.steps (0 : MRat))
    | eq_p31zero9_conformance_zero43 {n cs f c d} : kCodeSeq.has_sort cs MSort.CodeSeq → kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → MRat.has_sort d MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.validCode f d) kBool.true → kBool.eqe (kBool.not (kBool.IsNaN f c)) kBool.true → kBool.eqe (kBool.not (kBool.IsNaN f d)) kBool.true → kBool.eqe (kBool.or (kBool.IsInfinite f c) (kBool.IsInfinite f d)) kBool.true → kBool.eqe (kBool.not (kBool.and (kBool.and (kBool.IsInfinite f d) (kBool.eqeq₄ (kBool.IsSignMinus f c) (kBool.IsSignMinus f d))) (kBool.IsInfinite f c))) kBool.true → kKappa.eqe (kKappa.observationKappa (kObservation.observation n cs f c d)) kKappa.kInfinity
    | eq_p31zero9_conformance_zero44 {n cs f c d} : kCodeSeq.has_sort cs MSort.CodeSeq → kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → MRat.has_sort d MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.validCode f d) kBool.true → kBool.eqe (kBool.IsFinite f c) kBool.true → kBool.eqe (kBool.IsFinite f d) kBool.true → kKappa.eqe (kKappa.observationKappa (kObservation.observation n cs f c d)) (kKappa.steps (if ((MRat.finiteRank f c) - (MRat.finiteRank f d)) < 0 then - ((MRat.finiteRank f c) - (MRat.finiteRank f d)) else ((MRat.finiteRank f c) - (MRat.finiteRank f d))))
    | eq_p31zero9_conformance_zero45 : kKappa.eqe (kKappa.batchKappa kObservationSeq.onil) (kKappa.steps (0 : MRat))
    | eq_p31zero9_conformance_zero46 {o os} : kObservation.has_sort o MSort.Observation → kObservationSeq.has_sort os MSort.ObservationSeq → kKappa.eqe (kKappa.batchKappa (kObservationSeq.ocons o os)) (kKappa.mergeKappa (kKappa.observationKappa o) (kKappa.batchKappa os))
    | eq_p31zero9_conformance_zero47 {k} : kKappa.has_sort k MSort.Kappa → kKappa.eqe (kKappa.mergeKappa kKappa.kNaN k) kKappa.kNaN
    | eq_p31zero9_conformance_zero48 : kKappa.eqe (kKappa.mergeKappa kKappa.kInfinity kKappa.kNaN) kKappa.kNaN
    | eq_p31zero9_conformance_zero49 {a} : MRat.has_sort a MSort.Nat → kKappa.eqe (kKappa.mergeKappa (kKappa.steps a) kKappa.kNaN) kKappa.kNaN
    | eq_p31zero9_conformance_zero5zero : kKappa.eqe (kKappa.mergeKappa kKappa.kInfinity kKappa.kInfinity) kKappa.kInfinity
    | eq_p31zero9_conformance_zero51 {a} : MRat.has_sort a MSort.Nat → kKappa.eqe (kKappa.mergeKappa kKappa.kInfinity (kKappa.steps a)) kKappa.kInfinity
    | eq_p31zero9_conformance_zero52 {a} : MRat.has_sort a MSort.Nat → kKappa.eqe (kKappa.mergeKappa (kKappa.steps a) kKappa.kInfinity) kKappa.kInfinity
    | eq_p31zero9_conformance_zero53 {a b} : MRat.has_sort a MSort.Nat → MRat.has_sort b MSort.Nat → kKappa.eqe (kKappa.mergeKappa (kKappa.steps a) (kKappa.steps b)) (kKappa.steps (max a b))
    | eq_p31zero9_part_bound_empty : kKappa.eqe (kKappa.partBound kKappaPartSeq.knil) (kKappa.steps (0 : MRat))
    | eq_p31zero9_part_bound_cons {cs k kp} : kCodeSeq.has_sort cs MSort.CodeSeq → kKappa.has_sort k MSort.Kappa → kKappaPartSeq.has_sort kp MSort.KappaPartSeq → kKappa.eqe (kKappa.partBound (kKappaPartSeq.kcons (kKappaPart.kappaPart cs k) kp)) (kKappa.mergeKappa k (kKappa.partBound kp))
    | eq_p31zero9_decl_exact_kappa {s₁ name e} : kSpecialization.has_sort s₁ MSort.Specialization → kEvidence.has_sort e MSort.Evidence → kBool.eqe (kBool.wellFormedDeclaration (kDeclaration.exact s₁ name e)) kBool.true → kBool.eqe (kBool.numericResult s₁) kBool.true → kKappa.eqe (kKappa.declarationKappa (kDeclaration.exact s₁ name e)) (kKappa.steps (0 : MRat))
    | eq_p31zero9_decl_approx_kappa {s₁ name k e} : kSpecialization.has_sort s₁ MSort.Specialization → kKappa.has_sort k MSort.Kappa → kEvidence.has_sort e MSort.Evidence → kBool.eqe (kBool.wellFormedDeclaration (kDeclaration.approximate s₁ name k e)) kBool.true → kKappa.eqe (kKappa.declarationKappa (kDeclaration.approximate s₁ name k e)) k
    | eq_p31zero9_decl_partition_kappa {s₁ name cs kp e} : kSpecialization.has_sort s₁ MSort.Specialization → kCodeSeq.has_sort cs MSort.CodeSeq → kKappaPartSeq.has_sort kp MSort.KappaPartSeq → kEvidence.has_sort e MSort.Evidence → kBool.eqe (kBool.wellFormedDeclaration (kDeclaration.partitioned s₁ name cs kp e)) kBool.true → kKappa.eqe (kKappa.declarationKappa (kDeclaration.partitioned s₁ name cs kp e)) (kKappa.partBound kp)

  inductive kObservation.eqe: kObservation → kObservation → Prop
    | from_eqa {a b} : kObservation.eqa a b → kObservation.eqe a b
    | symm {a b} : kObservation.eqe a b → kObservation.eqe b a
    | trans {a b c} : kObservation.eqe a b → kObservation.eqe b c → kObservation.eqe a c
    -- Congruence axioms for each operator
    | eqe_observation {a₀ b₀ : MString} {a₁ b₁ : kCodeSeq} {a₂ b₂ : kFormat} {a₃ b₃ a₄ b₄ : MRat} : a₀ = b₀ → kCodeSeq.eqe a₁ b₁ → kFormat.eqe a₂ b₂ → a₃ = b₃ → a₄ = b₄ → kObservation.eqe (kObservation.observation a₀ a₁ a₂ a₃ a₄) (kObservation.observation b₀ b₁ b₂ b₃ b₄)
    | eqe_at {a₀ b₀ : kObservationSeq} {a₁ b₁ : MRat} : kObservationSeq.eqe a₀ b₀ → a₁ = b₁ → kObservation.eqe (kObservation.«at» a₀ a₁) (kObservation.«at» b₀ b₁)
    -- Equations
    | eq_p31zero9_sequences_zerozero3 {x xs} : kObservation.has_sort x MSort.Observation → kObservationSeq.has_sort xs MSort.ObservationSeq → kObservation.eqe (kObservation.«at» (kObservationSeq.ocons x xs) (0 : MRat)) x
    | eq_p31zero9_sequences_zerozero4 {x xs n} : kObservation.has_sort x MSort.Observation → kObservationSeq.has_sort xs MSort.ObservationSeq → MRat.has_sort n MSort.Nat → kBool.eqe (if (0 : MRat) < n then kBool.true else kBool.false) kBool.true → kObservation.eqe (kObservation.«at» (kObservationSeq.ocons x xs) n) (kObservation.«at» xs (if n ≤ (1 : MRat) then (1 : MRat) - n else n - (1 : MRat)))

  inductive kDeclaration.eqe: kDeclaration → kDeclaration → Prop
    | from_eqa {a b} : kDeclaration.eqa a b → kDeclaration.eqe a b
    | symm {a b} : kDeclaration.eqe a b → kDeclaration.eqe b a
    | trans {a b c} : kDeclaration.eqe a b → kDeclaration.eqe b c → kDeclaration.eqe a c
    -- Congruence axioms for each operator
    | eqe_exact {a₀ b₀ : kSpecialization} {a₁ b₁ : MString} {a₂ b₂ : kEvidence} : kSpecialization.eqe a₀ b₀ → a₁ = b₁ → kEvidence.eqe a₂ b₂ → kDeclaration.eqe (kDeclaration.exact a₀ a₁ a₂) (kDeclaration.exact b₀ b₁ b₂)
    | eqe_approximate {a₀ b₀ : kSpecialization} {a₁ b₁ : MString} {a₂ b₂ : kKappa} {a₃ b₃ : kEvidence} : kSpecialization.eqe a₀ b₀ → a₁ = b₁ → kKappa.eqe a₂ b₂ → kEvidence.eqe a₃ b₃ → kDeclaration.eqe (kDeclaration.approximate a₀ a₁ a₂ a₃) (kDeclaration.approximate b₀ b₁ b₂ b₃)
    | eqe_at {a₀ b₀ : kDeclarationSeq} {a₁ b₁ : MRat} : kDeclarationSeq.eqe a₀ b₀ → a₁ = b₁ → kDeclaration.eqe (kDeclaration.«at» a₀ a₁) (kDeclaration.«at» b₀ b₁)
    | eqe_partitioned {a₀ b₀ : kSpecialization} {a₁ b₁ : MString} {a₂ b₂ : kCodeSeq} {a₃ b₃ : kKappaPartSeq} {a₄ b₄ : kEvidence} : kSpecialization.eqe a₀ b₀ → a₁ = b₁ → kCodeSeq.eqe a₂ b₂ → kKappaPartSeq.eqe a₃ b₃ → kEvidence.eqe a₄ b₄ → kDeclaration.eqe (kDeclaration.partitioned a₀ a₁ a₂ a₃ a₄) (kDeclaration.partitioned b₀ b₁ b₂ b₃ b₄)
    -- Equations
    | eq_p31zero9_sequences_zerozero3 {x xs} : kDeclaration.has_sort x MSort.Declaration → kDeclarationSeq.has_sort xs MSort.DeclarationSeq → kDeclaration.eqe (kDeclaration.«at» (kDeclarationSeq.dcons x xs) (0 : MRat)) x
    | eq_p31zero9_sequences_zerozero4 {x xs n} : kDeclaration.has_sort x MSort.Declaration → kDeclarationSeq.has_sort xs MSort.DeclarationSeq → MRat.has_sort n MSort.Nat → kBool.eqe (if (0 : MRat) < n then kBool.true else kBool.false) kBool.true → kDeclaration.eqe (kDeclaration.«at» (kDeclarationSeq.dcons x xs) n) (kDeclaration.«at» xs (if n ≤ (1 : MRat) then (1 : MRat) - n else n - (1 : MRat)))

  inductive kEvidence.eqe: kEvidence → kEvidence → Prop
    | from_eqa {a b} : kEvidence.eqa a b → kEvidence.eqe a b
    | symm {a b} : kEvidence.eqe a b → kEvidence.eqe b a
    | trans {a b c} : kEvidence.eqe a b → kEvidence.eqe b c → kEvidence.eqe a c
    -- Congruence axioms for each operator

  inductive kKappaPart.eqe: kKappaPart → kKappaPart → Prop
    | from_eqa {a b} : kKappaPart.eqa a b → kKappaPart.eqe a b
    | symm {a b} : kKappaPart.eqe a b → kKappaPart.eqe b a
    | trans {a b c} : kKappaPart.eqe a b → kKappaPart.eqe b c → kKappaPart.eqe a c
    -- Congruence axioms for each operator
    | eqe_kappaPart {a₀ b₀ : kCodeSeq} {a₁ b₁ : kKappa} : kCodeSeq.eqe a₀ b₀ → kKappa.eqe a₁ b₁ → kKappaPart.eqe (kKappaPart.kappaPart a₀ a₁) (kKappaPart.kappaPart b₀ b₁)
    | eqe_at {a₀ b₀ : kKappaPartSeq} {a₁ b₁ : MRat} : kKappaPartSeq.eqe a₀ b₀ → a₁ = b₁ → kKappaPart.eqe (kKappaPart.«at» a₀ a₁) (kKappaPart.«at» b₀ b₁)
    -- Equations
    | eq_p31zero9_sequences_zerozero3 {x xs} : kKappaPart.has_sort x MSort.KappaPart → kKappaPartSeq.has_sort xs MSort.KappaPartSeq → kKappaPart.eqe (kKappaPart.«at» (kKappaPartSeq.kcons x xs) (0 : MRat)) x
    | eq_p31zero9_sequences_zerozero4 {x xs n} : kKappaPart.has_sort x MSort.KappaPart → kKappaPartSeq.has_sort xs MSort.KappaPartSeq → MRat.has_sort n MSort.Nat → kBool.eqe (if (0 : MRat) < n then kBool.true else kBool.false) kBool.true → kKappaPart.eqe (kKappaPart.«at» (kKappaPartSeq.kcons x xs) n) (kKappaPart.«at» xs (if n ≤ (1 : MRat) then (1 : MRat) - n else n - (1 : MRat)))

  inductive kArityEntry.eqe: kArityEntry → kArityEntry → Prop
    | from_eqa {a b} : kArityEntry.eqa a b → kArityEntry.eqe a b
    | symm {a b} : kArityEntry.eqe a b → kArityEntry.eqe b a
    | trans {a b c} : kArityEntry.eqe a b → kArityEntry.eqe b c → kArityEntry.eqe a c
    -- Congruence axioms for each operator
    | eqe_entry {a₀ b₀ : MString} {a₁ b₁ : MRat} : a₀ = b₀ → a₁ = b₁ → kArityEntry.eqe (kArityEntry.entry a₀ a₁) (kArityEntry.entry b₀ b₁)
    | eqe_at {a₀ b₀ : kArityTable} {a₁ b₁ : MRat} : kArityTable.eqe a₀ b₀ → a₁ = b₁ → kArityEntry.eqe (kArityEntry.«at» a₀ a₁) (kArityEntry.«at» b₀ b₁)
    -- Equations
    | eq_p31zero9_sequences_zerozero3 {x xs} : kArityEntry.has_sort x MSort.ArityEntry → kArityTable.has_sort xs MSort.ArityTable → kArityEntry.eqe (kArityEntry.«at» (kArityTable.acons x xs) (0 : MRat)) x
    | eq_p31zero9_sequences_zerozero4 {x xs n} : kArityEntry.has_sort x MSort.ArityEntry → kArityTable.has_sort xs MSort.ArityTable → MRat.has_sort n MSort.Nat → kBool.eqe (if (0 : MRat) < n then kBool.true else kBool.false) kBool.true → kArityEntry.eqe (kArityEntry.«at» (kArityTable.acons x xs) n) (kArityEntry.«at» xs (if n ≤ (1 : MRat) then (1 : MRat) - n else n - (1 : MRat)))

  inductive kKappaPartSeq.eqe: kKappaPartSeq → kKappaPartSeq → Prop
    | from_eqa {a b} : kKappaPartSeq.eqa a b → kKappaPartSeq.eqe a b
    | symm {a b} : kKappaPartSeq.eqe a b → kKappaPartSeq.eqe b a
    | trans {a b c} : kKappaPartSeq.eqe a b → kKappaPartSeq.eqe b c → kKappaPartSeq.eqe a c
    -- Congruence axioms for each operator
    | eqe_kcons {a₀ b₀ : kKappaPart} {a₁ b₁ : kKappaPartSeq} : kKappaPart.eqe a₀ b₀ → kKappaPartSeq.eqe a₁ b₁ → kKappaPartSeq.eqe (kKappaPartSeq.kcons a₀ a₁) (kKappaPartSeq.kcons b₀ b₁)

  inductive kPartitionSeq.eqe: kPartitionSeq → kPartitionSeq → Prop
    | from_eqa {a b} : kPartitionSeq.eqa a b → kPartitionSeq.eqe a b
    | symm {a b} : kPartitionSeq.eqe a b → kPartitionSeq.eqe b a
    | trans {a b c} : kPartitionSeq.eqe a b → kPartitionSeq.eqe b c → kPartitionSeq.eqe a c
    -- Congruence axioms for each operator
    | eqe_pcons {a₀ b₀ : kCodeSeq} {a₁ b₁ : kPartitionSeq} : kCodeSeq.eqe a₀ b₀ → kPartitionSeq.eqe a₁ b₁ → kPartitionSeq.eqe (kPartitionSeq.pcons a₀ a₁) (kPartitionSeq.pcons b₀ b₁)
    | eqe_partRegions {a b : kKappaPartSeq} : kKappaPartSeq.eqe a b → kPartitionSeq.eqe (kPartitionSeq.partRegions a) (kPartitionSeq.partRegions b)
    -- Equations
    | eq_p31zero9_part_regions_empty : kPartitionSeq.eqe (kPartitionSeq.partRegions kKappaPartSeq.knil) kPartitionSeq.pnil
    | eq_p31zero9_part_regions_cons {cs k kp} : kCodeSeq.has_sort cs MSort.CodeSeq → kKappa.has_sort k MSort.Kappa → kKappaPartSeq.has_sort kp MSort.KappaPartSeq → kPartitionSeq.eqe (kPartitionSeq.partRegions (kKappaPartSeq.kcons (kKappaPart.kappaPart cs k) kp)) (kPartitionSeq.pcons cs (kPartitionSeq.partRegions kp))

  inductive kDeclarationSeq.eqe: kDeclarationSeq → kDeclarationSeq → Prop
    | from_eqa {a b} : kDeclarationSeq.eqa a b → kDeclarationSeq.eqe a b
    | symm {a b} : kDeclarationSeq.eqe a b → kDeclarationSeq.eqe b a
    | trans {a b c} : kDeclarationSeq.eqe a b → kDeclarationSeq.eqe b c → kDeclarationSeq.eqe a c
    -- Congruence axioms for each operator
    | eqe_dcons {a₀ b₀ : kDeclaration} {a₁ b₁ : kDeclarationSeq} : kDeclaration.eqe a₀ b₀ → kDeclarationSeq.eqe a₁ b₁ → kDeclarationSeq.eqe (kDeclarationSeq.dcons a₀ a₁) (kDeclarationSeq.dcons b₀ b₁)

  inductive kSpecializationSeq.eqe: kSpecializationSeq → kSpecializationSeq → Prop
    | from_eqa {a b} : kSpecializationSeq.eqa a b → kSpecializationSeq.eqe a b
    | symm {a b} : kSpecializationSeq.eqe a b → kSpecializationSeq.eqe b a
    | trans {a b c} : kSpecializationSeq.eqe a b → kSpecializationSeq.eqe b c → kSpecializationSeq.eqe a c
    -- Congruence axioms for each operator
    | eqe_scons {a₀ b₀ : kSpecialization} {a₁ b₁ : kSpecializationSeq} : kSpecialization.eqe a₀ b₀ → kSpecializationSeq.eqe a₁ b₁ → kSpecializationSeq.eqe (kSpecializationSeq.scons a₀ a₁) (kSpecializationSeq.scons b₀ b₁)

  inductive kClassEnum.eqe: kClassEnum → kClassEnum → Prop
    | from_eqa {a b} : kClassEnum.eqa a b → kClassEnum.eqe a b
    | symm {a b} : kClassEnum.eqe a b → kClassEnum.eqe b a
    | trans {a b c} : kClassEnum.eqe a b → kClassEnum.eqe b c → kClassEnum.eqe a c
    -- Congruence axioms for each operator
    | eqe_Class {a₀ b₀ : kFormat} {a₁ b₁ : MRat} : kFormat.eqe a₀ b₀ → a₁ = b₁ → kClassEnum.eqe (kClassEnum.Class a₀ a₁) (kClassEnum.Class b₀ b₁)
    | eqe_ifthenelsefi {a₀ b₀ : kBool} {a₁ b₁ a₂ b₂ : kClassEnum} : kBool.eqe a₀ b₀ → kClassEnum.eqe a₁ b₁ → kClassEnum.eqe a₂ b₂ → kClassEnum.eqe (kClassEnum.ifthenelsefi a₀ a₁ a₂) (kClassEnum.ifthenelsefi b₀ b₁ b₂)
    -- Equations
    | eq_p31zero9_predicates_zero15 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.IsNaN f c) kBool.true → kClassEnum.eqe (kClassEnum.Class f c) kClassEnum.ClsNaN
    | eq_p31zero9_predicates_zero16 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.IsZero f c) kBool.true → kClassEnum.eqe (kClassEnum.Class f c) kClassEnum.ClsZero
    | eq_p31zero9_predicates_zero17 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.IsInfinite f c) kBool.true → kClassEnum.eqe (kClassEnum.Class f c) (kClassEnum.ifthenelsefi (kBool.IsSignMinus f c) kClassEnum.ClsNegativeInfinity kClassEnum.ClsPositiveInfinity)
    | eq_p31zero9_predicates_zero18 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.IsNormal f c) kBool.true → kClassEnum.eqe (kClassEnum.Class f c) (kClassEnum.ifthenelsefi (kBool.IsSignMinus f c) kClassEnum.ClsNegativeNormal kClassEnum.ClsPositiveNormal)
    | eq_p31zero9_predicates_zero19 {f c} : kFormat.has_sort f MSort.Format → MRat.has_sort c MSort.Int → kBool.eqe (kBool.validCode f c) kBool.true → kBool.eqe (kBool.IsSubnormal f c) kBool.true → kClassEnum.eqe (kClassEnum.Class f c) (kClassEnum.ifthenelsefi (kBool.IsSignMinus f c) kClassEnum.ClsNegativeSubnormal kClassEnum.ClsPositiveSubnormal)
    | eq_itet {l r} : kClassEnum.eqe (kClassEnum.ifthenelsefi kBool.true l r) l
    | eq_itef {l r} : kClassEnum.eqe (kClassEnum.ifthenelsefi kBool.false l r) r

  inductive kObservationSeq.eqe: kObservationSeq → kObservationSeq → Prop
    | from_eqa {a b} : kObservationSeq.eqa a b → kObservationSeq.eqe a b
    | symm {a b} : kObservationSeq.eqe a b → kObservationSeq.eqe b a
    | trans {a b c} : kObservationSeq.eqe a b → kObservationSeq.eqe b c → kObservationSeq.eqe a c
    -- Congruence axioms for each operator
    | eqe_ocons {a₀ b₀ : kObservation} {a₁ b₁ : kObservationSeq} : kObservation.eqe a₀ b₀ → kObservationSeq.eqe a₁ b₁ → kObservationSeq.eqe (kObservationSeq.ocons a₀ a₁) (kObservationSeq.ocons b₀ b₁)

  inductive kArityTable.eqe: kArityTable → kArityTable → Prop
    | from_eqa {a b} : kArityTable.eqa a b → kArityTable.eqe a b
    | symm {a b} : kArityTable.eqe a b → kArityTable.eqe b a
    | trans {a b c} : kArityTable.eqe a b → kArityTable.eqe b c → kArityTable.eqe a c
    -- Congruence axioms for each operator
    | eqe_acons {a₀ b₀ : kArityEntry} {a₁ b₁ : kArityTable} : kArityEntry.eqe a₀ b₀ → kArityTable.eqe a₁ b₁ → kArityTable.eqe (kArityTable.acons a₀ a₁) (kArityTable.acons b₀ b₁)
    -- Equations
    | eq_p31zero9_decl_numeric_table : kArityTable.eqe kArityTable.numericArityTable (kArityTable.acons (kArityEntry.entry ("Convert" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("Abs" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("Negate" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("Sqrt" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("Recip" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("RSqrt" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("Exp" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("Exp2" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("Log" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("Log2" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("LogOnePlus" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("ExpMinusOne" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("Sin" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("Cos" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("Tan" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("ArcSin" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("ArcCos" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("ArcTan" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("Sinh" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("Cosh" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("Tanh" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("ArcSinh" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("ArcCosh" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("ArcTanh" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("SinPi" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("CosPi" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("TanPi" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("ArcSinPi" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("ArcCosPi" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("ArcTanPi" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("Softplus" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("CopySign" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("Add" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("Subtract" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("Multiply" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("Divide" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("Hypot" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ArcTan2" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ArcTan2Pi" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("Minimum" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("Maximum" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("MinimumNumber" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("MaximumNumber" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("MinimumMagnitude" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("MaximumMagnitude" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("MinimumMagnitudeNumber" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("MaximumMagnitudeNumber" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("MinimumFinite" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("MaximumFinite" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledConvert" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledAbs" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledNegate" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledSqrt" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledRecip" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledRSqrt" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledExp" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledExp2" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledLog" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledLog2" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledLogOnePlus" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledExpMinusOne" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledSin" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledCos" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledTan" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledArcSin" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledArcCos" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledArcTan" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledSinh" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledCosh" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledTanh" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledArcSinh" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledArcCosh" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledArcTanh" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledSinPi" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledCosPi" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledTanPi" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledArcSinPi" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledArcCosPi" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledArcTanPi" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledSoftplus" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("FMA" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("FAA" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("Clamp" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledCopySign" : MString) (5 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledAdd" : MString) (5 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledSubtract" : MString) (5 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledMultiply" : MString) (5 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledDivide" : MString) (5 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledHypot" : MString) (5 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledArcTan2" : MString) (5 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledArcTan2Pi" : MString) (5 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledMinimum" : MString) (5 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledMaximum" : MString) (5 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledMinimumNumber" : MString) (5 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledMaximumNumber" : MString) (5 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledMinimumMagnitude" : MString) (5 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledMaximumMagnitude" : MString) (5 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledMinimumMagnitudeNumber" : MString) (5 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledMaximumMagnitudeNumber" : MString) (5 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledMinimumFinite" : MString) (5 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledMaximumFinite" : MString) (5 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledFMA" : MString) (7 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledFAA" : MString) (7 : MRat)) (kArityTable.acons (kArityEntry.entry ("ScaledClamp" : MString) (7 : MRat)) kArityTable.anil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | eq_p31zero9_decl_plain_table : kArityTable.eqe kArityTable.plainArityTable (kArityTable.acons (kArityEntry.entry ("RoundOf" : MString) (0 : MRat)) (kArityTable.acons (kArityEntry.entry ("SatOf" : MString) (0 : MRat)) (kArityTable.acons (kArityEntry.entry ("IsZero" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("IsOne" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("IsNaN" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("IsInfinite" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("IsFinite" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("IsSignMinus" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("IsNormal" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("IsSubnormal" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("Class" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("BitwidthOf" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("PrecisionOf" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("ExponentBitwidthOf" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("TrailingSignificandBitwidthOf" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("ExponentBiasOf" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("SignednessOf" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("DomainOf" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("MaxFiniteOf" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("MinFiniteOf" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("MinPositiveOf" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("MaxSubnormalOf" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("MinNormalOf" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("NextGreaterThan" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("NextLessThan" : MString) (1 : MRat)) (kArityTable.acons (kArityEntry.entry ("CompareLess" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("CompareLessEqual" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("CompareEqual" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("CompareGreater" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("CompareGreaterEqual" : MString) (2 : MRat)) (kArityTable.acons (kArityEntry.entry ("TotalOrder" : MString) (2 : MRat)) kArityTable.anil)))))))))))))))))))))))))))))))
    | eq_p31zero9_block_element_arity_table : kArityTable.eqe kArityTable.blockElementArityTable (kArityTable.acons (kArityEntry.entry ("ConvertFromBlock" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("ConvertToBlock" : MString) (3 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockConvert" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockAbs" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockNegate" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockSqrt" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockRecip" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockRSqrt" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockExp" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockExp2" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockLog" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockLog2" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockLogOnePlus" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockExpMinusOne" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockSin" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockCos" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockTan" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockArcSin" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockArcCos" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockArcTan" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockSinh" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockCosh" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockTanh" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockArcSinh" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockArcCosh" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockArcTanh" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockSinPi" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockCosPi" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockTanPi" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockArcSinPi" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockArcCosPi" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockArcTanPi" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockSoftplus" : MString) (4 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockCopySign" : MString) (6 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockAdd" : MString) (6 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockSubtract" : MString) (6 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockMultiply" : MString) (6 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockDivide" : MString) (6 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockHypot" : MString) (6 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockArcTan2" : MString) (6 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockArcTan2Pi" : MString) (6 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockMinimum" : MString) (6 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockMaximum" : MString) (6 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockMinimumNumber" : MString) (6 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockMaximumNumber" : MString) (6 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockMinimumMagnitude" : MString) (6 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockMaximumMagnitude" : MString) (6 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockMinimumMagnitudeNumber" : MString) (6 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockMaximumMagnitudeNumber" : MString) (6 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockMinimumFinite" : MString) (6 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockMaximumFinite" : MString) (6 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockFMA" : MString) (8 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockFAA" : MString) (8 : MRat)) (kArityTable.acons (kArityEntry.entry ("BlockClamp" : MString) (8 : MRat)) kArityTable.anil))))))))))))))))))))))))))))))))))))))))))))))))))))))

end
end Maude
