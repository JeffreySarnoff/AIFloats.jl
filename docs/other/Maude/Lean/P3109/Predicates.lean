-- Extracted from ../spec2.lean, lines 725-961.
-- See PLAN.md and manifest.json for provenance.
import P3109.Native.Operators

namespace Maude
-- Kind assignment
def kind : MSort → Type
  | MSort.Bool => kBool
  | MSort.Zero => MRat
  | MSort.NzNat => MRat
  | MSort.Nat => MRat
  | MSort.NzInt => MRat
  | MSort.Int => MRat
  | MSort.PosRat => MRat
  | MSort.NzRat => MRat
  | MSort.Rat => MRat
  | MSort.Real => kXReal
  | MSort.Number => kXReal
  | MSort.Infinity => kXReal
  | MSort.XReal => kXReal
  | MSort.Format => kFormat
  | MSort.Signedness => kSignedness
  | MSort.Domain => kDomain
  | MSort.BoundQuery => kBoundQuery
  | MSort.RandomSeq => kRandomSeq
  | MSort.RoundMode => kBlockRoundMode
  | MSort.SatMode => kSatMode
  | MSort.ProjSpec => kProjSpec
  | MSort.BlockRoundMode => kBlockRoundMode
  | MSort.BlockProjSpec => kBlockProjSpec
  | MSort.XSeq => kXSeq
  | MSort.CodeSeq => kCodeSeq
  | MSort.Block => kBlock
  | MSort.String => MString
  | MSort.Char => MString
  | MSort.FindResult => MRat
  | MSort.FormatSeq => kFormatSeq
  | MSort.Specialization => kSpecialization
  | MSort.Kappa => kKappa
  | MSort.Observation => kObservation
  | MSort.Declaration => kDeclaration
  | MSort.Evidence => kEvidence
  | MSort.KappaPart => kKappaPart
  | MSort.ArityEntry => kArityEntry
  | MSort.KappaPartSeq => kKappaPartSeq
  | MSort.PartitionSeq => kPartitionSeq
  | MSort.DeclarationSeq => kDeclarationSeq
  | MSort.SpecializationSeq => kSpecializationSeq
  | MSort.ClassEnum => kClassEnum
  | MSort.ObservationSeq => kObservationSeq
  | MSort.ArityTable => kArityTable

-- Predicates recognizing constructor terms
mutual

  def kBool.ctor_only : kBool → Prop
    | kBool.true => true
    | kBool.false => true
    | _ => false

  def kXReal.ctor_only : kXReal → Prop
    | (kXReal.fin a) => true
    | kXReal.posInf => true
    | kXReal.negInf => true
    | kXReal.nan => true
    | (kXReal.realAdd a₀ a₁) => a₀.ctor_only ∧ a₁.ctor_only
    | (kXReal.realMultiply a₀ a₁) => a₀.ctor_only ∧ a₁.ctor_only
    | (kXReal.realNegate a) => a.ctor_only
    | (kXReal.realAbs a) => a.ctor_only
    | (kXReal.realDivide a₀ a₁) => a₀.ctor_only ∧ a₁.ctor_only
    | (kXReal.piMultiple a) => true
    | (kXReal.exprSqrt a) => a.ctor_only
    | (kXReal.exprExp a) => a.ctor_only
    | (kXReal.exprExp2 a) => a.ctor_only
    | (kXReal.exprLog a) => a.ctor_only
    | (kXReal.exprLog2 a) => a.ctor_only
    | (kXReal.exprSin a) => a.ctor_only
    | (kXReal.exprCos a) => a.ctor_only
    | (kXReal.exprTan a) => a.ctor_only
    | (kXReal.exprArcSin a) => a.ctor_only
    | (kXReal.exprArcCos a) => a.ctor_only
    | (kXReal.exprArcTan a) => a.ctor_only
    | (kXReal.exprSinh a) => a.ctor_only
    | (kXReal.exprCosh a) => a.ctor_only
    | (kXReal.exprTanh a) => a.ctor_only
    | (kXReal.exprArcSinh a) => a.ctor_only
    | (kXReal.exprArcCosh a) => a.ctor_only
    | (kXReal.exprArcTanh a) => a.ctor_only
    | _ => false

  def kFormat.ctor_only : kFormat → Prop
    | (kFormat.Binary a₀ a₁ a₂ a₃) => a₂.ctor_only ∧ a₃.ctor_only
    | kFormat.binary64 => true
    | kFormat.binary32 => true
    | kFormat.binary16 => true
    | kFormat.BFloat16 => true
    | _ => false

  def kSignedness.ctor_only : kSignedness → Prop
    | kSignedness.Signed => true
    | kSignedness.Unsigned => true
    | _ => false

  def kDomain.ctor_only : kDomain → Prop
    | kDomain.Finite => true
    | kDomain.Extended => true
    | _ => false

  def kBoundQuery.ctor_only : kBoundQuery → Prop
    | kBoundQuery.maxFiniteQuery => true
    | kBoundQuery.minFiniteQuery => true
    | kBoundQuery.minPositiveQuery => true
    | kBoundQuery.maxSubnormalQuery => true
    | kBoundQuery.minNormalQuery => true

  def kRandomSeq.ctor_only : kRandomSeq → Prop
    | kRandomSeq.rnil => true
    | (kRandomSeq.rcons a₀ a₁) => a₁.ctor_only

  def kBlockRoundMode.ctor_only : kBlockRoundMode → Prop
    | kBlockRoundMode.NearestTiesToEven => true
    | kBlockRoundMode.NearestTiesToAway => true
    | kBlockRoundMode.TowardPositive => true
    | kBlockRoundMode.TowardNegative => true
    | kBlockRoundMode.TowardZero => true
    | kBlockRoundMode.ToOdd => true
    | (kBlockRoundMode.StochasticA a₀ a₁) => true
    | (kBlockRoundMode.StochasticB a₀ a₁) => true
    | (kBlockRoundMode.StochasticC a₀ a₁) => true
    | (kBlockRoundMode.BlockStochasticA a₀ a₁) => a₁.ctor_only
    | (kBlockRoundMode.BlockStochasticB a₀ a₁) => a₁.ctor_only
    | (kBlockRoundMode.BlockStochasticC a₀ a₁) => a₁.ctor_only
    | _ => false

  def kSatMode.ctor_only : kSatMode → Prop
    | kSatMode.SatNone => true
    | kSatMode.SatFinite => true
    | kSatMode.SatPropagate => true
    | _ => false

  def kProjSpec.ctor_only : kProjSpec → Prop
    | (kProjSpec.proj a₀ a₁) => a₀.ctor_only ∧ a₁.ctor_only
    | _ => false

  def kBlockProjSpec.ctor_only : kBlockProjSpec → Prop
    | (kBlockProjSpec.bproj a₀ a₁) => a₀.ctor_only ∧ a₁.ctor_only
    | _ => false

  def kXSeq.ctor_only : kXSeq → Prop
    | kXSeq.xnil => true
    | (kXSeq.xcons a₀ a₁) => a₀.ctor_only ∧ a₁.ctor_only
    | _ => false

  def kCodeSeq.ctor_only : kCodeSeq → Prop
    | kCodeSeq.cnil => true
    | (kCodeSeq.ccons a₀ a₁) => a₁.ctor_only
    | _ => false

  def kBlock.ctor_only : kBlock → Prop
    | (kBlock.block a₀ a₁) => a₁.ctor_only
    | _ => false

  def kFormatSeq.ctor_only : kFormatSeq → Prop
    | kFormatSeq.fnil => true
    | (kFormatSeq.fcons a₀ a₁) => a₀.ctor_only ∧ a₁.ctor_only

  def kSpecialization.ctor_only : kSpecialization → Prop
    | (kSpecialization.numeric a₀ a₁ a₂) => a₁.ctor_only ∧ a₂.ctor_only
    | (kSpecialization.plain a₀ a₁) => a₁.ctor_only
    | (kSpecialization.blockElements a₀ a₁ a₂ a₃) => a₂.ctor_only ∧ a₃.ctor_only
    | (kSpecialization.blockReduction a₀ a₁ a₂ a₃) => a₂.ctor_only ∧ a₃.ctor_only
    | (kSpecialization.blockScale a₀ a₁ a₂ a₃ a₄) => a₂.ctor_only ∧ a₃.ctor_only ∧ a₄.ctor_only
    | _ => false

  def kKappa.ctor_only : kKappa → Prop
    | (kKappa.steps a) => true
    | kKappa.kNaN => true
    | kKappa.kInfinity => true
    | _ => false

  def kObservation.ctor_only : kObservation → Prop
    | (kObservation.observation a₀ a₁ a₂ a₃ a₄) => a₁.ctor_only ∧ a₂.ctor_only
    | _ => false

  def kDeclaration.ctor_only : kDeclaration → Prop
    | (kDeclaration.exact a₀ a₁ a₂) => a₀.ctor_only ∧ a₂.ctor_only
    | (kDeclaration.approximate a₀ a₁ a₂ a₃) => a₀.ctor_only ∧ a₂.ctor_only ∧ a₃.ctor_only
    | (kDeclaration.partitioned a₀ a₁ a₂ a₃ a₄) => a₀.ctor_only ∧ a₂.ctor_only ∧ a₃.ctor_only ∧ a₄.ctor_only
    | _ => false

  def kEvidence.ctor_only : kEvidence → Prop
    | kEvidence.pendingEvidence => true
    | kEvidence.sampleEvidence => true
    | kEvidence.exhaustiveEvidence => true
    | kEvidence.proofEvidence => true

  def kKappaPart.ctor_only : kKappaPart → Prop
    | (kKappaPart.kappaPart a₀ a₁) => a₀.ctor_only ∧ a₁.ctor_only
    | _ => false

  def kArityEntry.ctor_only : kArityEntry → Prop
    | (kArityEntry.entry a₀ a₁) => true
    | _ => false

  def kKappaPartSeq.ctor_only : kKappaPartSeq → Prop
    | kKappaPartSeq.knil => true
    | (kKappaPartSeq.kcons a₀ a₁) => a₀.ctor_only ∧ a₁.ctor_only

  def kPartitionSeq.ctor_only : kPartitionSeq → Prop
    | kPartitionSeq.pnil => true
    | (kPartitionSeq.pcons a₀ a₁) => a₀.ctor_only ∧ a₁.ctor_only
    | _ => false

  def kDeclarationSeq.ctor_only : kDeclarationSeq → Prop
    | kDeclarationSeq.dnil => true
    | (kDeclarationSeq.dcons a₀ a₁) => a₀.ctor_only ∧ a₁.ctor_only

  def kSpecializationSeq.ctor_only : kSpecializationSeq → Prop
    | kSpecializationSeq.snil => true
    | (kSpecializationSeq.scons a₀ a₁) => a₀.ctor_only ∧ a₁.ctor_only

  def kClassEnum.ctor_only : kClassEnum → Prop
    | kClassEnum.ClsNaN => true
    | kClassEnum.ClsNegativeInfinity => true
    | kClassEnum.ClsNegativeNormal => true
    | kClassEnum.ClsNegativeSubnormal => true
    | kClassEnum.ClsZero => true
    | kClassEnum.ClsPositiveSubnormal => true
    | kClassEnum.ClsPositiveNormal => true
    | kClassEnum.ClsPositiveInfinity => true
    | _ => false

  def kObservationSeq.ctor_only : kObservationSeq → Prop
    | kObservationSeq.onil => true
    | (kObservationSeq.ocons a₀ a₁) => a₀.ctor_only ∧ a₁.ctor_only

  def kArityTable.ctor_only : kArityTable → Prop
    | kArityTable.anil => true
    | (kArityTable.acons a₀ a₁) => a₀.ctor_only ∧ a₁.ctor_only
    | _ => false
end

end Maude
