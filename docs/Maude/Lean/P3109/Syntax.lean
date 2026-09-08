-- Extracted from ../spec2.lean, lines 74-549.
-- See PLAN.md and manifest.json for provenance.
import P3109.Foundations

namespace Maude
-- Kinds and their operators

inductive kBoundQuery
  | maxFiniteQuery
  | minFiniteQuery
  | minPositiveQuery
  | maxSubnormalQuery
  | minNormalQuery

inductive kEvidence
  | pendingEvidence
  | sampleEvidence
  | exhaustiveEvidence
  | proofEvidence

mutual

  inductive kArityEntry
    | entry : MString → MRat → kArityEntry
    | «at» : kArityTable → MRat → kArityEntry

  inductive kArityTable
    | anil
    | acons : kArityEntry → kArityTable → kArityTable
    | numericArityTable
    | plainArityTable
    | blockElementArityTable

  inductive kBlock
    | block : MRat → kCodeSeq → kBlock
    | ConvertToBlockMaxAbsFinite : MRat → kFormat → kFormat → kFormat → kProjSpec → kBlockProjSpec → kCodeSeq → kBlock
    | computedBlock : MRat → kFormat → kFormat → kBlockProjSpec → MRat → kXSeq → kBlock
    | BlockConvert : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockAbs : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockNegate : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockCopySign : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockAdd : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockSubtract : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockMultiply : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockDivide : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockFMA : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockFAA : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockRecip : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockMinimum : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockMaximum : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockMinimumNumber : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockMaximumNumber : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockMinimumMagnitude : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockMaximumMagnitude : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockMinimumMagnitudeNumber : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockMaximumMagnitudeNumber : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockMinimumFinite : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockMaximumFinite : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockClamp : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockSqrt : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockRSqrt : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockExp : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockExp2 : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockLog : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockLog2 : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockLogOnePlus : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockExpMinusOne : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockSin : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockCos : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockTan : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockArcSin : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockArcCos : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockArcTan : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockSinh : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockCosh : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockTanh : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockArcSinh : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockArcCosh : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockArcTanh : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockSinPi : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockCosPi : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockTanPi : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockArcSinPi : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockArcCosPi : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockArcTanPi : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockSoftplus : MRat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kBlock
    | BlockHypot : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockArcTan2 : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock
    | BlockArcTan2Pi : MRat → kFormat → kFormat → kFormat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → MRat → kCodeSeq → MRat → kBlock

  inductive kBlockProjSpec
    | bproj : kBlockRoundMode → kSatMode → kBlockProjSpec
    | singletonLift : kProjSpec → kBlockProjSpec

  inductive kBlockRoundMode
    | NearestTiesToEven
    | NearestTiesToAway
    | TowardPositive
    | TowardNegative
    | TowardZero
    | ToOdd
    | StochasticA : MRat → MRat → kBlockRoundMode
    | StochasticB : MRat → MRat → kBlockRoundMode
    | StochasticC : MRat → MRat → kBlockRoundMode
    | BlockStochasticA : MRat → kRandomSeq → kBlockRoundMode
    | BlockStochasticB : MRat → kRandomSeq → kBlockRoundMode
    | BlockStochasticC : MRat → kRandomSeq → kBlockRoundMode
    | RoundOf : kProjSpec → kBlockRoundMode

  inductive kBool
    | true
    | false
    | and : kBool → kBool → kBool
    | or : kBool → kBool → kBool
    | xor : kBool → kBool → kBool
    | not : kBool → kBool
    | implies : kBool → kBool → kBool
    | lt₀ : MRat → MRat → kBool
    | lteq₀ : MRat → MRat → kBool
    | gt₀ : MRat → MRat → kBool
    | gteq₀ : MRat → MRat → kBool
    | divides : MRat → MRat → kBool
    | xNaN : kXReal → kBool
    | xInfinite : kXReal → kBool
    | xFinite : kXReal → kBool
    | xMinus : kXReal → kBool
    | xLt : kXReal → kXReal → kBool
    | xLe : kXReal → kXReal → kBool
    | xEq : kXReal → kXReal → kBool
    | even : MRat → kBool
    | validFormat : kFormat → kBool
    | internalFormat : kFormat → kBool
    | externalDatum : kFormat → kXReal → kBool
    | validCode : kFormat → MRat → kBool
    | datum : kFormat → kXReal → kBool
    | candidateDatum : kFormat → MRat → MRat → kBool
    | randomInRange : MRat → MRat → kBool
    | validRound : kBlockRoundMode → kBool
    | validProjection : kProjSpec → kBool
    | validBlockProjection : kBlockProjSpec → MRat → kBool
    | validRandoms : MRat → kRandomSeq → kBool
    | deterministic : kBlockRoundMode → kBool
    | roundAway : kBlockRoundMode → MRat → MRat → kBool → kBool
    | clipsHigh : kBlockRoundMode → kBool
    | clipsLow : kBlockRoundMode → kBool
    | validCodes : kFormat → kCodeSeq → kBool
    | validBlock : MRat → kFormat → kFormat → MRat → kCodeSeq → kBool
    | lt₁ : MString → MString → kBool
    | lteq₁ : MString → MString → kBool
    | gt₁ : MString → MString → kBool
    | gteq₁ : MString → MString → kBool
    | CompareLess : kFormat → kFormat → MRat → MRat → kBool
    | CompareLessEqual : kFormat → kFormat → MRat → MRat → kBool
    | CompareEqual : kFormat → kFormat → MRat → MRat → kBool
    | CompareGreaterEqual : kFormat → kFormat → MRat → MRat → kBool
    | CompareGreater : kFormat → kFormat → MRat → MRat → kBool
    | IsZero : kFormat → MRat → kBool
    | IsOne : kFormat → MRat → kBool
    | IsNaN : kFormat → MRat → kBool
    | IsInfinite : kFormat → MRat → kBool
    | IsFinite : kFormat → MRat → kBool
    | IsSignMinus : kFormat → MRat → kBool
    | IsNormal : kFormat → MRat → kBool
    | IsSubnormal : kFormat → MRat → kBool
    | inF4 : kFormat → kBool
    | inF8 : kFormat → kBool
    | inFs : kFormat → kBool
    | allowedExternal : kFormat → kBool
    | containsFormat : kFormat → kFormatSeq → kBool
    | validFX : kFormatSeq → kBool
    | validFXTail : kFormatSeq → kBool
    | allFormats : kFormatSeq → kBool
    | required : kSpecialization → kFormatSeq → kBool
    | requiredNumeric : MString → kFormatSeq → kFormatSeq → kBool
    | requiredPlain : MString → kFormatSeq → kFormatSeq → kBool
    | minmaxName : MString → kBool
    | compareName : MString → kBool
    | predicateName : MString → kBool
    | formatNameOp : MString → kBool
    | numericPlainName : MString → kBool
    | blockElementArity : MString → MRat → kBool
    | numericResult : kSpecialization → kBool
    | hasDeclaration : kSpecialization → kDeclarationSeq → kBool
    | declarationsCover : kSpecializationSeq → kDeclarationSeq → kBool
    | partition : kCodeSeq → kPartitionSeq → kBool
    | partitionDisjoint : kPartitionSeq → kBool
    | validSpecialization : kSpecialization → kBool
    | numericArity : MString → MRat → kBool
    | plainArity : MString → MRat → kBool
    | wellFormedDeclaration : kDeclaration → kBool
    | evidenceComplete : kEvidence → kBool
    | memberCode : MRat → kCodeSeq → kBool
    | disjointCodes : kCodeSeq → kCodeSeq → kBool
    | uniqueCodes : kCodeSeq → kBool
    | subsetCodes : kCodeSeq → kCodeSeq → kBool
    | partition2 : kCodeSeq → kCodeSeq → kCodeSeq → kBool
    | inArityTable : MString → MRat → kArityTable → kBool
    | TotalOrder : kFormat → kFormat → MRat → MRat → kBool
    | eqeq₀ : MRat → MRat → kBool
    | ifthenelsefi : kBool → kBool → kBool → kBool
    | eqeq₁ : kSignedness → kSignedness → kBool
    | eqeq₂ : kDomain → kDomain → kBool
    | eqslasheq₀ : MRat → MRat → kBool
    | eqeq₃ : kBlockRoundMode → kBlockRoundMode → kBool
    | eqeq₄ : kBool → kBool → kBool
    | eqeq₅ : MString → MString → kBool
    | eqeq₆ : kFormat → kFormat → kBool
    | eqeq₇ : kProjSpec → kProjSpec → kBool
    | eqslasheq₁ : kBool → kBool → kBool
    | eqslasheq₂ : MString → MString → kBool
    | eqeq₈ : kSpecialization → kSpecialization → kBool

  inductive kCodeSeq
    | cnil
    | ccons : MRat → kCodeSeq → kCodeSeq
    | blockProject : MRat → kFormat → kFormat → kBlockProjSpec → MRat → kXSeq → kCodeSeq
    | projectElements : kFormat → kBlockProjSpec → kXReal → kXSeq → MRat → kCodeSeq
    | projectUnscaled : kFormat → kBlockProjSpec → kXSeq → MRat → kCodeSeq
    | «at» : kPartitionSeq → MRat → kCodeSeq
    | partitionUnion : kPartitionSeq → kCodeSeq
    | appendCodes : kCodeSeq → kCodeSeq → kCodeSeq
    | ConvertFromBlock : MRat → kFormat → kFormat → kFormat → kBlockProjSpec → MRat → kCodeSeq → kCodeSeq
    | ConvertToBlock : MRat → kFormat → kFormat → kFormat → kBlockProjSpec → kCodeSeq → MRat → kCodeSeq

  inductive kDeclaration
    | exact : kSpecialization → MString → kEvidence → kDeclaration
    | approximate : kSpecialization → MString → kKappa → kEvidence → kDeclaration
    | «at» : kDeclarationSeq → MRat → kDeclaration
    | partitioned : kSpecialization → MString → kCodeSeq → kKappaPartSeq → kEvidence → kDeclaration

  inductive kDeclarationSeq
    | dnil
    | dcons : kDeclaration → kDeclarationSeq → kDeclarationSeq

  inductive kDomain
    | Finite
    | Extended
    | DomainOf : kFormat → kDomain

  inductive kFormat
    | Binary : MRat → MRat → kSignedness → kDomain → kFormat
    | binary64
    | binary32
    | binary16
    | BFloat16
    | «at» : kFormatSeq → MRat → kFormat

  inductive kFormatSeq
    | fnil
    | fcons : kFormat → kFormatSeq → kFormatSeq

  inductive kKappa
    | steps : MRat → kKappa
    | kNaN
    | kInfinity
    | partBound : kKappaPartSeq → kKappa
    | declarationKappa : kDeclaration → kKappa
    | observationKappa : kObservation → kKappa
    | batchKappa : kObservationSeq → kKappa
    | mergeKappa : kKappa → kKappa → kKappa

  inductive kKappaPart
    | kappaPart : kCodeSeq → kKappa → kKappaPart
    | «at» : kKappaPartSeq → MRat → kKappaPart

  inductive kKappaPartSeq
    | knil
    | kcons : kKappaPart → kKappaPartSeq → kKappaPartSeq

  inductive kObservation
    | observation : MString → kCodeSeq → kFormat → MRat → MRat → kObservation
    | «at» : kObservationSeq → MRat → kObservation

  inductive kObservationSeq
    | onil
    | ocons : kObservation → kObservationSeq → kObservationSeq

  inductive kPartitionSeq
    | pnil
    | pcons : kCodeSeq → kPartitionSeq → kPartitionSeq
    | partRegions : kKappaPartSeq → kPartitionSeq

  inductive kProjSpec
    | proj : kBlockRoundMode → kSatMode → kProjSpec
    | projectionAt : kBlockProjSpec → MRat → kProjSpec

  inductive kRandomSeq
    | rnil
    | rcons : MRat → kRandomSeq → kRandomSeq

  inductive kSatMode
    | SatNone
    | SatFinite
    | SatPropagate
    | SatOf : kProjSpec → kSatMode

  inductive kSignedness
    | Signed
    | Unsigned
    | SignednessOf : kFormat → kSignedness

  inductive kSpecialization
    | numeric : MString → kFormatSeq → kProjSpec → kSpecialization
    | plain : MString → kFormatSeq → kSpecialization
    | blockElements : MString → MRat → kFormatSeq → kBlockProjSpec → kSpecialization
    | blockReduction : MString → MRat → kFormatSeq → kProjSpec → kSpecialization
    | blockScale : MString → MRat → kFormatSeq → kProjSpec → kBlockProjSpec → kSpecialization
    | «at» : kSpecializationSeq → MRat → kSpecialization
    | declaredIdentity : kDeclaration → kSpecialization

  inductive kSpecializationSeq
    | snil
    | scons : kSpecialization → kSpecializationSeq → kSpecializationSeq

  inductive kXReal
    | fin : MRat → kXReal
    | posInf
    | negInf
    | nan
    | externalDecode : kFormat → MRat → kXReal
    | decode : kFormat → MRat → kXReal
    | roundToPrecision : MRat → MRat → kBlockRoundMode → kXReal → kXReal
    | saturate : MRat → MRat → kSatMode → kBlockRoundMode → kXReal → kSignedness → kDomain → kXReal
    | overflow : kSignedness → kDomain → kBool → kXReal
    | omegaConvert : kXReal → kXReal
    | omegaAbs : kXReal → kXReal
    | omegaNegate : kXReal → kXReal
    | omegaRecip : kXReal → kXReal
    | omegaCopySign : kXReal → kXReal → kXReal
    | omegaAdd : kXReal → kXReal → kXReal
    | omegaSubtract : kXReal → kXReal → kXReal
    | omegaMultiply : kXReal → kXReal → kXReal
    | omegaDivide : kXReal → kXReal → kXReal
    | omegaFMA : kXReal → kXReal → kXReal → kXReal
    | omegaFAA : kXReal → kXReal → kXReal → kXReal
    | «at» : kXSeq → MRat → kXReal
    | normalizeElement : kXReal → kXReal → kXReal
    | omegaMinimum : kXReal → kXReal → kXReal
    | omegaMaximum : kXReal → kXReal → kXReal
    | omegaMinimumNumber : kXReal → kXReal → kXReal
    | omegaMaximumNumber : kXReal → kXReal → kXReal
    | omegaMinimumMagnitude : kXReal → kXReal → kXReal
    | omegaMaximumMagnitude : kXReal → kXReal → kXReal
    | omegaMinimumMagnitudeNumber : kXReal → kXReal → kXReal
    | omegaMaximumMagnitudeNumber : kXReal → kXReal → kXReal
    | omegaMinimumFinite : kXReal → kXReal → kXReal
    | omegaMaximumFinite : kXReal → kXReal → kXReal
    | omegaClamp : kXReal → kXReal → kXReal → kXReal
    | foldAdd : kXReal → kXSeq → kXReal
    | foldMultiply : kXReal → kXSeq → kXReal
    | foldMaximumFinite : kXReal → kXSeq → kXReal
    | realAdd : kXReal → kXReal → kXReal
    | realMultiply : kXReal → kXReal → kXReal
    | realNegate : kXReal → kXReal
    | realAbs : kXReal → kXReal
    | realDivide : kXReal → kXReal → kXReal
    | piMultiple : MRat → kXReal
    | pi
    | omegaHypot : kXReal → kXReal → kXReal
    | omegaArcTan2 : kXReal → kXReal → kXReal
    | omegaArcTan2Pi : kXReal → kXReal → kXReal
    | omegaSqrt : kXReal → kXReal
    | omegaRSqrt : kXReal → kXReal
    | omegaExp : kXReal → kXReal
    | omegaExp2 : kXReal → kXReal
    | omegaLog : kXReal → kXReal
    | omegaLog2 : kXReal → kXReal
    | omegaLogOnePlus : kXReal → kXReal
    | omegaExpMinusOne : kXReal → kXReal
    | omegaSin : kXReal → kXReal
    | omegaCos : kXReal → kXReal
    | omegaTan : kXReal → kXReal
    | omegaArcSin : kXReal → kXReal
    | omegaArcCos : kXReal → kXReal
    | omegaArcTan : kXReal → kXReal
    | omegaSinh : kXReal → kXReal
    | omegaCosh : kXReal → kXReal
    | omegaTanh : kXReal → kXReal
    | omegaArcSinh : kXReal → kXReal
    | omegaArcCosh : kXReal → kXReal
    | omegaArcTanh : kXReal → kXReal
    | omegaSinPi : kXReal → kXReal
    | omegaCosPi : kXReal → kXReal
    | omegaTanPi : kXReal → kXReal
    | omegaArcSinPi : kXReal → kXReal
    | omegaArcCosPi : kXReal → kXReal
    | omegaArcTanPi : kXReal → kXReal
    | omegaSoftplus : kXReal → kXReal
    | exprSqrt : kXReal → kXReal
    | exprExp : kXReal → kXReal
    | exprExp2 : kXReal → kXReal
    | exprLog : kXReal → kXReal
    | exprLog2 : kXReal → kXReal
    | exprSin : kXReal → kXReal
    | exprCos : kXReal → kXReal
    | exprTan : kXReal → kXReal
    | exprArcSin : kXReal → kXReal
    | exprArcCos : kXReal → kXReal
    | exprArcTan : kXReal → kXReal
    | exprSinh : kXReal → kXReal
    | exprCosh : kXReal → kXReal
    | exprTanh : kXReal → kXReal
    | exprArcSinh : kXReal → kXReal
    | exprArcCosh : kXReal → kXReal
    | exprArcTanh : kXReal → kXReal
    | ifthenelsefi : kBool → kXReal → kXReal → kXReal

  inductive kXSeq
    | xnil
    | xcons : kXReal → kXSeq → kXSeq
    | decodeElements : kFormat → kCodeSeq → kXSeq
    | multiplyElements : kXReal → kXSeq → kXSeq
    | blockDecode : MRat → kFormat → kFormat → MRat → kCodeSeq → kXSeq
    | absElements : kXSeq → kXSeq
    | pairProducts : kXSeq → kXSeq → kXSeq
    | mapConvert : kXSeq → kXSeq
    | mapAbs : kXSeq → kXSeq
    | mapNegate : kXSeq → kXSeq
    | mapCopySign : kXSeq → kXSeq → kXSeq
    | mapAdd : kXSeq → kXSeq → kXSeq
    | mapSubtract : kXSeq → kXSeq → kXSeq
    | mapMultiply : kXSeq → kXSeq → kXSeq
    | mapDivide : kXSeq → kXSeq → kXSeq
    | mapFMA : kXSeq → kXSeq → kXSeq → kXSeq
    | mapFAA : kXSeq → kXSeq → kXSeq → kXSeq
    | mapRecip : kXSeq → kXSeq
    | mapMinimum : kXSeq → kXSeq → kXSeq
    | mapMaximum : kXSeq → kXSeq → kXSeq
    | mapMinimumNumber : kXSeq → kXSeq → kXSeq
    | mapMaximumNumber : kXSeq → kXSeq → kXSeq
    | mapMinimumMagnitude : kXSeq → kXSeq → kXSeq
    | mapMaximumMagnitude : kXSeq → kXSeq → kXSeq
    | mapMinimumMagnitudeNumber : kXSeq → kXSeq → kXSeq
    | mapMaximumMagnitudeNumber : kXSeq → kXSeq → kXSeq
    | mapMinimumFinite : kXSeq → kXSeq → kXSeq
    | mapMaximumFinite : kXSeq → kXSeq → kXSeq
    | mapClamp : kXSeq → kXSeq → kXSeq → kXSeq
    | mapSqrt : kXSeq → kXSeq
    | mapRSqrt : kXSeq → kXSeq
    | mapExp : kXSeq → kXSeq
    | mapExp2 : kXSeq → kXSeq
    | mapLog : kXSeq → kXSeq
    | mapLog2 : kXSeq → kXSeq
    | mapLogOnePlus : kXSeq → kXSeq
    | mapExpMinusOne : kXSeq → kXSeq
    | mapSin : kXSeq → kXSeq
    | mapCos : kXSeq → kXSeq
    | mapTan : kXSeq → kXSeq
    | mapArcSin : kXSeq → kXSeq
    | mapArcCos : kXSeq → kXSeq
    | mapArcTan : kXSeq → kXSeq
    | mapSinh : kXSeq → kXSeq
    | mapCosh : kXSeq → kXSeq
    | mapTanh : kXSeq → kXSeq
    | mapArcSinh : kXSeq → kXSeq
    | mapArcCosh : kXSeq → kXSeq
    | mapArcTanh : kXSeq → kXSeq
    | mapSinPi : kXSeq → kXSeq
    | mapCosPi : kXSeq → kXSeq
    | mapTanPi : kXSeq → kXSeq
    | mapArcSinPi : kXSeq → kXSeq
    | mapArcCosPi : kXSeq → kXSeq
    | mapArcTanPi : kXSeq → kXSeq
    | mapSoftplus : kXSeq → kXSeq
    | mapHypot : kXSeq → kXSeq → kXSeq
    | mapArcTan2 : kXSeq → kXSeq → kXSeq
    | mapArcTan2Pi : kXSeq → kXSeq → kXSeq
end

inductive kClassEnum
  | ClsNaN
  | ClsNegativeInfinity
  | ClsNegativeNormal
  | ClsNegativeSubnormal
  | ClsZero
  | ClsPositiveSubnormal
  | ClsPositiveNormal
  | ClsPositiveInfinity
  | Class : kFormat → MRat → kClassEnum
  | ifthenelsefi : kBool → kClassEnum → kClassEnum → kClassEnum

end Maude
