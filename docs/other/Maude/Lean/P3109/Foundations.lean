-- Extracted from ../spec2.lean, lines 2-73.
-- See PLAN.md and manifest.json for provenance.

namespace Maude

-- Builtin Maude types replaced by Lean types
abbrev MRat := Rat
abbrev MString := String

-- Sorts
inductive MSort
  | Bool
  | Zero
  | NzNat
  | Nat
  | NzInt
  | Int
  | PosRat
  | NzRat
  | Rat
  | Real
  | Number
  | Infinity
  | XReal
  | Format
  | Signedness
  | Domain
  | BoundQuery
  | RandomSeq
  | RoundMode
  | SatMode
  | ProjSpec
  | BlockRoundMode
  | BlockProjSpec
  | XSeq
  | CodeSeq
  | Block
  | String
  | Char
  | FindResult
  | FormatSeq
  | Specialization
  | Kappa
  | Observation
  | Declaration
  | Evidence
  | KappaPart
  | ArityEntry
  | KappaPartSeq
  | PartitionSeq
  | DeclarationSeq
  | SpecializationSeq
  | ClassEnum
  | ObservationSeq
  | ArityTable

-- Generator of the subsort relation
def subsort : MSort → MSort → Prop
  | MSort.Zero, MSort.Nat => true
  | MSort.NzNat, MSort.Nat => true
  | MSort.NzNat, MSort.NzInt => true
  | MSort.NzInt, MSort.Int => true
  | MSort.Nat, MSort.Int => true
  | MSort.NzNat, MSort.PosRat => true
  | MSort.NzInt, MSort.NzRat => true
  | MSort.PosRat, MSort.NzRat => true
  | MSort.NzRat, MSort.Rat => true
  | MSort.Int, MSort.Rat => true
  | MSort.Real, MSort.Number => true
  | MSort.Infinity, MSort.Number => true
  | MSort.Number, MSort.XReal => true
  | MSort.RoundMode, MSort.BlockRoundMode => true
  | MSort.Char, MSort.String => true
  | MSort.Nat, MSort.FindResult => true
  | _, _ => false

end Maude
