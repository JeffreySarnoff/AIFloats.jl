import P3109

-- Client checks for names, exported attributes, rewrite lemmas, and instances.
open Maude

example : MRat = Rat := rfl
example : kind MSort.Bool = kBool := rfl
example (a : kBool) : a.eqe a := by simp
example (a : kXReal) : a.eqe a := kXReal.eqe_refl a
example (a : kBlock) : a.rw_star a := .refl (kBlock.eqe_refl a)
example {a b c : kBool} (h : a.rw_star b) :
    (kBool.and a c).rw_star (kBool.and b c) := kBool.rw_star_sub_and₀ h
example : kBoundQuery.repr .maxFiniteQuery = "maxFiniteQuery" := rfl
example : kEvidence.repr .proofEvidence = "proofEvidence" := rfl
example : Repr kBlock := inferInstance
example : Repr kArityTable := inferInstance

-- These remain declarations with precisely the source's axiom status.
#check MRat.modExp
#check MRat.ascii
#check MRat.find
#check MRat.rfind
#check MString.char
#check MRat.eqe_modExp
