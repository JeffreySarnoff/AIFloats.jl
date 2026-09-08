import P3109.Relations.AxiomaticEquality
open Maude
example : MRat = Rat := rfl
example : kind MSort.Bool = kBool := rfl
example (a : kBool) : a.eqa a := .refl
#check MRat.modExp
#check MRat.ascii
#check MRat.find
#check MRat.rfind
#check MString.char
