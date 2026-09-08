-- Extracted from ../spec2.lean, lines 20396-20413.
-- See PLAN.md and manifest.json for provenance.
import P3109.Lemmas.Rewriting.Rationals

namespace Maude
namespace MString

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_char {a b : MRat} : MRat.rw_star a b →
      MString.rw_star (char a) (char b)
    | .step h => .step (rw_one.sub_char h)
    | .refl h => .refl (eqe_char h)
    | .trans h₀ h₁ => .trans (rw_star_sub_char h₀) (rw_star_sub_char h₁)
  theorem rw_star_sub_specializationName {a b : kSpecialization} : a.rw_star b →
      MString.rw_star (specializationName a) (specializationName b)
    | .step h => .step (rw_one.sub_specializationName h)
    | .refl h => .refl (eqe_specializationName h)
    | .trans h₀ h₁ => .trans (rw_star_sub_specializationName h₀) (rw_star_sub_specializationName h₁)
end MString

end Maude
