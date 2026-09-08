-- Extracted from ../spec2.lean, lines 10261-11232.
-- See PLAN.md and manifest.json for provenance.
import P3109.Lemmas.Equations.Native

namespace Maude
-- Lemmas for the rewriting relation

namespace kBool
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kBool} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kBool} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kBool} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kBool} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_and₀ {a b a₁ : kBool} : a.rw_star b →
      (and a a₁).rw_star (and b a₁)
    | .step h => .step (rw_one.sub_and₀ h)
    | .refl h => .refl (eqe.eqe_and h (kBool.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_and₀ h₀) (rw_star_sub_and₀ h₁)
  theorem rw_star_sub_and₁ {a₀ a b : kBool} : a.rw_star b →
      (and a₀ a).rw_star (and a₀ b)
    | .step h => .step (rw_one.sub_and₁ h)
    | .refl h => .refl (eqe.eqe_and (kBool.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_and₁ h₀) (rw_star_sub_and₁ h₁)
  theorem rw_star_sub_or₀ {a b a₁ : kBool} : a.rw_star b →
      (or a a₁).rw_star (or b a₁)
    | .step h => .step (rw_one.sub_or₀ h)
    | .refl h => .refl (eqe.eqe_or h (kBool.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_or₀ h₀) (rw_star_sub_or₀ h₁)
  theorem rw_star_sub_or₁ {a₀ a b : kBool} : a.rw_star b →
      (or a₀ a).rw_star (or a₀ b)
    | .step h => .step (rw_one.sub_or₁ h)
    | .refl h => .refl (eqe.eqe_or (kBool.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_or₁ h₀) (rw_star_sub_or₁ h₁)
  theorem rw_star_sub_xor₀ {a b a₁ : kBool} : a.rw_star b →
      (xor a a₁).rw_star (xor b a₁)
    | .step h => .step (rw_one.sub_xor₀ h)
    | .refl h => .refl (eqe.eqe_xor h (kBool.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_xor₀ h₀) (rw_star_sub_xor₀ h₁)
  theorem rw_star_sub_xor₁ {a₀ a b : kBool} : a.rw_star b →
      (xor a₀ a).rw_star (xor a₀ b)
    | .step h => .step (rw_one.sub_xor₁ h)
    | .refl h => .refl (eqe.eqe_xor (kBool.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_xor₁ h₀) (rw_star_sub_xor₁ h₁)
  theorem rw_star_sub_not {a b : kBool} : a.rw_star b →
      (not a).rw_star (not b)
    | .step h => .step (rw_one.sub_not h)
    | .refl h => .refl (eqe.eqe_not h)
    | .trans h₀ h₁ => .trans (rw_star_sub_not h₀) (rw_star_sub_not h₁)
  theorem rw_star_sub_implies₀ {a b a₁ : kBool} : a.rw_star b →
      (implies a a₁).rw_star (implies b a₁)
    | .step h => .step (rw_one.sub_implies₀ h)
    | .refl h => .refl (eqe.eqe_implies h (kBool.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_implies₀ h₀) (rw_star_sub_implies₀ h₁)
  theorem rw_star_sub_implies₁ {a₀ a b : kBool} : a.rw_star b →
      (implies a₀ a).rw_star (implies a₀ b)
    | .step h => .step (rw_one.sub_implies₁ h)
    | .refl h => .refl (eqe.eqe_implies (kBool.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_implies₁ h₀) (rw_star_sub_implies₁ h₁)
  theorem rw_star_sub_lt₀₀ {a b a₁ : MRat} : MRat.rw_star a b →
      (lt₀ a a₁).rw_star (lt₀ b a₁)
    | .step h => .step (rw_one.sub_lt₀₀ h)
    | .refl h => .refl (eqe.eqe_lt₀ h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_lt₀₀ h₀) (rw_star_sub_lt₀₀ h₁)
  theorem rw_star_sub_lt₀₁ {a₀ a b : MRat} : MRat.rw_star a b →
      (lt₀ a₀ a).rw_star (lt₀ a₀ b)
    | .step h => .step (rw_one.sub_lt₀₁ h)
    | .refl h => .refl (eqe.eqe_lt₀ rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_lt₀₁ h₀) (rw_star_sub_lt₀₁ h₁)
  theorem rw_star_sub_lteq₀₀ {a b a₁ : MRat} : MRat.rw_star a b →
      (lteq₀ a a₁).rw_star (lteq₀ b a₁)
    | .step h => .step (rw_one.sub_lteq₀₀ h)
    | .refl h => .refl (eqe.eqe_lteq₀ h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_lteq₀₀ h₀) (rw_star_sub_lteq₀₀ h₁)
  theorem rw_star_sub_lteq₀₁ {a₀ a b : MRat} : MRat.rw_star a b →
      (lteq₀ a₀ a).rw_star (lteq₀ a₀ b)
    | .step h => .step (rw_one.sub_lteq₀₁ h)
    | .refl h => .refl (eqe.eqe_lteq₀ rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_lteq₀₁ h₀) (rw_star_sub_lteq₀₁ h₁)
  theorem rw_star_sub_gt₀₀ {a b a₁ : MRat} : MRat.rw_star a b →
      (gt₀ a a₁).rw_star (gt₀ b a₁)
    | .step h => .step (rw_one.sub_gt₀₀ h)
    | .refl h => .refl (eqe.eqe_gt₀ h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_gt₀₀ h₀) (rw_star_sub_gt₀₀ h₁)
  theorem rw_star_sub_gt₀₁ {a₀ a b : MRat} : MRat.rw_star a b →
      (gt₀ a₀ a).rw_star (gt₀ a₀ b)
    | .step h => .step (rw_one.sub_gt₀₁ h)
    | .refl h => .refl (eqe.eqe_gt₀ rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_gt₀₁ h₀) (rw_star_sub_gt₀₁ h₁)
  theorem rw_star_sub_gteq₀₀ {a b a₁ : MRat} : MRat.rw_star a b →
      (gteq₀ a a₁).rw_star (gteq₀ b a₁)
    | .step h => .step (rw_one.sub_gteq₀₀ h)
    | .refl h => .refl (eqe.eqe_gteq₀ h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_gteq₀₀ h₀) (rw_star_sub_gteq₀₀ h₁)
  theorem rw_star_sub_gteq₀₁ {a₀ a b : MRat} : MRat.rw_star a b →
      (gteq₀ a₀ a).rw_star (gteq₀ a₀ b)
    | .step h => .step (rw_one.sub_gteq₀₁ h)
    | .refl h => .refl (eqe.eqe_gteq₀ rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_gteq₀₁ h₀) (rw_star_sub_gteq₀₁ h₁)
  theorem rw_star_sub_divides₀ {a b a₁ : MRat} : MRat.rw_star a b →
      (divides a a₁).rw_star (divides b a₁)
    | .step h => .step (rw_one.sub_divides₀ h)
    | .refl h => .refl (eqe.eqe_divides h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_divides₀ h₀) (rw_star_sub_divides₀ h₁)
  theorem rw_star_sub_divides₁ {a₀ a b : MRat} : MRat.rw_star a b →
      (divides a₀ a).rw_star (divides a₀ b)
    | .step h => .step (rw_one.sub_divides₁ h)
    | .refl h => .refl (eqe.eqe_divides rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_divides₁ h₀) (rw_star_sub_divides₁ h₁)
  theorem rw_star_sub_xNaN {a b : kXReal} : a.rw_star b →
      (xNaN a).rw_star (xNaN b)
    | .step h => .step (rw_one.sub_xNaN h)
    | .refl h => .refl (eqe.eqe_xNaN h)
    | .trans h₀ h₁ => .trans (rw_star_sub_xNaN h₀) (rw_star_sub_xNaN h₁)
  theorem rw_star_sub_xInfinite {a b : kXReal} : a.rw_star b →
      (xInfinite a).rw_star (xInfinite b)
    | .step h => .step (rw_one.sub_xInfinite h)
    | .refl h => .refl (eqe.eqe_xInfinite h)
    | .trans h₀ h₁ => .trans (rw_star_sub_xInfinite h₀) (rw_star_sub_xInfinite h₁)
  theorem rw_star_sub_xFinite {a b : kXReal} : a.rw_star b →
      (xFinite a).rw_star (xFinite b)
    | .step h => .step (rw_one.sub_xFinite h)
    | .refl h => .refl (eqe.eqe_xFinite h)
    | .trans h₀ h₁ => .trans (rw_star_sub_xFinite h₀) (rw_star_sub_xFinite h₁)
  theorem rw_star_sub_xMinus {a b : kXReal} : a.rw_star b →
      (xMinus a).rw_star (xMinus b)
    | .step h => .step (rw_one.sub_xMinus h)
    | .refl h => .refl (eqe.eqe_xMinus h)
    | .trans h₀ h₁ => .trans (rw_star_sub_xMinus h₀) (rw_star_sub_xMinus h₁)
  theorem rw_star_sub_xLt₀ {a b a₁ : kXReal} : a.rw_star b →
      (xLt a a₁).rw_star (xLt b a₁)
    | .step h => .step (rw_one.sub_xLt₀ h)
    | .refl h => .refl (eqe.eqe_xLt h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_xLt₀ h₀) (rw_star_sub_xLt₀ h₁)
  theorem rw_star_sub_xLt₁ {a₀ a b : kXReal} : a.rw_star b →
      (xLt a₀ a).rw_star (xLt a₀ b)
    | .step h => .step (rw_one.sub_xLt₁ h)
    | .refl h => .refl (eqe.eqe_xLt (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_xLt₁ h₀) (rw_star_sub_xLt₁ h₁)
  theorem rw_star_sub_xLe₀ {a b a₁ : kXReal} : a.rw_star b →
      (xLe a a₁).rw_star (xLe b a₁)
    | .step h => .step (rw_one.sub_xLe₀ h)
    | .refl h => .refl (eqe.eqe_xLe h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_xLe₀ h₀) (rw_star_sub_xLe₀ h₁)
  theorem rw_star_sub_xLe₁ {a₀ a b : kXReal} : a.rw_star b →
      (xLe a₀ a).rw_star (xLe a₀ b)
    | .step h => .step (rw_one.sub_xLe₁ h)
    | .refl h => .refl (eqe.eqe_xLe (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_xLe₁ h₀) (rw_star_sub_xLe₁ h₁)
  theorem rw_star_sub_xEq₀ {a b a₁ : kXReal} : a.rw_star b →
      (xEq a a₁).rw_star (xEq b a₁)
    | .step h => .step (rw_one.sub_xEq₀ h)
    | .refl h => .refl (eqe.eqe_xEq h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_xEq₀ h₀) (rw_star_sub_xEq₀ h₁)
  theorem rw_star_sub_xEq₁ {a₀ a b : kXReal} : a.rw_star b →
      (xEq a₀ a).rw_star (xEq a₀ b)
    | .step h => .step (rw_one.sub_xEq₁ h)
    | .refl h => .refl (eqe.eqe_xEq (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_xEq₁ h₀) (rw_star_sub_xEq₁ h₁)
  theorem rw_star_sub_even {a b : MRat} : MRat.rw_star a b →
      (even a).rw_star (even b)
    | .step h => .step (rw_one.sub_even h)
    | .refl h => .refl (eqe.eqe_even h)
    | .trans h₀ h₁ => .trans (rw_star_sub_even h₀) (rw_star_sub_even h₁)
  theorem rw_star_sub_validFormat {a b : kFormat} : a.rw_star b →
      (validFormat a).rw_star (validFormat b)
    | .step h => .step (rw_one.sub_validFormat h)
    | .refl h => .refl (eqe.eqe_validFormat h)
    | .trans h₀ h₁ => .trans (rw_star_sub_validFormat h₀) (rw_star_sub_validFormat h₁)
  theorem rw_star_sub_internalFormat {a b : kFormat} : a.rw_star b →
      (internalFormat a).rw_star (internalFormat b)
    | .step h => .step (rw_one.sub_internalFormat h)
    | .refl h => .refl (eqe.eqe_internalFormat h)
    | .trans h₀ h₁ => .trans (rw_star_sub_internalFormat h₀) (rw_star_sub_internalFormat h₁)
  theorem rw_star_sub_externalDatum₀ {a b : kFormat} {a₁ : kXReal} : a.rw_star b →
      (externalDatum a a₁).rw_star (externalDatum b a₁)
    | .step h => .step (rw_one.sub_externalDatum₀ h)
    | .refl h => .refl (eqe.eqe_externalDatum h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_externalDatum₀ h₀) (rw_star_sub_externalDatum₀ h₁)
  theorem rw_star_sub_externalDatum₁ {a₀ : kFormat} {a b : kXReal} : a.rw_star b →
      (externalDatum a₀ a).rw_star (externalDatum a₀ b)
    | .step h => .step (rw_one.sub_externalDatum₁ h)
    | .refl h => .refl (eqe.eqe_externalDatum (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_externalDatum₁ h₀) (rw_star_sub_externalDatum₁ h₁)
  theorem rw_star_sub_validCode₀ {a b : kFormat} {a₁ : MRat} : a.rw_star b →
      (validCode a a₁).rw_star (validCode b a₁)
    | .step h => .step (rw_one.sub_validCode₀ h)
    | .refl h => .refl (eqe.eqe_validCode h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_validCode₀ h₀) (rw_star_sub_validCode₀ h₁)
  theorem rw_star_sub_validCode₁ {a₀ : kFormat} {a b : MRat} : MRat.rw_star a b →
      (validCode a₀ a).rw_star (validCode a₀ b)
    | .step h => .step (rw_one.sub_validCode₁ h)
    | .refl h => .refl (eqe.eqe_validCode (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_validCode₁ h₀) (rw_star_sub_validCode₁ h₁)
  theorem rw_star_sub_datum₀ {a b : kFormat} {a₁ : kXReal} : a.rw_star b →
      (datum a a₁).rw_star (datum b a₁)
    | .step h => .step (rw_one.sub_datum₀ h)
    | .refl h => .refl (eqe.eqe_datum h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_datum₀ h₀) (rw_star_sub_datum₀ h₁)
  theorem rw_star_sub_datum₁ {a₀ : kFormat} {a b : kXReal} : a.rw_star b →
      (datum a₀ a).rw_star (datum a₀ b)
    | .step h => .step (rw_one.sub_datum₁ h)
    | .refl h => .refl (eqe.eqe_datum (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_datum₁ h₀) (rw_star_sub_datum₁ h₁)
  theorem rw_star_sub_candidateDatum₀ {a b : kFormat} {a₁ a₂ : MRat} : a.rw_star b →
      (candidateDatum a a₁ a₂).rw_star (candidateDatum b a₁ a₂)
    | .step h => .step (rw_one.sub_candidateDatum₀ h)
    | .refl h => .refl (eqe.eqe_candidateDatum h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_candidateDatum₀ h₀) (rw_star_sub_candidateDatum₀ h₁)
  theorem rw_star_sub_candidateDatum₁ {a₀ : kFormat} {a b a₂ : MRat} : MRat.rw_star a b →
      (candidateDatum a₀ a a₂).rw_star (candidateDatum a₀ b a₂)
    | .step h => .step (rw_one.sub_candidateDatum₁ h)
    | .refl h => .refl (eqe.eqe_candidateDatum (kFormat.eqe_refl a₀) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_candidateDatum₁ h₀) (rw_star_sub_candidateDatum₁ h₁)
  theorem rw_star_sub_candidateDatum₂ {a₀ : kFormat} {a₁ a b : MRat} : MRat.rw_star a b →
      (candidateDatum a₀ a₁ a).rw_star (candidateDatum a₀ a₁ b)
    | .step h => .step (rw_one.sub_candidateDatum₂ h)
    | .refl h => .refl (eqe.eqe_candidateDatum (kFormat.eqe_refl a₀) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_candidateDatum₂ h₀) (rw_star_sub_candidateDatum₂ h₁)
  theorem rw_star_sub_randomInRange₀ {a b a₁ : MRat} : MRat.rw_star a b →
      (randomInRange a a₁).rw_star (randomInRange b a₁)
    | .step h => .step (rw_one.sub_randomInRange₀ h)
    | .refl h => .refl (eqe.eqe_randomInRange h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_randomInRange₀ h₀) (rw_star_sub_randomInRange₀ h₁)
  theorem rw_star_sub_randomInRange₁ {a₀ a b : MRat} : MRat.rw_star a b →
      (randomInRange a₀ a).rw_star (randomInRange a₀ b)
    | .step h => .step (rw_one.sub_randomInRange₁ h)
    | .refl h => .refl (eqe.eqe_randomInRange rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_randomInRange₁ h₀) (rw_star_sub_randomInRange₁ h₁)
  theorem rw_star_sub_validRound {a b : kBlockRoundMode} : a.rw_star b →
      (validRound a).rw_star (validRound b)
    | .step h => .step (rw_one.sub_validRound h)
    | .refl h => .refl (eqe.eqe_validRound h)
    | .trans h₀ h₁ => .trans (rw_star_sub_validRound h₀) (rw_star_sub_validRound h₁)
  theorem rw_star_sub_validProjection {a b : kProjSpec} : a.rw_star b →
      (validProjection a).rw_star (validProjection b)
    | .step h => .step (rw_one.sub_validProjection h)
    | .refl h => .refl (eqe.eqe_validProjection h)
    | .trans h₀ h₁ => .trans (rw_star_sub_validProjection h₀) (rw_star_sub_validProjection h₁)
  theorem rw_star_sub_validBlockProjection₀ {a b : kBlockProjSpec} {a₁ : MRat} : a.rw_star b →
      (validBlockProjection a a₁).rw_star (validBlockProjection b a₁)
    | .step h => .step (rw_one.sub_validBlockProjection₀ h)
    | .refl h => .refl (eqe.eqe_validBlockProjection h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_validBlockProjection₀ h₀) (rw_star_sub_validBlockProjection₀ h₁)
  theorem rw_star_sub_validBlockProjection₁ {a₀ : kBlockProjSpec} {a b : MRat} : MRat.rw_star a b →
      (validBlockProjection a₀ a).rw_star (validBlockProjection a₀ b)
    | .step h => .step (rw_one.sub_validBlockProjection₁ h)
    | .refl h => .refl (eqe.eqe_validBlockProjection (kBlockProjSpec.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_validBlockProjection₁ h₀) (rw_star_sub_validBlockProjection₁ h₁)
  theorem rw_star_sub_validRandoms₀ {a b : MRat} {a₁ : kRandomSeq} : MRat.rw_star a b →
      (validRandoms a a₁).rw_star (validRandoms b a₁)
    | .step h => .step (rw_one.sub_validRandoms₀ h)
    | .refl h => .refl (eqe.eqe_validRandoms h (kRandomSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_validRandoms₀ h₀) (rw_star_sub_validRandoms₀ h₁)
  theorem rw_star_sub_validRandoms₁ {a₀ : MRat} {a b : kRandomSeq} : a.rw_star b →
      (validRandoms a₀ a).rw_star (validRandoms a₀ b)
    | .step h => .step (rw_one.sub_validRandoms₁ h)
    | .refl h => .refl (eqe.eqe_validRandoms rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_validRandoms₁ h₀) (rw_star_sub_validRandoms₁ h₁)
  theorem rw_star_sub_deterministic {a b : kBlockRoundMode} : a.rw_star b →
      (deterministic a).rw_star (deterministic b)
    | .step h => .step (rw_one.sub_deterministic h)
    | .refl h => .refl (eqe.eqe_deterministic h)
    | .trans h₀ h₁ => .trans (rw_star_sub_deterministic h₀) (rw_star_sub_deterministic h₁)
  theorem rw_star_sub_roundAway₀ {a b : kBlockRoundMode} {a₁ a₂ : MRat} {a₃ : kBool} : a.rw_star b →
      (roundAway a a₁ a₂ a₃).rw_star (roundAway b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_roundAway₀ h)
    | .refl h => .refl (eqe.eqe_roundAway h rfl rfl (kBool.eqe_refl a₃))
    | .trans h₀ h₁ => .trans (rw_star_sub_roundAway₀ h₀) (rw_star_sub_roundAway₀ h₁)
  theorem rw_star_sub_roundAway₁ {a₀ : kBlockRoundMode} {a b a₂ : MRat} {a₃ : kBool} : MRat.rw_star a b →
      (roundAway a₀ a a₂ a₃).rw_star (roundAway a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_roundAway₁ h)
    | .refl h => .refl (eqe.eqe_roundAway (kBlockRoundMode.eqe_refl a₀) h rfl (kBool.eqe_refl a₃))
    | .trans h₀ h₁ => .trans (rw_star_sub_roundAway₁ h₀) (rw_star_sub_roundAway₁ h₁)
  theorem rw_star_sub_roundAway₂ {a₀ : kBlockRoundMode} {a₁ a b : MRat} {a₃ : kBool} : MRat.rw_star a b →
      (roundAway a₀ a₁ a a₃).rw_star (roundAway a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_roundAway₂ h)
    | .refl h => .refl (eqe.eqe_roundAway (kBlockRoundMode.eqe_refl a₀) rfl h (kBool.eqe_refl a₃))
    | .trans h₀ h₁ => .trans (rw_star_sub_roundAway₂ h₀) (rw_star_sub_roundAway₂ h₁)
  theorem rw_star_sub_roundAway₃ {a₀ : kBlockRoundMode} {a₁ a₂ : MRat} {a b : kBool} : a.rw_star b →
      (roundAway a₀ a₁ a₂ a).rw_star (roundAway a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_roundAway₃ h)
    | .refl h => .refl (eqe.eqe_roundAway (kBlockRoundMode.eqe_refl a₀) rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_roundAway₃ h₀) (rw_star_sub_roundAway₃ h₁)
  theorem rw_star_sub_clipsHigh {a b : kBlockRoundMode} : a.rw_star b →
      (clipsHigh a).rw_star (clipsHigh b)
    | .step h => .step (rw_one.sub_clipsHigh h)
    | .refl h => .refl (eqe.eqe_clipsHigh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_clipsHigh h₀) (rw_star_sub_clipsHigh h₁)
  theorem rw_star_sub_clipsLow {a b : kBlockRoundMode} : a.rw_star b →
      (clipsLow a).rw_star (clipsLow b)
    | .step h => .step (rw_one.sub_clipsLow h)
    | .refl h => .refl (eqe.eqe_clipsLow h)
    | .trans h₀ h₁ => .trans (rw_star_sub_clipsLow h₀) (rw_star_sub_clipsLow h₁)
  theorem rw_star_sub_validCodes₀ {a b : kFormat} {a₁ : kCodeSeq} : a.rw_star b →
      (validCodes a a₁).rw_star (validCodes b a₁)
    | .step h => .step (rw_one.sub_validCodes₀ h)
    | .refl h => .refl (eqe.eqe_validCodes h (kCodeSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_validCodes₀ h₀) (rw_star_sub_validCodes₀ h₁)
  theorem rw_star_sub_validCodes₁ {a₀ : kFormat} {a b : kCodeSeq} : a.rw_star b →
      (validCodes a₀ a).rw_star (validCodes a₀ b)
    | .step h => .step (rw_one.sub_validCodes₁ h)
    | .refl h => .refl (eqe.eqe_validCodes (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_validCodes₁ h₀) (rw_star_sub_validCodes₁ h₁)
  theorem rw_star_sub_validBlock₀ {a b : MRat} {a₁ a₂ : kFormat} {a₃ : MRat} {a₄ : kCodeSeq} : MRat.rw_star a b →
      (validBlock a a₁ a₂ a₃ a₄).rw_star (validBlock b a₁ a₂ a₃ a₄)
    | .step h => .step (rw_one.sub_validBlock₀ h)
    | .refl h => .refl (eqe.eqe_validBlock h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) rfl (kCodeSeq.eqe_refl a₄))
    | .trans h₀ h₁ => .trans (rw_star_sub_validBlock₀ h₀) (rw_star_sub_validBlock₀ h₁)
  theorem rw_star_sub_validBlock₁ {a₀ : MRat} {a b a₂ : kFormat} {a₃ : MRat} {a₄ : kCodeSeq} : a.rw_star b →
      (validBlock a₀ a a₂ a₃ a₄).rw_star (validBlock a₀ b a₂ a₃ a₄)
    | .step h => .step (rw_one.sub_validBlock₁ h)
    | .refl h => .refl (eqe.eqe_validBlock rfl h (kFormat.eqe_refl a₂) rfl (kCodeSeq.eqe_refl a₄))
    | .trans h₀ h₁ => .trans (rw_star_sub_validBlock₁ h₀) (rw_star_sub_validBlock₁ h₁)
  theorem rw_star_sub_validBlock₂ {a₀ : MRat} {a₁ a b : kFormat} {a₃ : MRat} {a₄ : kCodeSeq} : a.rw_star b →
      (validBlock a₀ a₁ a a₃ a₄).rw_star (validBlock a₀ a₁ b a₃ a₄)
    | .step h => .step (rw_one.sub_validBlock₂ h)
    | .refl h => .refl (eqe.eqe_validBlock rfl (kFormat.eqe_refl a₁) h rfl (kCodeSeq.eqe_refl a₄))
    | .trans h₀ h₁ => .trans (rw_star_sub_validBlock₂ h₀) (rw_star_sub_validBlock₂ h₁)
  theorem rw_star_sub_validBlock₃ {a₀ : MRat} {a₁ a₂ : kFormat} {a b : MRat} {a₄ : kCodeSeq} : MRat.rw_star a b →
      (validBlock a₀ a₁ a₂ a a₄).rw_star (validBlock a₀ a₁ a₂ b a₄)
    | .step h => .step (rw_one.sub_validBlock₃ h)
    | .refl h => .refl (eqe.eqe_validBlock rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kCodeSeq.eqe_refl a₄))
    | .trans h₀ h₁ => .trans (rw_star_sub_validBlock₃ h₀) (rw_star_sub_validBlock₃ h₁)
  theorem rw_star_sub_validBlock₄ {a₀ : MRat} {a₁ a₂ : kFormat} {a₃ : MRat} {a b : kCodeSeq} : a.rw_star b →
      (validBlock a₀ a₁ a₂ a₃ a).rw_star (validBlock a₀ a₁ a₂ a₃ b)
    | .step h => .step (rw_one.sub_validBlock₄ h)
    | .refl h => .refl (eqe.eqe_validBlock rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_validBlock₄ h₀) (rw_star_sub_validBlock₄ h₁)
  theorem rw_star_sub_lt₁₀ {a b a₁ : MString} : MString.rw_star a b →
      (lt₁ a a₁).rw_star (lt₁ b a₁)
    | .step h => .step (rw_one.sub_lt₁₀ h)
    | .refl h => .refl (eqe.eqe_lt₁ h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_lt₁₀ h₀) (rw_star_sub_lt₁₀ h₁)
  theorem rw_star_sub_lt₁₁ {a₀ a b : MString} : MString.rw_star a b →
      (lt₁ a₀ a).rw_star (lt₁ a₀ b)
    | .step h => .step (rw_one.sub_lt₁₁ h)
    | .refl h => .refl (eqe.eqe_lt₁ rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_lt₁₁ h₀) (rw_star_sub_lt₁₁ h₁)
  theorem rw_star_sub_lteq₁₀ {a b a₁ : MString} : MString.rw_star a b →
      (lteq₁ a a₁).rw_star (lteq₁ b a₁)
    | .step h => .step (rw_one.sub_lteq₁₀ h)
    | .refl h => .refl (eqe.eqe_lteq₁ h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_lteq₁₀ h₀) (rw_star_sub_lteq₁₀ h₁)
  theorem rw_star_sub_lteq₁₁ {a₀ a b : MString} : MString.rw_star a b →
      (lteq₁ a₀ a).rw_star (lteq₁ a₀ b)
    | .step h => .step (rw_one.sub_lteq₁₁ h)
    | .refl h => .refl (eqe.eqe_lteq₁ rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_lteq₁₁ h₀) (rw_star_sub_lteq₁₁ h₁)
  theorem rw_star_sub_gt₁₀ {a b a₁ : MString} : MString.rw_star a b →
      (gt₁ a a₁).rw_star (gt₁ b a₁)
    | .step h => .step (rw_one.sub_gt₁₀ h)
    | .refl h => .refl (eqe.eqe_gt₁ h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_gt₁₀ h₀) (rw_star_sub_gt₁₀ h₁)
  theorem rw_star_sub_gt₁₁ {a₀ a b : MString} : MString.rw_star a b →
      (gt₁ a₀ a).rw_star (gt₁ a₀ b)
    | .step h => .step (rw_one.sub_gt₁₁ h)
    | .refl h => .refl (eqe.eqe_gt₁ rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_gt₁₁ h₀) (rw_star_sub_gt₁₁ h₁)
  theorem rw_star_sub_gteq₁₀ {a b a₁ : MString} : MString.rw_star a b →
      (gteq₁ a a₁).rw_star (gteq₁ b a₁)
    | .step h => .step (rw_one.sub_gteq₁₀ h)
    | .refl h => .refl (eqe.eqe_gteq₁ h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_gteq₁₀ h₀) (rw_star_sub_gteq₁₀ h₁)
  theorem rw_star_sub_gteq₁₁ {a₀ a b : MString} : MString.rw_star a b →
      (gteq₁ a₀ a).rw_star (gteq₁ a₀ b)
    | .step h => .step (rw_one.sub_gteq₁₁ h)
    | .refl h => .refl (eqe.eqe_gteq₁ rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_gteq₁₁ h₀) (rw_star_sub_gteq₁₁ h₁)
  theorem rw_star_sub_CompareLess₀ {a b a₁ : kFormat} {a₂ a₃ : MRat} : a.rw_star b →
      (CompareLess a a₁ a₂ a₃).rw_star (CompareLess b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_CompareLess₀ h)
    | .refl h => .refl (eqe.eqe_CompareLess h (kFormat.eqe_refl a₁) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareLess₀ h₀) (rw_star_sub_CompareLess₀ h₁)
  theorem rw_star_sub_CompareLess₁ {a₀ a b : kFormat} {a₂ a₃ : MRat} : a.rw_star b →
      (CompareLess a₀ a a₂ a₃).rw_star (CompareLess a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_CompareLess₁ h)
    | .refl h => .refl (eqe.eqe_CompareLess (kFormat.eqe_refl a₀) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareLess₁ h₀) (rw_star_sub_CompareLess₁ h₁)
  theorem rw_star_sub_CompareLess₂ {a₀ a₁ : kFormat} {a b a₃ : MRat} : MRat.rw_star a b →
      (CompareLess a₀ a₁ a a₃).rw_star (CompareLess a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_CompareLess₂ h)
    | .refl h => .refl (eqe.eqe_CompareLess (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareLess₂ h₀) (rw_star_sub_CompareLess₂ h₁)
  theorem rw_star_sub_CompareLess₃ {a₀ a₁ : kFormat} {a₂ a b : MRat} : MRat.rw_star a b →
      (CompareLess a₀ a₁ a₂ a).rw_star (CompareLess a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_CompareLess₃ h)
    | .refl h => .refl (eqe.eqe_CompareLess (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareLess₃ h₀) (rw_star_sub_CompareLess₃ h₁)
  theorem rw_star_sub_CompareLessEqual₀ {a b a₁ : kFormat} {a₂ a₃ : MRat} : a.rw_star b →
      (CompareLessEqual a a₁ a₂ a₃).rw_star (CompareLessEqual b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_CompareLessEqual₀ h)
    | .refl h => .refl (eqe.eqe_CompareLessEqual h (kFormat.eqe_refl a₁) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareLessEqual₀ h₀) (rw_star_sub_CompareLessEqual₀ h₁)
  theorem rw_star_sub_CompareLessEqual₁ {a₀ a b : kFormat} {a₂ a₃ : MRat} : a.rw_star b →
      (CompareLessEqual a₀ a a₂ a₃).rw_star (CompareLessEqual a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_CompareLessEqual₁ h)
    | .refl h => .refl (eqe.eqe_CompareLessEqual (kFormat.eqe_refl a₀) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareLessEqual₁ h₀) (rw_star_sub_CompareLessEqual₁ h₁)
  theorem rw_star_sub_CompareLessEqual₂ {a₀ a₁ : kFormat} {a b a₃ : MRat} : MRat.rw_star a b →
      (CompareLessEqual a₀ a₁ a a₃).rw_star (CompareLessEqual a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_CompareLessEqual₂ h)
    | .refl h => .refl (eqe.eqe_CompareLessEqual (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareLessEqual₂ h₀) (rw_star_sub_CompareLessEqual₂ h₁)
  theorem rw_star_sub_CompareLessEqual₃ {a₀ a₁ : kFormat} {a₂ a b : MRat} : MRat.rw_star a b →
      (CompareLessEqual a₀ a₁ a₂ a).rw_star (CompareLessEqual a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_CompareLessEqual₃ h)
    | .refl h => .refl (eqe.eqe_CompareLessEqual (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareLessEqual₃ h₀) (rw_star_sub_CompareLessEqual₃ h₁)
  theorem rw_star_sub_CompareEqual₀ {a b a₁ : kFormat} {a₂ a₃ : MRat} : a.rw_star b →
      (CompareEqual a a₁ a₂ a₃).rw_star (CompareEqual b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_CompareEqual₀ h)
    | .refl h => .refl (eqe.eqe_CompareEqual h (kFormat.eqe_refl a₁) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareEqual₀ h₀) (rw_star_sub_CompareEqual₀ h₁)
  theorem rw_star_sub_CompareEqual₁ {a₀ a b : kFormat} {a₂ a₃ : MRat} : a.rw_star b →
      (CompareEqual a₀ a a₂ a₃).rw_star (CompareEqual a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_CompareEqual₁ h)
    | .refl h => .refl (eqe.eqe_CompareEqual (kFormat.eqe_refl a₀) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareEqual₁ h₀) (rw_star_sub_CompareEqual₁ h₁)
  theorem rw_star_sub_CompareEqual₂ {a₀ a₁ : kFormat} {a b a₃ : MRat} : MRat.rw_star a b →
      (CompareEqual a₀ a₁ a a₃).rw_star (CompareEqual a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_CompareEqual₂ h)
    | .refl h => .refl (eqe.eqe_CompareEqual (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareEqual₂ h₀) (rw_star_sub_CompareEqual₂ h₁)
  theorem rw_star_sub_CompareEqual₃ {a₀ a₁ : kFormat} {a₂ a b : MRat} : MRat.rw_star a b →
      (CompareEqual a₀ a₁ a₂ a).rw_star (CompareEqual a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_CompareEqual₃ h)
    | .refl h => .refl (eqe.eqe_CompareEqual (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareEqual₃ h₀) (rw_star_sub_CompareEqual₃ h₁)
  theorem rw_star_sub_CompareGreaterEqual₀ {a b a₁ : kFormat} {a₂ a₃ : MRat} : a.rw_star b →
      (CompareGreaterEqual a a₁ a₂ a₃).rw_star (CompareGreaterEqual b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_CompareGreaterEqual₀ h)
    | .refl h => .refl (eqe.eqe_CompareGreaterEqual h (kFormat.eqe_refl a₁) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareGreaterEqual₀ h₀) (rw_star_sub_CompareGreaterEqual₀ h₁)
  theorem rw_star_sub_CompareGreaterEqual₁ {a₀ a b : kFormat} {a₂ a₃ : MRat} : a.rw_star b →
      (CompareGreaterEqual a₀ a a₂ a₃).rw_star (CompareGreaterEqual a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_CompareGreaterEqual₁ h)
    | .refl h => .refl (eqe.eqe_CompareGreaterEqual (kFormat.eqe_refl a₀) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareGreaterEqual₁ h₀) (rw_star_sub_CompareGreaterEqual₁ h₁)
  theorem rw_star_sub_CompareGreaterEqual₂ {a₀ a₁ : kFormat} {a b a₃ : MRat} : MRat.rw_star a b →
      (CompareGreaterEqual a₀ a₁ a a₃).rw_star (CompareGreaterEqual a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_CompareGreaterEqual₂ h)
    | .refl h => .refl (eqe.eqe_CompareGreaterEqual (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareGreaterEqual₂ h₀) (rw_star_sub_CompareGreaterEqual₂ h₁)
  theorem rw_star_sub_CompareGreaterEqual₃ {a₀ a₁ : kFormat} {a₂ a b : MRat} : MRat.rw_star a b →
      (CompareGreaterEqual a₀ a₁ a₂ a).rw_star (CompareGreaterEqual a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_CompareGreaterEqual₃ h)
    | .refl h => .refl (eqe.eqe_CompareGreaterEqual (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareGreaterEqual₃ h₀) (rw_star_sub_CompareGreaterEqual₃ h₁)
  theorem rw_star_sub_CompareGreater₀ {a b a₁ : kFormat} {a₂ a₃ : MRat} : a.rw_star b →
      (CompareGreater a a₁ a₂ a₃).rw_star (CompareGreater b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_CompareGreater₀ h)
    | .refl h => .refl (eqe.eqe_CompareGreater h (kFormat.eqe_refl a₁) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareGreater₀ h₀) (rw_star_sub_CompareGreater₀ h₁)
  theorem rw_star_sub_CompareGreater₁ {a₀ a b : kFormat} {a₂ a₃ : MRat} : a.rw_star b →
      (CompareGreater a₀ a a₂ a₃).rw_star (CompareGreater a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_CompareGreater₁ h)
    | .refl h => .refl (eqe.eqe_CompareGreater (kFormat.eqe_refl a₀) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareGreater₁ h₀) (rw_star_sub_CompareGreater₁ h₁)
  theorem rw_star_sub_CompareGreater₂ {a₀ a₁ : kFormat} {a b a₃ : MRat} : MRat.rw_star a b →
      (CompareGreater a₀ a₁ a a₃).rw_star (CompareGreater a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_CompareGreater₂ h)
    | .refl h => .refl (eqe.eqe_CompareGreater (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareGreater₂ h₀) (rw_star_sub_CompareGreater₂ h₁)
  theorem rw_star_sub_CompareGreater₃ {a₀ a₁ : kFormat} {a₂ a b : MRat} : MRat.rw_star a b →
      (CompareGreater a₀ a₁ a₂ a).rw_star (CompareGreater a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_CompareGreater₃ h)
    | .refl h => .refl (eqe.eqe_CompareGreater (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_CompareGreater₃ h₀) (rw_star_sub_CompareGreater₃ h₁)
  theorem rw_star_sub_IsZero₀ {a b : kFormat} {a₁ : MRat} : a.rw_star b →
      (IsZero a a₁).rw_star (IsZero b a₁)
    | .step h => .step (rw_one.sub_IsZero₀ h)
    | .refl h => .refl (eqe.eqe_IsZero h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_IsZero₀ h₀) (rw_star_sub_IsZero₀ h₁)
  theorem rw_star_sub_IsZero₁ {a₀ : kFormat} {a b : MRat} : MRat.rw_star a b →
      (IsZero a₀ a).rw_star (IsZero a₀ b)
    | .step h => .step (rw_one.sub_IsZero₁ h)
    | .refl h => .refl (eqe.eqe_IsZero (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_IsZero₁ h₀) (rw_star_sub_IsZero₁ h₁)
  theorem rw_star_sub_IsOne₀ {a b : kFormat} {a₁ : MRat} : a.rw_star b →
      (IsOne a a₁).rw_star (IsOne b a₁)
    | .step h => .step (rw_one.sub_IsOne₀ h)
    | .refl h => .refl (eqe.eqe_IsOne h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_IsOne₀ h₀) (rw_star_sub_IsOne₀ h₁)
  theorem rw_star_sub_IsOne₁ {a₀ : kFormat} {a b : MRat} : MRat.rw_star a b →
      (IsOne a₀ a).rw_star (IsOne a₀ b)
    | .step h => .step (rw_one.sub_IsOne₁ h)
    | .refl h => .refl (eqe.eqe_IsOne (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_IsOne₁ h₀) (rw_star_sub_IsOne₁ h₁)
  theorem rw_star_sub_IsNaN₀ {a b : kFormat} {a₁ : MRat} : a.rw_star b →
      (IsNaN a a₁).rw_star (IsNaN b a₁)
    | .step h => .step (rw_one.sub_IsNaN₀ h)
    | .refl h => .refl (eqe.eqe_IsNaN h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_IsNaN₀ h₀) (rw_star_sub_IsNaN₀ h₁)
  theorem rw_star_sub_IsNaN₁ {a₀ : kFormat} {a b : MRat} : MRat.rw_star a b →
      (IsNaN a₀ a).rw_star (IsNaN a₀ b)
    | .step h => .step (rw_one.sub_IsNaN₁ h)
    | .refl h => .refl (eqe.eqe_IsNaN (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_IsNaN₁ h₀) (rw_star_sub_IsNaN₁ h₁)
  theorem rw_star_sub_IsInfinite₀ {a b : kFormat} {a₁ : MRat} : a.rw_star b →
      (IsInfinite a a₁).rw_star (IsInfinite b a₁)
    | .step h => .step (rw_one.sub_IsInfinite₀ h)
    | .refl h => .refl (eqe.eqe_IsInfinite h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_IsInfinite₀ h₀) (rw_star_sub_IsInfinite₀ h₁)
  theorem rw_star_sub_IsInfinite₁ {a₀ : kFormat} {a b : MRat} : MRat.rw_star a b →
      (IsInfinite a₀ a).rw_star (IsInfinite a₀ b)
    | .step h => .step (rw_one.sub_IsInfinite₁ h)
    | .refl h => .refl (eqe.eqe_IsInfinite (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_IsInfinite₁ h₀) (rw_star_sub_IsInfinite₁ h₁)
  theorem rw_star_sub_IsFinite₀ {a b : kFormat} {a₁ : MRat} : a.rw_star b →
      (IsFinite a a₁).rw_star (IsFinite b a₁)
    | .step h => .step (rw_one.sub_IsFinite₀ h)
    | .refl h => .refl (eqe.eqe_IsFinite h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_IsFinite₀ h₀) (rw_star_sub_IsFinite₀ h₁)
  theorem rw_star_sub_IsFinite₁ {a₀ : kFormat} {a b : MRat} : MRat.rw_star a b →
      (IsFinite a₀ a).rw_star (IsFinite a₀ b)
    | .step h => .step (rw_one.sub_IsFinite₁ h)
    | .refl h => .refl (eqe.eqe_IsFinite (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_IsFinite₁ h₀) (rw_star_sub_IsFinite₁ h₁)
  theorem rw_star_sub_IsSignMinus₀ {a b : kFormat} {a₁ : MRat} : a.rw_star b →
      (IsSignMinus a a₁).rw_star (IsSignMinus b a₁)
    | .step h => .step (rw_one.sub_IsSignMinus₀ h)
    | .refl h => .refl (eqe.eqe_IsSignMinus h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_IsSignMinus₀ h₀) (rw_star_sub_IsSignMinus₀ h₁)
  theorem rw_star_sub_IsSignMinus₁ {a₀ : kFormat} {a b : MRat} : MRat.rw_star a b →
      (IsSignMinus a₀ a).rw_star (IsSignMinus a₀ b)
    | .step h => .step (rw_one.sub_IsSignMinus₁ h)
    | .refl h => .refl (eqe.eqe_IsSignMinus (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_IsSignMinus₁ h₀) (rw_star_sub_IsSignMinus₁ h₁)
  theorem rw_star_sub_IsNormal₀ {a b : kFormat} {a₁ : MRat} : a.rw_star b →
      (IsNormal a a₁).rw_star (IsNormal b a₁)
    | .step h => .step (rw_one.sub_IsNormal₀ h)
    | .refl h => .refl (eqe.eqe_IsNormal h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_IsNormal₀ h₀) (rw_star_sub_IsNormal₀ h₁)
  theorem rw_star_sub_IsNormal₁ {a₀ : kFormat} {a b : MRat} : MRat.rw_star a b →
      (IsNormal a₀ a).rw_star (IsNormal a₀ b)
    | .step h => .step (rw_one.sub_IsNormal₁ h)
    | .refl h => .refl (eqe.eqe_IsNormal (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_IsNormal₁ h₀) (rw_star_sub_IsNormal₁ h₁)
  theorem rw_star_sub_IsSubnormal₀ {a b : kFormat} {a₁ : MRat} : a.rw_star b →
      (IsSubnormal a a₁).rw_star (IsSubnormal b a₁)
    | .step h => .step (rw_one.sub_IsSubnormal₀ h)
    | .refl h => .refl (eqe.eqe_IsSubnormal h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_IsSubnormal₀ h₀) (rw_star_sub_IsSubnormal₀ h₁)
  theorem rw_star_sub_IsSubnormal₁ {a₀ : kFormat} {a b : MRat} : MRat.rw_star a b →
      (IsSubnormal a₀ a).rw_star (IsSubnormal a₀ b)
    | .step h => .step (rw_one.sub_IsSubnormal₁ h)
    | .refl h => .refl (eqe.eqe_IsSubnormal (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_IsSubnormal₁ h₀) (rw_star_sub_IsSubnormal₁ h₁)
  theorem rw_star_sub_inF4 {a b : kFormat} : a.rw_star b →
      (inF4 a).rw_star (inF4 b)
    | .step h => .step (rw_one.sub_inF4 h)
    | .refl h => .refl (eqe.eqe_inF4 h)
    | .trans h₀ h₁ => .trans (rw_star_sub_inF4 h₀) (rw_star_sub_inF4 h₁)
  theorem rw_star_sub_inF8 {a b : kFormat} : a.rw_star b →
      (inF8 a).rw_star (inF8 b)
    | .step h => .step (rw_one.sub_inF8 h)
    | .refl h => .refl (eqe.eqe_inF8 h)
    | .trans h₀ h₁ => .trans (rw_star_sub_inF8 h₀) (rw_star_sub_inF8 h₁)
  theorem rw_star_sub_inFs {a b : kFormat} : a.rw_star b →
      (inFs a).rw_star (inFs b)
    | .step h => .step (rw_one.sub_inFs h)
    | .refl h => .refl (eqe.eqe_inFs h)
    | .trans h₀ h₁ => .trans (rw_star_sub_inFs h₀) (rw_star_sub_inFs h₁)
  theorem rw_star_sub_allowedExternal {a b : kFormat} : a.rw_star b →
      (allowedExternal a).rw_star (allowedExternal b)
    | .step h => .step (rw_one.sub_allowedExternal h)
    | .refl h => .refl (eqe.eqe_allowedExternal h)
    | .trans h₀ h₁ => .trans (rw_star_sub_allowedExternal h₀) (rw_star_sub_allowedExternal h₁)
  theorem rw_star_sub_containsFormat₀ {a b : kFormat} {a₁ : kFormatSeq} : a.rw_star b →
      (containsFormat a a₁).rw_star (containsFormat b a₁)
    | .step h => .step (rw_one.sub_containsFormat₀ h)
    | .refl h => .refl (eqe.eqe_containsFormat h (kFormatSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_containsFormat₀ h₀) (rw_star_sub_containsFormat₀ h₁)
  theorem rw_star_sub_containsFormat₁ {a₀ : kFormat} {a b : kFormatSeq} : a.rw_star b →
      (containsFormat a₀ a).rw_star (containsFormat a₀ b)
    | .step h => .step (rw_one.sub_containsFormat₁ h)
    | .refl h => .refl (eqe.eqe_containsFormat (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_containsFormat₁ h₀) (rw_star_sub_containsFormat₁ h₁)
  theorem rw_star_sub_validFX {a b : kFormatSeq} : a.rw_star b →
      (validFX a).rw_star (validFX b)
    | .step h => .step (rw_one.sub_validFX h)
    | .refl h => .refl (eqe.eqe_validFX h)
    | .trans h₀ h₁ => .trans (rw_star_sub_validFX h₀) (rw_star_sub_validFX h₁)
  theorem rw_star_sub_validFXTail {a b : kFormatSeq} : a.rw_star b →
      (validFXTail a).rw_star (validFXTail b)
    | .step h => .step (rw_one.sub_validFXTail h)
    | .refl h => .refl (eqe.eqe_validFXTail h)
    | .trans h₀ h₁ => .trans (rw_star_sub_validFXTail h₀) (rw_star_sub_validFXTail h₁)
  theorem rw_star_sub_allFormats {a b : kFormatSeq} : a.rw_star b →
      (allFormats a).rw_star (allFormats b)
    | .step h => .step (rw_one.sub_allFormats h)
    | .refl h => .refl (eqe.eqe_allFormats h)
    | .trans h₀ h₁ => .trans (rw_star_sub_allFormats h₀) (rw_star_sub_allFormats h₁)
  theorem rw_star_sub_required₀ {a b : kSpecialization} {a₁ : kFormatSeq} : a.rw_star b →
      (required a a₁).rw_star (required b a₁)
    | .step h => .step (rw_one.sub_required₀ h)
    | .refl h => .refl (eqe.eqe_required h (kFormatSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_required₀ h₀) (rw_star_sub_required₀ h₁)
  theorem rw_star_sub_required₁ {a₀ : kSpecialization} {a b : kFormatSeq} : a.rw_star b →
      (required a₀ a).rw_star (required a₀ b)
    | .step h => .step (rw_one.sub_required₁ h)
    | .refl h => .refl (eqe.eqe_required (kSpecialization.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_required₁ h₀) (rw_star_sub_required₁ h₁)
  theorem rw_star_sub_requiredNumeric₀ {a b : MString} {a₁ a₂ : kFormatSeq} : MString.rw_star a b →
      (requiredNumeric a a₁ a₂).rw_star (requiredNumeric b a₁ a₂)
    | .step h => .step (rw_one.sub_requiredNumeric₀ h)
    | .refl h => .refl (eqe.eqe_requiredNumeric h (kFormatSeq.eqe_refl a₁) (kFormatSeq.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_requiredNumeric₀ h₀) (rw_star_sub_requiredNumeric₀ h₁)
  theorem rw_star_sub_requiredNumeric₁ {a₀ : MString} {a b a₂ : kFormatSeq} : a.rw_star b →
      (requiredNumeric a₀ a a₂).rw_star (requiredNumeric a₀ b a₂)
    | .step h => .step (rw_one.sub_requiredNumeric₁ h)
    | .refl h => .refl (eqe.eqe_requiredNumeric rfl h (kFormatSeq.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_requiredNumeric₁ h₀) (rw_star_sub_requiredNumeric₁ h₁)
  theorem rw_star_sub_requiredNumeric₂ {a₀ : MString} {a₁ a b : kFormatSeq} : a.rw_star b →
      (requiredNumeric a₀ a₁ a).rw_star (requiredNumeric a₀ a₁ b)
    | .step h => .step (rw_one.sub_requiredNumeric₂ h)
    | .refl h => .refl (eqe.eqe_requiredNumeric rfl (kFormatSeq.eqe_refl a₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_requiredNumeric₂ h₀) (rw_star_sub_requiredNumeric₂ h₁)
  theorem rw_star_sub_requiredPlain₀ {a b : MString} {a₁ a₂ : kFormatSeq} : MString.rw_star a b →
      (requiredPlain a a₁ a₂).rw_star (requiredPlain b a₁ a₂)
    | .step h => .step (rw_one.sub_requiredPlain₀ h)
    | .refl h => .refl (eqe.eqe_requiredPlain h (kFormatSeq.eqe_refl a₁) (kFormatSeq.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_requiredPlain₀ h₀) (rw_star_sub_requiredPlain₀ h₁)
  theorem rw_star_sub_requiredPlain₁ {a₀ : MString} {a b a₂ : kFormatSeq} : a.rw_star b →
      (requiredPlain a₀ a a₂).rw_star (requiredPlain a₀ b a₂)
    | .step h => .step (rw_one.sub_requiredPlain₁ h)
    | .refl h => .refl (eqe.eqe_requiredPlain rfl h (kFormatSeq.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_requiredPlain₁ h₀) (rw_star_sub_requiredPlain₁ h₁)
  theorem rw_star_sub_requiredPlain₂ {a₀ : MString} {a₁ a b : kFormatSeq} : a.rw_star b →
      (requiredPlain a₀ a₁ a).rw_star (requiredPlain a₀ a₁ b)
    | .step h => .step (rw_one.sub_requiredPlain₂ h)
    | .refl h => .refl (eqe.eqe_requiredPlain rfl (kFormatSeq.eqe_refl a₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_requiredPlain₂ h₀) (rw_star_sub_requiredPlain₂ h₁)
  theorem rw_star_sub_minmaxName {a b : MString} : MString.rw_star a b →
      (minmaxName a).rw_star (minmaxName b)
    | .step h => .step (rw_one.sub_minmaxName h)
    | .refl h => .refl (eqe.eqe_minmaxName h)
    | .trans h₀ h₁ => .trans (rw_star_sub_minmaxName h₀) (rw_star_sub_minmaxName h₁)
  theorem rw_star_sub_compareName {a b : MString} : MString.rw_star a b →
      (compareName a).rw_star (compareName b)
    | .step h => .step (rw_one.sub_compareName h)
    | .refl h => .refl (eqe.eqe_compareName h)
    | .trans h₀ h₁ => .trans (rw_star_sub_compareName h₀) (rw_star_sub_compareName h₁)
  theorem rw_star_sub_predicateName {a b : MString} : MString.rw_star a b →
      (predicateName a).rw_star (predicateName b)
    | .step h => .step (rw_one.sub_predicateName h)
    | .refl h => .refl (eqe.eqe_predicateName h)
    | .trans h₀ h₁ => .trans (rw_star_sub_predicateName h₀) (rw_star_sub_predicateName h₁)
  theorem rw_star_sub_formatNameOp {a b : MString} : MString.rw_star a b →
      (formatNameOp a).rw_star (formatNameOp b)
    | .step h => .step (rw_one.sub_formatNameOp h)
    | .refl h => .refl (eqe.eqe_formatNameOp h)
    | .trans h₀ h₁ => .trans (rw_star_sub_formatNameOp h₀) (rw_star_sub_formatNameOp h₁)
  theorem rw_star_sub_numericPlainName {a b : MString} : MString.rw_star a b →
      (numericPlainName a).rw_star (numericPlainName b)
    | .step h => .step (rw_one.sub_numericPlainName h)
    | .refl h => .refl (eqe.eqe_numericPlainName h)
    | .trans h₀ h₁ => .trans (rw_star_sub_numericPlainName h₀) (rw_star_sub_numericPlainName h₁)
  theorem rw_star_sub_blockElementArity₀ {a b : MString} {a₁ : MRat} : MString.rw_star a b →
      (blockElementArity a a₁).rw_star (blockElementArity b a₁)
    | .step h => .step (rw_one.sub_blockElementArity₀ h)
    | .refl h => .refl (eqe.eqe_blockElementArity h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_blockElementArity₀ h₀) (rw_star_sub_blockElementArity₀ h₁)
  theorem rw_star_sub_blockElementArity₁ {a₀ : MString} {a b : MRat} : MRat.rw_star a b →
      (blockElementArity a₀ a).rw_star (blockElementArity a₀ b)
    | .step h => .step (rw_one.sub_blockElementArity₁ h)
    | .refl h => .refl (eqe.eqe_blockElementArity rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_blockElementArity₁ h₀) (rw_star_sub_blockElementArity₁ h₁)
  theorem rw_star_sub_numericResult {a b : kSpecialization} : a.rw_star b →
      (numericResult a).rw_star (numericResult b)
    | .step h => .step (rw_one.sub_numericResult h)
    | .refl h => .refl (eqe.eqe_numericResult h)
    | .trans h₀ h₁ => .trans (rw_star_sub_numericResult h₀) (rw_star_sub_numericResult h₁)
  theorem rw_star_sub_hasDeclaration₀ {a b : kSpecialization} {a₁ : kDeclarationSeq} : a.rw_star b →
      (hasDeclaration a a₁).rw_star (hasDeclaration b a₁)
    | .step h => .step (rw_one.sub_hasDeclaration₀ h)
    | .refl h => .refl (eqe.eqe_hasDeclaration h (kDeclarationSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_hasDeclaration₀ h₀) (rw_star_sub_hasDeclaration₀ h₁)
  theorem rw_star_sub_hasDeclaration₁ {a₀ : kSpecialization} {a b : kDeclarationSeq} : a.rw_star b →
      (hasDeclaration a₀ a).rw_star (hasDeclaration a₀ b)
    | .step h => .step (rw_one.sub_hasDeclaration₁ h)
    | .refl h => .refl (eqe.eqe_hasDeclaration (kSpecialization.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_hasDeclaration₁ h₀) (rw_star_sub_hasDeclaration₁ h₁)
  theorem rw_star_sub_declarationsCover₀ {a b : kSpecializationSeq} {a₁ : kDeclarationSeq} : a.rw_star b →
      (declarationsCover a a₁).rw_star (declarationsCover b a₁)
    | .step h => .step (rw_one.sub_declarationsCover₀ h)
    | .refl h => .refl (eqe.eqe_declarationsCover h (kDeclarationSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_declarationsCover₀ h₀) (rw_star_sub_declarationsCover₀ h₁)
  theorem rw_star_sub_declarationsCover₁ {a₀ : kSpecializationSeq} {a b : kDeclarationSeq} : a.rw_star b →
      (declarationsCover a₀ a).rw_star (declarationsCover a₀ b)
    | .step h => .step (rw_one.sub_declarationsCover₁ h)
    | .refl h => .refl (eqe.eqe_declarationsCover (kSpecializationSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_declarationsCover₁ h₀) (rw_star_sub_declarationsCover₁ h₁)
  theorem rw_star_sub_partition₀ {a b : kCodeSeq} {a₁ : kPartitionSeq} : a.rw_star b →
      (partition a a₁).rw_star (partition b a₁)
    | .step h => .step (rw_one.sub_partition₀ h)
    | .refl h => .refl (eqe.eqe_partition h (kPartitionSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_partition₀ h₀) (rw_star_sub_partition₀ h₁)
  theorem rw_star_sub_partition₁ {a₀ : kCodeSeq} {a b : kPartitionSeq} : a.rw_star b →
      (partition a₀ a).rw_star (partition a₀ b)
    | .step h => .step (rw_one.sub_partition₁ h)
    | .refl h => .refl (eqe.eqe_partition (kCodeSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_partition₁ h₀) (rw_star_sub_partition₁ h₁)
  theorem rw_star_sub_partitionDisjoint {a b : kPartitionSeq} : a.rw_star b →
      (partitionDisjoint a).rw_star (partitionDisjoint b)
    | .step h => .step (rw_one.sub_partitionDisjoint h)
    | .refl h => .refl (eqe.eqe_partitionDisjoint h)
    | .trans h₀ h₁ => .trans (rw_star_sub_partitionDisjoint h₀) (rw_star_sub_partitionDisjoint h₁)
  theorem rw_star_sub_validSpecialization {a b : kSpecialization} : a.rw_star b →
      (validSpecialization a).rw_star (validSpecialization b)
    | .step h => .step (rw_one.sub_validSpecialization h)
    | .refl h => .refl (eqe.eqe_validSpecialization h)
    | .trans h₀ h₁ => .trans (rw_star_sub_validSpecialization h₀) (rw_star_sub_validSpecialization h₁)
  theorem rw_star_sub_numericArity₀ {a b : MString} {a₁ : MRat} : MString.rw_star a b →
      (numericArity a a₁).rw_star (numericArity b a₁)
    | .step h => .step (rw_one.sub_numericArity₀ h)
    | .refl h => .refl (eqe.eqe_numericArity h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_numericArity₀ h₀) (rw_star_sub_numericArity₀ h₁)
  theorem rw_star_sub_numericArity₁ {a₀ : MString} {a b : MRat} : MRat.rw_star a b →
      (numericArity a₀ a).rw_star (numericArity a₀ b)
    | .step h => .step (rw_one.sub_numericArity₁ h)
    | .refl h => .refl (eqe.eqe_numericArity rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_numericArity₁ h₀) (rw_star_sub_numericArity₁ h₁)
  theorem rw_star_sub_plainArity₀ {a b : MString} {a₁ : MRat} : MString.rw_star a b →
      (plainArity a a₁).rw_star (plainArity b a₁)
    | .step h => .step (rw_one.sub_plainArity₀ h)
    | .refl h => .refl (eqe.eqe_plainArity h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_plainArity₀ h₀) (rw_star_sub_plainArity₀ h₁)
  theorem rw_star_sub_plainArity₁ {a₀ : MString} {a b : MRat} : MRat.rw_star a b →
      (plainArity a₀ a).rw_star (plainArity a₀ b)
    | .step h => .step (rw_one.sub_plainArity₁ h)
    | .refl h => .refl (eqe.eqe_plainArity rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_plainArity₁ h₀) (rw_star_sub_plainArity₁ h₁)
  theorem rw_star_sub_wellFormedDeclaration {a b : kDeclaration} : a.rw_star b →
      (wellFormedDeclaration a).rw_star (wellFormedDeclaration b)
    | .step h => .step (rw_one.sub_wellFormedDeclaration h)
    | .refl h => .refl (eqe.eqe_wellFormedDeclaration h)
    | .trans h₀ h₁ => .trans (rw_star_sub_wellFormedDeclaration h₀) (rw_star_sub_wellFormedDeclaration h₁)
  theorem rw_star_sub_evidenceComplete {a b : kEvidence} : a.rw_star b →
      (evidenceComplete a).rw_star (evidenceComplete b)
    | .step h => .step (rw_one.sub_evidenceComplete h)
    | .refl h => .refl (eqe.eqe_evidenceComplete h)
    | .trans h₀ h₁ => .trans (rw_star_sub_evidenceComplete h₀) (rw_star_sub_evidenceComplete h₁)
  theorem rw_star_sub_memberCode₀ {a b : MRat} {a₁ : kCodeSeq} : MRat.rw_star a b →
      (memberCode a a₁).rw_star (memberCode b a₁)
    | .step h => .step (rw_one.sub_memberCode₀ h)
    | .refl h => .refl (eqe.eqe_memberCode h (kCodeSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_memberCode₀ h₀) (rw_star_sub_memberCode₀ h₁)
  theorem rw_star_sub_memberCode₁ {a₀ : MRat} {a b : kCodeSeq} : a.rw_star b →
      (memberCode a₀ a).rw_star (memberCode a₀ b)
    | .step h => .step (rw_one.sub_memberCode₁ h)
    | .refl h => .refl (eqe.eqe_memberCode rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_memberCode₁ h₀) (rw_star_sub_memberCode₁ h₁)
  theorem rw_star_sub_disjointCodes₀ {a b a₁ : kCodeSeq} : a.rw_star b →
      (disjointCodes a a₁).rw_star (disjointCodes b a₁)
    | .step h => .step (rw_one.sub_disjointCodes₀ h)
    | .refl h => .refl (eqe.eqe_disjointCodes h (kCodeSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_disjointCodes₀ h₀) (rw_star_sub_disjointCodes₀ h₁)
  theorem rw_star_sub_disjointCodes₁ {a₀ a b : kCodeSeq} : a.rw_star b →
      (disjointCodes a₀ a).rw_star (disjointCodes a₀ b)
    | .step h => .step (rw_one.sub_disjointCodes₁ h)
    | .refl h => .refl (eqe.eqe_disjointCodes (kCodeSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_disjointCodes₁ h₀) (rw_star_sub_disjointCodes₁ h₁)
  theorem rw_star_sub_uniqueCodes {a b : kCodeSeq} : a.rw_star b →
      (uniqueCodes a).rw_star (uniqueCodes b)
    | .step h => .step (rw_one.sub_uniqueCodes h)
    | .refl h => .refl (eqe.eqe_uniqueCodes h)
    | .trans h₀ h₁ => .trans (rw_star_sub_uniqueCodes h₀) (rw_star_sub_uniqueCodes h₁)
  theorem rw_star_sub_subsetCodes₀ {a b a₁ : kCodeSeq} : a.rw_star b →
      (subsetCodes a a₁).rw_star (subsetCodes b a₁)
    | .step h => .step (rw_one.sub_subsetCodes₀ h)
    | .refl h => .refl (eqe.eqe_subsetCodes h (kCodeSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_subsetCodes₀ h₀) (rw_star_sub_subsetCodes₀ h₁)
  theorem rw_star_sub_subsetCodes₁ {a₀ a b : kCodeSeq} : a.rw_star b →
      (subsetCodes a₀ a).rw_star (subsetCodes a₀ b)
    | .step h => .step (rw_one.sub_subsetCodes₁ h)
    | .refl h => .refl (eqe.eqe_subsetCodes (kCodeSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_subsetCodes₁ h₀) (rw_star_sub_subsetCodes₁ h₁)
  theorem rw_star_sub_partition2₀ {a b a₁ a₂ : kCodeSeq} : a.rw_star b →
      (partition2 a a₁ a₂).rw_star (partition2 b a₁ a₂)
    | .step h => .step (rw_one.sub_partition2₀ h)
    | .refl h => .refl (eqe.eqe_partition2 h (kCodeSeq.eqe_refl a₁) (kCodeSeq.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_partition2₀ h₀) (rw_star_sub_partition2₀ h₁)
  theorem rw_star_sub_partition2₁ {a₀ a b a₂ : kCodeSeq} : a.rw_star b →
      (partition2 a₀ a a₂).rw_star (partition2 a₀ b a₂)
    | .step h => .step (rw_one.sub_partition2₁ h)
    | .refl h => .refl (eqe.eqe_partition2 (kCodeSeq.eqe_refl a₀) h (kCodeSeq.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_partition2₁ h₀) (rw_star_sub_partition2₁ h₁)
  theorem rw_star_sub_partition2₂ {a₀ a₁ a b : kCodeSeq} : a.rw_star b →
      (partition2 a₀ a₁ a).rw_star (partition2 a₀ a₁ b)
    | .step h => .step (rw_one.sub_partition2₂ h)
    | .refl h => .refl (eqe.eqe_partition2 (kCodeSeq.eqe_refl a₀) (kCodeSeq.eqe_refl a₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_partition2₂ h₀) (rw_star_sub_partition2₂ h₁)
  theorem rw_star_sub_inArityTable₀ {a b : MString} {a₁ : MRat} {a₂ : kArityTable} : MString.rw_star a b →
      (inArityTable a a₁ a₂).rw_star (inArityTable b a₁ a₂)
    | .step h => .step (rw_one.sub_inArityTable₀ h)
    | .refl h => .refl (eqe.eqe_inArityTable h rfl (kArityTable.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_inArityTable₀ h₀) (rw_star_sub_inArityTable₀ h₁)
  theorem rw_star_sub_inArityTable₁ {a₀ : MString} {a b : MRat} {a₂ : kArityTable} : MRat.rw_star a b →
      (inArityTable a₀ a a₂).rw_star (inArityTable a₀ b a₂)
    | .step h => .step (rw_one.sub_inArityTable₁ h)
    | .refl h => .refl (eqe.eqe_inArityTable rfl h (kArityTable.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_inArityTable₁ h₀) (rw_star_sub_inArityTable₁ h₁)
  theorem rw_star_sub_inArityTable₂ {a₀ : MString} {a₁ : MRat} {a b : kArityTable} : a.rw_star b →
      (inArityTable a₀ a₁ a).rw_star (inArityTable a₀ a₁ b)
    | .step h => .step (rw_one.sub_inArityTable₂ h)
    | .refl h => .refl (eqe.eqe_inArityTable rfl rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_inArityTable₂ h₀) (rw_star_sub_inArityTable₂ h₁)
  theorem rw_star_sub_TotalOrder₀ {a b a₁ : kFormat} {a₂ a₃ : MRat} : a.rw_star b →
      (TotalOrder a a₁ a₂ a₃).rw_star (TotalOrder b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_TotalOrder₀ h)
    | .refl h => .refl (eqe.eqe_TotalOrder h (kFormat.eqe_refl a₁) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_TotalOrder₀ h₀) (rw_star_sub_TotalOrder₀ h₁)
  theorem rw_star_sub_TotalOrder₁ {a₀ a b : kFormat} {a₂ a₃ : MRat} : a.rw_star b →
      (TotalOrder a₀ a a₂ a₃).rw_star (TotalOrder a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_TotalOrder₁ h)
    | .refl h => .refl (eqe.eqe_TotalOrder (kFormat.eqe_refl a₀) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_TotalOrder₁ h₀) (rw_star_sub_TotalOrder₁ h₁)
  theorem rw_star_sub_TotalOrder₂ {a₀ a₁ : kFormat} {a b a₃ : MRat} : MRat.rw_star a b →
      (TotalOrder a₀ a₁ a a₃).rw_star (TotalOrder a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_TotalOrder₂ h)
    | .refl h => .refl (eqe.eqe_TotalOrder (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_TotalOrder₂ h₀) (rw_star_sub_TotalOrder₂ h₁)
  theorem rw_star_sub_TotalOrder₃ {a₀ a₁ : kFormat} {a₂ a b : MRat} : MRat.rw_star a b →
      (TotalOrder a₀ a₁ a₂ a).rw_star (TotalOrder a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_TotalOrder₃ h)
    | .refl h => .refl (eqe.eqe_TotalOrder (kFormat.eqe_refl a₀) (kFormat.eqe_refl a₁) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_TotalOrder₃ h₀) (rw_star_sub_TotalOrder₃ h₁)
  theorem rw_star_sub_eqeq₀₀ {a b a₁ : MRat} : MRat.rw_star a b →
      (eqeq₀ a a₁).rw_star (eqeq₀ b a₁)
    | .step h => .step (rw_one.sub_eqeq₀₀ h)
    | .refl h => .refl (eqe.eqe_eqeq₀ h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_eqeq₀₀ h₀) (rw_star_sub_eqeq₀₀ h₁)
  theorem rw_star_sub_eqeq₀₁ {a₀ a b : MRat} : MRat.rw_star a b →
      (eqeq₀ a₀ a).rw_star (eqeq₀ a₀ b)
    | .step h => .step (rw_one.sub_eqeq₀₁ h)
    | .refl h => .refl (eqe.eqe_eqeq₀ rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_eqeq₀₁ h₀) (rw_star_sub_eqeq₀₁ h₁)
  theorem rw_star_sub_ifthenelsefi₀ {a b a₁ a₂ : kBool} : a.rw_star b →
      (ifthenelsefi a a₁ a₂).rw_star (ifthenelsefi b a₁ a₂)
    | .step h => .step (rw_one.sub_ifthenelsefi₀ h)
    | .refl h => .refl (eqe.eqe_ifthenelsefi h (kBool.eqe_refl a₁) (kBool.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_ifthenelsefi₀ h₀) (rw_star_sub_ifthenelsefi₀ h₁)
  theorem rw_star_sub_ifthenelsefi₁ {a₀ a b a₂ : kBool} : a.rw_star b →
      (ifthenelsefi a₀ a a₂).rw_star (ifthenelsefi a₀ b a₂)
    | .step h => .step (rw_one.sub_ifthenelsefi₁ h)
    | .refl h => .refl (eqe.eqe_ifthenelsefi (kBool.eqe_refl a₀) h (kBool.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_ifthenelsefi₁ h₀) (rw_star_sub_ifthenelsefi₁ h₁)
  theorem rw_star_sub_ifthenelsefi₂ {a₀ a₁ a b : kBool} : a.rw_star b →
      (ifthenelsefi a₀ a₁ a).rw_star (ifthenelsefi a₀ a₁ b)
    | .step h => .step (rw_one.sub_ifthenelsefi₂ h)
    | .refl h => .refl (eqe.eqe_ifthenelsefi (kBool.eqe_refl a₀) (kBool.eqe_refl a₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ifthenelsefi₂ h₀) (rw_star_sub_ifthenelsefi₂ h₁)
  theorem rw_star_sub_eqeq₁₀ {a b a₁ : kSignedness} : a.rw_star b →
      (eqeq₁ a a₁).rw_star (eqeq₁ b a₁)
    | .step h => .step (rw_one.sub_eqeq₁₀ h)
    | .refl h => .refl (eqe.eqe_eqeq₁ h (kSignedness.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_eqeq₁₀ h₀) (rw_star_sub_eqeq₁₀ h₁)
  theorem rw_star_sub_eqeq₁₁ {a₀ a b : kSignedness} : a.rw_star b →
      (eqeq₁ a₀ a).rw_star (eqeq₁ a₀ b)
    | .step h => .step (rw_one.sub_eqeq₁₁ h)
    | .refl h => .refl (eqe.eqe_eqeq₁ (kSignedness.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_eqeq₁₁ h₀) (rw_star_sub_eqeq₁₁ h₁)
  theorem rw_star_sub_eqeq₂₀ {a b a₁ : kDomain} : a.rw_star b →
      (eqeq₂ a a₁).rw_star (eqeq₂ b a₁)
    | .step h => .step (rw_one.sub_eqeq₂₀ h)
    | .refl h => .refl (eqe.eqe_eqeq₂ h (kDomain.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_eqeq₂₀ h₀) (rw_star_sub_eqeq₂₀ h₁)
  theorem rw_star_sub_eqeq₂₁ {a₀ a b : kDomain} : a.rw_star b →
      (eqeq₂ a₀ a).rw_star (eqeq₂ a₀ b)
    | .step h => .step (rw_one.sub_eqeq₂₁ h)
    | .refl h => .refl (eqe.eqe_eqeq₂ (kDomain.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_eqeq₂₁ h₀) (rw_star_sub_eqeq₂₁ h₁)
  theorem rw_star_sub_eqslasheq₀₀ {a b a₁ : MRat} : MRat.rw_star a b →
      (eqslasheq₀ a a₁).rw_star (eqslasheq₀ b a₁)
    | .step h => .step (rw_one.sub_eqslasheq₀₀ h)
    | .refl h => .refl (eqe.eqe_eqslasheq₀ h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_eqslasheq₀₀ h₀) (rw_star_sub_eqslasheq₀₀ h₁)
  theorem rw_star_sub_eqslasheq₀₁ {a₀ a b : MRat} : MRat.rw_star a b →
      (eqslasheq₀ a₀ a).rw_star (eqslasheq₀ a₀ b)
    | .step h => .step (rw_one.sub_eqslasheq₀₁ h)
    | .refl h => .refl (eqe.eqe_eqslasheq₀ rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_eqslasheq₀₁ h₀) (rw_star_sub_eqslasheq₀₁ h₁)
  theorem rw_star_sub_eqeq₃₀ {a b a₁ : kBlockRoundMode} : a.rw_star b →
      (eqeq₃ a a₁).rw_star (eqeq₃ b a₁)
    | .step h => .step (rw_one.sub_eqeq₃₀ h)
    | .refl h => .refl (eqe.eqe_eqeq₃ h (kBlockRoundMode.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_eqeq₃₀ h₀) (rw_star_sub_eqeq₃₀ h₁)
  theorem rw_star_sub_eqeq₃₁ {a₀ a b : kBlockRoundMode} : a.rw_star b →
      (eqeq₃ a₀ a).rw_star (eqeq₃ a₀ b)
    | .step h => .step (rw_one.sub_eqeq₃₁ h)
    | .refl h => .refl (eqe.eqe_eqeq₃ (kBlockRoundMode.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_eqeq₃₁ h₀) (rw_star_sub_eqeq₃₁ h₁)
  theorem rw_star_sub_eqeq₄₀ {a b a₁ : kBool} : a.rw_star b →
      (eqeq₄ a a₁).rw_star (eqeq₄ b a₁)
    | .step h => .step (rw_one.sub_eqeq₄₀ h)
    | .refl h => .refl (eqe.eqe_eqeq₄ h (kBool.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_eqeq₄₀ h₀) (rw_star_sub_eqeq₄₀ h₁)
  theorem rw_star_sub_eqeq₄₁ {a₀ a b : kBool} : a.rw_star b →
      (eqeq₄ a₀ a).rw_star (eqeq₄ a₀ b)
    | .step h => .step (rw_one.sub_eqeq₄₁ h)
    | .refl h => .refl (eqe.eqe_eqeq₄ (kBool.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_eqeq₄₁ h₀) (rw_star_sub_eqeq₄₁ h₁)
  theorem rw_star_sub_eqeq₅₀ {a b a₁ : MString} : MString.rw_star a b →
      (eqeq₅ a a₁).rw_star (eqeq₅ b a₁)
    | .step h => .step (rw_one.sub_eqeq₅₀ h)
    | .refl h => .refl (eqe.eqe_eqeq₅ h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_eqeq₅₀ h₀) (rw_star_sub_eqeq₅₀ h₁)
  theorem rw_star_sub_eqeq₅₁ {a₀ a b : MString} : MString.rw_star a b →
      (eqeq₅ a₀ a).rw_star (eqeq₅ a₀ b)
    | .step h => .step (rw_one.sub_eqeq₅₁ h)
    | .refl h => .refl (eqe.eqe_eqeq₅ rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_eqeq₅₁ h₀) (rw_star_sub_eqeq₅₁ h₁)
  theorem rw_star_sub_eqeq₆₀ {a b a₁ : kFormat} : a.rw_star b →
      (eqeq₆ a a₁).rw_star (eqeq₆ b a₁)
    | .step h => .step (rw_one.sub_eqeq₆₀ h)
    | .refl h => .refl (eqe.eqe_eqeq₆ h (kFormat.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_eqeq₆₀ h₀) (rw_star_sub_eqeq₆₀ h₁)
  theorem rw_star_sub_eqeq₆₁ {a₀ a b : kFormat} : a.rw_star b →
      (eqeq₆ a₀ a).rw_star (eqeq₆ a₀ b)
    | .step h => .step (rw_one.sub_eqeq₆₁ h)
    | .refl h => .refl (eqe.eqe_eqeq₆ (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_eqeq₆₁ h₀) (rw_star_sub_eqeq₆₁ h₁)
  theorem rw_star_sub_eqeq₇₀ {a b a₁ : kProjSpec} : a.rw_star b →
      (eqeq₇ a a₁).rw_star (eqeq₇ b a₁)
    | .step h => .step (rw_one.sub_eqeq₇₀ h)
    | .refl h => .refl (eqe.eqe_eqeq₇ h (kProjSpec.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_eqeq₇₀ h₀) (rw_star_sub_eqeq₇₀ h₁)
  theorem rw_star_sub_eqeq₇₁ {a₀ a b : kProjSpec} : a.rw_star b →
      (eqeq₇ a₀ a).rw_star (eqeq₇ a₀ b)
    | .step h => .step (rw_one.sub_eqeq₇₁ h)
    | .refl h => .refl (eqe.eqe_eqeq₇ (kProjSpec.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_eqeq₇₁ h₀) (rw_star_sub_eqeq₇₁ h₁)
  theorem rw_star_sub_eqslasheq₁₀ {a b a₁ : kBool} : a.rw_star b →
      (eqslasheq₁ a a₁).rw_star (eqslasheq₁ b a₁)
    | .step h => .step (rw_one.sub_eqslasheq₁₀ h)
    | .refl h => .refl (eqe.eqe_eqslasheq₁ h (kBool.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_eqslasheq₁₀ h₀) (rw_star_sub_eqslasheq₁₀ h₁)
  theorem rw_star_sub_eqslasheq₁₁ {a₀ a b : kBool} : a.rw_star b →
      (eqslasheq₁ a₀ a).rw_star (eqslasheq₁ a₀ b)
    | .step h => .step (rw_one.sub_eqslasheq₁₁ h)
    | .refl h => .refl (eqe.eqe_eqslasheq₁ (kBool.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_eqslasheq₁₁ h₀) (rw_star_sub_eqslasheq₁₁ h₁)
  theorem rw_star_sub_eqslasheq₂₀ {a b a₁ : MString} : MString.rw_star a b →
      (eqslasheq₂ a a₁).rw_star (eqslasheq₂ b a₁)
    | .step h => .step (rw_one.sub_eqslasheq₂₀ h)
    | .refl h => .refl (eqe.eqe_eqslasheq₂ h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_eqslasheq₂₀ h₀) (rw_star_sub_eqslasheq₂₀ h₁)
  theorem rw_star_sub_eqslasheq₂₁ {a₀ a b : MString} : MString.rw_star a b →
      (eqslasheq₂ a₀ a).rw_star (eqslasheq₂ a₀ b)
    | .step h => .step (rw_one.sub_eqslasheq₂₁ h)
    | .refl h => .refl (eqe.eqe_eqslasheq₂ rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_eqslasheq₂₁ h₀) (rw_star_sub_eqslasheq₂₁ h₁)
  theorem rw_star_sub_eqeq₈₀ {a b a₁ : kSpecialization} : a.rw_star b →
      (eqeq₈ a a₁).rw_star (eqeq₈ b a₁)
    | .step h => .step (rw_one.sub_eqeq₈₀ h)
    | .refl h => .refl (eqe.eqe_eqeq₈ h (kSpecialization.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_eqeq₈₀ h₀) (rw_star_sub_eqeq₈₀ h₁)
  theorem rw_star_sub_eqeq₈₁ {a₀ a b : kSpecialization} : a.rw_star b →
      (eqeq₈ a₀ a).rw_star (eqeq₈ a₀ b)
    | .step h => .step (rw_one.sub_eqeq₈₁ h)
    | .refl h => .refl (eqe.eqe_eqeq₈ (kSpecialization.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_eqeq₈₁ h₀) (rw_star_sub_eqeq₈₁ h₁)
end kBool

end Maude
