-- Extracted from ../spec2.lean, lines 12258-12927.
-- See PLAN.md and manifest.json for provenance.
import P3109.Lemmas.Rewriting.Formats

namespace Maude
namespace kXSeq
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kXSeq} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kXSeq} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kXSeq} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kXSeq} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_xcons₀ {a b : kXReal} {a₁ : kXSeq} : a.rw_star b →
      (xcons a a₁).rw_star (xcons b a₁)
    | .step h => .step (rw_one.sub_xcons₀ h)
    | .refl h => .refl (eqe.eqe_xcons h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_xcons₀ h₀) (rw_star_sub_xcons₀ h₁)
  theorem rw_star_sub_xcons₁ {a₀ : kXReal} {a b : kXSeq} : a.rw_star b →
      (xcons a₀ a).rw_star (xcons a₀ b)
    | .step h => .step (rw_one.sub_xcons₁ h)
    | .refl h => .refl (eqe.eqe_xcons (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_xcons₁ h₀) (rw_star_sub_xcons₁ h₁)
  theorem rw_star_sub_decodeElements₀ {a b : kFormat} {a₁ : kCodeSeq} : a.rw_star b →
      (decodeElements a a₁).rw_star (decodeElements b a₁)
    | .step h => .step (rw_one.sub_decodeElements₀ h)
    | .refl h => .refl (eqe.eqe_decodeElements h (kCodeSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_decodeElements₀ h₀) (rw_star_sub_decodeElements₀ h₁)
  theorem rw_star_sub_decodeElements₁ {a₀ : kFormat} {a b : kCodeSeq} : a.rw_star b →
      (decodeElements a₀ a).rw_star (decodeElements a₀ b)
    | .step h => .step (rw_one.sub_decodeElements₁ h)
    | .refl h => .refl (eqe.eqe_decodeElements (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_decodeElements₁ h₀) (rw_star_sub_decodeElements₁ h₁)
  theorem rw_star_sub_multiplyElements₀ {a b : kXReal} {a₁ : kXSeq} : a.rw_star b →
      (multiplyElements a a₁).rw_star (multiplyElements b a₁)
    | .step h => .step (rw_one.sub_multiplyElements₀ h)
    | .refl h => .refl (eqe.eqe_multiplyElements h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_multiplyElements₀ h₀) (rw_star_sub_multiplyElements₀ h₁)
  theorem rw_star_sub_multiplyElements₁ {a₀ : kXReal} {a b : kXSeq} : a.rw_star b →
      (multiplyElements a₀ a).rw_star (multiplyElements a₀ b)
    | .step h => .step (rw_one.sub_multiplyElements₁ h)
    | .refl h => .refl (eqe.eqe_multiplyElements (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_multiplyElements₁ h₀) (rw_star_sub_multiplyElements₁ h₁)
  theorem rw_star_sub_blockDecode₀ {a b : MRat} {a₁ a₂ : kFormat} {a₃ : MRat} {a₄ : kCodeSeq} : MRat.rw_star a b →
      (blockDecode a a₁ a₂ a₃ a₄).rw_star (blockDecode b a₁ a₂ a₃ a₄)
    | .step h => .step (rw_one.sub_blockDecode₀ h)
    | .refl h => .refl (eqe.eqe_blockDecode h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) rfl (kCodeSeq.eqe_refl a₄))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockDecode₀ h₀) (rw_star_sub_blockDecode₀ h₁)
  theorem rw_star_sub_blockDecode₁ {a₀ : MRat} {a b a₂ : kFormat} {a₃ : MRat} {a₄ : kCodeSeq} : a.rw_star b →
      (blockDecode a₀ a a₂ a₃ a₄).rw_star (blockDecode a₀ b a₂ a₃ a₄)
    | .step h => .step (rw_one.sub_blockDecode₁ h)
    | .refl h => .refl (eqe.eqe_blockDecode rfl h (kFormat.eqe_refl a₂) rfl (kCodeSeq.eqe_refl a₄))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockDecode₁ h₀) (rw_star_sub_blockDecode₁ h₁)
  theorem rw_star_sub_blockDecode₂ {a₀ : MRat} {a₁ a b : kFormat} {a₃ : MRat} {a₄ : kCodeSeq} : a.rw_star b →
      (blockDecode a₀ a₁ a a₃ a₄).rw_star (blockDecode a₀ a₁ b a₃ a₄)
    | .step h => .step (rw_one.sub_blockDecode₂ h)
    | .refl h => .refl (eqe.eqe_blockDecode rfl (kFormat.eqe_refl a₁) h rfl (kCodeSeq.eqe_refl a₄))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockDecode₂ h₀) (rw_star_sub_blockDecode₂ h₁)
  theorem rw_star_sub_blockDecode₃ {a₀ : MRat} {a₁ a₂ : kFormat} {a b : MRat} {a₄ : kCodeSeq} : MRat.rw_star a b →
      (blockDecode a₀ a₁ a₂ a a₄).rw_star (blockDecode a₀ a₁ a₂ b a₄)
    | .step h => .step (rw_one.sub_blockDecode₃ h)
    | .refl h => .refl (eqe.eqe_blockDecode rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kCodeSeq.eqe_refl a₄))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockDecode₃ h₀) (rw_star_sub_blockDecode₃ h₁)
  theorem rw_star_sub_blockDecode₄ {a₀ : MRat} {a₁ a₂ : kFormat} {a₃ : MRat} {a b : kCodeSeq} : a.rw_star b →
      (blockDecode a₀ a₁ a₂ a₃ a).rw_star (blockDecode a₀ a₁ a₂ a₃ b)
    | .step h => .step (rw_one.sub_blockDecode₄ h)
    | .refl h => .refl (eqe.eqe_blockDecode rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_blockDecode₄ h₀) (rw_star_sub_blockDecode₄ h₁)
  theorem rw_star_sub_absElements {a b : kXSeq} : a.rw_star b →
      (absElements a).rw_star (absElements b)
    | .step h => .step (rw_one.sub_absElements h)
    | .refl h => .refl (eqe.eqe_absElements h)
    | .trans h₀ h₁ => .trans (rw_star_sub_absElements h₀) (rw_star_sub_absElements h₁)
  theorem rw_star_sub_pairProducts₀ {a b a₁ : kXSeq} : a.rw_star b →
      (pairProducts a a₁).rw_star (pairProducts b a₁)
    | .step h => .step (rw_one.sub_pairProducts₀ h)
    | .refl h => .refl (eqe.eqe_pairProducts h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_pairProducts₀ h₀) (rw_star_sub_pairProducts₀ h₁)
  theorem rw_star_sub_pairProducts₁ {a₀ a b : kXSeq} : a.rw_star b →
      (pairProducts a₀ a).rw_star (pairProducts a₀ b)
    | .step h => .step (rw_one.sub_pairProducts₁ h)
    | .refl h => .refl (eqe.eqe_pairProducts (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_pairProducts₁ h₀) (rw_star_sub_pairProducts₁ h₁)
  theorem rw_star_sub_mapConvert {a b : kXSeq} : a.rw_star b →
      (mapConvert a).rw_star (mapConvert b)
    | .step h => .step (rw_one.sub_mapConvert h)
    | .refl h => .refl (eqe.eqe_mapConvert h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapConvert h₀) (rw_star_sub_mapConvert h₁)
  theorem rw_star_sub_mapAbs {a b : kXSeq} : a.rw_star b →
      (mapAbs a).rw_star (mapAbs b)
    | .step h => .step (rw_one.sub_mapAbs h)
    | .refl h => .refl (eqe.eqe_mapAbs h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapAbs h₀) (rw_star_sub_mapAbs h₁)
  theorem rw_star_sub_mapNegate {a b : kXSeq} : a.rw_star b →
      (mapNegate a).rw_star (mapNegate b)
    | .step h => .step (rw_one.sub_mapNegate h)
    | .refl h => .refl (eqe.eqe_mapNegate h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapNegate h₀) (rw_star_sub_mapNegate h₁)
  theorem rw_star_sub_mapCopySign₀ {a b a₁ : kXSeq} : a.rw_star b →
      (mapCopySign a a₁).rw_star (mapCopySign b a₁)
    | .step h => .step (rw_one.sub_mapCopySign₀ h)
    | .refl h => .refl (eqe.eqe_mapCopySign h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapCopySign₀ h₀) (rw_star_sub_mapCopySign₀ h₁)
  theorem rw_star_sub_mapCopySign₁ {a₀ a b : kXSeq} : a.rw_star b →
      (mapCopySign a₀ a).rw_star (mapCopySign a₀ b)
    | .step h => .step (rw_one.sub_mapCopySign₁ h)
    | .refl h => .refl (eqe.eqe_mapCopySign (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapCopySign₁ h₀) (rw_star_sub_mapCopySign₁ h₁)
  theorem rw_star_sub_mapAdd₀ {a b a₁ : kXSeq} : a.rw_star b →
      (mapAdd a a₁).rw_star (mapAdd b a₁)
    | .step h => .step (rw_one.sub_mapAdd₀ h)
    | .refl h => .refl (eqe.eqe_mapAdd h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapAdd₀ h₀) (rw_star_sub_mapAdd₀ h₁)
  theorem rw_star_sub_mapAdd₁ {a₀ a b : kXSeq} : a.rw_star b →
      (mapAdd a₀ a).rw_star (mapAdd a₀ b)
    | .step h => .step (rw_one.sub_mapAdd₁ h)
    | .refl h => .refl (eqe.eqe_mapAdd (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapAdd₁ h₀) (rw_star_sub_mapAdd₁ h₁)
  theorem rw_star_sub_mapSubtract₀ {a b a₁ : kXSeq} : a.rw_star b →
      (mapSubtract a a₁).rw_star (mapSubtract b a₁)
    | .step h => .step (rw_one.sub_mapSubtract₀ h)
    | .refl h => .refl (eqe.eqe_mapSubtract h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapSubtract₀ h₀) (rw_star_sub_mapSubtract₀ h₁)
  theorem rw_star_sub_mapSubtract₁ {a₀ a b : kXSeq} : a.rw_star b →
      (mapSubtract a₀ a).rw_star (mapSubtract a₀ b)
    | .step h => .step (rw_one.sub_mapSubtract₁ h)
    | .refl h => .refl (eqe.eqe_mapSubtract (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapSubtract₁ h₀) (rw_star_sub_mapSubtract₁ h₁)
  theorem rw_star_sub_mapMultiply₀ {a b a₁ : kXSeq} : a.rw_star b →
      (mapMultiply a a₁).rw_star (mapMultiply b a₁)
    | .step h => .step (rw_one.sub_mapMultiply₀ h)
    | .refl h => .refl (eqe.eqe_mapMultiply h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMultiply₀ h₀) (rw_star_sub_mapMultiply₀ h₁)
  theorem rw_star_sub_mapMultiply₁ {a₀ a b : kXSeq} : a.rw_star b →
      (mapMultiply a₀ a).rw_star (mapMultiply a₀ b)
    | .step h => .step (rw_one.sub_mapMultiply₁ h)
    | .refl h => .refl (eqe.eqe_mapMultiply (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMultiply₁ h₀) (rw_star_sub_mapMultiply₁ h₁)
  theorem rw_star_sub_mapDivide₀ {a b a₁ : kXSeq} : a.rw_star b →
      (mapDivide a a₁).rw_star (mapDivide b a₁)
    | .step h => .step (rw_one.sub_mapDivide₀ h)
    | .refl h => .refl (eqe.eqe_mapDivide h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapDivide₀ h₀) (rw_star_sub_mapDivide₀ h₁)
  theorem rw_star_sub_mapDivide₁ {a₀ a b : kXSeq} : a.rw_star b →
      (mapDivide a₀ a).rw_star (mapDivide a₀ b)
    | .step h => .step (rw_one.sub_mapDivide₁ h)
    | .refl h => .refl (eqe.eqe_mapDivide (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapDivide₁ h₀) (rw_star_sub_mapDivide₁ h₁)
  theorem rw_star_sub_mapFMA₀ {a b a₁ a₂ : kXSeq} : a.rw_star b →
      (mapFMA a a₁ a₂).rw_star (mapFMA b a₁ a₂)
    | .step h => .step (rw_one.sub_mapFMA₀ h)
    | .refl h => .refl (eqe.eqe_mapFMA h (kXSeq.eqe_refl a₁) (kXSeq.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapFMA₀ h₀) (rw_star_sub_mapFMA₀ h₁)
  theorem rw_star_sub_mapFMA₁ {a₀ a b a₂ : kXSeq} : a.rw_star b →
      (mapFMA a₀ a a₂).rw_star (mapFMA a₀ b a₂)
    | .step h => .step (rw_one.sub_mapFMA₁ h)
    | .refl h => .refl (eqe.eqe_mapFMA (kXSeq.eqe_refl a₀) h (kXSeq.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapFMA₁ h₀) (rw_star_sub_mapFMA₁ h₁)
  theorem rw_star_sub_mapFMA₂ {a₀ a₁ a b : kXSeq} : a.rw_star b →
      (mapFMA a₀ a₁ a).rw_star (mapFMA a₀ a₁ b)
    | .step h => .step (rw_one.sub_mapFMA₂ h)
    | .refl h => .refl (eqe.eqe_mapFMA (kXSeq.eqe_refl a₀) (kXSeq.eqe_refl a₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapFMA₂ h₀) (rw_star_sub_mapFMA₂ h₁)
  theorem rw_star_sub_mapFAA₀ {a b a₁ a₂ : kXSeq} : a.rw_star b →
      (mapFAA a a₁ a₂).rw_star (mapFAA b a₁ a₂)
    | .step h => .step (rw_one.sub_mapFAA₀ h)
    | .refl h => .refl (eqe.eqe_mapFAA h (kXSeq.eqe_refl a₁) (kXSeq.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapFAA₀ h₀) (rw_star_sub_mapFAA₀ h₁)
  theorem rw_star_sub_mapFAA₁ {a₀ a b a₂ : kXSeq} : a.rw_star b →
      (mapFAA a₀ a a₂).rw_star (mapFAA a₀ b a₂)
    | .step h => .step (rw_one.sub_mapFAA₁ h)
    | .refl h => .refl (eqe.eqe_mapFAA (kXSeq.eqe_refl a₀) h (kXSeq.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapFAA₁ h₀) (rw_star_sub_mapFAA₁ h₁)
  theorem rw_star_sub_mapFAA₂ {a₀ a₁ a b : kXSeq} : a.rw_star b →
      (mapFAA a₀ a₁ a).rw_star (mapFAA a₀ a₁ b)
    | .step h => .step (rw_one.sub_mapFAA₂ h)
    | .refl h => .refl (eqe.eqe_mapFAA (kXSeq.eqe_refl a₀) (kXSeq.eqe_refl a₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapFAA₂ h₀) (rw_star_sub_mapFAA₂ h₁)
  theorem rw_star_sub_mapRecip {a b : kXSeq} : a.rw_star b →
      (mapRecip a).rw_star (mapRecip b)
    | .step h => .step (rw_one.sub_mapRecip h)
    | .refl h => .refl (eqe.eqe_mapRecip h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapRecip h₀) (rw_star_sub_mapRecip h₁)
  theorem rw_star_sub_mapMinimum₀ {a b a₁ : kXSeq} : a.rw_star b →
      (mapMinimum a a₁).rw_star (mapMinimum b a₁)
    | .step h => .step (rw_one.sub_mapMinimum₀ h)
    | .refl h => .refl (eqe.eqe_mapMinimum h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMinimum₀ h₀) (rw_star_sub_mapMinimum₀ h₁)
  theorem rw_star_sub_mapMinimum₁ {a₀ a b : kXSeq} : a.rw_star b →
      (mapMinimum a₀ a).rw_star (mapMinimum a₀ b)
    | .step h => .step (rw_one.sub_mapMinimum₁ h)
    | .refl h => .refl (eqe.eqe_mapMinimum (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMinimum₁ h₀) (rw_star_sub_mapMinimum₁ h₁)
  theorem rw_star_sub_mapMaximum₀ {a b a₁ : kXSeq} : a.rw_star b →
      (mapMaximum a a₁).rw_star (mapMaximum b a₁)
    | .step h => .step (rw_one.sub_mapMaximum₀ h)
    | .refl h => .refl (eqe.eqe_mapMaximum h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMaximum₀ h₀) (rw_star_sub_mapMaximum₀ h₁)
  theorem rw_star_sub_mapMaximum₁ {a₀ a b : kXSeq} : a.rw_star b →
      (mapMaximum a₀ a).rw_star (mapMaximum a₀ b)
    | .step h => .step (rw_one.sub_mapMaximum₁ h)
    | .refl h => .refl (eqe.eqe_mapMaximum (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMaximum₁ h₀) (rw_star_sub_mapMaximum₁ h₁)
  theorem rw_star_sub_mapMinimumNumber₀ {a b a₁ : kXSeq} : a.rw_star b →
      (mapMinimumNumber a a₁).rw_star (mapMinimumNumber b a₁)
    | .step h => .step (rw_one.sub_mapMinimumNumber₀ h)
    | .refl h => .refl (eqe.eqe_mapMinimumNumber h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMinimumNumber₀ h₀) (rw_star_sub_mapMinimumNumber₀ h₁)
  theorem rw_star_sub_mapMinimumNumber₁ {a₀ a b : kXSeq} : a.rw_star b →
      (mapMinimumNumber a₀ a).rw_star (mapMinimumNumber a₀ b)
    | .step h => .step (rw_one.sub_mapMinimumNumber₁ h)
    | .refl h => .refl (eqe.eqe_mapMinimumNumber (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMinimumNumber₁ h₀) (rw_star_sub_mapMinimumNumber₁ h₁)
  theorem rw_star_sub_mapMaximumNumber₀ {a b a₁ : kXSeq} : a.rw_star b →
      (mapMaximumNumber a a₁).rw_star (mapMaximumNumber b a₁)
    | .step h => .step (rw_one.sub_mapMaximumNumber₀ h)
    | .refl h => .refl (eqe.eqe_mapMaximumNumber h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMaximumNumber₀ h₀) (rw_star_sub_mapMaximumNumber₀ h₁)
  theorem rw_star_sub_mapMaximumNumber₁ {a₀ a b : kXSeq} : a.rw_star b →
      (mapMaximumNumber a₀ a).rw_star (mapMaximumNumber a₀ b)
    | .step h => .step (rw_one.sub_mapMaximumNumber₁ h)
    | .refl h => .refl (eqe.eqe_mapMaximumNumber (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMaximumNumber₁ h₀) (rw_star_sub_mapMaximumNumber₁ h₁)
  theorem rw_star_sub_mapMinimumMagnitude₀ {a b a₁ : kXSeq} : a.rw_star b →
      (mapMinimumMagnitude a a₁).rw_star (mapMinimumMagnitude b a₁)
    | .step h => .step (rw_one.sub_mapMinimumMagnitude₀ h)
    | .refl h => .refl (eqe.eqe_mapMinimumMagnitude h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMinimumMagnitude₀ h₀) (rw_star_sub_mapMinimumMagnitude₀ h₁)
  theorem rw_star_sub_mapMinimumMagnitude₁ {a₀ a b : kXSeq} : a.rw_star b →
      (mapMinimumMagnitude a₀ a).rw_star (mapMinimumMagnitude a₀ b)
    | .step h => .step (rw_one.sub_mapMinimumMagnitude₁ h)
    | .refl h => .refl (eqe.eqe_mapMinimumMagnitude (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMinimumMagnitude₁ h₀) (rw_star_sub_mapMinimumMagnitude₁ h₁)
  theorem rw_star_sub_mapMaximumMagnitude₀ {a b a₁ : kXSeq} : a.rw_star b →
      (mapMaximumMagnitude a a₁).rw_star (mapMaximumMagnitude b a₁)
    | .step h => .step (rw_one.sub_mapMaximumMagnitude₀ h)
    | .refl h => .refl (eqe.eqe_mapMaximumMagnitude h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMaximumMagnitude₀ h₀) (rw_star_sub_mapMaximumMagnitude₀ h₁)
  theorem rw_star_sub_mapMaximumMagnitude₁ {a₀ a b : kXSeq} : a.rw_star b →
      (mapMaximumMagnitude a₀ a).rw_star (mapMaximumMagnitude a₀ b)
    | .step h => .step (rw_one.sub_mapMaximumMagnitude₁ h)
    | .refl h => .refl (eqe.eqe_mapMaximumMagnitude (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMaximumMagnitude₁ h₀) (rw_star_sub_mapMaximumMagnitude₁ h₁)
  theorem rw_star_sub_mapMinimumMagnitudeNumber₀ {a b a₁ : kXSeq} : a.rw_star b →
      (mapMinimumMagnitudeNumber a a₁).rw_star (mapMinimumMagnitudeNumber b a₁)
    | .step h => .step (rw_one.sub_mapMinimumMagnitudeNumber₀ h)
    | .refl h => .refl (eqe.eqe_mapMinimumMagnitudeNumber h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMinimumMagnitudeNumber₀ h₀) (rw_star_sub_mapMinimumMagnitudeNumber₀ h₁)
  theorem rw_star_sub_mapMinimumMagnitudeNumber₁ {a₀ a b : kXSeq} : a.rw_star b →
      (mapMinimumMagnitudeNumber a₀ a).rw_star (mapMinimumMagnitudeNumber a₀ b)
    | .step h => .step (rw_one.sub_mapMinimumMagnitudeNumber₁ h)
    | .refl h => .refl (eqe.eqe_mapMinimumMagnitudeNumber (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMinimumMagnitudeNumber₁ h₀) (rw_star_sub_mapMinimumMagnitudeNumber₁ h₁)
  theorem rw_star_sub_mapMaximumMagnitudeNumber₀ {a b a₁ : kXSeq} : a.rw_star b →
      (mapMaximumMagnitudeNumber a a₁).rw_star (mapMaximumMagnitudeNumber b a₁)
    | .step h => .step (rw_one.sub_mapMaximumMagnitudeNumber₀ h)
    | .refl h => .refl (eqe.eqe_mapMaximumMagnitudeNumber h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMaximumMagnitudeNumber₀ h₀) (rw_star_sub_mapMaximumMagnitudeNumber₀ h₁)
  theorem rw_star_sub_mapMaximumMagnitudeNumber₁ {a₀ a b : kXSeq} : a.rw_star b →
      (mapMaximumMagnitudeNumber a₀ a).rw_star (mapMaximumMagnitudeNumber a₀ b)
    | .step h => .step (rw_one.sub_mapMaximumMagnitudeNumber₁ h)
    | .refl h => .refl (eqe.eqe_mapMaximumMagnitudeNumber (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMaximumMagnitudeNumber₁ h₀) (rw_star_sub_mapMaximumMagnitudeNumber₁ h₁)
  theorem rw_star_sub_mapMinimumFinite₀ {a b a₁ : kXSeq} : a.rw_star b →
      (mapMinimumFinite a a₁).rw_star (mapMinimumFinite b a₁)
    | .step h => .step (rw_one.sub_mapMinimumFinite₀ h)
    | .refl h => .refl (eqe.eqe_mapMinimumFinite h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMinimumFinite₀ h₀) (rw_star_sub_mapMinimumFinite₀ h₁)
  theorem rw_star_sub_mapMinimumFinite₁ {a₀ a b : kXSeq} : a.rw_star b →
      (mapMinimumFinite a₀ a).rw_star (mapMinimumFinite a₀ b)
    | .step h => .step (rw_one.sub_mapMinimumFinite₁ h)
    | .refl h => .refl (eqe.eqe_mapMinimumFinite (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMinimumFinite₁ h₀) (rw_star_sub_mapMinimumFinite₁ h₁)
  theorem rw_star_sub_mapMaximumFinite₀ {a b a₁ : kXSeq} : a.rw_star b →
      (mapMaximumFinite a a₁).rw_star (mapMaximumFinite b a₁)
    | .step h => .step (rw_one.sub_mapMaximumFinite₀ h)
    | .refl h => .refl (eqe.eqe_mapMaximumFinite h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMaximumFinite₀ h₀) (rw_star_sub_mapMaximumFinite₀ h₁)
  theorem rw_star_sub_mapMaximumFinite₁ {a₀ a b : kXSeq} : a.rw_star b →
      (mapMaximumFinite a₀ a).rw_star (mapMaximumFinite a₀ b)
    | .step h => .step (rw_one.sub_mapMaximumFinite₁ h)
    | .refl h => .refl (eqe.eqe_mapMaximumFinite (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapMaximumFinite₁ h₀) (rw_star_sub_mapMaximumFinite₁ h₁)
  theorem rw_star_sub_mapClamp₀ {a b a₁ a₂ : kXSeq} : a.rw_star b →
      (mapClamp a a₁ a₂).rw_star (mapClamp b a₁ a₂)
    | .step h => .step (rw_one.sub_mapClamp₀ h)
    | .refl h => .refl (eqe.eqe_mapClamp h (kXSeq.eqe_refl a₁) (kXSeq.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapClamp₀ h₀) (rw_star_sub_mapClamp₀ h₁)
  theorem rw_star_sub_mapClamp₁ {a₀ a b a₂ : kXSeq} : a.rw_star b →
      (mapClamp a₀ a a₂).rw_star (mapClamp a₀ b a₂)
    | .step h => .step (rw_one.sub_mapClamp₁ h)
    | .refl h => .refl (eqe.eqe_mapClamp (kXSeq.eqe_refl a₀) h (kXSeq.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapClamp₁ h₀) (rw_star_sub_mapClamp₁ h₁)
  theorem rw_star_sub_mapClamp₂ {a₀ a₁ a b : kXSeq} : a.rw_star b →
      (mapClamp a₀ a₁ a).rw_star (mapClamp a₀ a₁ b)
    | .step h => .step (rw_one.sub_mapClamp₂ h)
    | .refl h => .refl (eqe.eqe_mapClamp (kXSeq.eqe_refl a₀) (kXSeq.eqe_refl a₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapClamp₂ h₀) (rw_star_sub_mapClamp₂ h₁)
  theorem rw_star_sub_mapSqrt {a b : kXSeq} : a.rw_star b →
      (mapSqrt a).rw_star (mapSqrt b)
    | .step h => .step (rw_one.sub_mapSqrt h)
    | .refl h => .refl (eqe.eqe_mapSqrt h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapSqrt h₀) (rw_star_sub_mapSqrt h₁)
  theorem rw_star_sub_mapRSqrt {a b : kXSeq} : a.rw_star b →
      (mapRSqrt a).rw_star (mapRSqrt b)
    | .step h => .step (rw_one.sub_mapRSqrt h)
    | .refl h => .refl (eqe.eqe_mapRSqrt h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapRSqrt h₀) (rw_star_sub_mapRSqrt h₁)
  theorem rw_star_sub_mapExp {a b : kXSeq} : a.rw_star b →
      (mapExp a).rw_star (mapExp b)
    | .step h => .step (rw_one.sub_mapExp h)
    | .refl h => .refl (eqe.eqe_mapExp h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapExp h₀) (rw_star_sub_mapExp h₁)
  theorem rw_star_sub_mapExp2 {a b : kXSeq} : a.rw_star b →
      (mapExp2 a).rw_star (mapExp2 b)
    | .step h => .step (rw_one.sub_mapExp2 h)
    | .refl h => .refl (eqe.eqe_mapExp2 h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapExp2 h₀) (rw_star_sub_mapExp2 h₁)
  theorem rw_star_sub_mapLog {a b : kXSeq} : a.rw_star b →
      (mapLog a).rw_star (mapLog b)
    | .step h => .step (rw_one.sub_mapLog h)
    | .refl h => .refl (eqe.eqe_mapLog h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapLog h₀) (rw_star_sub_mapLog h₁)
  theorem rw_star_sub_mapLog2 {a b : kXSeq} : a.rw_star b →
      (mapLog2 a).rw_star (mapLog2 b)
    | .step h => .step (rw_one.sub_mapLog2 h)
    | .refl h => .refl (eqe.eqe_mapLog2 h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapLog2 h₀) (rw_star_sub_mapLog2 h₁)
  theorem rw_star_sub_mapLogOnePlus {a b : kXSeq} : a.rw_star b →
      (mapLogOnePlus a).rw_star (mapLogOnePlus b)
    | .step h => .step (rw_one.sub_mapLogOnePlus h)
    | .refl h => .refl (eqe.eqe_mapLogOnePlus h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapLogOnePlus h₀) (rw_star_sub_mapLogOnePlus h₁)
  theorem rw_star_sub_mapExpMinusOne {a b : kXSeq} : a.rw_star b →
      (mapExpMinusOne a).rw_star (mapExpMinusOne b)
    | .step h => .step (rw_one.sub_mapExpMinusOne h)
    | .refl h => .refl (eqe.eqe_mapExpMinusOne h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapExpMinusOne h₀) (rw_star_sub_mapExpMinusOne h₁)
  theorem rw_star_sub_mapSin {a b : kXSeq} : a.rw_star b →
      (mapSin a).rw_star (mapSin b)
    | .step h => .step (rw_one.sub_mapSin h)
    | .refl h => .refl (eqe.eqe_mapSin h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapSin h₀) (rw_star_sub_mapSin h₁)
  theorem rw_star_sub_mapCos {a b : kXSeq} : a.rw_star b →
      (mapCos a).rw_star (mapCos b)
    | .step h => .step (rw_one.sub_mapCos h)
    | .refl h => .refl (eqe.eqe_mapCos h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapCos h₀) (rw_star_sub_mapCos h₁)
  theorem rw_star_sub_mapTan {a b : kXSeq} : a.rw_star b →
      (mapTan a).rw_star (mapTan b)
    | .step h => .step (rw_one.sub_mapTan h)
    | .refl h => .refl (eqe.eqe_mapTan h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapTan h₀) (rw_star_sub_mapTan h₁)
  theorem rw_star_sub_mapArcSin {a b : kXSeq} : a.rw_star b →
      (mapArcSin a).rw_star (mapArcSin b)
    | .step h => .step (rw_one.sub_mapArcSin h)
    | .refl h => .refl (eqe.eqe_mapArcSin h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapArcSin h₀) (rw_star_sub_mapArcSin h₁)
  theorem rw_star_sub_mapArcCos {a b : kXSeq} : a.rw_star b →
      (mapArcCos a).rw_star (mapArcCos b)
    | .step h => .step (rw_one.sub_mapArcCos h)
    | .refl h => .refl (eqe.eqe_mapArcCos h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapArcCos h₀) (rw_star_sub_mapArcCos h₁)
  theorem rw_star_sub_mapArcTan {a b : kXSeq} : a.rw_star b →
      (mapArcTan a).rw_star (mapArcTan b)
    | .step h => .step (rw_one.sub_mapArcTan h)
    | .refl h => .refl (eqe.eqe_mapArcTan h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapArcTan h₀) (rw_star_sub_mapArcTan h₁)
  theorem rw_star_sub_mapSinh {a b : kXSeq} : a.rw_star b →
      (mapSinh a).rw_star (mapSinh b)
    | .step h => .step (rw_one.sub_mapSinh h)
    | .refl h => .refl (eqe.eqe_mapSinh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapSinh h₀) (rw_star_sub_mapSinh h₁)
  theorem rw_star_sub_mapCosh {a b : kXSeq} : a.rw_star b →
      (mapCosh a).rw_star (mapCosh b)
    | .step h => .step (rw_one.sub_mapCosh h)
    | .refl h => .refl (eqe.eqe_mapCosh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapCosh h₀) (rw_star_sub_mapCosh h₁)
  theorem rw_star_sub_mapTanh {a b : kXSeq} : a.rw_star b →
      (mapTanh a).rw_star (mapTanh b)
    | .step h => .step (rw_one.sub_mapTanh h)
    | .refl h => .refl (eqe.eqe_mapTanh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapTanh h₀) (rw_star_sub_mapTanh h₁)
  theorem rw_star_sub_mapArcSinh {a b : kXSeq} : a.rw_star b →
      (mapArcSinh a).rw_star (mapArcSinh b)
    | .step h => .step (rw_one.sub_mapArcSinh h)
    | .refl h => .refl (eqe.eqe_mapArcSinh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapArcSinh h₀) (rw_star_sub_mapArcSinh h₁)
  theorem rw_star_sub_mapArcCosh {a b : kXSeq} : a.rw_star b →
      (mapArcCosh a).rw_star (mapArcCosh b)
    | .step h => .step (rw_one.sub_mapArcCosh h)
    | .refl h => .refl (eqe.eqe_mapArcCosh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapArcCosh h₀) (rw_star_sub_mapArcCosh h₁)
  theorem rw_star_sub_mapArcTanh {a b : kXSeq} : a.rw_star b →
      (mapArcTanh a).rw_star (mapArcTanh b)
    | .step h => .step (rw_one.sub_mapArcTanh h)
    | .refl h => .refl (eqe.eqe_mapArcTanh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapArcTanh h₀) (rw_star_sub_mapArcTanh h₁)
  theorem rw_star_sub_mapSinPi {a b : kXSeq} : a.rw_star b →
      (mapSinPi a).rw_star (mapSinPi b)
    | .step h => .step (rw_one.sub_mapSinPi h)
    | .refl h => .refl (eqe.eqe_mapSinPi h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapSinPi h₀) (rw_star_sub_mapSinPi h₁)
  theorem rw_star_sub_mapCosPi {a b : kXSeq} : a.rw_star b →
      (mapCosPi a).rw_star (mapCosPi b)
    | .step h => .step (rw_one.sub_mapCosPi h)
    | .refl h => .refl (eqe.eqe_mapCosPi h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapCosPi h₀) (rw_star_sub_mapCosPi h₁)
  theorem rw_star_sub_mapTanPi {a b : kXSeq} : a.rw_star b →
      (mapTanPi a).rw_star (mapTanPi b)
    | .step h => .step (rw_one.sub_mapTanPi h)
    | .refl h => .refl (eqe.eqe_mapTanPi h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapTanPi h₀) (rw_star_sub_mapTanPi h₁)
  theorem rw_star_sub_mapArcSinPi {a b : kXSeq} : a.rw_star b →
      (mapArcSinPi a).rw_star (mapArcSinPi b)
    | .step h => .step (rw_one.sub_mapArcSinPi h)
    | .refl h => .refl (eqe.eqe_mapArcSinPi h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapArcSinPi h₀) (rw_star_sub_mapArcSinPi h₁)
  theorem rw_star_sub_mapArcCosPi {a b : kXSeq} : a.rw_star b →
      (mapArcCosPi a).rw_star (mapArcCosPi b)
    | .step h => .step (rw_one.sub_mapArcCosPi h)
    | .refl h => .refl (eqe.eqe_mapArcCosPi h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapArcCosPi h₀) (rw_star_sub_mapArcCosPi h₁)
  theorem rw_star_sub_mapArcTanPi {a b : kXSeq} : a.rw_star b →
      (mapArcTanPi a).rw_star (mapArcTanPi b)
    | .step h => .step (rw_one.sub_mapArcTanPi h)
    | .refl h => .refl (eqe.eqe_mapArcTanPi h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapArcTanPi h₀) (rw_star_sub_mapArcTanPi h₁)
  theorem rw_star_sub_mapSoftplus {a b : kXSeq} : a.rw_star b →
      (mapSoftplus a).rw_star (mapSoftplus b)
    | .step h => .step (rw_one.sub_mapSoftplus h)
    | .refl h => .refl (eqe.eqe_mapSoftplus h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapSoftplus h₀) (rw_star_sub_mapSoftplus h₁)
  theorem rw_star_sub_mapHypot₀ {a b a₁ : kXSeq} : a.rw_star b →
      (mapHypot a a₁).rw_star (mapHypot b a₁)
    | .step h => .step (rw_one.sub_mapHypot₀ h)
    | .refl h => .refl (eqe.eqe_mapHypot h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapHypot₀ h₀) (rw_star_sub_mapHypot₀ h₁)
  theorem rw_star_sub_mapHypot₁ {a₀ a b : kXSeq} : a.rw_star b →
      (mapHypot a₀ a).rw_star (mapHypot a₀ b)
    | .step h => .step (rw_one.sub_mapHypot₁ h)
    | .refl h => .refl (eqe.eqe_mapHypot (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapHypot₁ h₀) (rw_star_sub_mapHypot₁ h₁)
  theorem rw_star_sub_mapArcTan2₀ {a b a₁ : kXSeq} : a.rw_star b →
      (mapArcTan2 a a₁).rw_star (mapArcTan2 b a₁)
    | .step h => .step (rw_one.sub_mapArcTan2₀ h)
    | .refl h => .refl (eqe.eqe_mapArcTan2 h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapArcTan2₀ h₀) (rw_star_sub_mapArcTan2₀ h₁)
  theorem rw_star_sub_mapArcTan2₁ {a₀ a b : kXSeq} : a.rw_star b →
      (mapArcTan2 a₀ a).rw_star (mapArcTan2 a₀ b)
    | .step h => .step (rw_one.sub_mapArcTan2₁ h)
    | .refl h => .refl (eqe.eqe_mapArcTan2 (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapArcTan2₁ h₀) (rw_star_sub_mapArcTan2₁ h₁)
  theorem rw_star_sub_mapArcTan2Pi₀ {a b a₁ : kXSeq} : a.rw_star b →
      (mapArcTan2Pi a a₁).rw_star (mapArcTan2Pi b a₁)
    | .step h => .step (rw_one.sub_mapArcTan2Pi₀ h)
    | .refl h => .refl (eqe.eqe_mapArcTan2Pi h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mapArcTan2Pi₀ h₀) (rw_star_sub_mapArcTan2Pi₀ h₁)
  theorem rw_star_sub_mapArcTan2Pi₁ {a₀ a b : kXSeq} : a.rw_star b →
      (mapArcTan2Pi a₀ a).rw_star (mapArcTan2Pi a₀ b)
    | .step h => .step (rw_one.sub_mapArcTan2Pi₁ h)
    | .refl h => .refl (eqe.eqe_mapArcTan2Pi (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mapArcTan2Pi₁ h₀) (rw_star_sub_mapArcTan2Pi₁ h₁)
end kXSeq

namespace kCodeSeq
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kCodeSeq} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kCodeSeq} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kCodeSeq} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kCodeSeq} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_ccons₀ {a b : MRat} {a₁ : kCodeSeq} : MRat.rw_star a b →
      (ccons a a₁).rw_star (ccons b a₁)
    | .step h => .step (rw_one.sub_ccons₀ h)
    | .refl h => .refl (eqe.eqe_ccons h (kCodeSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_ccons₀ h₀) (rw_star_sub_ccons₀ h₁)
  theorem rw_star_sub_ccons₁ {a₀ : MRat} {a b : kCodeSeq} : a.rw_star b →
      (ccons a₀ a).rw_star (ccons a₀ b)
    | .step h => .step (rw_one.sub_ccons₁ h)
    | .refl h => .refl (eqe.eqe_ccons rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ccons₁ h₀) (rw_star_sub_ccons₁ h₁)
  theorem rw_star_sub_blockProject₀ {a b : MRat} {a₁ a₂ : kFormat} {a₃ : kBlockProjSpec} {a₄ : MRat} {a₅ : kXSeq} : MRat.rw_star a b →
      (blockProject a a₁ a₂ a₃ a₄ a₅).rw_star (blockProject b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_blockProject₀ h)
    | .refl h => .refl (eqe.eqe_blockProject h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kBlockProjSpec.eqe_refl a₃) rfl (kXSeq.eqe_refl a₅))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockProject₀ h₀) (rw_star_sub_blockProject₀ h₁)
  theorem rw_star_sub_blockProject₁ {a₀ : MRat} {a b a₂ : kFormat} {a₃ : kBlockProjSpec} {a₄ : MRat} {a₅ : kXSeq} : a.rw_star b →
      (blockProject a₀ a a₂ a₃ a₄ a₅).rw_star (blockProject a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_blockProject₁ h)
    | .refl h => .refl (eqe.eqe_blockProject rfl h (kFormat.eqe_refl a₂) (kBlockProjSpec.eqe_refl a₃) rfl (kXSeq.eqe_refl a₅))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockProject₁ h₀) (rw_star_sub_blockProject₁ h₁)
  theorem rw_star_sub_blockProject₂ {a₀ : MRat} {a₁ a b : kFormat} {a₃ : kBlockProjSpec} {a₄ : MRat} {a₅ : kXSeq} : a.rw_star b →
      (blockProject a₀ a₁ a a₃ a₄ a₅).rw_star (blockProject a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_blockProject₂ h)
    | .refl h => .refl (eqe.eqe_blockProject rfl (kFormat.eqe_refl a₁) h (kBlockProjSpec.eqe_refl a₃) rfl (kXSeq.eqe_refl a₅))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockProject₂ h₀) (rw_star_sub_blockProject₂ h₁)
  theorem rw_star_sub_blockProject₃ {a₀ : MRat} {a₁ a₂ : kFormat} {a b : kBlockProjSpec} {a₄ : MRat} {a₅ : kXSeq} : a.rw_star b →
      (blockProject a₀ a₁ a₂ a a₄ a₅).rw_star (blockProject a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_blockProject₃ h)
    | .refl h => .refl (eqe.eqe_blockProject rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl (kXSeq.eqe_refl a₅))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockProject₃ h₀) (rw_star_sub_blockProject₃ h₁)
  theorem rw_star_sub_blockProject₄ {a₀ : MRat} {a₁ a₂ : kFormat} {a₃ : kBlockProjSpec} {a b : MRat} {a₅ : kXSeq} : MRat.rw_star a b →
      (blockProject a₀ a₁ a₂ a₃ a a₅).rw_star (blockProject a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_blockProject₄ h)
    | .refl h => .refl (eqe.eqe_blockProject rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kBlockProjSpec.eqe_refl a₃) h (kXSeq.eqe_refl a₅))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockProject₄ h₀) (rw_star_sub_blockProject₄ h₁)
  theorem rw_star_sub_blockProject₅ {a₀ : MRat} {a₁ a₂ : kFormat} {a₃ : kBlockProjSpec} {a₄ : MRat} {a b : kXSeq} : a.rw_star b →
      (blockProject a₀ a₁ a₂ a₃ a₄ a).rw_star (blockProject a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_blockProject₅ h)
    | .refl h => .refl (eqe.eqe_blockProject rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kBlockProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_blockProject₅ h₀) (rw_star_sub_blockProject₅ h₁)
  theorem rw_star_sub_projectElements₀ {a b : kFormat} {a₁ : kBlockProjSpec} {a₂ : kXReal} {a₃ : kXSeq} {a₄ : MRat} : a.rw_star b →
      (projectElements a a₁ a₂ a₃ a₄).rw_star (projectElements b a₁ a₂ a₃ a₄)
    | .step h => .step (rw_one.sub_projectElements₀ h)
    | .refl h => .refl (eqe.eqe_projectElements h (kBlockProjSpec.eqe_refl a₁) (kXReal.eqe_refl a₂) (kXSeq.eqe_refl a₃) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_projectElements₀ h₀) (rw_star_sub_projectElements₀ h₁)
  theorem rw_star_sub_projectElements₁ {a₀ : kFormat} {a b : kBlockProjSpec} {a₂ : kXReal} {a₃ : kXSeq} {a₄ : MRat} : a.rw_star b →
      (projectElements a₀ a a₂ a₃ a₄).rw_star (projectElements a₀ b a₂ a₃ a₄)
    | .step h => .step (rw_one.sub_projectElements₁ h)
    | .refl h => .refl (eqe.eqe_projectElements (kFormat.eqe_refl a₀) h (kXReal.eqe_refl a₂) (kXSeq.eqe_refl a₃) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_projectElements₁ h₀) (rw_star_sub_projectElements₁ h₁)
  theorem rw_star_sub_projectElements₂ {a₀ : kFormat} {a₁ : kBlockProjSpec} {a b : kXReal} {a₃ : kXSeq} {a₄ : MRat} : a.rw_star b →
      (projectElements a₀ a₁ a a₃ a₄).rw_star (projectElements a₀ a₁ b a₃ a₄)
    | .step h => .step (rw_one.sub_projectElements₂ h)
    | .refl h => .refl (eqe.eqe_projectElements (kFormat.eqe_refl a₀) (kBlockProjSpec.eqe_refl a₁) h (kXSeq.eqe_refl a₃) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_projectElements₂ h₀) (rw_star_sub_projectElements₂ h₁)
  theorem rw_star_sub_projectElements₃ {a₀ : kFormat} {a₁ : kBlockProjSpec} {a₂ : kXReal} {a b : kXSeq} {a₄ : MRat} : a.rw_star b →
      (projectElements a₀ a₁ a₂ a a₄).rw_star (projectElements a₀ a₁ a₂ b a₄)
    | .step h => .step (rw_one.sub_projectElements₃ h)
    | .refl h => .refl (eqe.eqe_projectElements (kFormat.eqe_refl a₀) (kBlockProjSpec.eqe_refl a₁) (kXReal.eqe_refl a₂) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_projectElements₃ h₀) (rw_star_sub_projectElements₃ h₁)
  theorem rw_star_sub_projectElements₄ {a₀ : kFormat} {a₁ : kBlockProjSpec} {a₂ : kXReal} {a₃ : kXSeq} {a b : MRat} : MRat.rw_star a b →
      (projectElements a₀ a₁ a₂ a₃ a).rw_star (projectElements a₀ a₁ a₂ a₃ b)
    | .step h => .step (rw_one.sub_projectElements₄ h)
    | .refl h => .refl (eqe.eqe_projectElements (kFormat.eqe_refl a₀) (kBlockProjSpec.eqe_refl a₁) (kXReal.eqe_refl a₂) (kXSeq.eqe_refl a₃) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_projectElements₄ h₀) (rw_star_sub_projectElements₄ h₁)
  theorem rw_star_sub_projectUnscaled₀ {a b : kFormat} {a₁ : kBlockProjSpec} {a₂ : kXSeq} {a₃ : MRat} : a.rw_star b →
      (projectUnscaled a a₁ a₂ a₃).rw_star (projectUnscaled b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_projectUnscaled₀ h)
    | .refl h => .refl (eqe.eqe_projectUnscaled h (kBlockProjSpec.eqe_refl a₁) (kXSeq.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_projectUnscaled₀ h₀) (rw_star_sub_projectUnscaled₀ h₁)
  theorem rw_star_sub_projectUnscaled₁ {a₀ : kFormat} {a b : kBlockProjSpec} {a₂ : kXSeq} {a₃ : MRat} : a.rw_star b →
      (projectUnscaled a₀ a a₂ a₃).rw_star (projectUnscaled a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_projectUnscaled₁ h)
    | .refl h => .refl (eqe.eqe_projectUnscaled (kFormat.eqe_refl a₀) h (kXSeq.eqe_refl a₂) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_projectUnscaled₁ h₀) (rw_star_sub_projectUnscaled₁ h₁)
  theorem rw_star_sub_projectUnscaled₂ {a₀ : kFormat} {a₁ : kBlockProjSpec} {a b : kXSeq} {a₃ : MRat} : a.rw_star b →
      (projectUnscaled a₀ a₁ a a₃).rw_star (projectUnscaled a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_projectUnscaled₂ h)
    | .refl h => .refl (eqe.eqe_projectUnscaled (kFormat.eqe_refl a₀) (kBlockProjSpec.eqe_refl a₁) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_projectUnscaled₂ h₀) (rw_star_sub_projectUnscaled₂ h₁)
  theorem rw_star_sub_projectUnscaled₃ {a₀ : kFormat} {a₁ : kBlockProjSpec} {a₂ : kXSeq} {a b : MRat} : MRat.rw_star a b →
      (projectUnscaled a₀ a₁ a₂ a).rw_star (projectUnscaled a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_projectUnscaled₃ h)
    | .refl h => .refl (eqe.eqe_projectUnscaled (kFormat.eqe_refl a₀) (kBlockProjSpec.eqe_refl a₁) (kXSeq.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_projectUnscaled₃ h₀) (rw_star_sub_projectUnscaled₃ h₁)
  theorem rw_star_sub_at₀ {a b : kPartitionSeq} {a₁ : MRat} : a.rw_star b →
      («at» a a₁).rw_star («at» b a₁)
    | .step h => .step (rw_one.sub_at₀ h)
    | .refl h => .refl (eqe.eqe_at h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₀ h₀) (rw_star_sub_at₀ h₁)
  theorem rw_star_sub_at₁ {a₀ : kPartitionSeq} {a b : MRat} : MRat.rw_star a b →
      («at» a₀ a).rw_star («at» a₀ b)
    | .step h => .step (rw_one.sub_at₁ h)
    | .refl h => .refl (eqe.eqe_at (kPartitionSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₁ h₀) (rw_star_sub_at₁ h₁)
  theorem rw_star_sub_partitionUnion {a b : kPartitionSeq} : a.rw_star b →
      (partitionUnion a).rw_star (partitionUnion b)
    | .step h => .step (rw_one.sub_partitionUnion h)
    | .refl h => .refl (eqe.eqe_partitionUnion h)
    | .trans h₀ h₁ => .trans (rw_star_sub_partitionUnion h₀) (rw_star_sub_partitionUnion h₁)
  theorem rw_star_sub_appendCodes₀ {a b a₁ : kCodeSeq} : a.rw_star b →
      (appendCodes a a₁).rw_star (appendCodes b a₁)
    | .step h => .step (rw_one.sub_appendCodes₀ h)
    | .refl h => .refl (eqe.eqe_appendCodes h (kCodeSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_appendCodes₀ h₀) (rw_star_sub_appendCodes₀ h₁)
  theorem rw_star_sub_appendCodes₁ {a₀ a b : kCodeSeq} : a.rw_star b →
      (appendCodes a₀ a).rw_star (appendCodes a₀ b)
    | .step h => .step (rw_one.sub_appendCodes₁ h)
    | .refl h => .refl (eqe.eqe_appendCodes (kCodeSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_appendCodes₁ h₀) (rw_star_sub_appendCodes₁ h₁)
  theorem rw_star_sub_ConvertFromBlock₀ {a b : MRat} {a₁ a₂ a₃ : kFormat} {a₄ : kBlockProjSpec} {a₅ : MRat} {a₆ : kCodeSeq} : MRat.rw_star a b →
      (ConvertFromBlock a a₁ a₂ a₃ a₄ a₅ a₆).rw_star (ConvertFromBlock b a₁ a₂ a₃ a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_ConvertFromBlock₀ h)
    | .refl h => .refl (eqe.eqe_ConvertFromBlock h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kBlockProjSpec.eqe_refl a₄) rfl (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertFromBlock₀ h₀) (rw_star_sub_ConvertFromBlock₀ h₁)
  theorem rw_star_sub_ConvertFromBlock₁ {a₀ : MRat} {a b a₂ a₃ : kFormat} {a₄ : kBlockProjSpec} {a₅ : MRat} {a₆ : kCodeSeq} : a.rw_star b →
      (ConvertFromBlock a₀ a a₂ a₃ a₄ a₅ a₆).rw_star (ConvertFromBlock a₀ b a₂ a₃ a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_ConvertFromBlock₁ h)
    | .refl h => .refl (eqe.eqe_ConvertFromBlock rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kBlockProjSpec.eqe_refl a₄) rfl (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertFromBlock₁ h₀) (rw_star_sub_ConvertFromBlock₁ h₁)
  theorem rw_star_sub_ConvertFromBlock₂ {a₀ : MRat} {a₁ a b a₃ : kFormat} {a₄ : kBlockProjSpec} {a₅ : MRat} {a₆ : kCodeSeq} : a.rw_star b →
      (ConvertFromBlock a₀ a₁ a a₃ a₄ a₅ a₆).rw_star (ConvertFromBlock a₀ a₁ b a₃ a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_ConvertFromBlock₂ h)
    | .refl h => .refl (eqe.eqe_ConvertFromBlock rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kBlockProjSpec.eqe_refl a₄) rfl (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertFromBlock₂ h₀) (rw_star_sub_ConvertFromBlock₂ h₁)
  theorem rw_star_sub_ConvertFromBlock₃ {a₀ : MRat} {a₁ a₂ a b : kFormat} {a₄ : kBlockProjSpec} {a₅ : MRat} {a₆ : kCodeSeq} : a.rw_star b →
      (ConvertFromBlock a₀ a₁ a₂ a a₄ a₅ a₆).rw_star (ConvertFromBlock a₀ a₁ a₂ b a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_ConvertFromBlock₃ h)
    | .refl h => .refl (eqe.eqe_ConvertFromBlock rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kBlockProjSpec.eqe_refl a₄) rfl (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertFromBlock₃ h₀) (rw_star_sub_ConvertFromBlock₃ h₁)
  theorem rw_star_sub_ConvertFromBlock₄ {a₀ : MRat} {a₁ a₂ a₃ : kFormat} {a b : kBlockProjSpec} {a₅ : MRat} {a₆ : kCodeSeq} : a.rw_star b →
      (ConvertFromBlock a₀ a₁ a₂ a₃ a a₅ a₆).rw_star (ConvertFromBlock a₀ a₁ a₂ a₃ b a₅ a₆)
    | .step h => .step (rw_one.sub_ConvertFromBlock₄ h)
    | .refl h => .refl (eqe.eqe_ConvertFromBlock rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h rfl (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertFromBlock₄ h₀) (rw_star_sub_ConvertFromBlock₄ h₁)
  theorem rw_star_sub_ConvertFromBlock₅ {a₀ : MRat} {a₁ a₂ a₃ : kFormat} {a₄ : kBlockProjSpec} {a b : MRat} {a₆ : kCodeSeq} : MRat.rw_star a b →
      (ConvertFromBlock a₀ a₁ a₂ a₃ a₄ a a₆).rw_star (ConvertFromBlock a₀ a₁ a₂ a₃ a₄ b a₆)
    | .step h => .step (rw_one.sub_ConvertFromBlock₅ h)
    | .refl h => .refl (eqe.eqe_ConvertFromBlock rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kBlockProjSpec.eqe_refl a₄) h (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertFromBlock₅ h₀) (rw_star_sub_ConvertFromBlock₅ h₁)
  theorem rw_star_sub_ConvertFromBlock₆ {a₀ : MRat} {a₁ a₂ a₃ : kFormat} {a₄ : kBlockProjSpec} {a₅ : MRat} {a b : kCodeSeq} : a.rw_star b →
      (ConvertFromBlock a₀ a₁ a₂ a₃ a₄ a₅ a).rw_star (ConvertFromBlock a₀ a₁ a₂ a₃ a₄ a₅ b)
    | .step h => .step (rw_one.sub_ConvertFromBlock₆ h)
    | .refl h => .refl (eqe.eqe_ConvertFromBlock rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kBlockProjSpec.eqe_refl a₄) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertFromBlock₆ h₀) (rw_star_sub_ConvertFromBlock₆ h₁)
  theorem rw_star_sub_ConvertToBlock₀ {a b : MRat} {a₁ a₂ a₃ : kFormat} {a₄ : kBlockProjSpec} {a₅ : kCodeSeq} {a₆ : MRat} : MRat.rw_star a b →
      (ConvertToBlock a a₁ a₂ a₃ a₄ a₅ a₆).rw_star (ConvertToBlock b a₁ a₂ a₃ a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_ConvertToBlock₀ h)
    | .refl h => .refl (eqe.eqe_ConvertToBlock h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kBlockProjSpec.eqe_refl a₄) (kCodeSeq.eqe_refl a₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertToBlock₀ h₀) (rw_star_sub_ConvertToBlock₀ h₁)
  theorem rw_star_sub_ConvertToBlock₁ {a₀ : MRat} {a b a₂ a₃ : kFormat} {a₄ : kBlockProjSpec} {a₅ : kCodeSeq} {a₆ : MRat} : a.rw_star b →
      (ConvertToBlock a₀ a a₂ a₃ a₄ a₅ a₆).rw_star (ConvertToBlock a₀ b a₂ a₃ a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_ConvertToBlock₁ h)
    | .refl h => .refl (eqe.eqe_ConvertToBlock rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kBlockProjSpec.eqe_refl a₄) (kCodeSeq.eqe_refl a₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertToBlock₁ h₀) (rw_star_sub_ConvertToBlock₁ h₁)
  theorem rw_star_sub_ConvertToBlock₂ {a₀ : MRat} {a₁ a b a₃ : kFormat} {a₄ : kBlockProjSpec} {a₅ : kCodeSeq} {a₆ : MRat} : a.rw_star b →
      (ConvertToBlock a₀ a₁ a a₃ a₄ a₅ a₆).rw_star (ConvertToBlock a₀ a₁ b a₃ a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_ConvertToBlock₂ h)
    | .refl h => .refl (eqe.eqe_ConvertToBlock rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kBlockProjSpec.eqe_refl a₄) (kCodeSeq.eqe_refl a₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertToBlock₂ h₀) (rw_star_sub_ConvertToBlock₂ h₁)
  theorem rw_star_sub_ConvertToBlock₃ {a₀ : MRat} {a₁ a₂ a b : kFormat} {a₄ : kBlockProjSpec} {a₅ : kCodeSeq} {a₆ : MRat} : a.rw_star b →
      (ConvertToBlock a₀ a₁ a₂ a a₄ a₅ a₆).rw_star (ConvertToBlock a₀ a₁ a₂ b a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_ConvertToBlock₃ h)
    | .refl h => .refl (eqe.eqe_ConvertToBlock rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kBlockProjSpec.eqe_refl a₄) (kCodeSeq.eqe_refl a₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertToBlock₃ h₀) (rw_star_sub_ConvertToBlock₃ h₁)
  theorem rw_star_sub_ConvertToBlock₄ {a₀ : MRat} {a₁ a₂ a₃ : kFormat} {a b : kBlockProjSpec} {a₅ : kCodeSeq} {a₆ : MRat} : a.rw_star b →
      (ConvertToBlock a₀ a₁ a₂ a₃ a a₅ a₆).rw_star (ConvertToBlock a₀ a₁ a₂ a₃ b a₅ a₆)
    | .step h => .step (rw_one.sub_ConvertToBlock₄ h)
    | .refl h => .refl (eqe.eqe_ConvertToBlock rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kCodeSeq.eqe_refl a₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertToBlock₄ h₀) (rw_star_sub_ConvertToBlock₄ h₁)
  theorem rw_star_sub_ConvertToBlock₅ {a₀ : MRat} {a₁ a₂ a₃ : kFormat} {a₄ : kBlockProjSpec} {a b : kCodeSeq} {a₆ : MRat} : a.rw_star b →
      (ConvertToBlock a₀ a₁ a₂ a₃ a₄ a a₆).rw_star (ConvertToBlock a₀ a₁ a₂ a₃ a₄ b a₆)
    | .step h => .step (rw_one.sub_ConvertToBlock₅ h)
    | .refl h => .refl (eqe.eqe_ConvertToBlock rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kBlockProjSpec.eqe_refl a₄) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertToBlock₅ h₀) (rw_star_sub_ConvertToBlock₅ h₁)
  theorem rw_star_sub_ConvertToBlock₆ {a₀ : MRat} {a₁ a₂ a₃ : kFormat} {a₄ : kBlockProjSpec} {a₅ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (ConvertToBlock a₀ a₁ a₂ a₃ a₄ a₅ a).rw_star (ConvertToBlock a₀ a₁ a₂ a₃ a₄ a₅ b)
    | .step h => .step (rw_one.sub_ConvertToBlock₆ h)
    | .refl h => .refl (eqe.eqe_ConvertToBlock rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kBlockProjSpec.eqe_refl a₄) (kCodeSeq.eqe_refl a₅) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertToBlock₆ h₀) (rw_star_sub_ConvertToBlock₆ h₁)
end kCodeSeq

end Maude
