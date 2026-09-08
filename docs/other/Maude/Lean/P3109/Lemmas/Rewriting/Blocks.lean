-- Extracted from ../spec2.lean, lines 12928-15842.
-- See PLAN.md and manifest.json for provenance.
import P3109.Lemmas.Rewriting.Sequences

namespace Maude
namespace kBlock
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kBlock} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kBlock} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kBlock} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kBlock} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_block₀ {a b : MRat} {a₁ : kCodeSeq} : MRat.rw_star a b →
      (block a a₁).rw_star (block b a₁)
    | .step h => .step (rw_one.sub_block₀ h)
    | .refl h => .refl (eqe.eqe_block h (kCodeSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_block₀ h₀) (rw_star_sub_block₀ h₁)
  theorem rw_star_sub_block₁ {a₀ : MRat} {a b : kCodeSeq} : a.rw_star b →
      (block a₀ a).rw_star (block a₀ b)
    | .step h => .step (rw_one.sub_block₁ h)
    | .refl h => .refl (eqe.eqe_block rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_block₁ h₀) (rw_star_sub_block₁ h₁)
  theorem rw_star_sub_ConvertToBlockMaxAbsFinite₀ {a b : MRat} {a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ : kBlockProjSpec} {a₆ : kCodeSeq} : MRat.rw_star a b →
      (ConvertToBlockMaxAbsFinite a a₁ a₂ a₃ a₄ a₅ a₆).rw_star (ConvertToBlockMaxAbsFinite b a₁ a₂ a₃ a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_ConvertToBlockMaxAbsFinite₀ h)
    | .refl h => .refl (eqe.eqe_ConvertToBlockMaxAbsFinite h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertToBlockMaxAbsFinite₀ h₀) (rw_star_sub_ConvertToBlockMaxAbsFinite₀ h₁)
  theorem rw_star_sub_ConvertToBlockMaxAbsFinite₁ {a₀ : MRat} {a b a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ : kBlockProjSpec} {a₆ : kCodeSeq} : a.rw_star b →
      (ConvertToBlockMaxAbsFinite a₀ a a₂ a₃ a₄ a₅ a₆).rw_star (ConvertToBlockMaxAbsFinite a₀ b a₂ a₃ a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_ConvertToBlockMaxAbsFinite₁ h)
    | .refl h => .refl (eqe.eqe_ConvertToBlockMaxAbsFinite rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertToBlockMaxAbsFinite₁ h₀) (rw_star_sub_ConvertToBlockMaxAbsFinite₁ h₁)
  theorem rw_star_sub_ConvertToBlockMaxAbsFinite₂ {a₀ : MRat} {a₁ a b a₃ : kFormat} {a₄ : kProjSpec} {a₅ : kBlockProjSpec} {a₆ : kCodeSeq} : a.rw_star b →
      (ConvertToBlockMaxAbsFinite a₀ a₁ a a₃ a₄ a₅ a₆).rw_star (ConvertToBlockMaxAbsFinite a₀ a₁ b a₃ a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_ConvertToBlockMaxAbsFinite₂ h)
    | .refl h => .refl (eqe.eqe_ConvertToBlockMaxAbsFinite rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertToBlockMaxAbsFinite₂ h₀) (rw_star_sub_ConvertToBlockMaxAbsFinite₂ h₁)
  theorem rw_star_sub_ConvertToBlockMaxAbsFinite₃ {a₀ : MRat} {a₁ a₂ a b : kFormat} {a₄ : kProjSpec} {a₅ : kBlockProjSpec} {a₆ : kCodeSeq} : a.rw_star b →
      (ConvertToBlockMaxAbsFinite a₀ a₁ a₂ a a₄ a₅ a₆).rw_star (ConvertToBlockMaxAbsFinite a₀ a₁ a₂ b a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_ConvertToBlockMaxAbsFinite₃ h)
    | .refl h => .refl (eqe.eqe_ConvertToBlockMaxAbsFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kProjSpec.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertToBlockMaxAbsFinite₃ h₀) (rw_star_sub_ConvertToBlockMaxAbsFinite₃ h₁)
  theorem rw_star_sub_ConvertToBlockMaxAbsFinite₄ {a₀ : MRat} {a₁ a₂ a₃ : kFormat} {a b : kProjSpec} {a₅ : kBlockProjSpec} {a₆ : kCodeSeq} : a.rw_star b →
      (ConvertToBlockMaxAbsFinite a₀ a₁ a₂ a₃ a a₅ a₆).rw_star (ConvertToBlockMaxAbsFinite a₀ a₁ a₂ a₃ b a₅ a₆)
    | .step h => .step (rw_one.sub_ConvertToBlockMaxAbsFinite₄ h)
    | .refl h => .refl (eqe.eqe_ConvertToBlockMaxAbsFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertToBlockMaxAbsFinite₄ h₀) (rw_star_sub_ConvertToBlockMaxAbsFinite₄ h₁)
  theorem rw_star_sub_ConvertToBlockMaxAbsFinite₅ {a₀ : MRat} {a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a b : kBlockProjSpec} {a₆ : kCodeSeq} : a.rw_star b →
      (ConvertToBlockMaxAbsFinite a₀ a₁ a₂ a₃ a₄ a a₆).rw_star (ConvertToBlockMaxAbsFinite a₀ a₁ a₂ a₃ a₄ b a₆)
    | .step h => .step (rw_one.sub_ConvertToBlockMaxAbsFinite₅ h)
    | .refl h => .refl (eqe.eqe_ConvertToBlockMaxAbsFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) h (kCodeSeq.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertToBlockMaxAbsFinite₅ h₀) (rw_star_sub_ConvertToBlockMaxAbsFinite₅ h₁)
  theorem rw_star_sub_ConvertToBlockMaxAbsFinite₆ {a₀ : MRat} {a₁ a₂ a₃ : kFormat} {a₄ : kProjSpec} {a₅ : kBlockProjSpec} {a b : kCodeSeq} : a.rw_star b →
      (ConvertToBlockMaxAbsFinite a₀ a₁ a₂ a₃ a₄ a₅ a).rw_star (ConvertToBlockMaxAbsFinite a₀ a₁ a₂ a₃ a₄ a₅ b)
    | .step h => .step (rw_one.sub_ConvertToBlockMaxAbsFinite₆ h)
    | .refl h => .refl (eqe.eqe_ConvertToBlockMaxAbsFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kProjSpec.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ConvertToBlockMaxAbsFinite₆ h₀) (rw_star_sub_ConvertToBlockMaxAbsFinite₆ h₁)
  theorem rw_star_sub_computedBlock₀ {a b : MRat} {a₁ a₂ : kFormat} {a₃ : kBlockProjSpec} {a₄ : MRat} {a₅ : kXSeq} : MRat.rw_star a b →
      (computedBlock a a₁ a₂ a₃ a₄ a₅).rw_star (computedBlock b a₁ a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_computedBlock₀ h)
    | .refl h => .refl (eqe.eqe_computedBlock h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kBlockProjSpec.eqe_refl a₃) rfl (kXSeq.eqe_refl a₅))
    | .trans h₀ h₁ => .trans (rw_star_sub_computedBlock₀ h₀) (rw_star_sub_computedBlock₀ h₁)
  theorem rw_star_sub_computedBlock₁ {a₀ : MRat} {a b a₂ : kFormat} {a₃ : kBlockProjSpec} {a₄ : MRat} {a₅ : kXSeq} : a.rw_star b →
      (computedBlock a₀ a a₂ a₃ a₄ a₅).rw_star (computedBlock a₀ b a₂ a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_computedBlock₁ h)
    | .refl h => .refl (eqe.eqe_computedBlock rfl h (kFormat.eqe_refl a₂) (kBlockProjSpec.eqe_refl a₃) rfl (kXSeq.eqe_refl a₅))
    | .trans h₀ h₁ => .trans (rw_star_sub_computedBlock₁ h₀) (rw_star_sub_computedBlock₁ h₁)
  theorem rw_star_sub_computedBlock₂ {a₀ : MRat} {a₁ a b : kFormat} {a₃ : kBlockProjSpec} {a₄ : MRat} {a₅ : kXSeq} : a.rw_star b →
      (computedBlock a₀ a₁ a a₃ a₄ a₅).rw_star (computedBlock a₀ a₁ b a₃ a₄ a₅)
    | .step h => .step (rw_one.sub_computedBlock₂ h)
    | .refl h => .refl (eqe.eqe_computedBlock rfl (kFormat.eqe_refl a₁) h (kBlockProjSpec.eqe_refl a₃) rfl (kXSeq.eqe_refl a₅))
    | .trans h₀ h₁ => .trans (rw_star_sub_computedBlock₂ h₀) (rw_star_sub_computedBlock₂ h₁)
  theorem rw_star_sub_computedBlock₃ {a₀ : MRat} {a₁ a₂ : kFormat} {a b : kBlockProjSpec} {a₄ : MRat} {a₅ : kXSeq} : a.rw_star b →
      (computedBlock a₀ a₁ a₂ a a₄ a₅).rw_star (computedBlock a₀ a₁ a₂ b a₄ a₅)
    | .step h => .step (rw_one.sub_computedBlock₃ h)
    | .refl h => .refl (eqe.eqe_computedBlock rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl (kXSeq.eqe_refl a₅))
    | .trans h₀ h₁ => .trans (rw_star_sub_computedBlock₃ h₀) (rw_star_sub_computedBlock₃ h₁)
  theorem rw_star_sub_computedBlock₄ {a₀ : MRat} {a₁ a₂ : kFormat} {a₃ : kBlockProjSpec} {a b : MRat} {a₅ : kXSeq} : MRat.rw_star a b →
      (computedBlock a₀ a₁ a₂ a₃ a a₅).rw_star (computedBlock a₀ a₁ a₂ a₃ b a₅)
    | .step h => .step (rw_one.sub_computedBlock₄ h)
    | .refl h => .refl (eqe.eqe_computedBlock rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kBlockProjSpec.eqe_refl a₃) h (kXSeq.eqe_refl a₅))
    | .trans h₀ h₁ => .trans (rw_star_sub_computedBlock₄ h₀) (rw_star_sub_computedBlock₄ h₁)
  theorem rw_star_sub_computedBlock₅ {a₀ : MRat} {a₁ a₂ : kFormat} {a₃ : kBlockProjSpec} {a₄ : MRat} {a b : kXSeq} : a.rw_star b →
      (computedBlock a₀ a₁ a₂ a₃ a₄ a).rw_star (computedBlock a₀ a₁ a₂ a₃ a₄ b)
    | .step h => .step (rw_one.sub_computedBlock₅ h)
    | .refl h => .refl (eqe.eqe_computedBlock rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kBlockProjSpec.eqe_refl a₃) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_computedBlock₅ h₀) (rw_star_sub_computedBlock₅ h₁)
  theorem rw_star_sub_BlockConvert₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockConvert a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockConvert b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockConvert₀ h)
    | .refl h => .refl (eqe.eqe_BlockConvert h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockConvert₀ h₀) (rw_star_sub_BlockConvert₀ h₁)
  theorem rw_star_sub_BlockConvert₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockConvert a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockConvert a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockConvert₁ h)
    | .refl h => .refl (eqe.eqe_BlockConvert rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockConvert₁ h₀) (rw_star_sub_BlockConvert₁ h₁)
  theorem rw_star_sub_BlockConvert₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockConvert a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockConvert a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockConvert₂ h)
    | .refl h => .refl (eqe.eqe_BlockConvert rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockConvert₂ h₀) (rw_star_sub_BlockConvert₂ h₁)
  theorem rw_star_sub_BlockConvert₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockConvert a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockConvert a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockConvert₃ h)
    | .refl h => .refl (eqe.eqe_BlockConvert rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockConvert₃ h₀) (rw_star_sub_BlockConvert₃ h₁)
  theorem rw_star_sub_BlockConvert₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockConvert a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockConvert a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockConvert₄ h)
    | .refl h => .refl (eqe.eqe_BlockConvert rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockConvert₄ h₀) (rw_star_sub_BlockConvert₄ h₁)
  theorem rw_star_sub_BlockConvert₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockConvert a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockConvert a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockConvert₅ h)
    | .refl h => .refl (eqe.eqe_BlockConvert rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockConvert₅ h₀) (rw_star_sub_BlockConvert₅ h₁)
  theorem rw_star_sub_BlockConvert₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockConvert a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockConvert a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockConvert₆ h)
    | .refl h => .refl (eqe.eqe_BlockConvert rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockConvert₆ h₀) (rw_star_sub_BlockConvert₆ h₁)
  theorem rw_star_sub_BlockConvert₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockConvert a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockConvert a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockConvert₇ h)
    | .refl h => .refl (eqe.eqe_BlockConvert rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockConvert₇ h₀) (rw_star_sub_BlockConvert₇ h₁)
  theorem rw_star_sub_BlockConvert₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockConvert a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockConvert a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockConvert₈ h)
    | .refl h => .refl (eqe.eqe_BlockConvert rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockConvert₈ h₀) (rw_star_sub_BlockConvert₈ h₁)
  theorem rw_star_sub_BlockAbs₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockAbs a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockAbs b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockAbs₀ h)
    | .refl h => .refl (eqe.eqe_BlockAbs h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAbs₀ h₀) (rw_star_sub_BlockAbs₀ h₁)
  theorem rw_star_sub_BlockAbs₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockAbs a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockAbs a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockAbs₁ h)
    | .refl h => .refl (eqe.eqe_BlockAbs rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAbs₁ h₀) (rw_star_sub_BlockAbs₁ h₁)
  theorem rw_star_sub_BlockAbs₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockAbs a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockAbs a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockAbs₂ h)
    | .refl h => .refl (eqe.eqe_BlockAbs rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAbs₂ h₀) (rw_star_sub_BlockAbs₂ h₁)
  theorem rw_star_sub_BlockAbs₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockAbs a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockAbs a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockAbs₃ h)
    | .refl h => .refl (eqe.eqe_BlockAbs rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAbs₃ h₀) (rw_star_sub_BlockAbs₃ h₁)
  theorem rw_star_sub_BlockAbs₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockAbs a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockAbs a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockAbs₄ h)
    | .refl h => .refl (eqe.eqe_BlockAbs rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAbs₄ h₀) (rw_star_sub_BlockAbs₄ h₁)
  theorem rw_star_sub_BlockAbs₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockAbs a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockAbs a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockAbs₅ h)
    | .refl h => .refl (eqe.eqe_BlockAbs rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAbs₅ h₀) (rw_star_sub_BlockAbs₅ h₁)
  theorem rw_star_sub_BlockAbs₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockAbs a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockAbs a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockAbs₆ h)
    | .refl h => .refl (eqe.eqe_BlockAbs rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAbs₆ h₀) (rw_star_sub_BlockAbs₆ h₁)
  theorem rw_star_sub_BlockAbs₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockAbs a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockAbs a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockAbs₇ h)
    | .refl h => .refl (eqe.eqe_BlockAbs rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAbs₇ h₀) (rw_star_sub_BlockAbs₇ h₁)
  theorem rw_star_sub_BlockAbs₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockAbs a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockAbs a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockAbs₈ h)
    | .refl h => .refl (eqe.eqe_BlockAbs rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAbs₈ h₀) (rw_star_sub_BlockAbs₈ h₁)
  theorem rw_star_sub_BlockNegate₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockNegate a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockNegate b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockNegate₀ h)
    | .refl h => .refl (eqe.eqe_BlockNegate h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockNegate₀ h₀) (rw_star_sub_BlockNegate₀ h₁)
  theorem rw_star_sub_BlockNegate₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockNegate a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockNegate a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockNegate₁ h)
    | .refl h => .refl (eqe.eqe_BlockNegate rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockNegate₁ h₀) (rw_star_sub_BlockNegate₁ h₁)
  theorem rw_star_sub_BlockNegate₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockNegate a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockNegate a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockNegate₂ h)
    | .refl h => .refl (eqe.eqe_BlockNegate rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockNegate₂ h₀) (rw_star_sub_BlockNegate₂ h₁)
  theorem rw_star_sub_BlockNegate₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockNegate a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockNegate a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockNegate₃ h)
    | .refl h => .refl (eqe.eqe_BlockNegate rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockNegate₃ h₀) (rw_star_sub_BlockNegate₃ h₁)
  theorem rw_star_sub_BlockNegate₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockNegate a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockNegate a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockNegate₄ h)
    | .refl h => .refl (eqe.eqe_BlockNegate rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockNegate₄ h₀) (rw_star_sub_BlockNegate₄ h₁)
  theorem rw_star_sub_BlockNegate₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockNegate a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockNegate a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockNegate₅ h)
    | .refl h => .refl (eqe.eqe_BlockNegate rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockNegate₅ h₀) (rw_star_sub_BlockNegate₅ h₁)
  theorem rw_star_sub_BlockNegate₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockNegate a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockNegate a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockNegate₆ h)
    | .refl h => .refl (eqe.eqe_BlockNegate rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockNegate₆ h₀) (rw_star_sub_BlockNegate₆ h₁)
  theorem rw_star_sub_BlockNegate₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockNegate a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockNegate a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockNegate₇ h)
    | .refl h => .refl (eqe.eqe_BlockNegate rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockNegate₇ h₀) (rw_star_sub_BlockNegate₇ h₁)
  theorem rw_star_sub_BlockNegate₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockNegate a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockNegate a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockNegate₈ h)
    | .refl h => .refl (eqe.eqe_BlockNegate rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockNegate₈ h₀) (rw_star_sub_BlockNegate₈ h₁)
  theorem rw_star_sub_BlockCopySign₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockCopySign a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockCopySign b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockCopySign₀ h)
    | .refl h => .refl (eqe.eqe_BlockCopySign h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCopySign₀ h₀) (rw_star_sub_BlockCopySign₀ h₁)
  theorem rw_star_sub_BlockCopySign₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockCopySign a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockCopySign a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockCopySign₁ h)
    | .refl h => .refl (eqe.eqe_BlockCopySign rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCopySign₁ h₀) (rw_star_sub_BlockCopySign₁ h₁)
  theorem rw_star_sub_BlockCopySign₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockCopySign a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockCopySign a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockCopySign₂ h)
    | .refl h => .refl (eqe.eqe_BlockCopySign rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCopySign₂ h₀) (rw_star_sub_BlockCopySign₂ h₁)
  theorem rw_star_sub_BlockCopySign₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockCopySign a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockCopySign a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockCopySign₃ h)
    | .refl h => .refl (eqe.eqe_BlockCopySign rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCopySign₃ h₀) (rw_star_sub_BlockCopySign₃ h₁)
  theorem rw_star_sub_BlockCopySign₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockCopySign a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockCopySign a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockCopySign₄ h)
    | .refl h => .refl (eqe.eqe_BlockCopySign rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCopySign₄ h₀) (rw_star_sub_BlockCopySign₄ h₁)
  theorem rw_star_sub_BlockCopySign₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockCopySign a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockCopySign a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockCopySign₅ h)
    | .refl h => .refl (eqe.eqe_BlockCopySign rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCopySign₅ h₀) (rw_star_sub_BlockCopySign₅ h₁)
  theorem rw_star_sub_BlockCopySign₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockCopySign₆ h)
    | .refl h => .refl (eqe.eqe_BlockCopySign rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCopySign₆ h₀) (rw_star_sub_BlockCopySign₆ h₁)
  theorem rw_star_sub_BlockCopySign₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockCopySign₇ h)
    | .refl h => .refl (eqe.eqe_BlockCopySign rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCopySign₇ h₀) (rw_star_sub_BlockCopySign₇ h₁)
  theorem rw_star_sub_BlockCopySign₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a b : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockCopySign₈ h)
    | .refl h => .refl (eqe.eqe_BlockCopySign rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) h (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCopySign₈ h₀) (rw_star_sub_BlockCopySign₈ h₁)
  theorem rw_star_sub_BlockCopySign₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a b : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂).rw_star (BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockCopySign₉ h)
    | .refl h => .refl (eqe.eqe_BlockCopySign rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl h rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCopySign₉ h₀) (rw_star_sub_BlockCopySign₉ h₁)
  theorem rw_star_sub_BlockCopySign₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂).rw_star (BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockCopySign₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockCopySign rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCopySign₁₀ h₀) (rw_star_sub_BlockCopySign₁₀ h₁)
  theorem rw_star_sub_BlockCopySign₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂).rw_star (BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | .step h => .step (rw_one.sub_BlockCopySign₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockCopySign rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCopySign₁₁ h₀) (rw_star_sub_BlockCopySign₁₁ h₁)
  theorem rw_star_sub_BlockCopySign₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a).rw_star (BlockCopySign a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | .step h => .step (rw_one.sub_BlockCopySign₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockCopySign rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCopySign₁₂ h₀) (rw_star_sub_BlockCopySign₁₂ h₁)
  theorem rw_star_sub_BlockAdd₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockAdd a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockAdd b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockAdd₀ h)
    | .refl h => .refl (eqe.eqe_BlockAdd h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAdd₀ h₀) (rw_star_sub_BlockAdd₀ h₁)
  theorem rw_star_sub_BlockAdd₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockAdd a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockAdd a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockAdd₁ h)
    | .refl h => .refl (eqe.eqe_BlockAdd rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAdd₁ h₀) (rw_star_sub_BlockAdd₁ h₁)
  theorem rw_star_sub_BlockAdd₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockAdd a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockAdd a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockAdd₂ h)
    | .refl h => .refl (eqe.eqe_BlockAdd rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAdd₂ h₀) (rw_star_sub_BlockAdd₂ h₁)
  theorem rw_star_sub_BlockAdd₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockAdd a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockAdd a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockAdd₃ h)
    | .refl h => .refl (eqe.eqe_BlockAdd rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAdd₃ h₀) (rw_star_sub_BlockAdd₃ h₁)
  theorem rw_star_sub_BlockAdd₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockAdd a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockAdd a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockAdd₄ h)
    | .refl h => .refl (eqe.eqe_BlockAdd rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAdd₄ h₀) (rw_star_sub_BlockAdd₄ h₁)
  theorem rw_star_sub_BlockAdd₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockAdd a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockAdd a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockAdd₅ h)
    | .refl h => .refl (eqe.eqe_BlockAdd rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAdd₅ h₀) (rw_star_sub_BlockAdd₅ h₁)
  theorem rw_star_sub_BlockAdd₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockAdd₆ h)
    | .refl h => .refl (eqe.eqe_BlockAdd rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAdd₆ h₀) (rw_star_sub_BlockAdd₆ h₁)
  theorem rw_star_sub_BlockAdd₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockAdd₇ h)
    | .refl h => .refl (eqe.eqe_BlockAdd rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAdd₇ h₀) (rw_star_sub_BlockAdd₇ h₁)
  theorem rw_star_sub_BlockAdd₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a b : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockAdd₈ h)
    | .refl h => .refl (eqe.eqe_BlockAdd rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) h (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAdd₈ h₀) (rw_star_sub_BlockAdd₈ h₁)
  theorem rw_star_sub_BlockAdd₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a b : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂).rw_star (BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockAdd₉ h)
    | .refl h => .refl (eqe.eqe_BlockAdd rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl h rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAdd₉ h₀) (rw_star_sub_BlockAdd₉ h₁)
  theorem rw_star_sub_BlockAdd₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂).rw_star (BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockAdd₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockAdd rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAdd₁₀ h₀) (rw_star_sub_BlockAdd₁₀ h₁)
  theorem rw_star_sub_BlockAdd₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂).rw_star (BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | .step h => .step (rw_one.sub_BlockAdd₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockAdd rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAdd₁₁ h₀) (rw_star_sub_BlockAdd₁₁ h₁)
  theorem rw_star_sub_BlockAdd₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a).rw_star (BlockAdd a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | .step h => .step (rw_one.sub_BlockAdd₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockAdd rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockAdd₁₂ h₀) (rw_star_sub_BlockAdd₁₂ h₁)
  theorem rw_star_sub_BlockSubtract₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockSubtract a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockSubtract b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockSubtract₀ h)
    | .refl h => .refl (eqe.eqe_BlockSubtract h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSubtract₀ h₀) (rw_star_sub_BlockSubtract₀ h₁)
  theorem rw_star_sub_BlockSubtract₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockSubtract a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockSubtract a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockSubtract₁ h)
    | .refl h => .refl (eqe.eqe_BlockSubtract rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSubtract₁ h₀) (rw_star_sub_BlockSubtract₁ h₁)
  theorem rw_star_sub_BlockSubtract₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockSubtract a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockSubtract a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockSubtract₂ h)
    | .refl h => .refl (eqe.eqe_BlockSubtract rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSubtract₂ h₀) (rw_star_sub_BlockSubtract₂ h₁)
  theorem rw_star_sub_BlockSubtract₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockSubtract a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockSubtract a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockSubtract₃ h)
    | .refl h => .refl (eqe.eqe_BlockSubtract rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSubtract₃ h₀) (rw_star_sub_BlockSubtract₃ h₁)
  theorem rw_star_sub_BlockSubtract₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockSubtract a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockSubtract a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockSubtract₄ h)
    | .refl h => .refl (eqe.eqe_BlockSubtract rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSubtract₄ h₀) (rw_star_sub_BlockSubtract₄ h₁)
  theorem rw_star_sub_BlockSubtract₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockSubtract a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockSubtract a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockSubtract₅ h)
    | .refl h => .refl (eqe.eqe_BlockSubtract rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSubtract₅ h₀) (rw_star_sub_BlockSubtract₅ h₁)
  theorem rw_star_sub_BlockSubtract₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockSubtract₆ h)
    | .refl h => .refl (eqe.eqe_BlockSubtract rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSubtract₆ h₀) (rw_star_sub_BlockSubtract₆ h₁)
  theorem rw_star_sub_BlockSubtract₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockSubtract₇ h)
    | .refl h => .refl (eqe.eqe_BlockSubtract rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSubtract₇ h₀) (rw_star_sub_BlockSubtract₇ h₁)
  theorem rw_star_sub_BlockSubtract₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a b : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockSubtract₈ h)
    | .refl h => .refl (eqe.eqe_BlockSubtract rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) h (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSubtract₈ h₀) (rw_star_sub_BlockSubtract₈ h₁)
  theorem rw_star_sub_BlockSubtract₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a b : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂).rw_star (BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockSubtract₉ h)
    | .refl h => .refl (eqe.eqe_BlockSubtract rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl h rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSubtract₉ h₀) (rw_star_sub_BlockSubtract₉ h₁)
  theorem rw_star_sub_BlockSubtract₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂).rw_star (BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockSubtract₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockSubtract rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSubtract₁₀ h₀) (rw_star_sub_BlockSubtract₁₀ h₁)
  theorem rw_star_sub_BlockSubtract₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂).rw_star (BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | .step h => .step (rw_one.sub_BlockSubtract₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockSubtract rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSubtract₁₁ h₀) (rw_star_sub_BlockSubtract₁₁ h₁)
  theorem rw_star_sub_BlockSubtract₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a).rw_star (BlockSubtract a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | .step h => .step (rw_one.sub_BlockSubtract₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockSubtract rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSubtract₁₂ h₀) (rw_star_sub_BlockSubtract₁₂ h₁)
  theorem rw_star_sub_BlockMultiply₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMultiply a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMultiply b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMultiply₀ h)
    | .refl h => .refl (eqe.eqe_BlockMultiply h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMultiply₀ h₀) (rw_star_sub_BlockMultiply₀ h₁)
  theorem rw_star_sub_BlockMultiply₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMultiply a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMultiply a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMultiply₁ h)
    | .refl h => .refl (eqe.eqe_BlockMultiply rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMultiply₁ h₀) (rw_star_sub_BlockMultiply₁ h₁)
  theorem rw_star_sub_BlockMultiply₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMultiply a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMultiply a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMultiply₂ h)
    | .refl h => .refl (eqe.eqe_BlockMultiply rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMultiply₂ h₀) (rw_star_sub_BlockMultiply₂ h₁)
  theorem rw_star_sub_BlockMultiply₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMultiply a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMultiply a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMultiply₃ h)
    | .refl h => .refl (eqe.eqe_BlockMultiply rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMultiply₃ h₀) (rw_star_sub_BlockMultiply₃ h₁)
  theorem rw_star_sub_BlockMultiply₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMultiply a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMultiply a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMultiply₄ h)
    | .refl h => .refl (eqe.eqe_BlockMultiply rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMultiply₄ h₀) (rw_star_sub_BlockMultiply₄ h₁)
  theorem rw_star_sub_BlockMultiply₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMultiply a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMultiply a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMultiply₅ h)
    | .refl h => .refl (eqe.eqe_BlockMultiply rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMultiply₅ h₀) (rw_star_sub_BlockMultiply₅ h₁)
  theorem rw_star_sub_BlockMultiply₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMultiply₆ h)
    | .refl h => .refl (eqe.eqe_BlockMultiply rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMultiply₆ h₀) (rw_star_sub_BlockMultiply₆ h₁)
  theorem rw_star_sub_BlockMultiply₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMultiply₇ h)
    | .refl h => .refl (eqe.eqe_BlockMultiply rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMultiply₇ h₀) (rw_star_sub_BlockMultiply₇ h₁)
  theorem rw_star_sub_BlockMultiply₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a b : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMultiply₈ h)
    | .refl h => .refl (eqe.eqe_BlockMultiply rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) h (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMultiply₈ h₀) (rw_star_sub_BlockMultiply₈ h₁)
  theorem rw_star_sub_BlockMultiply₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a b : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂).rw_star (BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMultiply₉ h)
    | .refl h => .refl (eqe.eqe_BlockMultiply rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl h rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMultiply₉ h₀) (rw_star_sub_BlockMultiply₉ h₁)
  theorem rw_star_sub_BlockMultiply₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂).rw_star (BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMultiply₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockMultiply rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMultiply₁₀ h₀) (rw_star_sub_BlockMultiply₁₀ h₁)
  theorem rw_star_sub_BlockMultiply₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂).rw_star (BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | .step h => .step (rw_one.sub_BlockMultiply₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockMultiply rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMultiply₁₁ h₀) (rw_star_sub_BlockMultiply₁₁ h₁)
  theorem rw_star_sub_BlockMultiply₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a).rw_star (BlockMultiply a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | .step h => .step (rw_one.sub_BlockMultiply₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockMultiply rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMultiply₁₂ h₀) (rw_star_sub_BlockMultiply₁₂ h₁)
  theorem rw_star_sub_BlockDivide₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockDivide a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockDivide b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockDivide₀ h)
    | .refl h => .refl (eqe.eqe_BlockDivide h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDivide₀ h₀) (rw_star_sub_BlockDivide₀ h₁)
  theorem rw_star_sub_BlockDivide₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockDivide a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockDivide a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockDivide₁ h)
    | .refl h => .refl (eqe.eqe_BlockDivide rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDivide₁ h₀) (rw_star_sub_BlockDivide₁ h₁)
  theorem rw_star_sub_BlockDivide₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockDivide a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockDivide a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockDivide₂ h)
    | .refl h => .refl (eqe.eqe_BlockDivide rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDivide₂ h₀) (rw_star_sub_BlockDivide₂ h₁)
  theorem rw_star_sub_BlockDivide₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockDivide a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockDivide a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockDivide₃ h)
    | .refl h => .refl (eqe.eqe_BlockDivide rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDivide₃ h₀) (rw_star_sub_BlockDivide₃ h₁)
  theorem rw_star_sub_BlockDivide₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockDivide a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockDivide a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockDivide₄ h)
    | .refl h => .refl (eqe.eqe_BlockDivide rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDivide₄ h₀) (rw_star_sub_BlockDivide₄ h₁)
  theorem rw_star_sub_BlockDivide₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockDivide a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockDivide a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockDivide₅ h)
    | .refl h => .refl (eqe.eqe_BlockDivide rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDivide₅ h₀) (rw_star_sub_BlockDivide₅ h₁)
  theorem rw_star_sub_BlockDivide₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockDivide₆ h)
    | .refl h => .refl (eqe.eqe_BlockDivide rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDivide₆ h₀) (rw_star_sub_BlockDivide₆ h₁)
  theorem rw_star_sub_BlockDivide₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockDivide₇ h)
    | .refl h => .refl (eqe.eqe_BlockDivide rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDivide₇ h₀) (rw_star_sub_BlockDivide₇ h₁)
  theorem rw_star_sub_BlockDivide₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a b : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockDivide₈ h)
    | .refl h => .refl (eqe.eqe_BlockDivide rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) h (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDivide₈ h₀) (rw_star_sub_BlockDivide₈ h₁)
  theorem rw_star_sub_BlockDivide₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a b : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂).rw_star (BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockDivide₉ h)
    | .refl h => .refl (eqe.eqe_BlockDivide rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl h rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDivide₉ h₀) (rw_star_sub_BlockDivide₉ h₁)
  theorem rw_star_sub_BlockDivide₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂).rw_star (BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockDivide₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockDivide rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDivide₁₀ h₀) (rw_star_sub_BlockDivide₁₀ h₁)
  theorem rw_star_sub_BlockDivide₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂).rw_star (BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | .step h => .step (rw_one.sub_BlockDivide₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockDivide rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDivide₁₁ h₀) (rw_star_sub_BlockDivide₁₁ h₁)
  theorem rw_star_sub_BlockDivide₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a).rw_star (BlockDivide a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | .step h => .step (rw_one.sub_BlockDivide₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockDivide rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockDivide₁₂ h₀) (rw_star_sub_BlockDivide₁₂ h₁)
  theorem rw_star_sub_BlockFMA₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : MRat.rw_star a b →
      (BlockFMA a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFMA b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFMA₀ h)
    | .refl h => .refl (eqe.eqe_BlockFMA h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFMA₀ h₀) (rw_star_sub_BlockFMA₀ h₁)
  theorem rw_star_sub_BlockFMA₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFMA a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFMA a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFMA₁ h)
    | .refl h => .refl (eqe.eqe_BlockFMA rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFMA₁ h₀) (rw_star_sub_BlockFMA₁ h₁)
  theorem rw_star_sub_BlockFMA₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFMA a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFMA a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFMA₂ h)
    | .refl h => .refl (eqe.eqe_BlockFMA rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFMA₂ h₀) (rw_star_sub_BlockFMA₂ h₁)
  theorem rw_star_sub_BlockFMA₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFMA a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFMA a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFMA₃ h)
    | .refl h => .refl (eqe.eqe_BlockFMA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFMA₃ h₀) (rw_star_sub_BlockFMA₃ h₁)
  theorem rw_star_sub_BlockFMA₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFMA a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFMA a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFMA₄ h)
    | .refl h => .refl (eqe.eqe_BlockFMA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFMA₄ h₀) (rw_star_sub_BlockFMA₄ h₁)
  theorem rw_star_sub_BlockFMA₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFMA a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFMA a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFMA₅ h)
    | .refl h => .refl (eqe.eqe_BlockFMA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFMA₅ h₀) (rw_star_sub_BlockFMA₅ h₁)
  theorem rw_star_sub_BlockFMA₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFMA₆ h)
    | .refl h => .refl (eqe.eqe_BlockFMA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFMA₆ h₀) (rw_star_sub_BlockFMA₆ h₁)
  theorem rw_star_sub_BlockFMA₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a b a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFMA₇ h)
    | .refl h => .refl (eqe.eqe_BlockFMA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFMA₇ h₀) (rw_star_sub_BlockFMA₇ h₁)
  theorem rw_star_sub_BlockFMA₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFMA₈ h)
    | .refl h => .refl (eqe.eqe_BlockFMA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) h (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFMA₈ h₀) (rw_star_sub_BlockFMA₈ h₁)
  theorem rw_star_sub_BlockFMA₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a b : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFMA₉ h)
    | .refl h => .refl (eqe.eqe_BlockFMA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) h rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFMA₉ h₀) (rw_star_sub_BlockFMA₉ h₁)
  theorem rw_star_sub_BlockFMA₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : MRat.rw_star a b →
      (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFMA₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockFMA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFMA₁₀ h₀) (rw_star_sub_BlockFMA₁₀ h₁)
  theorem rw_star_sub_BlockFMA₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFMA₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockFMA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl h rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFMA₁₁ h₀) (rw_star_sub_BlockFMA₁₁ h₁)
  theorem rw_star_sub_BlockFMA₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : MRat.rw_star a b →
      (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFMA₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockFMA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFMA₁₂ h₀) (rw_star_sub_BlockFMA₁₂ h₁)
  theorem rw_star_sub_BlockFMA₁₃ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a b : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a a₁₄ a₁₅ a₁₆).rw_star (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFMA₁₃ h)
    | .refl h => .refl (eqe.eqe_BlockFMA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl h rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFMA₁₃ h₀) (rw_star_sub_BlockFMA₁₃ h₁)
  theorem rw_star_sub_BlockFMA₁₄ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a b : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : MRat.rw_star a b →
      (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a a₁₅ a₁₆).rw_star (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFMA₁₄ h)
    | .refl h => .refl (eqe.eqe_BlockFMA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) h (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFMA₁₄ h₀) (rw_star_sub_BlockFMA₁₄ h₁)
  theorem rw_star_sub_BlockFMA₁₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a b : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a a₁₆).rw_star (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ b a₁₆)
    | .step h => .step (rw_one.sub_BlockFMA₁₅ h)
    | .refl h => .refl (eqe.eqe_BlockFMA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFMA₁₅ h₀) (rw_star_sub_BlockFMA₁₅ h₁)
  theorem rw_star_sub_BlockFMA₁₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a).rw_star (BlockFMA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ b)
    | .step h => .step (rw_one.sub_BlockFMA₁₆ h)
    | .refl h => .refl (eqe.eqe_BlockFMA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFMA₁₆ h₀) (rw_star_sub_BlockFMA₁₆ h₁)
  theorem rw_star_sub_BlockFAA₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : MRat.rw_star a b →
      (BlockFAA a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFAA b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFAA₀ h)
    | .refl h => .refl (eqe.eqe_BlockFAA h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFAA₀ h₀) (rw_star_sub_BlockFAA₀ h₁)
  theorem rw_star_sub_BlockFAA₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFAA a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFAA a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFAA₁ h)
    | .refl h => .refl (eqe.eqe_BlockFAA rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFAA₁ h₀) (rw_star_sub_BlockFAA₁ h₁)
  theorem rw_star_sub_BlockFAA₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFAA a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFAA a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFAA₂ h)
    | .refl h => .refl (eqe.eqe_BlockFAA rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFAA₂ h₀) (rw_star_sub_BlockFAA₂ h₁)
  theorem rw_star_sub_BlockFAA₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFAA a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFAA a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFAA₃ h)
    | .refl h => .refl (eqe.eqe_BlockFAA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFAA₃ h₀) (rw_star_sub_BlockFAA₃ h₁)
  theorem rw_star_sub_BlockFAA₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFAA a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFAA a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFAA₄ h)
    | .refl h => .refl (eqe.eqe_BlockFAA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFAA₄ h₀) (rw_star_sub_BlockFAA₄ h₁)
  theorem rw_star_sub_BlockFAA₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFAA a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFAA a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFAA₅ h)
    | .refl h => .refl (eqe.eqe_BlockFAA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFAA₅ h₀) (rw_star_sub_BlockFAA₅ h₁)
  theorem rw_star_sub_BlockFAA₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFAA₆ h)
    | .refl h => .refl (eqe.eqe_BlockFAA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFAA₆ h₀) (rw_star_sub_BlockFAA₆ h₁)
  theorem rw_star_sub_BlockFAA₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a b a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFAA₇ h)
    | .refl h => .refl (eqe.eqe_BlockFAA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFAA₇ h₀) (rw_star_sub_BlockFAA₇ h₁)
  theorem rw_star_sub_BlockFAA₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFAA₈ h)
    | .refl h => .refl (eqe.eqe_BlockFAA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) h (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFAA₈ h₀) (rw_star_sub_BlockFAA₈ h₁)
  theorem rw_star_sub_BlockFAA₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a b : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFAA₉ h)
    | .refl h => .refl (eqe.eqe_BlockFAA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) h rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFAA₉ h₀) (rw_star_sub_BlockFAA₉ h₁)
  theorem rw_star_sub_BlockFAA₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : MRat.rw_star a b →
      (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFAA₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockFAA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFAA₁₀ h₀) (rw_star_sub_BlockFAA₁₀ h₁)
  theorem rw_star_sub_BlockFAA₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFAA₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockFAA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl h rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFAA₁₁ h₀) (rw_star_sub_BlockFAA₁₁ h₁)
  theorem rw_star_sub_BlockFAA₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : MRat.rw_star a b →
      (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFAA₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockFAA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFAA₁₂ h₀) (rw_star_sub_BlockFAA₁₂ h₁)
  theorem rw_star_sub_BlockFAA₁₃ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a b : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a a₁₄ a₁₅ a₁₆).rw_star (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFAA₁₃ h)
    | .refl h => .refl (eqe.eqe_BlockFAA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl h rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFAA₁₃ h₀) (rw_star_sub_BlockFAA₁₃ h₁)
  theorem rw_star_sub_BlockFAA₁₄ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a b : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : MRat.rw_star a b →
      (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a a₁₅ a₁₆).rw_star (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockFAA₁₄ h)
    | .refl h => .refl (eqe.eqe_BlockFAA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) h (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFAA₁₄ h₀) (rw_star_sub_BlockFAA₁₄ h₁)
  theorem rw_star_sub_BlockFAA₁₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a b : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a a₁₆).rw_star (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ b a₁₆)
    | .step h => .step (rw_one.sub_BlockFAA₁₅ h)
    | .refl h => .refl (eqe.eqe_BlockFAA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFAA₁₅ h₀) (rw_star_sub_BlockFAA₁₅ h₁)
  theorem rw_star_sub_BlockFAA₁₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a).rw_star (BlockFAA a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ b)
    | .step h => .step (rw_one.sub_BlockFAA₁₆ h)
    | .refl h => .refl (eqe.eqe_BlockFAA rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockFAA₁₆ h₀) (rw_star_sub_BlockFAA₁₆ h₁)
  theorem rw_star_sub_BlockRecip₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockRecip a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockRecip b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockRecip₀ h)
    | .refl h => .refl (eqe.eqe_BlockRecip h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockRecip₀ h₀) (rw_star_sub_BlockRecip₀ h₁)
  theorem rw_star_sub_BlockRecip₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockRecip a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockRecip a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockRecip₁ h)
    | .refl h => .refl (eqe.eqe_BlockRecip rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockRecip₁ h₀) (rw_star_sub_BlockRecip₁ h₁)
  theorem rw_star_sub_BlockRecip₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockRecip a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockRecip a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockRecip₂ h)
    | .refl h => .refl (eqe.eqe_BlockRecip rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockRecip₂ h₀) (rw_star_sub_BlockRecip₂ h₁)
  theorem rw_star_sub_BlockRecip₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockRecip a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockRecip a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockRecip₃ h)
    | .refl h => .refl (eqe.eqe_BlockRecip rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockRecip₃ h₀) (rw_star_sub_BlockRecip₃ h₁)
  theorem rw_star_sub_BlockRecip₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockRecip a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockRecip a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockRecip₄ h)
    | .refl h => .refl (eqe.eqe_BlockRecip rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockRecip₄ h₀) (rw_star_sub_BlockRecip₄ h₁)
  theorem rw_star_sub_BlockRecip₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockRecip a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockRecip a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockRecip₅ h)
    | .refl h => .refl (eqe.eqe_BlockRecip rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockRecip₅ h₀) (rw_star_sub_BlockRecip₅ h₁)
  theorem rw_star_sub_BlockRecip₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockRecip a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockRecip a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockRecip₆ h)
    | .refl h => .refl (eqe.eqe_BlockRecip rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockRecip₆ h₀) (rw_star_sub_BlockRecip₆ h₁)
  theorem rw_star_sub_BlockRecip₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockRecip a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockRecip a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockRecip₇ h)
    | .refl h => .refl (eqe.eqe_BlockRecip rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockRecip₇ h₀) (rw_star_sub_BlockRecip₇ h₁)
  theorem rw_star_sub_BlockRecip₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockRecip a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockRecip a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockRecip₈ h)
    | .refl h => .refl (eqe.eqe_BlockRecip rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockRecip₈ h₀) (rw_star_sub_BlockRecip₈ h₁)
  theorem rw_star_sub_BlockMinimum₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMinimum a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimum b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimum₀ h)
    | .refl h => .refl (eqe.eqe_BlockMinimum h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimum₀ h₀) (rw_star_sub_BlockMinimum₀ h₁)
  theorem rw_star_sub_BlockMinimum₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimum a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimum a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimum₁ h)
    | .refl h => .refl (eqe.eqe_BlockMinimum rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimum₁ h₀) (rw_star_sub_BlockMinimum₁ h₁)
  theorem rw_star_sub_BlockMinimum₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimum a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimum a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimum₂ h)
    | .refl h => .refl (eqe.eqe_BlockMinimum rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimum₂ h₀) (rw_star_sub_BlockMinimum₂ h₁)
  theorem rw_star_sub_BlockMinimum₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimum a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimum a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimum₃ h)
    | .refl h => .refl (eqe.eqe_BlockMinimum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimum₃ h₀) (rw_star_sub_BlockMinimum₃ h₁)
  theorem rw_star_sub_BlockMinimum₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimum a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimum a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimum₄ h)
    | .refl h => .refl (eqe.eqe_BlockMinimum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimum₄ h₀) (rw_star_sub_BlockMinimum₄ h₁)
  theorem rw_star_sub_BlockMinimum₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimum a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimum a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimum₅ h)
    | .refl h => .refl (eqe.eqe_BlockMinimum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimum₅ h₀) (rw_star_sub_BlockMinimum₅ h₁)
  theorem rw_star_sub_BlockMinimum₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimum₆ h)
    | .refl h => .refl (eqe.eqe_BlockMinimum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimum₆ h₀) (rw_star_sub_BlockMinimum₆ h₁)
  theorem rw_star_sub_BlockMinimum₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimum₇ h)
    | .refl h => .refl (eqe.eqe_BlockMinimum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimum₇ h₀) (rw_star_sub_BlockMinimum₇ h₁)
  theorem rw_star_sub_BlockMinimum₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a b : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimum₈ h)
    | .refl h => .refl (eqe.eqe_BlockMinimum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) h (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimum₈ h₀) (rw_star_sub_BlockMinimum₈ h₁)
  theorem rw_star_sub_BlockMinimum₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a b : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂).rw_star (BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimum₉ h)
    | .refl h => .refl (eqe.eqe_BlockMinimum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl h rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimum₉ h₀) (rw_star_sub_BlockMinimum₉ h₁)
  theorem rw_star_sub_BlockMinimum₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂).rw_star (BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimum₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockMinimum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimum₁₀ h₀) (rw_star_sub_BlockMinimum₁₀ h₁)
  theorem rw_star_sub_BlockMinimum₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂).rw_star (BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimum₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockMinimum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimum₁₁ h₀) (rw_star_sub_BlockMinimum₁₁ h₁)
  theorem rw_star_sub_BlockMinimum₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a).rw_star (BlockMinimum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | .step h => .step (rw_one.sub_BlockMinimum₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockMinimum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimum₁₂ h₀) (rw_star_sub_BlockMinimum₁₂ h₁)
  theorem rw_star_sub_BlockMaximum₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMaximum a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximum b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximum₀ h)
    | .refl h => .refl (eqe.eqe_BlockMaximum h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximum₀ h₀) (rw_star_sub_BlockMaximum₀ h₁)
  theorem rw_star_sub_BlockMaximum₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximum a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximum a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximum₁ h)
    | .refl h => .refl (eqe.eqe_BlockMaximum rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximum₁ h₀) (rw_star_sub_BlockMaximum₁ h₁)
  theorem rw_star_sub_BlockMaximum₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximum a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximum a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximum₂ h)
    | .refl h => .refl (eqe.eqe_BlockMaximum rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximum₂ h₀) (rw_star_sub_BlockMaximum₂ h₁)
  theorem rw_star_sub_BlockMaximum₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximum a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximum a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximum₃ h)
    | .refl h => .refl (eqe.eqe_BlockMaximum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximum₃ h₀) (rw_star_sub_BlockMaximum₃ h₁)
  theorem rw_star_sub_BlockMaximum₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximum a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximum a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximum₄ h)
    | .refl h => .refl (eqe.eqe_BlockMaximum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximum₄ h₀) (rw_star_sub_BlockMaximum₄ h₁)
  theorem rw_star_sub_BlockMaximum₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximum a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximum a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximum₅ h)
    | .refl h => .refl (eqe.eqe_BlockMaximum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximum₅ h₀) (rw_star_sub_BlockMaximum₅ h₁)
  theorem rw_star_sub_BlockMaximum₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximum₆ h)
    | .refl h => .refl (eqe.eqe_BlockMaximum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximum₆ h₀) (rw_star_sub_BlockMaximum₆ h₁)
  theorem rw_star_sub_BlockMaximum₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximum₇ h)
    | .refl h => .refl (eqe.eqe_BlockMaximum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximum₇ h₀) (rw_star_sub_BlockMaximum₇ h₁)
  theorem rw_star_sub_BlockMaximum₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a b : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximum₈ h)
    | .refl h => .refl (eqe.eqe_BlockMaximum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) h (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximum₈ h₀) (rw_star_sub_BlockMaximum₈ h₁)
  theorem rw_star_sub_BlockMaximum₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a b : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂).rw_star (BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximum₉ h)
    | .refl h => .refl (eqe.eqe_BlockMaximum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl h rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximum₉ h₀) (rw_star_sub_BlockMaximum₉ h₁)
  theorem rw_star_sub_BlockMaximum₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂).rw_star (BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximum₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockMaximum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximum₁₀ h₀) (rw_star_sub_BlockMaximum₁₀ h₁)
  theorem rw_star_sub_BlockMaximum₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂).rw_star (BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximum₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockMaximum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximum₁₁ h₀) (rw_star_sub_BlockMaximum₁₁ h₁)
  theorem rw_star_sub_BlockMaximum₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a).rw_star (BlockMaximum a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | .step h => .step (rw_one.sub_BlockMaximum₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockMaximum rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximum₁₂ h₀) (rw_star_sub_BlockMaximum₁₂ h₁)
  theorem rw_star_sub_BlockMinimumNumber₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMinimumNumber a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumNumber b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumNumber₀ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumNumber h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumNumber₀ h₀) (rw_star_sub_BlockMinimumNumber₀ h₁)
  theorem rw_star_sub_BlockMinimumNumber₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumNumber a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumNumber a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumNumber₁ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumNumber rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumNumber₁ h₀) (rw_star_sub_BlockMinimumNumber₁ h₁)
  theorem rw_star_sub_BlockMinimumNumber₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumNumber a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumNumber a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumNumber₂ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumNumber rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumNumber₂ h₀) (rw_star_sub_BlockMinimumNumber₂ h₁)
  theorem rw_star_sub_BlockMinimumNumber₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumNumber a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumNumber a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumNumber₃ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumNumber₃ h₀) (rw_star_sub_BlockMinimumNumber₃ h₁)
  theorem rw_star_sub_BlockMinimumNumber₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumNumber a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumNumber a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumNumber₄ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumNumber₄ h₀) (rw_star_sub_BlockMinimumNumber₄ h₁)
  theorem rw_star_sub_BlockMinimumNumber₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumNumber₅ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumNumber₅ h₀) (rw_star_sub_BlockMinimumNumber₅ h₁)
  theorem rw_star_sub_BlockMinimumNumber₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumNumber₆ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumNumber₆ h₀) (rw_star_sub_BlockMinimumNumber₆ h₁)
  theorem rw_star_sub_BlockMinimumNumber₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumNumber₇ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumNumber₇ h₀) (rw_star_sub_BlockMinimumNumber₇ h₁)
  theorem rw_star_sub_BlockMinimumNumber₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a b : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumNumber₈ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) h (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumNumber₈ h₀) (rw_star_sub_BlockMinimumNumber₈ h₁)
  theorem rw_star_sub_BlockMinimumNumber₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a b : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumNumber₉ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl h rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumNumber₉ h₀) (rw_star_sub_BlockMinimumNumber₉ h₁)
  theorem rw_star_sub_BlockMinimumNumber₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂).rw_star (BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumNumber₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumNumber₁₀ h₀) (rw_star_sub_BlockMinimumNumber₁₀ h₁)
  theorem rw_star_sub_BlockMinimumNumber₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂).rw_star (BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumNumber₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumNumber₁₁ h₀) (rw_star_sub_BlockMinimumNumber₁₁ h₁)
  theorem rw_star_sub_BlockMinimumNumber₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a).rw_star (BlockMinimumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | .step h => .step (rw_one.sub_BlockMinimumNumber₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumNumber₁₂ h₀) (rw_star_sub_BlockMinimumNumber₁₂ h₁)
  theorem rw_star_sub_BlockMaximumNumber₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMaximumNumber a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumNumber b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumNumber₀ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumNumber h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumNumber₀ h₀) (rw_star_sub_BlockMaximumNumber₀ h₁)
  theorem rw_star_sub_BlockMaximumNumber₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumNumber a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumNumber a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumNumber₁ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumNumber rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumNumber₁ h₀) (rw_star_sub_BlockMaximumNumber₁ h₁)
  theorem rw_star_sub_BlockMaximumNumber₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumNumber a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumNumber a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumNumber₂ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumNumber rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumNumber₂ h₀) (rw_star_sub_BlockMaximumNumber₂ h₁)
  theorem rw_star_sub_BlockMaximumNumber₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumNumber a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumNumber a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumNumber₃ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumNumber₃ h₀) (rw_star_sub_BlockMaximumNumber₃ h₁)
  theorem rw_star_sub_BlockMaximumNumber₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumNumber a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumNumber a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumNumber₄ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumNumber₄ h₀) (rw_star_sub_BlockMaximumNumber₄ h₁)
  theorem rw_star_sub_BlockMaximumNumber₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumNumber₅ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumNumber₅ h₀) (rw_star_sub_BlockMaximumNumber₅ h₁)
  theorem rw_star_sub_BlockMaximumNumber₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumNumber₆ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumNumber₆ h₀) (rw_star_sub_BlockMaximumNumber₆ h₁)
  theorem rw_star_sub_BlockMaximumNumber₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumNumber₇ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumNumber₇ h₀) (rw_star_sub_BlockMaximumNumber₇ h₁)
  theorem rw_star_sub_BlockMaximumNumber₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a b : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumNumber₈ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) h (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumNumber₈ h₀) (rw_star_sub_BlockMaximumNumber₈ h₁)
  theorem rw_star_sub_BlockMaximumNumber₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a b : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumNumber₉ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl h rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumNumber₉ h₀) (rw_star_sub_BlockMaximumNumber₉ h₁)
  theorem rw_star_sub_BlockMaximumNumber₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂).rw_star (BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumNumber₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumNumber₁₀ h₀) (rw_star_sub_BlockMaximumNumber₁₀ h₁)
  theorem rw_star_sub_BlockMaximumNumber₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂).rw_star (BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumNumber₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumNumber₁₁ h₀) (rw_star_sub_BlockMaximumNumber₁₁ h₁)
  theorem rw_star_sub_BlockMaximumNumber₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a).rw_star (BlockMaximumNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | .step h => .step (rw_one.sub_BlockMaximumNumber₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumNumber₁₂ h₀) (rw_star_sub_BlockMaximumNumber₁₂ h₁)
  theorem rw_star_sub_BlockMinimumMagnitude₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMinimumMagnitude a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitude b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitude₀ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitude h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitude₀ h₀) (rw_star_sub_BlockMinimumMagnitude₀ h₁)
  theorem rw_star_sub_BlockMinimumMagnitude₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumMagnitude a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitude a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitude₁ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitude rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitude₁ h₀) (rw_star_sub_BlockMinimumMagnitude₁ h₁)
  theorem rw_star_sub_BlockMinimumMagnitude₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumMagnitude a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitude a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitude₂ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitude rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitude₂ h₀) (rw_star_sub_BlockMinimumMagnitude₂ h₁)
  theorem rw_star_sub_BlockMinimumMagnitude₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumMagnitude a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitude a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitude₃ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitude₃ h₀) (rw_star_sub_BlockMinimumMagnitude₃ h₁)
  theorem rw_star_sub_BlockMinimumMagnitude₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumMagnitude a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitude a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitude₄ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitude₄ h₀) (rw_star_sub_BlockMinimumMagnitude₄ h₁)
  theorem rw_star_sub_BlockMinimumMagnitude₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitude₅ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitude₅ h₀) (rw_star_sub_BlockMinimumMagnitude₅ h₁)
  theorem rw_star_sub_BlockMinimumMagnitude₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitude₆ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitude₆ h₀) (rw_star_sub_BlockMinimumMagnitude₆ h₁)
  theorem rw_star_sub_BlockMinimumMagnitude₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitude₇ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitude₇ h₀) (rw_star_sub_BlockMinimumMagnitude₇ h₁)
  theorem rw_star_sub_BlockMinimumMagnitude₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a b : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitude₈ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) h (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitude₈ h₀) (rw_star_sub_BlockMinimumMagnitude₈ h₁)
  theorem rw_star_sub_BlockMinimumMagnitude₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a b : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitude₉ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl h rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitude₉ h₀) (rw_star_sub_BlockMinimumMagnitude₉ h₁)
  theorem rw_star_sub_BlockMinimumMagnitude₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂).rw_star (BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitude₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitude₁₀ h₀) (rw_star_sub_BlockMinimumMagnitude₁₀ h₁)
  theorem rw_star_sub_BlockMinimumMagnitude₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂).rw_star (BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitude₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitude₁₁ h₀) (rw_star_sub_BlockMinimumMagnitude₁₁ h₁)
  theorem rw_star_sub_BlockMinimumMagnitude₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a).rw_star (BlockMinimumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitude₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitude₁₂ h₀) (rw_star_sub_BlockMinimumMagnitude₁₂ h₁)
  theorem rw_star_sub_BlockMaximumMagnitude₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMaximumMagnitude a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitude b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitude₀ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitude h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitude₀ h₀) (rw_star_sub_BlockMaximumMagnitude₀ h₁)
  theorem rw_star_sub_BlockMaximumMagnitude₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumMagnitude a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitude a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitude₁ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitude rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitude₁ h₀) (rw_star_sub_BlockMaximumMagnitude₁ h₁)
  theorem rw_star_sub_BlockMaximumMagnitude₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumMagnitude a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitude a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitude₂ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitude rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitude₂ h₀) (rw_star_sub_BlockMaximumMagnitude₂ h₁)
  theorem rw_star_sub_BlockMaximumMagnitude₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumMagnitude a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitude a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitude₃ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitude₃ h₀) (rw_star_sub_BlockMaximumMagnitude₃ h₁)
  theorem rw_star_sub_BlockMaximumMagnitude₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumMagnitude a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitude a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitude₄ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitude₄ h₀) (rw_star_sub_BlockMaximumMagnitude₄ h₁)
  theorem rw_star_sub_BlockMaximumMagnitude₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitude₅ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitude₅ h₀) (rw_star_sub_BlockMaximumMagnitude₅ h₁)
  theorem rw_star_sub_BlockMaximumMagnitude₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitude₆ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitude₆ h₀) (rw_star_sub_BlockMaximumMagnitude₆ h₁)
  theorem rw_star_sub_BlockMaximumMagnitude₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitude₇ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitude₇ h₀) (rw_star_sub_BlockMaximumMagnitude₇ h₁)
  theorem rw_star_sub_BlockMaximumMagnitude₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a b : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitude₈ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) h (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitude₈ h₀) (rw_star_sub_BlockMaximumMagnitude₈ h₁)
  theorem rw_star_sub_BlockMaximumMagnitude₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a b : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitude₉ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl h rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitude₉ h₀) (rw_star_sub_BlockMaximumMagnitude₉ h₁)
  theorem rw_star_sub_BlockMaximumMagnitude₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂).rw_star (BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitude₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitude₁₀ h₀) (rw_star_sub_BlockMaximumMagnitude₁₀ h₁)
  theorem rw_star_sub_BlockMaximumMagnitude₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂).rw_star (BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitude₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitude₁₁ h₀) (rw_star_sub_BlockMaximumMagnitude₁₁ h₁)
  theorem rw_star_sub_BlockMaximumMagnitude₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a).rw_star (BlockMaximumMagnitude a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitude₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitude rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitude₁₂ h₀) (rw_star_sub_BlockMaximumMagnitude₁₂ h₁)
  theorem rw_star_sub_BlockMinimumMagnitudeNumber₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMinimumMagnitudeNumber a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitudeNumber b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitudeNumber₀ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitudeNumber h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitudeNumber₀ h₀) (rw_star_sub_BlockMinimumMagnitudeNumber₀ h₁)
  theorem rw_star_sub_BlockMinimumMagnitudeNumber₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumMagnitudeNumber a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitudeNumber a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitudeNumber₁ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitudeNumber rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitudeNumber₁ h₀) (rw_star_sub_BlockMinimumMagnitudeNumber₁ h₁)
  theorem rw_star_sub_BlockMinimumMagnitudeNumber₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumMagnitudeNumber a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitudeNumber a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitudeNumber₂ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitudeNumber rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitudeNumber₂ h₀) (rw_star_sub_BlockMinimumMagnitudeNumber₂ h₁)
  theorem rw_star_sub_BlockMinimumMagnitudeNumber₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitudeNumber a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitudeNumber₃ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitudeNumber₃ h₀) (rw_star_sub_BlockMinimumMagnitudeNumber₃ h₁)
  theorem rw_star_sub_BlockMinimumMagnitudeNumber₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitudeNumber₄ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitudeNumber₄ h₀) (rw_star_sub_BlockMinimumMagnitudeNumber₄ h₁)
  theorem rw_star_sub_BlockMinimumMagnitudeNumber₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitudeNumber₅ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitudeNumber₅ h₀) (rw_star_sub_BlockMinimumMagnitudeNumber₅ h₁)
  theorem rw_star_sub_BlockMinimumMagnitudeNumber₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitudeNumber₆ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitudeNumber₆ h₀) (rw_star_sub_BlockMinimumMagnitudeNumber₆ h₁)
  theorem rw_star_sub_BlockMinimumMagnitudeNumber₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitudeNumber₇ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitudeNumber₇ h₀) (rw_star_sub_BlockMinimumMagnitudeNumber₇ h₁)
  theorem rw_star_sub_BlockMinimumMagnitudeNumber₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a b : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitudeNumber₈ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) h (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitudeNumber₈ h₀) (rw_star_sub_BlockMinimumMagnitudeNumber₈ h₁)
  theorem rw_star_sub_BlockMinimumMagnitudeNumber₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a b : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitudeNumber₉ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl h rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitudeNumber₉ h₀) (rw_star_sub_BlockMinimumMagnitudeNumber₉ h₁)
  theorem rw_star_sub_BlockMinimumMagnitudeNumber₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂).rw_star (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitudeNumber₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitudeNumber₁₀ h₀) (rw_star_sub_BlockMinimumMagnitudeNumber₁₀ h₁)
  theorem rw_star_sub_BlockMinimumMagnitudeNumber₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂).rw_star (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitudeNumber₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitudeNumber₁₁ h₀) (rw_star_sub_BlockMinimumMagnitudeNumber₁₁ h₁)
  theorem rw_star_sub_BlockMinimumMagnitudeNumber₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a).rw_star (BlockMinimumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | .step h => .step (rw_one.sub_BlockMinimumMagnitudeNumber₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumMagnitudeNumber₁₂ h₀) (rw_star_sub_BlockMinimumMagnitudeNumber₁₂ h₁)
  theorem rw_star_sub_BlockMaximumMagnitudeNumber₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMaximumMagnitudeNumber a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitudeNumber b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitudeNumber₀ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitudeNumber h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitudeNumber₀ h₀) (rw_star_sub_BlockMaximumMagnitudeNumber₀ h₁)
  theorem rw_star_sub_BlockMaximumMagnitudeNumber₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumMagnitudeNumber a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitudeNumber a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitudeNumber₁ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitudeNumber rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitudeNumber₁ h₀) (rw_star_sub_BlockMaximumMagnitudeNumber₁ h₁)
  theorem rw_star_sub_BlockMaximumMagnitudeNumber₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumMagnitudeNumber a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitudeNumber a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitudeNumber₂ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitudeNumber rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitudeNumber₂ h₀) (rw_star_sub_BlockMaximumMagnitudeNumber₂ h₁)
  theorem rw_star_sub_BlockMaximumMagnitudeNumber₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitudeNumber a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitudeNumber₃ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitudeNumber₃ h₀) (rw_star_sub_BlockMaximumMagnitudeNumber₃ h₁)
  theorem rw_star_sub_BlockMaximumMagnitudeNumber₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitudeNumber₄ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitudeNumber₄ h₀) (rw_star_sub_BlockMaximumMagnitudeNumber₄ h₁)
  theorem rw_star_sub_BlockMaximumMagnitudeNumber₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitudeNumber₅ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitudeNumber₅ h₀) (rw_star_sub_BlockMaximumMagnitudeNumber₅ h₁)
  theorem rw_star_sub_BlockMaximumMagnitudeNumber₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitudeNumber₆ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitudeNumber₆ h₀) (rw_star_sub_BlockMaximumMagnitudeNumber₆ h₁)
  theorem rw_star_sub_BlockMaximumMagnitudeNumber₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitudeNumber₇ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitudeNumber₇ h₀) (rw_star_sub_BlockMaximumMagnitudeNumber₇ h₁)
  theorem rw_star_sub_BlockMaximumMagnitudeNumber₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a b : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitudeNumber₈ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) h (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitudeNumber₈ h₀) (rw_star_sub_BlockMaximumMagnitudeNumber₈ h₁)
  theorem rw_star_sub_BlockMaximumMagnitudeNumber₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a b : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitudeNumber₉ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl h rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitudeNumber₉ h₀) (rw_star_sub_BlockMaximumMagnitudeNumber₉ h₁)
  theorem rw_star_sub_BlockMaximumMagnitudeNumber₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂).rw_star (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitudeNumber₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitudeNumber₁₀ h₀) (rw_star_sub_BlockMaximumMagnitudeNumber₁₀ h₁)
  theorem rw_star_sub_BlockMaximumMagnitudeNumber₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂).rw_star (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitudeNumber₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitudeNumber₁₁ h₀) (rw_star_sub_BlockMaximumMagnitudeNumber₁₁ h₁)
  theorem rw_star_sub_BlockMaximumMagnitudeNumber₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a).rw_star (BlockMaximumMagnitudeNumber a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | .step h => .step (rw_one.sub_BlockMaximumMagnitudeNumber₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumMagnitudeNumber rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumMagnitudeNumber₁₂ h₀) (rw_star_sub_BlockMaximumMagnitudeNumber₁₂ h₁)
  theorem rw_star_sub_BlockMinimumFinite₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMinimumFinite a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumFinite b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumFinite₀ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumFinite h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumFinite₀ h₀) (rw_star_sub_BlockMinimumFinite₀ h₁)
  theorem rw_star_sub_BlockMinimumFinite₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumFinite a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumFinite a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumFinite₁ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumFinite rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumFinite₁ h₀) (rw_star_sub_BlockMinimumFinite₁ h₁)
  theorem rw_star_sub_BlockMinimumFinite₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumFinite a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumFinite a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumFinite₂ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumFinite rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumFinite₂ h₀) (rw_star_sub_BlockMinimumFinite₂ h₁)
  theorem rw_star_sub_BlockMinimumFinite₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumFinite a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumFinite a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumFinite₃ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumFinite₃ h₀) (rw_star_sub_BlockMinimumFinite₃ h₁)
  theorem rw_star_sub_BlockMinimumFinite₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumFinite a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumFinite a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumFinite₄ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumFinite₄ h₀) (rw_star_sub_BlockMinimumFinite₄ h₁)
  theorem rw_star_sub_BlockMinimumFinite₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumFinite₅ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumFinite₅ h₀) (rw_star_sub_BlockMinimumFinite₅ h₁)
  theorem rw_star_sub_BlockMinimumFinite₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumFinite₆ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumFinite₆ h₀) (rw_star_sub_BlockMinimumFinite₆ h₁)
  theorem rw_star_sub_BlockMinimumFinite₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumFinite₇ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumFinite₇ h₀) (rw_star_sub_BlockMinimumFinite₇ h₁)
  theorem rw_star_sub_BlockMinimumFinite₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a b : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumFinite₈ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) h (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumFinite₈ h₀) (rw_star_sub_BlockMinimumFinite₈ h₁)
  theorem rw_star_sub_BlockMinimumFinite₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a b : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂).rw_star (BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumFinite₉ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl h rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumFinite₉ h₀) (rw_star_sub_BlockMinimumFinite₉ h₁)
  theorem rw_star_sub_BlockMinimumFinite₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂).rw_star (BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumFinite₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumFinite₁₀ h₀) (rw_star_sub_BlockMinimumFinite₁₀ h₁)
  theorem rw_star_sub_BlockMinimumFinite₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂).rw_star (BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | .step h => .step (rw_one.sub_BlockMinimumFinite₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumFinite₁₁ h₀) (rw_star_sub_BlockMinimumFinite₁₁ h₁)
  theorem rw_star_sub_BlockMinimumFinite₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a).rw_star (BlockMinimumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | .step h => .step (rw_one.sub_BlockMinimumFinite₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockMinimumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMinimumFinite₁₂ h₀) (rw_star_sub_BlockMinimumFinite₁₂ h₁)
  theorem rw_star_sub_BlockMaximumFinite₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMaximumFinite a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumFinite b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumFinite₀ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumFinite h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumFinite₀ h₀) (rw_star_sub_BlockMaximumFinite₀ h₁)
  theorem rw_star_sub_BlockMaximumFinite₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumFinite a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumFinite a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumFinite₁ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumFinite rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumFinite₁ h₀) (rw_star_sub_BlockMaximumFinite₁ h₁)
  theorem rw_star_sub_BlockMaximumFinite₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumFinite a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumFinite a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumFinite₂ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumFinite rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumFinite₂ h₀) (rw_star_sub_BlockMaximumFinite₂ h₁)
  theorem rw_star_sub_BlockMaximumFinite₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumFinite a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumFinite a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumFinite₃ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumFinite₃ h₀) (rw_star_sub_BlockMaximumFinite₃ h₁)
  theorem rw_star_sub_BlockMaximumFinite₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumFinite a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumFinite a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumFinite₄ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumFinite₄ h₀) (rw_star_sub_BlockMaximumFinite₄ h₁)
  theorem rw_star_sub_BlockMaximumFinite₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumFinite₅ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumFinite₅ h₀) (rw_star_sub_BlockMaximumFinite₅ h₁)
  theorem rw_star_sub_BlockMaximumFinite₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumFinite₆ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumFinite₆ h₀) (rw_star_sub_BlockMaximumFinite₆ h₁)
  theorem rw_star_sub_BlockMaximumFinite₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumFinite₇ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumFinite₇ h₀) (rw_star_sub_BlockMaximumFinite₇ h₁)
  theorem rw_star_sub_BlockMaximumFinite₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a b : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumFinite₈ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) h (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumFinite₈ h₀) (rw_star_sub_BlockMaximumFinite₈ h₁)
  theorem rw_star_sub_BlockMaximumFinite₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a b : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂).rw_star (BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumFinite₉ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl h rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumFinite₉ h₀) (rw_star_sub_BlockMaximumFinite₉ h₁)
  theorem rw_star_sub_BlockMaximumFinite₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂).rw_star (BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumFinite₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumFinite₁₀ h₀) (rw_star_sub_BlockMaximumFinite₁₀ h₁)
  theorem rw_star_sub_BlockMaximumFinite₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂).rw_star (BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | .step h => .step (rw_one.sub_BlockMaximumFinite₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumFinite₁₁ h₀) (rw_star_sub_BlockMaximumFinite₁₁ h₁)
  theorem rw_star_sub_BlockMaximumFinite₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a).rw_star (BlockMaximumFinite a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | .step h => .step (rw_one.sub_BlockMaximumFinite₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockMaximumFinite rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockMaximumFinite₁₂ h₀) (rw_star_sub_BlockMaximumFinite₁₂ h₁)
  theorem rw_star_sub_BlockClamp₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : MRat.rw_star a b →
      (BlockClamp a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockClamp b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockClamp₀ h)
    | .refl h => .refl (eqe.eqe_BlockClamp h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockClamp₀ h₀) (rw_star_sub_BlockClamp₀ h₁)
  theorem rw_star_sub_BlockClamp₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockClamp a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockClamp a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockClamp₁ h)
    | .refl h => .refl (eqe.eqe_BlockClamp rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockClamp₁ h₀) (rw_star_sub_BlockClamp₁ h₁)
  theorem rw_star_sub_BlockClamp₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockClamp a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockClamp a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockClamp₂ h)
    | .refl h => .refl (eqe.eqe_BlockClamp rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockClamp₂ h₀) (rw_star_sub_BlockClamp₂ h₁)
  theorem rw_star_sub_BlockClamp₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockClamp a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockClamp a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockClamp₃ h)
    | .refl h => .refl (eqe.eqe_BlockClamp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockClamp₃ h₀) (rw_star_sub_BlockClamp₃ h₁)
  theorem rw_star_sub_BlockClamp₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockClamp a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockClamp a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockClamp₄ h)
    | .refl h => .refl (eqe.eqe_BlockClamp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockClamp₄ h₀) (rw_star_sub_BlockClamp₄ h₁)
  theorem rw_star_sub_BlockClamp₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockClamp a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockClamp a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockClamp₅ h)
    | .refl h => .refl (eqe.eqe_BlockClamp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockClamp₅ h₀) (rw_star_sub_BlockClamp₅ h₁)
  theorem rw_star_sub_BlockClamp₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockClamp₆ h)
    | .refl h => .refl (eqe.eqe_BlockClamp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockClamp₆ h₀) (rw_star_sub_BlockClamp₆ h₁)
  theorem rw_star_sub_BlockClamp₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a b a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockClamp₇ h)
    | .refl h => .refl (eqe.eqe_BlockClamp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockClamp₇ h₀) (rw_star_sub_BlockClamp₇ h₁)
  theorem rw_star_sub_BlockClamp₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a b : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockClamp₈ h)
    | .refl h => .refl (eqe.eqe_BlockClamp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) h (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockClamp₈ h₀) (rw_star_sub_BlockClamp₈ h₁)
  theorem rw_star_sub_BlockClamp₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a b : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockClamp₉ h)
    | .refl h => .refl (eqe.eqe_BlockClamp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) h rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockClamp₉ h₀) (rw_star_sub_BlockClamp₉ h₁)
  theorem rw_star_sub_BlockClamp₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : MRat.rw_star a b →
      (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockClamp₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockClamp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockClamp₁₀ h₀) (rw_star_sub_BlockClamp₁₀ h₁)
  theorem rw_star_sub_BlockClamp₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂ a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂ a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockClamp₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockClamp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl h rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockClamp₁₁ h₀) (rw_star_sub_BlockClamp₁₁ h₁)
  theorem rw_star_sub_BlockClamp₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : MRat.rw_star a b →
      (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a a₁₃ a₁₄ a₁₅ a₁₆).rw_star (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b a₁₃ a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockClamp₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockClamp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockClamp₁₂ h₀) (rw_star_sub_BlockClamp₁₂ h₁)
  theorem rw_star_sub_BlockClamp₁₃ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a b : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a a₁₄ a₁₅ a₁₆).rw_star (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b a₁₄ a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockClamp₁₃ h)
    | .refl h => .refl (eqe.eqe_BlockClamp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl h rfl (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockClamp₁₃ h₀) (rw_star_sub_BlockClamp₁₃ h₁)
  theorem rw_star_sub_BlockClamp₁₄ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a b : MRat} {a₁₅ : kCodeSeq} {a₁₆ : MRat} : MRat.rw_star a b →
      (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a a₁₅ a₁₆).rw_star (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b a₁₅ a₁₆)
    | .step h => .step (rw_one.sub_BlockClamp₁₄ h)
    | .refl h => .refl (eqe.eqe_BlockClamp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) h (kCodeSeq.eqe_refl a₁₅) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockClamp₁₄ h₀) (rw_star_sub_BlockClamp₁₄ h₁)
  theorem rw_star_sub_BlockClamp₁₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a b : kCodeSeq} {a₁₆ : MRat} : a.rw_star b →
      (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a a₁₆).rw_star (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ b a₁₆)
    | .step h => .step (rw_one.sub_BlockClamp₁₅ h)
    | .refl h => .refl (eqe.eqe_BlockClamp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockClamp₁₅ h₀) (rw_star_sub_BlockClamp₁₅ h₁)
  theorem rw_star_sub_BlockClamp₁₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : kFormat} {a₉ : kBlockProjSpec} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} {a₁₃ : kCodeSeq} {a₁₄ : MRat} {a₁₅ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a).rw_star (BlockClamp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ b)
    | .step h => .step (rw_one.sub_BlockClamp₁₆ h)
    | .refl h => .refl (eqe.eqe_BlockClamp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kFormat.eqe_refl a₇) (kFormat.eqe_refl a₈) (kBlockProjSpec.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl (kCodeSeq.eqe_refl a₁₃) rfl (kCodeSeq.eqe_refl a₁₅) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockClamp₁₆ h₀) (rw_star_sub_BlockClamp₁₆ h₁)
  theorem rw_star_sub_BlockSqrt₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockSqrt a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockSqrt b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSqrt₀ h)
    | .refl h => .refl (eqe.eqe_BlockSqrt h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSqrt₀ h₀) (rw_star_sub_BlockSqrt₀ h₁)
  theorem rw_star_sub_BlockSqrt₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSqrt a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockSqrt a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSqrt₁ h)
    | .refl h => .refl (eqe.eqe_BlockSqrt rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSqrt₁ h₀) (rw_star_sub_BlockSqrt₁ h₁)
  theorem rw_star_sub_BlockSqrt₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSqrt a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockSqrt a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSqrt₂ h)
    | .refl h => .refl (eqe.eqe_BlockSqrt rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSqrt₂ h₀) (rw_star_sub_BlockSqrt₂ h₁)
  theorem rw_star_sub_BlockSqrt₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSqrt a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockSqrt a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSqrt₃ h)
    | .refl h => .refl (eqe.eqe_BlockSqrt rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSqrt₃ h₀) (rw_star_sub_BlockSqrt₃ h₁)
  theorem rw_star_sub_BlockSqrt₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSqrt a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockSqrt a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSqrt₄ h)
    | .refl h => .refl (eqe.eqe_BlockSqrt rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSqrt₄ h₀) (rw_star_sub_BlockSqrt₄ h₁)
  theorem rw_star_sub_BlockSqrt₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSqrt a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockSqrt a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSqrt₅ h)
    | .refl h => .refl (eqe.eqe_BlockSqrt rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSqrt₅ h₀) (rw_star_sub_BlockSqrt₅ h₁)
  theorem rw_star_sub_BlockSqrt₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockSqrt a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockSqrt a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSqrt₆ h)
    | .refl h => .refl (eqe.eqe_BlockSqrt rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSqrt₆ h₀) (rw_star_sub_BlockSqrt₆ h₁)
  theorem rw_star_sub_BlockSqrt₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockSqrt₇ h)
    | .refl h => .refl (eqe.eqe_BlockSqrt rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSqrt₇ h₀) (rw_star_sub_BlockSqrt₇ h₁)
  theorem rw_star_sub_BlockSqrt₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockSqrt₈ h)
    | .refl h => .refl (eqe.eqe_BlockSqrt rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSqrt₈ h₀) (rw_star_sub_BlockSqrt₈ h₁)
  theorem rw_star_sub_BlockRSqrt₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockRSqrt a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockRSqrt b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockRSqrt₀ h)
    | .refl h => .refl (eqe.eqe_BlockRSqrt h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockRSqrt₀ h₀) (rw_star_sub_BlockRSqrt₀ h₁)
  theorem rw_star_sub_BlockRSqrt₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockRSqrt a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockRSqrt a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockRSqrt₁ h)
    | .refl h => .refl (eqe.eqe_BlockRSqrt rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockRSqrt₁ h₀) (rw_star_sub_BlockRSqrt₁ h₁)
  theorem rw_star_sub_BlockRSqrt₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockRSqrt a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockRSqrt a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockRSqrt₂ h)
    | .refl h => .refl (eqe.eqe_BlockRSqrt rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockRSqrt₂ h₀) (rw_star_sub_BlockRSqrt₂ h₁)
  theorem rw_star_sub_BlockRSqrt₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockRSqrt a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockRSqrt a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockRSqrt₃ h)
    | .refl h => .refl (eqe.eqe_BlockRSqrt rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockRSqrt₃ h₀) (rw_star_sub_BlockRSqrt₃ h₁)
  theorem rw_star_sub_BlockRSqrt₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockRSqrt a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockRSqrt a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockRSqrt₄ h)
    | .refl h => .refl (eqe.eqe_BlockRSqrt rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockRSqrt₄ h₀) (rw_star_sub_BlockRSqrt₄ h₁)
  theorem rw_star_sub_BlockRSqrt₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockRSqrt a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockRSqrt a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockRSqrt₅ h)
    | .refl h => .refl (eqe.eqe_BlockRSqrt rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockRSqrt₅ h₀) (rw_star_sub_BlockRSqrt₅ h₁)
  theorem rw_star_sub_BlockRSqrt₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockRSqrt a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockRSqrt a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockRSqrt₆ h)
    | .refl h => .refl (eqe.eqe_BlockRSqrt rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockRSqrt₆ h₀) (rw_star_sub_BlockRSqrt₆ h₁)
  theorem rw_star_sub_BlockRSqrt₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockRSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockRSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockRSqrt₇ h)
    | .refl h => .refl (eqe.eqe_BlockRSqrt rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockRSqrt₇ h₀) (rw_star_sub_BlockRSqrt₇ h₁)
  theorem rw_star_sub_BlockRSqrt₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockRSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockRSqrt a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockRSqrt₈ h)
    | .refl h => .refl (eqe.eqe_BlockRSqrt rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockRSqrt₈ h₀) (rw_star_sub_BlockRSqrt₈ h₁)
  theorem rw_star_sub_BlockExp₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockExp a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockExp b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExp₀ h)
    | .refl h => .refl (eqe.eqe_BlockExp h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExp₀ h₀) (rw_star_sub_BlockExp₀ h₁)
  theorem rw_star_sub_BlockExp₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockExp a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockExp a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExp₁ h)
    | .refl h => .refl (eqe.eqe_BlockExp rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExp₁ h₀) (rw_star_sub_BlockExp₁ h₁)
  theorem rw_star_sub_BlockExp₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockExp a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockExp a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExp₂ h)
    | .refl h => .refl (eqe.eqe_BlockExp rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExp₂ h₀) (rw_star_sub_BlockExp₂ h₁)
  theorem rw_star_sub_BlockExp₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockExp a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockExp a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExp₃ h)
    | .refl h => .refl (eqe.eqe_BlockExp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExp₃ h₀) (rw_star_sub_BlockExp₃ h₁)
  theorem rw_star_sub_BlockExp₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockExp a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockExp a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExp₄ h)
    | .refl h => .refl (eqe.eqe_BlockExp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExp₄ h₀) (rw_star_sub_BlockExp₄ h₁)
  theorem rw_star_sub_BlockExp₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockExp a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockExp a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExp₅ h)
    | .refl h => .refl (eqe.eqe_BlockExp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExp₅ h₀) (rw_star_sub_BlockExp₅ h₁)
  theorem rw_star_sub_BlockExp₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockExp a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockExp a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExp₆ h)
    | .refl h => .refl (eqe.eqe_BlockExp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExp₆ h₀) (rw_star_sub_BlockExp₆ h₁)
  theorem rw_star_sub_BlockExp₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockExp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockExp a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockExp₇ h)
    | .refl h => .refl (eqe.eqe_BlockExp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExp₇ h₀) (rw_star_sub_BlockExp₇ h₁)
  theorem rw_star_sub_BlockExp₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockExp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockExp a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockExp₈ h)
    | .refl h => .refl (eqe.eqe_BlockExp rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExp₈ h₀) (rw_star_sub_BlockExp₈ h₁)
  theorem rw_star_sub_BlockExp2₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockExp2 a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockExp2 b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExp2₀ h)
    | .refl h => .refl (eqe.eqe_BlockExp2 h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExp2₀ h₀) (rw_star_sub_BlockExp2₀ h₁)
  theorem rw_star_sub_BlockExp2₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockExp2 a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockExp2 a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExp2₁ h)
    | .refl h => .refl (eqe.eqe_BlockExp2 rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExp2₁ h₀) (rw_star_sub_BlockExp2₁ h₁)
  theorem rw_star_sub_BlockExp2₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockExp2 a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockExp2 a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExp2₂ h)
    | .refl h => .refl (eqe.eqe_BlockExp2 rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExp2₂ h₀) (rw_star_sub_BlockExp2₂ h₁)
  theorem rw_star_sub_BlockExp2₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockExp2 a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockExp2 a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExp2₃ h)
    | .refl h => .refl (eqe.eqe_BlockExp2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExp2₃ h₀) (rw_star_sub_BlockExp2₃ h₁)
  theorem rw_star_sub_BlockExp2₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockExp2 a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockExp2 a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExp2₄ h)
    | .refl h => .refl (eqe.eqe_BlockExp2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExp2₄ h₀) (rw_star_sub_BlockExp2₄ h₁)
  theorem rw_star_sub_BlockExp2₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockExp2 a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockExp2 a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExp2₅ h)
    | .refl h => .refl (eqe.eqe_BlockExp2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExp2₅ h₀) (rw_star_sub_BlockExp2₅ h₁)
  theorem rw_star_sub_BlockExp2₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockExp2 a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockExp2 a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExp2₆ h)
    | .refl h => .refl (eqe.eqe_BlockExp2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExp2₆ h₀) (rw_star_sub_BlockExp2₆ h₁)
  theorem rw_star_sub_BlockExp2₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockExp2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockExp2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockExp2₇ h)
    | .refl h => .refl (eqe.eqe_BlockExp2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExp2₇ h₀) (rw_star_sub_BlockExp2₇ h₁)
  theorem rw_star_sub_BlockExp2₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockExp2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockExp2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockExp2₈ h)
    | .refl h => .refl (eqe.eqe_BlockExp2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExp2₈ h₀) (rw_star_sub_BlockExp2₈ h₁)
  theorem rw_star_sub_BlockLog₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockLog a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockLog b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLog₀ h)
    | .refl h => .refl (eqe.eqe_BlockLog h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLog₀ h₀) (rw_star_sub_BlockLog₀ h₁)
  theorem rw_star_sub_BlockLog₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockLog a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockLog a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLog₁ h)
    | .refl h => .refl (eqe.eqe_BlockLog rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLog₁ h₀) (rw_star_sub_BlockLog₁ h₁)
  theorem rw_star_sub_BlockLog₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockLog a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockLog a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLog₂ h)
    | .refl h => .refl (eqe.eqe_BlockLog rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLog₂ h₀) (rw_star_sub_BlockLog₂ h₁)
  theorem rw_star_sub_BlockLog₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockLog a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockLog a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLog₃ h)
    | .refl h => .refl (eqe.eqe_BlockLog rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLog₃ h₀) (rw_star_sub_BlockLog₃ h₁)
  theorem rw_star_sub_BlockLog₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockLog a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockLog a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLog₄ h)
    | .refl h => .refl (eqe.eqe_BlockLog rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLog₄ h₀) (rw_star_sub_BlockLog₄ h₁)
  theorem rw_star_sub_BlockLog₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockLog a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockLog a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLog₅ h)
    | .refl h => .refl (eqe.eqe_BlockLog rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLog₅ h₀) (rw_star_sub_BlockLog₅ h₁)
  theorem rw_star_sub_BlockLog₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockLog a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockLog a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLog₆ h)
    | .refl h => .refl (eqe.eqe_BlockLog rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLog₆ h₀) (rw_star_sub_BlockLog₆ h₁)
  theorem rw_star_sub_BlockLog₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockLog a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockLog a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockLog₇ h)
    | .refl h => .refl (eqe.eqe_BlockLog rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLog₇ h₀) (rw_star_sub_BlockLog₇ h₁)
  theorem rw_star_sub_BlockLog₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockLog a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockLog a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockLog₈ h)
    | .refl h => .refl (eqe.eqe_BlockLog rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLog₈ h₀) (rw_star_sub_BlockLog₈ h₁)
  theorem rw_star_sub_BlockLog2₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockLog2 a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockLog2 b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLog2₀ h)
    | .refl h => .refl (eqe.eqe_BlockLog2 h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLog2₀ h₀) (rw_star_sub_BlockLog2₀ h₁)
  theorem rw_star_sub_BlockLog2₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockLog2 a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockLog2 a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLog2₁ h)
    | .refl h => .refl (eqe.eqe_BlockLog2 rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLog2₁ h₀) (rw_star_sub_BlockLog2₁ h₁)
  theorem rw_star_sub_BlockLog2₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockLog2 a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockLog2 a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLog2₂ h)
    | .refl h => .refl (eqe.eqe_BlockLog2 rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLog2₂ h₀) (rw_star_sub_BlockLog2₂ h₁)
  theorem rw_star_sub_BlockLog2₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockLog2 a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockLog2 a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLog2₃ h)
    | .refl h => .refl (eqe.eqe_BlockLog2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLog2₃ h₀) (rw_star_sub_BlockLog2₃ h₁)
  theorem rw_star_sub_BlockLog2₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockLog2 a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockLog2 a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLog2₄ h)
    | .refl h => .refl (eqe.eqe_BlockLog2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLog2₄ h₀) (rw_star_sub_BlockLog2₄ h₁)
  theorem rw_star_sub_BlockLog2₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockLog2 a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockLog2 a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLog2₅ h)
    | .refl h => .refl (eqe.eqe_BlockLog2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLog2₅ h₀) (rw_star_sub_BlockLog2₅ h₁)
  theorem rw_star_sub_BlockLog2₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockLog2 a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockLog2 a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLog2₆ h)
    | .refl h => .refl (eqe.eqe_BlockLog2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLog2₆ h₀) (rw_star_sub_BlockLog2₆ h₁)
  theorem rw_star_sub_BlockLog2₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockLog2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockLog2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockLog2₇ h)
    | .refl h => .refl (eqe.eqe_BlockLog2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLog2₇ h₀) (rw_star_sub_BlockLog2₇ h₁)
  theorem rw_star_sub_BlockLog2₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockLog2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockLog2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockLog2₈ h)
    | .refl h => .refl (eqe.eqe_BlockLog2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLog2₈ h₀) (rw_star_sub_BlockLog2₈ h₁)
  theorem rw_star_sub_BlockLogOnePlus₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockLogOnePlus a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockLogOnePlus b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLogOnePlus₀ h)
    | .refl h => .refl (eqe.eqe_BlockLogOnePlus h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLogOnePlus₀ h₀) (rw_star_sub_BlockLogOnePlus₀ h₁)
  theorem rw_star_sub_BlockLogOnePlus₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockLogOnePlus a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockLogOnePlus a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLogOnePlus₁ h)
    | .refl h => .refl (eqe.eqe_BlockLogOnePlus rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLogOnePlus₁ h₀) (rw_star_sub_BlockLogOnePlus₁ h₁)
  theorem rw_star_sub_BlockLogOnePlus₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockLogOnePlus a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockLogOnePlus a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLogOnePlus₂ h)
    | .refl h => .refl (eqe.eqe_BlockLogOnePlus rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLogOnePlus₂ h₀) (rw_star_sub_BlockLogOnePlus₂ h₁)
  theorem rw_star_sub_BlockLogOnePlus₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockLogOnePlus a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockLogOnePlus a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLogOnePlus₃ h)
    | .refl h => .refl (eqe.eqe_BlockLogOnePlus rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLogOnePlus₃ h₀) (rw_star_sub_BlockLogOnePlus₃ h₁)
  theorem rw_star_sub_BlockLogOnePlus₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockLogOnePlus a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockLogOnePlus a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLogOnePlus₄ h)
    | .refl h => .refl (eqe.eqe_BlockLogOnePlus rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLogOnePlus₄ h₀) (rw_star_sub_BlockLogOnePlus₄ h₁)
  theorem rw_star_sub_BlockLogOnePlus₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockLogOnePlus a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockLogOnePlus a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLogOnePlus₅ h)
    | .refl h => .refl (eqe.eqe_BlockLogOnePlus rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLogOnePlus₅ h₀) (rw_star_sub_BlockLogOnePlus₅ h₁)
  theorem rw_star_sub_BlockLogOnePlus₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockLogOnePlus a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockLogOnePlus a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockLogOnePlus₆ h)
    | .refl h => .refl (eqe.eqe_BlockLogOnePlus rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLogOnePlus₆ h₀) (rw_star_sub_BlockLogOnePlus₆ h₁)
  theorem rw_star_sub_BlockLogOnePlus₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockLogOnePlus a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockLogOnePlus a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockLogOnePlus₇ h)
    | .refl h => .refl (eqe.eqe_BlockLogOnePlus rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLogOnePlus₇ h₀) (rw_star_sub_BlockLogOnePlus₇ h₁)
  theorem rw_star_sub_BlockLogOnePlus₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockLogOnePlus a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockLogOnePlus a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockLogOnePlus₈ h)
    | .refl h => .refl (eqe.eqe_BlockLogOnePlus rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockLogOnePlus₈ h₀) (rw_star_sub_BlockLogOnePlus₈ h₁)
  theorem rw_star_sub_BlockExpMinusOne₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockExpMinusOne a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockExpMinusOne b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExpMinusOne₀ h)
    | .refl h => .refl (eqe.eqe_BlockExpMinusOne h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExpMinusOne₀ h₀) (rw_star_sub_BlockExpMinusOne₀ h₁)
  theorem rw_star_sub_BlockExpMinusOne₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockExpMinusOne a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockExpMinusOne a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExpMinusOne₁ h)
    | .refl h => .refl (eqe.eqe_BlockExpMinusOne rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExpMinusOne₁ h₀) (rw_star_sub_BlockExpMinusOne₁ h₁)
  theorem rw_star_sub_BlockExpMinusOne₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockExpMinusOne a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockExpMinusOne a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExpMinusOne₂ h)
    | .refl h => .refl (eqe.eqe_BlockExpMinusOne rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExpMinusOne₂ h₀) (rw_star_sub_BlockExpMinusOne₂ h₁)
  theorem rw_star_sub_BlockExpMinusOne₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockExpMinusOne a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockExpMinusOne a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExpMinusOne₃ h)
    | .refl h => .refl (eqe.eqe_BlockExpMinusOne rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExpMinusOne₃ h₀) (rw_star_sub_BlockExpMinusOne₃ h₁)
  theorem rw_star_sub_BlockExpMinusOne₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockExpMinusOne a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockExpMinusOne a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExpMinusOne₄ h)
    | .refl h => .refl (eqe.eqe_BlockExpMinusOne rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExpMinusOne₄ h₀) (rw_star_sub_BlockExpMinusOne₄ h₁)
  theorem rw_star_sub_BlockExpMinusOne₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockExpMinusOne a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockExpMinusOne a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExpMinusOne₅ h)
    | .refl h => .refl (eqe.eqe_BlockExpMinusOne rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExpMinusOne₅ h₀) (rw_star_sub_BlockExpMinusOne₅ h₁)
  theorem rw_star_sub_BlockExpMinusOne₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockExpMinusOne a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockExpMinusOne a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockExpMinusOne₆ h)
    | .refl h => .refl (eqe.eqe_BlockExpMinusOne rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExpMinusOne₆ h₀) (rw_star_sub_BlockExpMinusOne₆ h₁)
  theorem rw_star_sub_BlockExpMinusOne₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockExpMinusOne a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockExpMinusOne a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockExpMinusOne₇ h)
    | .refl h => .refl (eqe.eqe_BlockExpMinusOne rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExpMinusOne₇ h₀) (rw_star_sub_BlockExpMinusOne₇ h₁)
  theorem rw_star_sub_BlockExpMinusOne₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockExpMinusOne a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockExpMinusOne a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockExpMinusOne₈ h)
    | .refl h => .refl (eqe.eqe_BlockExpMinusOne rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockExpMinusOne₈ h₀) (rw_star_sub_BlockExpMinusOne₈ h₁)
  theorem rw_star_sub_BlockSin₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockSin a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockSin b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSin₀ h)
    | .refl h => .refl (eqe.eqe_BlockSin h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSin₀ h₀) (rw_star_sub_BlockSin₀ h₁)
  theorem rw_star_sub_BlockSin₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSin a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockSin a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSin₁ h)
    | .refl h => .refl (eqe.eqe_BlockSin rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSin₁ h₀) (rw_star_sub_BlockSin₁ h₁)
  theorem rw_star_sub_BlockSin₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSin a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockSin a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSin₂ h)
    | .refl h => .refl (eqe.eqe_BlockSin rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSin₂ h₀) (rw_star_sub_BlockSin₂ h₁)
  theorem rw_star_sub_BlockSin₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSin a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockSin a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSin₃ h)
    | .refl h => .refl (eqe.eqe_BlockSin rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSin₃ h₀) (rw_star_sub_BlockSin₃ h₁)
  theorem rw_star_sub_BlockSin₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSin a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockSin a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSin₄ h)
    | .refl h => .refl (eqe.eqe_BlockSin rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSin₄ h₀) (rw_star_sub_BlockSin₄ h₁)
  theorem rw_star_sub_BlockSin₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSin a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockSin a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSin₅ h)
    | .refl h => .refl (eqe.eqe_BlockSin rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSin₅ h₀) (rw_star_sub_BlockSin₅ h₁)
  theorem rw_star_sub_BlockSin₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockSin a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockSin a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSin₆ h)
    | .refl h => .refl (eqe.eqe_BlockSin rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSin₆ h₀) (rw_star_sub_BlockSin₆ h₁)
  theorem rw_star_sub_BlockSin₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockSin₇ h)
    | .refl h => .refl (eqe.eqe_BlockSin rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSin₇ h₀) (rw_star_sub_BlockSin₇ h₁)
  theorem rw_star_sub_BlockSin₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockSin₈ h)
    | .refl h => .refl (eqe.eqe_BlockSin rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSin₈ h₀) (rw_star_sub_BlockSin₈ h₁)
  theorem rw_star_sub_BlockCos₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockCos a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockCos b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCos₀ h)
    | .refl h => .refl (eqe.eqe_BlockCos h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCos₀ h₀) (rw_star_sub_BlockCos₀ h₁)
  theorem rw_star_sub_BlockCos₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockCos a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockCos a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCos₁ h)
    | .refl h => .refl (eqe.eqe_BlockCos rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCos₁ h₀) (rw_star_sub_BlockCos₁ h₁)
  theorem rw_star_sub_BlockCos₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockCos a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockCos a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCos₂ h)
    | .refl h => .refl (eqe.eqe_BlockCos rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCos₂ h₀) (rw_star_sub_BlockCos₂ h₁)
  theorem rw_star_sub_BlockCos₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockCos a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockCos a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCos₃ h)
    | .refl h => .refl (eqe.eqe_BlockCos rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCos₃ h₀) (rw_star_sub_BlockCos₃ h₁)
  theorem rw_star_sub_BlockCos₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockCos a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockCos a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCos₄ h)
    | .refl h => .refl (eqe.eqe_BlockCos rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCos₄ h₀) (rw_star_sub_BlockCos₄ h₁)
  theorem rw_star_sub_BlockCos₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockCos a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockCos a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCos₅ h)
    | .refl h => .refl (eqe.eqe_BlockCos rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCos₅ h₀) (rw_star_sub_BlockCos₅ h₁)
  theorem rw_star_sub_BlockCos₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockCos a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockCos a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCos₆ h)
    | .refl h => .refl (eqe.eqe_BlockCos rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCos₆ h₀) (rw_star_sub_BlockCos₆ h₁)
  theorem rw_star_sub_BlockCos₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockCos₇ h)
    | .refl h => .refl (eqe.eqe_BlockCos rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCos₇ h₀) (rw_star_sub_BlockCos₇ h₁)
  theorem rw_star_sub_BlockCos₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockCos₈ h)
    | .refl h => .refl (eqe.eqe_BlockCos rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCos₈ h₀) (rw_star_sub_BlockCos₈ h₁)
  theorem rw_star_sub_BlockTan₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockTan a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockTan b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTan₀ h)
    | .refl h => .refl (eqe.eqe_BlockTan h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTan₀ h₀) (rw_star_sub_BlockTan₀ h₁)
  theorem rw_star_sub_BlockTan₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockTan a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockTan a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTan₁ h)
    | .refl h => .refl (eqe.eqe_BlockTan rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTan₁ h₀) (rw_star_sub_BlockTan₁ h₁)
  theorem rw_star_sub_BlockTan₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockTan a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockTan a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTan₂ h)
    | .refl h => .refl (eqe.eqe_BlockTan rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTan₂ h₀) (rw_star_sub_BlockTan₂ h₁)
  theorem rw_star_sub_BlockTan₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockTan a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockTan a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTan₃ h)
    | .refl h => .refl (eqe.eqe_BlockTan rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTan₃ h₀) (rw_star_sub_BlockTan₃ h₁)
  theorem rw_star_sub_BlockTan₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockTan a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockTan a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTan₄ h)
    | .refl h => .refl (eqe.eqe_BlockTan rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTan₄ h₀) (rw_star_sub_BlockTan₄ h₁)
  theorem rw_star_sub_BlockTan₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockTan a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockTan a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTan₅ h)
    | .refl h => .refl (eqe.eqe_BlockTan rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTan₅ h₀) (rw_star_sub_BlockTan₅ h₁)
  theorem rw_star_sub_BlockTan₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockTan a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockTan a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTan₆ h)
    | .refl h => .refl (eqe.eqe_BlockTan rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTan₆ h₀) (rw_star_sub_BlockTan₆ h₁)
  theorem rw_star_sub_BlockTan₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockTan₇ h)
    | .refl h => .refl (eqe.eqe_BlockTan rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTan₇ h₀) (rw_star_sub_BlockTan₇ h₁)
  theorem rw_star_sub_BlockTan₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockTan₈ h)
    | .refl h => .refl (eqe.eqe_BlockTan rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTan₈ h₀) (rw_star_sub_BlockTan₈ h₁)
  theorem rw_star_sub_BlockArcSin₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockArcSin a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcSin b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSin₀ h)
    | .refl h => .refl (eqe.eqe_BlockArcSin h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSin₀ h₀) (rw_star_sub_BlockArcSin₀ h₁)
  theorem rw_star_sub_BlockArcSin₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcSin a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcSin a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSin₁ h)
    | .refl h => .refl (eqe.eqe_BlockArcSin rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSin₁ h₀) (rw_star_sub_BlockArcSin₁ h₁)
  theorem rw_star_sub_BlockArcSin₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcSin a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcSin a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSin₂ h)
    | .refl h => .refl (eqe.eqe_BlockArcSin rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSin₂ h₀) (rw_star_sub_BlockArcSin₂ h₁)
  theorem rw_star_sub_BlockArcSin₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcSin a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcSin a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSin₃ h)
    | .refl h => .refl (eqe.eqe_BlockArcSin rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSin₃ h₀) (rw_star_sub_BlockArcSin₃ h₁)
  theorem rw_star_sub_BlockArcSin₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcSin a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockArcSin a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSin₄ h)
    | .refl h => .refl (eqe.eqe_BlockArcSin rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSin₄ h₀) (rw_star_sub_BlockArcSin₄ h₁)
  theorem rw_star_sub_BlockArcSin₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcSin a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockArcSin a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSin₅ h)
    | .refl h => .refl (eqe.eqe_BlockArcSin rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSin₅ h₀) (rw_star_sub_BlockArcSin₅ h₁)
  theorem rw_star_sub_BlockArcSin₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockArcSin a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockArcSin a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSin₆ h)
    | .refl h => .refl (eqe.eqe_BlockArcSin rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSin₆ h₀) (rw_star_sub_BlockArcSin₆ h₁)
  theorem rw_star_sub_BlockArcSin₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockArcSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockArcSin₇ h)
    | .refl h => .refl (eqe.eqe_BlockArcSin rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSin₇ h₀) (rw_star_sub_BlockArcSin₇ h₁)
  theorem rw_star_sub_BlockArcSin₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockArcSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockArcSin a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockArcSin₈ h)
    | .refl h => .refl (eqe.eqe_BlockArcSin rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSin₈ h₀) (rw_star_sub_BlockArcSin₈ h₁)
  theorem rw_star_sub_BlockArcCos₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockArcCos a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcCos b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCos₀ h)
    | .refl h => .refl (eqe.eqe_BlockArcCos h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCos₀ h₀) (rw_star_sub_BlockArcCos₀ h₁)
  theorem rw_star_sub_BlockArcCos₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcCos a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcCos a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCos₁ h)
    | .refl h => .refl (eqe.eqe_BlockArcCos rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCos₁ h₀) (rw_star_sub_BlockArcCos₁ h₁)
  theorem rw_star_sub_BlockArcCos₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcCos a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcCos a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCos₂ h)
    | .refl h => .refl (eqe.eqe_BlockArcCos rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCos₂ h₀) (rw_star_sub_BlockArcCos₂ h₁)
  theorem rw_star_sub_BlockArcCos₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcCos a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcCos a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCos₃ h)
    | .refl h => .refl (eqe.eqe_BlockArcCos rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCos₃ h₀) (rw_star_sub_BlockArcCos₃ h₁)
  theorem rw_star_sub_BlockArcCos₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcCos a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockArcCos a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCos₄ h)
    | .refl h => .refl (eqe.eqe_BlockArcCos rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCos₄ h₀) (rw_star_sub_BlockArcCos₄ h₁)
  theorem rw_star_sub_BlockArcCos₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcCos a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockArcCos a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCos₅ h)
    | .refl h => .refl (eqe.eqe_BlockArcCos rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCos₅ h₀) (rw_star_sub_BlockArcCos₅ h₁)
  theorem rw_star_sub_BlockArcCos₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockArcCos a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockArcCos a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCos₆ h)
    | .refl h => .refl (eqe.eqe_BlockArcCos rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCos₆ h₀) (rw_star_sub_BlockArcCos₆ h₁)
  theorem rw_star_sub_BlockArcCos₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockArcCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockArcCos₇ h)
    | .refl h => .refl (eqe.eqe_BlockArcCos rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCos₇ h₀) (rw_star_sub_BlockArcCos₇ h₁)
  theorem rw_star_sub_BlockArcCos₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockArcCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockArcCos a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockArcCos₈ h)
    | .refl h => .refl (eqe.eqe_BlockArcCos rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCos₈ h₀) (rw_star_sub_BlockArcCos₈ h₁)
  theorem rw_star_sub_BlockArcTan₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockArcTan a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcTan b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTan₀ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan₀ h₀) (rw_star_sub_BlockArcTan₀ h₁)
  theorem rw_star_sub_BlockArcTan₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcTan a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcTan a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTan₁ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan₁ h₀) (rw_star_sub_BlockArcTan₁ h₁)
  theorem rw_star_sub_BlockArcTan₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcTan a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcTan a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTan₂ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan₂ h₀) (rw_star_sub_BlockArcTan₂ h₁)
  theorem rw_star_sub_BlockArcTan₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcTan a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcTan a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTan₃ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan₃ h₀) (rw_star_sub_BlockArcTan₃ h₁)
  theorem rw_star_sub_BlockArcTan₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcTan a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockArcTan a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTan₄ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan₄ h₀) (rw_star_sub_BlockArcTan₄ h₁)
  theorem rw_star_sub_BlockArcTan₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcTan a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockArcTan a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTan₅ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan₅ h₀) (rw_star_sub_BlockArcTan₅ h₁)
  theorem rw_star_sub_BlockArcTan₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockArcTan a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockArcTan a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTan₆ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan₆ h₀) (rw_star_sub_BlockArcTan₆ h₁)
  theorem rw_star_sub_BlockArcTan₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockArcTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockArcTan₇ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan₇ h₀) (rw_star_sub_BlockArcTan₇ h₁)
  theorem rw_star_sub_BlockArcTan₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockArcTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockArcTan a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockArcTan₈ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan₈ h₀) (rw_star_sub_BlockArcTan₈ h₁)
  theorem rw_star_sub_BlockSinh₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockSinh a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockSinh b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSinh₀ h)
    | .refl h => .refl (eqe.eqe_BlockSinh h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSinh₀ h₀) (rw_star_sub_BlockSinh₀ h₁)
  theorem rw_star_sub_BlockSinh₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSinh a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockSinh a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSinh₁ h)
    | .refl h => .refl (eqe.eqe_BlockSinh rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSinh₁ h₀) (rw_star_sub_BlockSinh₁ h₁)
  theorem rw_star_sub_BlockSinh₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSinh a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockSinh a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSinh₂ h)
    | .refl h => .refl (eqe.eqe_BlockSinh rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSinh₂ h₀) (rw_star_sub_BlockSinh₂ h₁)
  theorem rw_star_sub_BlockSinh₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSinh a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockSinh a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSinh₃ h)
    | .refl h => .refl (eqe.eqe_BlockSinh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSinh₃ h₀) (rw_star_sub_BlockSinh₃ h₁)
  theorem rw_star_sub_BlockSinh₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSinh a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockSinh a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSinh₄ h)
    | .refl h => .refl (eqe.eqe_BlockSinh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSinh₄ h₀) (rw_star_sub_BlockSinh₄ h₁)
  theorem rw_star_sub_BlockSinh₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSinh a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockSinh a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSinh₅ h)
    | .refl h => .refl (eqe.eqe_BlockSinh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSinh₅ h₀) (rw_star_sub_BlockSinh₅ h₁)
  theorem rw_star_sub_BlockSinh₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockSinh a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockSinh a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSinh₆ h)
    | .refl h => .refl (eqe.eqe_BlockSinh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSinh₆ h₀) (rw_star_sub_BlockSinh₆ h₁)
  theorem rw_star_sub_BlockSinh₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockSinh₇ h)
    | .refl h => .refl (eqe.eqe_BlockSinh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSinh₇ h₀) (rw_star_sub_BlockSinh₇ h₁)
  theorem rw_star_sub_BlockSinh₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockSinh₈ h)
    | .refl h => .refl (eqe.eqe_BlockSinh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSinh₈ h₀) (rw_star_sub_BlockSinh₈ h₁)
  theorem rw_star_sub_BlockCosh₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockCosh a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockCosh b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCosh₀ h)
    | .refl h => .refl (eqe.eqe_BlockCosh h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCosh₀ h₀) (rw_star_sub_BlockCosh₀ h₁)
  theorem rw_star_sub_BlockCosh₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockCosh a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockCosh a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCosh₁ h)
    | .refl h => .refl (eqe.eqe_BlockCosh rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCosh₁ h₀) (rw_star_sub_BlockCosh₁ h₁)
  theorem rw_star_sub_BlockCosh₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockCosh a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockCosh a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCosh₂ h)
    | .refl h => .refl (eqe.eqe_BlockCosh rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCosh₂ h₀) (rw_star_sub_BlockCosh₂ h₁)
  theorem rw_star_sub_BlockCosh₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockCosh a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockCosh a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCosh₃ h)
    | .refl h => .refl (eqe.eqe_BlockCosh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCosh₃ h₀) (rw_star_sub_BlockCosh₃ h₁)
  theorem rw_star_sub_BlockCosh₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockCosh a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockCosh a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCosh₄ h)
    | .refl h => .refl (eqe.eqe_BlockCosh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCosh₄ h₀) (rw_star_sub_BlockCosh₄ h₁)
  theorem rw_star_sub_BlockCosh₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockCosh a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockCosh a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCosh₅ h)
    | .refl h => .refl (eqe.eqe_BlockCosh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCosh₅ h₀) (rw_star_sub_BlockCosh₅ h₁)
  theorem rw_star_sub_BlockCosh₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockCosh a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockCosh a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCosh₆ h)
    | .refl h => .refl (eqe.eqe_BlockCosh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCosh₆ h₀) (rw_star_sub_BlockCosh₆ h₁)
  theorem rw_star_sub_BlockCosh₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockCosh₇ h)
    | .refl h => .refl (eqe.eqe_BlockCosh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCosh₇ h₀) (rw_star_sub_BlockCosh₇ h₁)
  theorem rw_star_sub_BlockCosh₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockCosh₈ h)
    | .refl h => .refl (eqe.eqe_BlockCosh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCosh₈ h₀) (rw_star_sub_BlockCosh₈ h₁)
  theorem rw_star_sub_BlockTanh₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockTanh a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockTanh b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTanh₀ h)
    | .refl h => .refl (eqe.eqe_BlockTanh h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTanh₀ h₀) (rw_star_sub_BlockTanh₀ h₁)
  theorem rw_star_sub_BlockTanh₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockTanh a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockTanh a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTanh₁ h)
    | .refl h => .refl (eqe.eqe_BlockTanh rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTanh₁ h₀) (rw_star_sub_BlockTanh₁ h₁)
  theorem rw_star_sub_BlockTanh₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockTanh a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockTanh a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTanh₂ h)
    | .refl h => .refl (eqe.eqe_BlockTanh rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTanh₂ h₀) (rw_star_sub_BlockTanh₂ h₁)
  theorem rw_star_sub_BlockTanh₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockTanh a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockTanh a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTanh₃ h)
    | .refl h => .refl (eqe.eqe_BlockTanh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTanh₃ h₀) (rw_star_sub_BlockTanh₃ h₁)
  theorem rw_star_sub_BlockTanh₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockTanh a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockTanh a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTanh₄ h)
    | .refl h => .refl (eqe.eqe_BlockTanh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTanh₄ h₀) (rw_star_sub_BlockTanh₄ h₁)
  theorem rw_star_sub_BlockTanh₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockTanh a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockTanh a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTanh₅ h)
    | .refl h => .refl (eqe.eqe_BlockTanh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTanh₅ h₀) (rw_star_sub_BlockTanh₅ h₁)
  theorem rw_star_sub_BlockTanh₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockTanh a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockTanh a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTanh₆ h)
    | .refl h => .refl (eqe.eqe_BlockTanh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTanh₆ h₀) (rw_star_sub_BlockTanh₆ h₁)
  theorem rw_star_sub_BlockTanh₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockTanh₇ h)
    | .refl h => .refl (eqe.eqe_BlockTanh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTanh₇ h₀) (rw_star_sub_BlockTanh₇ h₁)
  theorem rw_star_sub_BlockTanh₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockTanh₈ h)
    | .refl h => .refl (eqe.eqe_BlockTanh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTanh₈ h₀) (rw_star_sub_BlockTanh₈ h₁)
  theorem rw_star_sub_BlockArcSinh₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockArcSinh a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcSinh b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSinh₀ h)
    | .refl h => .refl (eqe.eqe_BlockArcSinh h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSinh₀ h₀) (rw_star_sub_BlockArcSinh₀ h₁)
  theorem rw_star_sub_BlockArcSinh₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcSinh a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcSinh a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSinh₁ h)
    | .refl h => .refl (eqe.eqe_BlockArcSinh rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSinh₁ h₀) (rw_star_sub_BlockArcSinh₁ h₁)
  theorem rw_star_sub_BlockArcSinh₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcSinh a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcSinh a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSinh₂ h)
    | .refl h => .refl (eqe.eqe_BlockArcSinh rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSinh₂ h₀) (rw_star_sub_BlockArcSinh₂ h₁)
  theorem rw_star_sub_BlockArcSinh₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcSinh a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcSinh a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSinh₃ h)
    | .refl h => .refl (eqe.eqe_BlockArcSinh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSinh₃ h₀) (rw_star_sub_BlockArcSinh₃ h₁)
  theorem rw_star_sub_BlockArcSinh₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcSinh a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockArcSinh a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSinh₄ h)
    | .refl h => .refl (eqe.eqe_BlockArcSinh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSinh₄ h₀) (rw_star_sub_BlockArcSinh₄ h₁)
  theorem rw_star_sub_BlockArcSinh₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcSinh a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockArcSinh a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSinh₅ h)
    | .refl h => .refl (eqe.eqe_BlockArcSinh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSinh₅ h₀) (rw_star_sub_BlockArcSinh₅ h₁)
  theorem rw_star_sub_BlockArcSinh₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockArcSinh a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockArcSinh a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSinh₆ h)
    | .refl h => .refl (eqe.eqe_BlockArcSinh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSinh₆ h₀) (rw_star_sub_BlockArcSinh₆ h₁)
  theorem rw_star_sub_BlockArcSinh₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockArcSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockArcSinh₇ h)
    | .refl h => .refl (eqe.eqe_BlockArcSinh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSinh₇ h₀) (rw_star_sub_BlockArcSinh₇ h₁)
  theorem rw_star_sub_BlockArcSinh₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockArcSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockArcSinh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockArcSinh₈ h)
    | .refl h => .refl (eqe.eqe_BlockArcSinh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSinh₈ h₀) (rw_star_sub_BlockArcSinh₈ h₁)
  theorem rw_star_sub_BlockArcCosh₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockArcCosh a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcCosh b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCosh₀ h)
    | .refl h => .refl (eqe.eqe_BlockArcCosh h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCosh₀ h₀) (rw_star_sub_BlockArcCosh₀ h₁)
  theorem rw_star_sub_BlockArcCosh₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcCosh a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcCosh a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCosh₁ h)
    | .refl h => .refl (eqe.eqe_BlockArcCosh rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCosh₁ h₀) (rw_star_sub_BlockArcCosh₁ h₁)
  theorem rw_star_sub_BlockArcCosh₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcCosh a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcCosh a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCosh₂ h)
    | .refl h => .refl (eqe.eqe_BlockArcCosh rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCosh₂ h₀) (rw_star_sub_BlockArcCosh₂ h₁)
  theorem rw_star_sub_BlockArcCosh₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcCosh a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcCosh a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCosh₃ h)
    | .refl h => .refl (eqe.eqe_BlockArcCosh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCosh₃ h₀) (rw_star_sub_BlockArcCosh₃ h₁)
  theorem rw_star_sub_BlockArcCosh₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcCosh a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockArcCosh a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCosh₄ h)
    | .refl h => .refl (eqe.eqe_BlockArcCosh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCosh₄ h₀) (rw_star_sub_BlockArcCosh₄ h₁)
  theorem rw_star_sub_BlockArcCosh₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcCosh a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockArcCosh a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCosh₅ h)
    | .refl h => .refl (eqe.eqe_BlockArcCosh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCosh₅ h₀) (rw_star_sub_BlockArcCosh₅ h₁)
  theorem rw_star_sub_BlockArcCosh₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockArcCosh a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockArcCosh a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCosh₆ h)
    | .refl h => .refl (eqe.eqe_BlockArcCosh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCosh₆ h₀) (rw_star_sub_BlockArcCosh₆ h₁)
  theorem rw_star_sub_BlockArcCosh₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockArcCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockArcCosh₇ h)
    | .refl h => .refl (eqe.eqe_BlockArcCosh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCosh₇ h₀) (rw_star_sub_BlockArcCosh₇ h₁)
  theorem rw_star_sub_BlockArcCosh₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockArcCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockArcCosh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockArcCosh₈ h)
    | .refl h => .refl (eqe.eqe_BlockArcCosh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCosh₈ h₀) (rw_star_sub_BlockArcCosh₈ h₁)
  theorem rw_star_sub_BlockArcTanh₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockArcTanh a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcTanh b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTanh₀ h)
    | .refl h => .refl (eqe.eqe_BlockArcTanh h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTanh₀ h₀) (rw_star_sub_BlockArcTanh₀ h₁)
  theorem rw_star_sub_BlockArcTanh₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcTanh a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcTanh a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTanh₁ h)
    | .refl h => .refl (eqe.eqe_BlockArcTanh rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTanh₁ h₀) (rw_star_sub_BlockArcTanh₁ h₁)
  theorem rw_star_sub_BlockArcTanh₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcTanh a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcTanh a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTanh₂ h)
    | .refl h => .refl (eqe.eqe_BlockArcTanh rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTanh₂ h₀) (rw_star_sub_BlockArcTanh₂ h₁)
  theorem rw_star_sub_BlockArcTanh₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcTanh a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcTanh a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTanh₃ h)
    | .refl h => .refl (eqe.eqe_BlockArcTanh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTanh₃ h₀) (rw_star_sub_BlockArcTanh₃ h₁)
  theorem rw_star_sub_BlockArcTanh₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcTanh a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockArcTanh a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTanh₄ h)
    | .refl h => .refl (eqe.eqe_BlockArcTanh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTanh₄ h₀) (rw_star_sub_BlockArcTanh₄ h₁)
  theorem rw_star_sub_BlockArcTanh₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcTanh a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockArcTanh a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTanh₅ h)
    | .refl h => .refl (eqe.eqe_BlockArcTanh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTanh₅ h₀) (rw_star_sub_BlockArcTanh₅ h₁)
  theorem rw_star_sub_BlockArcTanh₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockArcTanh a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockArcTanh a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTanh₆ h)
    | .refl h => .refl (eqe.eqe_BlockArcTanh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTanh₆ h₀) (rw_star_sub_BlockArcTanh₆ h₁)
  theorem rw_star_sub_BlockArcTanh₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockArcTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockArcTanh₇ h)
    | .refl h => .refl (eqe.eqe_BlockArcTanh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTanh₇ h₀) (rw_star_sub_BlockArcTanh₇ h₁)
  theorem rw_star_sub_BlockArcTanh₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockArcTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockArcTanh a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockArcTanh₈ h)
    | .refl h => .refl (eqe.eqe_BlockArcTanh rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTanh₈ h₀) (rw_star_sub_BlockArcTanh₈ h₁)
  theorem rw_star_sub_BlockSinPi₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockSinPi a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockSinPi b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSinPi₀ h)
    | .refl h => .refl (eqe.eqe_BlockSinPi h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSinPi₀ h₀) (rw_star_sub_BlockSinPi₀ h₁)
  theorem rw_star_sub_BlockSinPi₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSinPi a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockSinPi a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSinPi₁ h)
    | .refl h => .refl (eqe.eqe_BlockSinPi rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSinPi₁ h₀) (rw_star_sub_BlockSinPi₁ h₁)
  theorem rw_star_sub_BlockSinPi₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSinPi a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockSinPi a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSinPi₂ h)
    | .refl h => .refl (eqe.eqe_BlockSinPi rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSinPi₂ h₀) (rw_star_sub_BlockSinPi₂ h₁)
  theorem rw_star_sub_BlockSinPi₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSinPi a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockSinPi a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSinPi₃ h)
    | .refl h => .refl (eqe.eqe_BlockSinPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSinPi₃ h₀) (rw_star_sub_BlockSinPi₃ h₁)
  theorem rw_star_sub_BlockSinPi₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSinPi a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockSinPi a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSinPi₄ h)
    | .refl h => .refl (eqe.eqe_BlockSinPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSinPi₄ h₀) (rw_star_sub_BlockSinPi₄ h₁)
  theorem rw_star_sub_BlockSinPi₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSinPi a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockSinPi a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSinPi₅ h)
    | .refl h => .refl (eqe.eqe_BlockSinPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSinPi₅ h₀) (rw_star_sub_BlockSinPi₅ h₁)
  theorem rw_star_sub_BlockSinPi₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockSinPi a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockSinPi a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSinPi₆ h)
    | .refl h => .refl (eqe.eqe_BlockSinPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSinPi₆ h₀) (rw_star_sub_BlockSinPi₆ h₁)
  theorem rw_star_sub_BlockSinPi₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockSinPi₇ h)
    | .refl h => .refl (eqe.eqe_BlockSinPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSinPi₇ h₀) (rw_star_sub_BlockSinPi₇ h₁)
  theorem rw_star_sub_BlockSinPi₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockSinPi₈ h)
    | .refl h => .refl (eqe.eqe_BlockSinPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSinPi₈ h₀) (rw_star_sub_BlockSinPi₈ h₁)
  theorem rw_star_sub_BlockCosPi₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockCosPi a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockCosPi b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCosPi₀ h)
    | .refl h => .refl (eqe.eqe_BlockCosPi h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCosPi₀ h₀) (rw_star_sub_BlockCosPi₀ h₁)
  theorem rw_star_sub_BlockCosPi₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockCosPi a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockCosPi a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCosPi₁ h)
    | .refl h => .refl (eqe.eqe_BlockCosPi rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCosPi₁ h₀) (rw_star_sub_BlockCosPi₁ h₁)
  theorem rw_star_sub_BlockCosPi₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockCosPi a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockCosPi a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCosPi₂ h)
    | .refl h => .refl (eqe.eqe_BlockCosPi rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCosPi₂ h₀) (rw_star_sub_BlockCosPi₂ h₁)
  theorem rw_star_sub_BlockCosPi₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockCosPi a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockCosPi a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCosPi₃ h)
    | .refl h => .refl (eqe.eqe_BlockCosPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCosPi₃ h₀) (rw_star_sub_BlockCosPi₃ h₁)
  theorem rw_star_sub_BlockCosPi₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockCosPi a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockCosPi a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCosPi₄ h)
    | .refl h => .refl (eqe.eqe_BlockCosPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCosPi₄ h₀) (rw_star_sub_BlockCosPi₄ h₁)
  theorem rw_star_sub_BlockCosPi₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockCosPi a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockCosPi a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCosPi₅ h)
    | .refl h => .refl (eqe.eqe_BlockCosPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCosPi₅ h₀) (rw_star_sub_BlockCosPi₅ h₁)
  theorem rw_star_sub_BlockCosPi₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockCosPi a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockCosPi a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockCosPi₆ h)
    | .refl h => .refl (eqe.eqe_BlockCosPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCosPi₆ h₀) (rw_star_sub_BlockCosPi₆ h₁)
  theorem rw_star_sub_BlockCosPi₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockCosPi₇ h)
    | .refl h => .refl (eqe.eqe_BlockCosPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCosPi₇ h₀) (rw_star_sub_BlockCosPi₇ h₁)
  theorem rw_star_sub_BlockCosPi₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockCosPi₈ h)
    | .refl h => .refl (eqe.eqe_BlockCosPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockCosPi₈ h₀) (rw_star_sub_BlockCosPi₈ h₁)
  theorem rw_star_sub_BlockTanPi₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockTanPi a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockTanPi b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTanPi₀ h)
    | .refl h => .refl (eqe.eqe_BlockTanPi h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTanPi₀ h₀) (rw_star_sub_BlockTanPi₀ h₁)
  theorem rw_star_sub_BlockTanPi₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockTanPi a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockTanPi a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTanPi₁ h)
    | .refl h => .refl (eqe.eqe_BlockTanPi rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTanPi₁ h₀) (rw_star_sub_BlockTanPi₁ h₁)
  theorem rw_star_sub_BlockTanPi₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockTanPi a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockTanPi a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTanPi₂ h)
    | .refl h => .refl (eqe.eqe_BlockTanPi rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTanPi₂ h₀) (rw_star_sub_BlockTanPi₂ h₁)
  theorem rw_star_sub_BlockTanPi₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockTanPi a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockTanPi a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTanPi₃ h)
    | .refl h => .refl (eqe.eqe_BlockTanPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTanPi₃ h₀) (rw_star_sub_BlockTanPi₃ h₁)
  theorem rw_star_sub_BlockTanPi₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockTanPi a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockTanPi a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTanPi₄ h)
    | .refl h => .refl (eqe.eqe_BlockTanPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTanPi₄ h₀) (rw_star_sub_BlockTanPi₄ h₁)
  theorem rw_star_sub_BlockTanPi₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockTanPi a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockTanPi a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTanPi₅ h)
    | .refl h => .refl (eqe.eqe_BlockTanPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTanPi₅ h₀) (rw_star_sub_BlockTanPi₅ h₁)
  theorem rw_star_sub_BlockTanPi₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockTanPi a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockTanPi a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockTanPi₆ h)
    | .refl h => .refl (eqe.eqe_BlockTanPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTanPi₆ h₀) (rw_star_sub_BlockTanPi₆ h₁)
  theorem rw_star_sub_BlockTanPi₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockTanPi₇ h)
    | .refl h => .refl (eqe.eqe_BlockTanPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTanPi₇ h₀) (rw_star_sub_BlockTanPi₇ h₁)
  theorem rw_star_sub_BlockTanPi₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockTanPi₈ h)
    | .refl h => .refl (eqe.eqe_BlockTanPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockTanPi₈ h₀) (rw_star_sub_BlockTanPi₈ h₁)
  theorem rw_star_sub_BlockArcSinPi₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockArcSinPi a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcSinPi b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSinPi₀ h)
    | .refl h => .refl (eqe.eqe_BlockArcSinPi h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSinPi₀ h₀) (rw_star_sub_BlockArcSinPi₀ h₁)
  theorem rw_star_sub_BlockArcSinPi₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcSinPi a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcSinPi a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSinPi₁ h)
    | .refl h => .refl (eqe.eqe_BlockArcSinPi rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSinPi₁ h₀) (rw_star_sub_BlockArcSinPi₁ h₁)
  theorem rw_star_sub_BlockArcSinPi₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcSinPi a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcSinPi a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSinPi₂ h)
    | .refl h => .refl (eqe.eqe_BlockArcSinPi rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSinPi₂ h₀) (rw_star_sub_BlockArcSinPi₂ h₁)
  theorem rw_star_sub_BlockArcSinPi₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcSinPi a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcSinPi a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSinPi₃ h)
    | .refl h => .refl (eqe.eqe_BlockArcSinPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSinPi₃ h₀) (rw_star_sub_BlockArcSinPi₃ h₁)
  theorem rw_star_sub_BlockArcSinPi₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcSinPi a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockArcSinPi a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSinPi₄ h)
    | .refl h => .refl (eqe.eqe_BlockArcSinPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSinPi₄ h₀) (rw_star_sub_BlockArcSinPi₄ h₁)
  theorem rw_star_sub_BlockArcSinPi₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcSinPi a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockArcSinPi a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSinPi₅ h)
    | .refl h => .refl (eqe.eqe_BlockArcSinPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSinPi₅ h₀) (rw_star_sub_BlockArcSinPi₅ h₁)
  theorem rw_star_sub_BlockArcSinPi₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockArcSinPi a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockArcSinPi a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcSinPi₆ h)
    | .refl h => .refl (eqe.eqe_BlockArcSinPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSinPi₆ h₀) (rw_star_sub_BlockArcSinPi₆ h₁)
  theorem rw_star_sub_BlockArcSinPi₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockArcSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockArcSinPi₇ h)
    | .refl h => .refl (eqe.eqe_BlockArcSinPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSinPi₇ h₀) (rw_star_sub_BlockArcSinPi₇ h₁)
  theorem rw_star_sub_BlockArcSinPi₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockArcSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockArcSinPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockArcSinPi₈ h)
    | .refl h => .refl (eqe.eqe_BlockArcSinPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcSinPi₈ h₀) (rw_star_sub_BlockArcSinPi₈ h₁)
  theorem rw_star_sub_BlockArcCosPi₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockArcCosPi a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcCosPi b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCosPi₀ h)
    | .refl h => .refl (eqe.eqe_BlockArcCosPi h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCosPi₀ h₀) (rw_star_sub_BlockArcCosPi₀ h₁)
  theorem rw_star_sub_BlockArcCosPi₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcCosPi a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcCosPi a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCosPi₁ h)
    | .refl h => .refl (eqe.eqe_BlockArcCosPi rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCosPi₁ h₀) (rw_star_sub_BlockArcCosPi₁ h₁)
  theorem rw_star_sub_BlockArcCosPi₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcCosPi a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcCosPi a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCosPi₂ h)
    | .refl h => .refl (eqe.eqe_BlockArcCosPi rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCosPi₂ h₀) (rw_star_sub_BlockArcCosPi₂ h₁)
  theorem rw_star_sub_BlockArcCosPi₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcCosPi a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcCosPi a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCosPi₃ h)
    | .refl h => .refl (eqe.eqe_BlockArcCosPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCosPi₃ h₀) (rw_star_sub_BlockArcCosPi₃ h₁)
  theorem rw_star_sub_BlockArcCosPi₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcCosPi a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockArcCosPi a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCosPi₄ h)
    | .refl h => .refl (eqe.eqe_BlockArcCosPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCosPi₄ h₀) (rw_star_sub_BlockArcCosPi₄ h₁)
  theorem rw_star_sub_BlockArcCosPi₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcCosPi a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockArcCosPi a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCosPi₅ h)
    | .refl h => .refl (eqe.eqe_BlockArcCosPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCosPi₅ h₀) (rw_star_sub_BlockArcCosPi₅ h₁)
  theorem rw_star_sub_BlockArcCosPi₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockArcCosPi a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockArcCosPi a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcCosPi₆ h)
    | .refl h => .refl (eqe.eqe_BlockArcCosPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCosPi₆ h₀) (rw_star_sub_BlockArcCosPi₆ h₁)
  theorem rw_star_sub_BlockArcCosPi₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockArcCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockArcCosPi₇ h)
    | .refl h => .refl (eqe.eqe_BlockArcCosPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCosPi₇ h₀) (rw_star_sub_BlockArcCosPi₇ h₁)
  theorem rw_star_sub_BlockArcCosPi₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockArcCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockArcCosPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockArcCosPi₈ h)
    | .refl h => .refl (eqe.eqe_BlockArcCosPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcCosPi₈ h₀) (rw_star_sub_BlockArcCosPi₈ h₁)
  theorem rw_star_sub_BlockArcTanPi₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockArcTanPi a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcTanPi b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTanPi₀ h)
    | .refl h => .refl (eqe.eqe_BlockArcTanPi h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTanPi₀ h₀) (rw_star_sub_BlockArcTanPi₀ h₁)
  theorem rw_star_sub_BlockArcTanPi₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcTanPi a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcTanPi a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTanPi₁ h)
    | .refl h => .refl (eqe.eqe_BlockArcTanPi rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTanPi₁ h₀) (rw_star_sub_BlockArcTanPi₁ h₁)
  theorem rw_star_sub_BlockArcTanPi₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcTanPi a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcTanPi a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTanPi₂ h)
    | .refl h => .refl (eqe.eqe_BlockArcTanPi rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTanPi₂ h₀) (rw_star_sub_BlockArcTanPi₂ h₁)
  theorem rw_star_sub_BlockArcTanPi₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcTanPi a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockArcTanPi a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTanPi₃ h)
    | .refl h => .refl (eqe.eqe_BlockArcTanPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTanPi₃ h₀) (rw_star_sub_BlockArcTanPi₃ h₁)
  theorem rw_star_sub_BlockArcTanPi₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcTanPi a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockArcTanPi a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTanPi₄ h)
    | .refl h => .refl (eqe.eqe_BlockArcTanPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTanPi₄ h₀) (rw_star_sub_BlockArcTanPi₄ h₁)
  theorem rw_star_sub_BlockArcTanPi₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcTanPi a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockArcTanPi a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTanPi₅ h)
    | .refl h => .refl (eqe.eqe_BlockArcTanPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTanPi₅ h₀) (rw_star_sub_BlockArcTanPi₅ h₁)
  theorem rw_star_sub_BlockArcTanPi₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockArcTanPi a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockArcTanPi a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockArcTanPi₆ h)
    | .refl h => .refl (eqe.eqe_BlockArcTanPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTanPi₆ h₀) (rw_star_sub_BlockArcTanPi₆ h₁)
  theorem rw_star_sub_BlockArcTanPi₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockArcTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockArcTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockArcTanPi₇ h)
    | .refl h => .refl (eqe.eqe_BlockArcTanPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTanPi₇ h₀) (rw_star_sub_BlockArcTanPi₇ h₁)
  theorem rw_star_sub_BlockArcTanPi₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockArcTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockArcTanPi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockArcTanPi₈ h)
    | .refl h => .refl (eqe.eqe_BlockArcTanPi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTanPi₈ h₀) (rw_star_sub_BlockArcTanPi₈ h₁)
  theorem rw_star_sub_BlockSoftplus₀ {a b : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockSoftplus a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockSoftplus b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSoftplus₀ h)
    | .refl h => .refl (eqe.eqe_BlockSoftplus h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSoftplus₀ h₀) (rw_star_sub_BlockSoftplus₀ h₁)
  theorem rw_star_sub_BlockSoftplus₁ {a₀ : MRat} {a b a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSoftplus a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockSoftplus a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSoftplus₁ h)
    | .refl h => .refl (eqe.eqe_BlockSoftplus rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSoftplus₁ h₀) (rw_star_sub_BlockSoftplus₁ h₁)
  theorem rw_star_sub_BlockSoftplus₂ {a₀ : MRat} {a₁ a b a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSoftplus a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈).rw_star (BlockSoftplus a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSoftplus₂ h)
    | .refl h => .refl (eqe.eqe_BlockSoftplus rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSoftplus₂ h₀) (rw_star_sub_BlockSoftplus₂ h₁)
  theorem rw_star_sub_BlockSoftplus₃ {a₀ : MRat} {a₁ a₂ a b a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSoftplus a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈).rw_star (BlockSoftplus a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSoftplus₃ h)
    | .refl h => .refl (eqe.eqe_BlockSoftplus rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSoftplus₃ h₀) (rw_star_sub_BlockSoftplus₃ h₁)
  theorem rw_star_sub_BlockSoftplus₄ {a₀ : MRat} {a₁ a₂ a₃ a b : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSoftplus a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈).rw_star (BlockSoftplus a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSoftplus₄ h)
    | .refl h => .refl (eqe.eqe_BlockSoftplus rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSoftplus₄ h₀) (rw_star_sub_BlockSoftplus₄ h₁)
  theorem rw_star_sub_BlockSoftplus₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a b : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSoftplus a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈).rw_star (BlockSoftplus a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSoftplus₅ h)
    | .refl h => .refl (eqe.eqe_BlockSoftplus rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h rfl (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSoftplus₅ h₀) (rw_star_sub_BlockSoftplus₅ h₁)
  theorem rw_star_sub_BlockSoftplus₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a b : MRat} {a₇ : kCodeSeq} {a₈ : MRat} : MRat.rw_star a b →
      (BlockSoftplus a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈).rw_star (BlockSoftplus a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈)
    | .step h => .step (rw_one.sub_BlockSoftplus₆ h)
    | .refl h => .refl (eqe.eqe_BlockSoftplus rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) h (kCodeSeq.eqe_refl a₇) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSoftplus₆ h₀) (rw_star_sub_BlockSoftplus₆ h₁)
  theorem rw_star_sub_BlockSoftplus₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a b : kCodeSeq} {a₈ : MRat} : a.rw_star b →
      (BlockSoftplus a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈).rw_star (BlockSoftplus a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈)
    | .step h => .step (rw_one.sub_BlockSoftplus₇ h)
    | .refl h => .refl (eqe.eqe_BlockSoftplus rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSoftplus₇ h₀) (rw_star_sub_BlockSoftplus₇ h₁)
  theorem rw_star_sub_BlockSoftplus₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ : kFormat} {a₅ : kBlockProjSpec} {a₆ : MRat} {a₇ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockSoftplus a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a).rw_star (BlockSoftplus a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b)
    | .step h => .step (rw_one.sub_BlockSoftplus₈ h)
    | .refl h => .refl (eqe.eqe_BlockSoftplus rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kBlockProjSpec.eqe_refl a₅) rfl (kCodeSeq.eqe_refl a₇) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockSoftplus₈ h₀) (rw_star_sub_BlockSoftplus₈ h₁)
  theorem rw_star_sub_BlockHypot₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockHypot a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockHypot b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockHypot₀ h)
    | .refl h => .refl (eqe.eqe_BlockHypot h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockHypot₀ h₀) (rw_star_sub_BlockHypot₀ h₁)
  theorem rw_star_sub_BlockHypot₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockHypot a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockHypot a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockHypot₁ h)
    | .refl h => .refl (eqe.eqe_BlockHypot rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockHypot₁ h₀) (rw_star_sub_BlockHypot₁ h₁)
  theorem rw_star_sub_BlockHypot₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockHypot a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockHypot a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockHypot₂ h)
    | .refl h => .refl (eqe.eqe_BlockHypot rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockHypot₂ h₀) (rw_star_sub_BlockHypot₂ h₁)
  theorem rw_star_sub_BlockHypot₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockHypot a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockHypot a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockHypot₃ h)
    | .refl h => .refl (eqe.eqe_BlockHypot rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockHypot₃ h₀) (rw_star_sub_BlockHypot₃ h₁)
  theorem rw_star_sub_BlockHypot₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockHypot a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockHypot a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockHypot₄ h)
    | .refl h => .refl (eqe.eqe_BlockHypot rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockHypot₄ h₀) (rw_star_sub_BlockHypot₄ h₁)
  theorem rw_star_sub_BlockHypot₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockHypot a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockHypot a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockHypot₅ h)
    | .refl h => .refl (eqe.eqe_BlockHypot rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockHypot₅ h₀) (rw_star_sub_BlockHypot₅ h₁)
  theorem rw_star_sub_BlockHypot₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockHypot₆ h)
    | .refl h => .refl (eqe.eqe_BlockHypot rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockHypot₆ h₀) (rw_star_sub_BlockHypot₆ h₁)
  theorem rw_star_sub_BlockHypot₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockHypot₇ h)
    | .refl h => .refl (eqe.eqe_BlockHypot rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockHypot₇ h₀) (rw_star_sub_BlockHypot₇ h₁)
  theorem rw_star_sub_BlockHypot₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a b : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockHypot₈ h)
    | .refl h => .refl (eqe.eqe_BlockHypot rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) h (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockHypot₈ h₀) (rw_star_sub_BlockHypot₈ h₁)
  theorem rw_star_sub_BlockHypot₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a b : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂).rw_star (BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockHypot₉ h)
    | .refl h => .refl (eqe.eqe_BlockHypot rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl h rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockHypot₉ h₀) (rw_star_sub_BlockHypot₉ h₁)
  theorem rw_star_sub_BlockHypot₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂).rw_star (BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockHypot₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockHypot rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockHypot₁₀ h₀) (rw_star_sub_BlockHypot₁₀ h₁)
  theorem rw_star_sub_BlockHypot₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂).rw_star (BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | .step h => .step (rw_one.sub_BlockHypot₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockHypot rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockHypot₁₁ h₀) (rw_star_sub_BlockHypot₁₁ h₁)
  theorem rw_star_sub_BlockHypot₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a).rw_star (BlockHypot a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | .step h => .step (rw_one.sub_BlockHypot₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockHypot rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockHypot₁₂ h₀) (rw_star_sub_BlockHypot₁₂ h₁)
  theorem rw_star_sub_BlockArcTan2₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockArcTan2 a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2 b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2₀ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2 h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2₀ h₀) (rw_star_sub_BlockArcTan2₀ h₁)
  theorem rw_star_sub_BlockArcTan2₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockArcTan2 a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2 a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2₁ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2 rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2₁ h₀) (rw_star_sub_BlockArcTan2₁ h₁)
  theorem rw_star_sub_BlockArcTan2₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockArcTan2 a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2 a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2₂ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2 rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2₂ h₀) (rw_star_sub_BlockArcTan2₂ h₁)
  theorem rw_star_sub_BlockArcTan2₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockArcTan2 a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2 a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2₃ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2₃ h₀) (rw_star_sub_BlockArcTan2₃ h₁)
  theorem rw_star_sub_BlockArcTan2₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockArcTan2 a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2 a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2₄ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2₄ h₀) (rw_star_sub_BlockArcTan2₄ h₁)
  theorem rw_star_sub_BlockArcTan2₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2 a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2₅ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2₅ h₀) (rw_star_sub_BlockArcTan2₅ h₁)
  theorem rw_star_sub_BlockArcTan2₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2₆ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2₆ h₀) (rw_star_sub_BlockArcTan2₆ h₁)
  theorem rw_star_sub_BlockArcTan2₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2₇ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2₇ h₀) (rw_star_sub_BlockArcTan2₇ h₁)
  theorem rw_star_sub_BlockArcTan2₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a b : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2₈ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) h (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2₈ h₀) (rw_star_sub_BlockArcTan2₈ h₁)
  theorem rw_star_sub_BlockArcTan2₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a b : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2₉ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl h rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2₉ h₀) (rw_star_sub_BlockArcTan2₉ h₁)
  theorem rw_star_sub_BlockArcTan2₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂).rw_star (BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2₁₀ h₀) (rw_star_sub_BlockArcTan2₁₀ h₁)
  theorem rw_star_sub_BlockArcTan2₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂).rw_star (BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2₁₁ h₀) (rw_star_sub_BlockArcTan2₁₁ h₁)
  theorem rw_star_sub_BlockArcTan2₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a).rw_star (BlockArcTan2 a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | .step h => .step (rw_one.sub_BlockArcTan2₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2 rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2₁₂ h₀) (rw_star_sub_BlockArcTan2₁₂ h₁)
  theorem rw_star_sub_BlockArcTan2Pi₀ {a b : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockArcTan2Pi a a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2Pi b a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2Pi₀ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2Pi h (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2Pi₀ h₀) (rw_star_sub_BlockArcTan2Pi₀ h₁)
  theorem rw_star_sub_BlockArcTan2Pi₁ {a₀ : MRat} {a b a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockArcTan2Pi a₀ a a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2Pi a₀ b a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2Pi₁ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2Pi rfl h (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2Pi₁ h₀) (rw_star_sub_BlockArcTan2Pi₁ h₁)
  theorem rw_star_sub_BlockArcTan2Pi₂ {a₀ : MRat} {a₁ a b a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockArcTan2Pi a₀ a₁ a a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2Pi a₀ a₁ b a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2Pi₂ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2Pi rfl (kFormat.eqe_refl a₁) h (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2Pi₂ h₀) (rw_star_sub_BlockArcTan2Pi₂ h₁)
  theorem rw_star_sub_BlockArcTan2Pi₃ {a₀ : MRat} {a₁ a₂ a b a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockArcTan2Pi a₀ a₁ a₂ a a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2Pi a₀ a₁ a₂ b a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2Pi₃ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2Pi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) h (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2Pi₃ h₀) (rw_star_sub_BlockArcTan2Pi₃ h₁)
  theorem rw_star_sub_BlockArcTan2Pi₄ {a₀ : MRat} {a₁ a₂ a₃ a b a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockArcTan2Pi a₀ a₁ a₂ a₃ a a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2Pi a₀ a₁ a₂ a₃ b a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2Pi₄ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2Pi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) h (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2Pi₄ h₀) (rw_star_sub_BlockArcTan2Pi₄ h₁)
  theorem rw_star_sub_BlockArcTan2Pi₅ {a₀ : MRat} {a₁ a₂ a₃ a₄ a b a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ b a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2Pi₅ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2Pi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) h (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2Pi₅ h₀) (rw_star_sub_BlockArcTan2Pi₅ h₁)
  theorem rw_star_sub_BlockArcTan2Pi₆ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a b : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a a₇ a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ b a₇ a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2Pi₆ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2Pi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) h (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2Pi₆ h₀) (rw_star_sub_BlockArcTan2Pi₆ h₁)
  theorem rw_star_sub_BlockArcTan2Pi₇ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a b : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a a₈ a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ b a₈ a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2Pi₇ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2Pi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) h rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2Pi₇ h₀) (rw_star_sub_BlockArcTan2Pi₇ h₁)
  theorem rw_star_sub_BlockArcTan2Pi₈ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a b : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a a₉ a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b a₉ a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2Pi₈ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2Pi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) h (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2Pi₈ h₀) (rw_star_sub_BlockArcTan2Pi₈ h₁)
  theorem rw_star_sub_BlockArcTan2Pi₉ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a b : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a a₁₀ a₁₁ a₁₂).rw_star (BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b a₁₀ a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2Pi₉ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2Pi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl h rfl (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2Pi₉ h₀) (rw_star_sub_BlockArcTan2Pi₉ h₁)
  theorem rw_star_sub_BlockArcTan2Pi₁₀ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a b : MRat} {a₁₁ : kCodeSeq} {a₁₂ : MRat} : MRat.rw_star a b →
      (BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a a₁₁ a₁₂).rw_star (BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b a₁₁ a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2Pi₁₀ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2Pi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) h (kCodeSeq.eqe_refl a₁₁) rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2Pi₁₀ h₀) (rw_star_sub_BlockArcTan2Pi₁₀ h₁)
  theorem rw_star_sub_BlockArcTan2Pi₁₁ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a b : kCodeSeq} {a₁₂ : MRat} : a.rw_star b →
      (BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a a₁₂).rw_star (BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b a₁₂)
    | .step h => .step (rw_one.sub_BlockArcTan2Pi₁₁ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2Pi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2Pi₁₁ h₀) (rw_star_sub_BlockArcTan2Pi₁₁ h₁)
  theorem rw_star_sub_BlockArcTan2Pi₁₂ {a₀ : MRat} {a₁ a₂ a₃ a₄ a₅ a₆ : kFormat} {a₇ : kBlockProjSpec} {a₈ : MRat} {a₉ : kCodeSeq} {a₁₀ : MRat} {a₁₁ : kCodeSeq} {a b : MRat} : MRat.rw_star a b →
      (BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a).rw_star (BlockArcTan2Pi a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b)
    | .step h => .step (rw_one.sub_BlockArcTan2Pi₁₂ h)
    | .refl h => .refl (eqe.eqe_BlockArcTan2Pi rfl (kFormat.eqe_refl a₁) (kFormat.eqe_refl a₂) (kFormat.eqe_refl a₃) (kFormat.eqe_refl a₄) (kFormat.eqe_refl a₅) (kFormat.eqe_refl a₆) (kBlockProjSpec.eqe_refl a₇) rfl (kCodeSeq.eqe_refl a₉) rfl (kCodeSeq.eqe_refl a₁₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockArcTan2Pi₁₂ h₀) (rw_star_sub_BlockArcTan2Pi₁₂ h₁)
end kBlock

end Maude
