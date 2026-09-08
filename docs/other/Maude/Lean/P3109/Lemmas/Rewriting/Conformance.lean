-- Extracted from ../spec2.lean, lines 15843-16527.
-- See PLAN.md and manifest.json for provenance.
import P3109.Lemmas.Rewriting.Blocks

namespace Maude
namespace kFormatSeq
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kFormatSeq} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kFormatSeq} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kFormatSeq} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kFormatSeq} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_fcons₀ {a b : kFormat} {a₁ : kFormatSeq} : a.rw_star b →
      (fcons a a₁).rw_star (fcons b a₁)
    | .step h => .step (rw_one.sub_fcons₀ h)
    | .refl h => .refl (eqe.eqe_fcons h (kFormatSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_fcons₀ h₀) (rw_star_sub_fcons₀ h₁)
  theorem rw_star_sub_fcons₁ {a₀ : kFormat} {a b : kFormatSeq} : a.rw_star b →
      (fcons a₀ a).rw_star (fcons a₀ b)
    | .step h => .step (rw_one.sub_fcons₁ h)
    | .refl h => .refl (eqe.eqe_fcons (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_fcons₁ h₀) (rw_star_sub_fcons₁ h₁)
end kFormatSeq

namespace kSpecialization
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kSpecialization} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kSpecialization} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kSpecialization} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kSpecialization} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_numeric₀ {a b : MString} {a₁ : kFormatSeq} {a₂ : kProjSpec} : MString.rw_star a b →
      (numeric a a₁ a₂).rw_star (numeric b a₁ a₂)
    | .step h => .step (rw_one.sub_numeric₀ h)
    | .refl h => .refl (eqe.eqe_numeric h (kFormatSeq.eqe_refl a₁) (kProjSpec.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_numeric₀ h₀) (rw_star_sub_numeric₀ h₁)
  theorem rw_star_sub_numeric₁ {a₀ : MString} {a b : kFormatSeq} {a₂ : kProjSpec} : a.rw_star b →
      (numeric a₀ a a₂).rw_star (numeric a₀ b a₂)
    | .step h => .step (rw_one.sub_numeric₁ h)
    | .refl h => .refl (eqe.eqe_numeric rfl h (kProjSpec.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_numeric₁ h₀) (rw_star_sub_numeric₁ h₁)
  theorem rw_star_sub_numeric₂ {a₀ : MString} {a₁ : kFormatSeq} {a b : kProjSpec} : a.rw_star b →
      (numeric a₀ a₁ a).rw_star (numeric a₀ a₁ b)
    | .step h => .step (rw_one.sub_numeric₂ h)
    | .refl h => .refl (eqe.eqe_numeric rfl (kFormatSeq.eqe_refl a₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_numeric₂ h₀) (rw_star_sub_numeric₂ h₁)
  theorem rw_star_sub_plain₀ {a b : MString} {a₁ : kFormatSeq} : MString.rw_star a b →
      (plain a a₁).rw_star (plain b a₁)
    | .step h => .step (rw_one.sub_plain₀ h)
    | .refl h => .refl (eqe.eqe_plain h (kFormatSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_plain₀ h₀) (rw_star_sub_plain₀ h₁)
  theorem rw_star_sub_plain₁ {a₀ : MString} {a b : kFormatSeq} : a.rw_star b →
      (plain a₀ a).rw_star (plain a₀ b)
    | .step h => .step (rw_one.sub_plain₁ h)
    | .refl h => .refl (eqe.eqe_plain rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_plain₁ h₀) (rw_star_sub_plain₁ h₁)
  theorem rw_star_sub_blockElements₀ {a b : MString} {a₁ : MRat} {a₂ : kFormatSeq} {a₃ : kBlockProjSpec} : MString.rw_star a b →
      (blockElements a a₁ a₂ a₃).rw_star (blockElements b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_blockElements₀ h)
    | .refl h => .refl (eqe.eqe_blockElements h rfl (kFormatSeq.eqe_refl a₂) (kBlockProjSpec.eqe_refl a₃))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockElements₀ h₀) (rw_star_sub_blockElements₀ h₁)
  theorem rw_star_sub_blockElements₁ {a₀ : MString} {a b : MRat} {a₂ : kFormatSeq} {a₃ : kBlockProjSpec} : MRat.rw_star a b →
      (blockElements a₀ a a₂ a₃).rw_star (blockElements a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_blockElements₁ h)
    | .refl h => .refl (eqe.eqe_blockElements rfl h (kFormatSeq.eqe_refl a₂) (kBlockProjSpec.eqe_refl a₃))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockElements₁ h₀) (rw_star_sub_blockElements₁ h₁)
  theorem rw_star_sub_blockElements₂ {a₀ : MString} {a₁ : MRat} {a b : kFormatSeq} {a₃ : kBlockProjSpec} : a.rw_star b →
      (blockElements a₀ a₁ a a₃).rw_star (blockElements a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_blockElements₂ h)
    | .refl h => .refl (eqe.eqe_blockElements rfl rfl h (kBlockProjSpec.eqe_refl a₃))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockElements₂ h₀) (rw_star_sub_blockElements₂ h₁)
  theorem rw_star_sub_blockElements₃ {a₀ : MString} {a₁ : MRat} {a₂ : kFormatSeq} {a b : kBlockProjSpec} : a.rw_star b →
      (blockElements a₀ a₁ a₂ a).rw_star (blockElements a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_blockElements₃ h)
    | .refl h => .refl (eqe.eqe_blockElements rfl rfl (kFormatSeq.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_blockElements₃ h₀) (rw_star_sub_blockElements₃ h₁)
  theorem rw_star_sub_blockReduction₀ {a b : MString} {a₁ : MRat} {a₂ : kFormatSeq} {a₃ : kProjSpec} : MString.rw_star a b →
      (blockReduction a a₁ a₂ a₃).rw_star (blockReduction b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_blockReduction₀ h)
    | .refl h => .refl (eqe.eqe_blockReduction h rfl (kFormatSeq.eqe_refl a₂) (kProjSpec.eqe_refl a₃))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockReduction₀ h₀) (rw_star_sub_blockReduction₀ h₁)
  theorem rw_star_sub_blockReduction₁ {a₀ : MString} {a b : MRat} {a₂ : kFormatSeq} {a₃ : kProjSpec} : MRat.rw_star a b →
      (blockReduction a₀ a a₂ a₃).rw_star (blockReduction a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_blockReduction₁ h)
    | .refl h => .refl (eqe.eqe_blockReduction rfl h (kFormatSeq.eqe_refl a₂) (kProjSpec.eqe_refl a₃))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockReduction₁ h₀) (rw_star_sub_blockReduction₁ h₁)
  theorem rw_star_sub_blockReduction₂ {a₀ : MString} {a₁ : MRat} {a b : kFormatSeq} {a₃ : kProjSpec} : a.rw_star b →
      (blockReduction a₀ a₁ a a₃).rw_star (blockReduction a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_blockReduction₂ h)
    | .refl h => .refl (eqe.eqe_blockReduction rfl rfl h (kProjSpec.eqe_refl a₃))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockReduction₂ h₀) (rw_star_sub_blockReduction₂ h₁)
  theorem rw_star_sub_blockReduction₃ {a₀ : MString} {a₁ : MRat} {a₂ : kFormatSeq} {a b : kProjSpec} : a.rw_star b →
      (blockReduction a₀ a₁ a₂ a).rw_star (blockReduction a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_blockReduction₃ h)
    | .refl h => .refl (eqe.eqe_blockReduction rfl rfl (kFormatSeq.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_blockReduction₃ h₀) (rw_star_sub_blockReduction₃ h₁)
  theorem rw_star_sub_blockScale₀ {a b : MString} {a₁ : MRat} {a₂ : kFormatSeq} {a₃ : kProjSpec} {a₄ : kBlockProjSpec} : MString.rw_star a b →
      (blockScale a a₁ a₂ a₃ a₄).rw_star (blockScale b a₁ a₂ a₃ a₄)
    | .step h => .step (rw_one.sub_blockScale₀ h)
    | .refl h => .refl (eqe.eqe_blockScale h rfl (kFormatSeq.eqe_refl a₂) (kProjSpec.eqe_refl a₃) (kBlockProjSpec.eqe_refl a₄))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockScale₀ h₀) (rw_star_sub_blockScale₀ h₁)
  theorem rw_star_sub_blockScale₁ {a₀ : MString} {a b : MRat} {a₂ : kFormatSeq} {a₃ : kProjSpec} {a₄ : kBlockProjSpec} : MRat.rw_star a b →
      (blockScale a₀ a a₂ a₃ a₄).rw_star (blockScale a₀ b a₂ a₃ a₄)
    | .step h => .step (rw_one.sub_blockScale₁ h)
    | .refl h => .refl (eqe.eqe_blockScale rfl h (kFormatSeq.eqe_refl a₂) (kProjSpec.eqe_refl a₃) (kBlockProjSpec.eqe_refl a₄))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockScale₁ h₀) (rw_star_sub_blockScale₁ h₁)
  theorem rw_star_sub_blockScale₂ {a₀ : MString} {a₁ : MRat} {a b : kFormatSeq} {a₃ : kProjSpec} {a₄ : kBlockProjSpec} : a.rw_star b →
      (blockScale a₀ a₁ a a₃ a₄).rw_star (blockScale a₀ a₁ b a₃ a₄)
    | .step h => .step (rw_one.sub_blockScale₂ h)
    | .refl h => .refl (eqe.eqe_blockScale rfl rfl h (kProjSpec.eqe_refl a₃) (kBlockProjSpec.eqe_refl a₄))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockScale₂ h₀) (rw_star_sub_blockScale₂ h₁)
  theorem rw_star_sub_blockScale₃ {a₀ : MString} {a₁ : MRat} {a₂ : kFormatSeq} {a b : kProjSpec} {a₄ : kBlockProjSpec} : a.rw_star b →
      (blockScale a₀ a₁ a₂ a a₄).rw_star (blockScale a₀ a₁ a₂ b a₄)
    | .step h => .step (rw_one.sub_blockScale₃ h)
    | .refl h => .refl (eqe.eqe_blockScale rfl rfl (kFormatSeq.eqe_refl a₂) h (kBlockProjSpec.eqe_refl a₄))
    | .trans h₀ h₁ => .trans (rw_star_sub_blockScale₃ h₀) (rw_star_sub_blockScale₃ h₁)
  theorem rw_star_sub_blockScale₄ {a₀ : MString} {a₁ : MRat} {a₂ : kFormatSeq} {a₃ : kProjSpec} {a b : kBlockProjSpec} : a.rw_star b →
      (blockScale a₀ a₁ a₂ a₃ a).rw_star (blockScale a₀ a₁ a₂ a₃ b)
    | .step h => .step (rw_one.sub_blockScale₄ h)
    | .refl h => .refl (eqe.eqe_blockScale rfl rfl (kFormatSeq.eqe_refl a₂) (kProjSpec.eqe_refl a₃) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_blockScale₄ h₀) (rw_star_sub_blockScale₄ h₁)
  theorem rw_star_sub_at₀ {a b : kSpecializationSeq} {a₁ : MRat} : a.rw_star b →
      («at» a a₁).rw_star («at» b a₁)
    | .step h => .step (rw_one.sub_at₀ h)
    | .refl h => .refl (eqe.eqe_at h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₀ h₀) (rw_star_sub_at₀ h₁)
  theorem rw_star_sub_at₁ {a₀ : kSpecializationSeq} {a b : MRat} : MRat.rw_star a b →
      («at» a₀ a).rw_star («at» a₀ b)
    | .step h => .step (rw_one.sub_at₁ h)
    | .refl h => .refl (eqe.eqe_at (kSpecializationSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₁ h₀) (rw_star_sub_at₁ h₁)
  theorem rw_star_sub_declaredIdentity {a b : kDeclaration} : a.rw_star b →
      (declaredIdentity a).rw_star (declaredIdentity b)
    | .step h => .step (rw_one.sub_declaredIdentity h)
    | .refl h => .refl (eqe.eqe_declaredIdentity h)
    | .trans h₀ h₁ => .trans (rw_star_sub_declaredIdentity h₀) (rw_star_sub_declaredIdentity h₁)
end kSpecialization

namespace kKappa
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kKappa} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kKappa} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kKappa} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kKappa} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_steps {a b : MRat} : MRat.rw_star a b →
      (steps a).rw_star (steps b)
    | .step h => .step (rw_one.sub_steps h)
    | .refl h => .refl (eqe.eqe_steps h)
    | .trans h₀ h₁ => .trans (rw_star_sub_steps h₀) (rw_star_sub_steps h₁)
  theorem rw_star_sub_partBound {a b : kKappaPartSeq} : a.rw_star b →
      (partBound a).rw_star (partBound b)
    | .step h => .step (rw_one.sub_partBound h)
    | .refl h => .refl (eqe.eqe_partBound h)
    | .trans h₀ h₁ => .trans (rw_star_sub_partBound h₀) (rw_star_sub_partBound h₁)
  theorem rw_star_sub_declarationKappa {a b : kDeclaration} : a.rw_star b →
      (declarationKappa a).rw_star (declarationKappa b)
    | .step h => .step (rw_one.sub_declarationKappa h)
    | .refl h => .refl (eqe.eqe_declarationKappa h)
    | .trans h₀ h₁ => .trans (rw_star_sub_declarationKappa h₀) (rw_star_sub_declarationKappa h₁)
  theorem rw_star_sub_observationKappa {a b : kObservation} : a.rw_star b →
      (observationKappa a).rw_star (observationKappa b)
    | .step h => .step (rw_one.sub_observationKappa h)
    | .refl h => .refl (eqe.eqe_observationKappa h)
    | .trans h₀ h₁ => .trans (rw_star_sub_observationKappa h₀) (rw_star_sub_observationKappa h₁)
  theorem rw_star_sub_batchKappa {a b : kObservationSeq} : a.rw_star b →
      (batchKappa a).rw_star (batchKappa b)
    | .step h => .step (rw_one.sub_batchKappa h)
    | .refl h => .refl (eqe.eqe_batchKappa h)
    | .trans h₀ h₁ => .trans (rw_star_sub_batchKappa h₀) (rw_star_sub_batchKappa h₁)
  theorem rw_star_sub_mergeKappa₀ {a b a₁ : kKappa} : a.rw_star b →
      (mergeKappa a a₁).rw_star (mergeKappa b a₁)
    | .step h => .step (rw_one.sub_mergeKappa₀ h)
    | .refl h => .refl (eqe.eqe_mergeKappa h (kKappa.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_mergeKappa₀ h₀) (rw_star_sub_mergeKappa₀ h₁)
  theorem rw_star_sub_mergeKappa₁ {a₀ a b : kKappa} : a.rw_star b →
      (mergeKappa a₀ a).rw_star (mergeKappa a₀ b)
    | .step h => .step (rw_one.sub_mergeKappa₁ h)
    | .refl h => .refl (eqe.eqe_mergeKappa (kKappa.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_mergeKappa₁ h₀) (rw_star_sub_mergeKappa₁ h₁)
end kKappa

namespace kObservation
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kObservation} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kObservation} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kObservation} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kObservation} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_observation₀ {a b : MString} {a₁ : kCodeSeq} {a₂ : kFormat} {a₃ a₄ : MRat} : MString.rw_star a b →
      (observation a a₁ a₂ a₃ a₄).rw_star (observation b a₁ a₂ a₃ a₄)
    | .step h => .step (rw_one.sub_observation₀ h)
    | .refl h => .refl (eqe.eqe_observation h (kCodeSeq.eqe_refl a₁) (kFormat.eqe_refl a₂) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_observation₀ h₀) (rw_star_sub_observation₀ h₁)
  theorem rw_star_sub_observation₁ {a₀ : MString} {a b : kCodeSeq} {a₂ : kFormat} {a₃ a₄ : MRat} : a.rw_star b →
      (observation a₀ a a₂ a₃ a₄).rw_star (observation a₀ b a₂ a₃ a₄)
    | .step h => .step (rw_one.sub_observation₁ h)
    | .refl h => .refl (eqe.eqe_observation rfl h (kFormat.eqe_refl a₂) rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_observation₁ h₀) (rw_star_sub_observation₁ h₁)
  theorem rw_star_sub_observation₂ {a₀ : MString} {a₁ : kCodeSeq} {a b : kFormat} {a₃ a₄ : MRat} : a.rw_star b →
      (observation a₀ a₁ a a₃ a₄).rw_star (observation a₀ a₁ b a₃ a₄)
    | .step h => .step (rw_one.sub_observation₂ h)
    | .refl h => .refl (eqe.eqe_observation rfl (kCodeSeq.eqe_refl a₁) h rfl rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_observation₂ h₀) (rw_star_sub_observation₂ h₁)
  theorem rw_star_sub_observation₃ {a₀ : MString} {a₁ : kCodeSeq} {a₂ : kFormat} {a b a₄ : MRat} : MRat.rw_star a b →
      (observation a₀ a₁ a₂ a a₄).rw_star (observation a₀ a₁ a₂ b a₄)
    | .step h => .step (rw_one.sub_observation₃ h)
    | .refl h => .refl (eqe.eqe_observation rfl (kCodeSeq.eqe_refl a₁) (kFormat.eqe_refl a₂) h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_observation₃ h₀) (rw_star_sub_observation₃ h₁)
  theorem rw_star_sub_observation₄ {a₀ : MString} {a₁ : kCodeSeq} {a₂ : kFormat} {a₃ a b : MRat} : MRat.rw_star a b →
      (observation a₀ a₁ a₂ a₃ a).rw_star (observation a₀ a₁ a₂ a₃ b)
    | .step h => .step (rw_one.sub_observation₄ h)
    | .refl h => .refl (eqe.eqe_observation rfl (kCodeSeq.eqe_refl a₁) (kFormat.eqe_refl a₂) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_observation₄ h₀) (rw_star_sub_observation₄ h₁)
  theorem rw_star_sub_at₀ {a b : kObservationSeq} {a₁ : MRat} : a.rw_star b →
      («at» a a₁).rw_star («at» b a₁)
    | .step h => .step (rw_one.sub_at₀ h)
    | .refl h => .refl (eqe.eqe_at h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₀ h₀) (rw_star_sub_at₀ h₁)
  theorem rw_star_sub_at₁ {a₀ : kObservationSeq} {a b : MRat} : MRat.rw_star a b →
      («at» a₀ a).rw_star («at» a₀ b)
    | .step h => .step (rw_one.sub_at₁ h)
    | .refl h => .refl (eqe.eqe_at (kObservationSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₁ h₀) (rw_star_sub_at₁ h₁)
end kObservation

namespace kDeclaration
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kDeclaration} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kDeclaration} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kDeclaration} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kDeclaration} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_exact₀ {a b : kSpecialization} {a₁ : MString} {a₂ : kEvidence} : a.rw_star b →
      (exact a a₁ a₂).rw_star (exact b a₁ a₂)
    | .step h => .step (rw_one.sub_exact₀ h)
    | .refl h => .refl (eqe.eqe_exact h rfl (kEvidence.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_exact₀ h₀) (rw_star_sub_exact₀ h₁)
  theorem rw_star_sub_exact₁ {a₀ : kSpecialization} {a b : MString} {a₂ : kEvidence} : MString.rw_star a b →
      (exact a₀ a a₂).rw_star (exact a₀ b a₂)
    | .step h => .step (rw_one.sub_exact₁ h)
    | .refl h => .refl (eqe.eqe_exact (kSpecialization.eqe_refl a₀) h (kEvidence.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_exact₁ h₀) (rw_star_sub_exact₁ h₁)
  theorem rw_star_sub_exact₂ {a₀ : kSpecialization} {a₁ : MString} {a b : kEvidence} : a.rw_star b →
      (exact a₀ a₁ a).rw_star (exact a₀ a₁ b)
    | .step h => .step (rw_one.sub_exact₂ h)
    | .refl h => .refl (eqe.eqe_exact (kSpecialization.eqe_refl a₀) rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_exact₂ h₀) (rw_star_sub_exact₂ h₁)
  theorem rw_star_sub_approximate₀ {a b : kSpecialization} {a₁ : MString} {a₂ : kKappa} {a₃ : kEvidence} : a.rw_star b →
      (approximate a a₁ a₂ a₃).rw_star (approximate b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_approximate₀ h)
    | .refl h => .refl (eqe.eqe_approximate h rfl (kKappa.eqe_refl a₂) (kEvidence.eqe_refl a₃))
    | .trans h₀ h₁ => .trans (rw_star_sub_approximate₀ h₀) (rw_star_sub_approximate₀ h₁)
  theorem rw_star_sub_approximate₁ {a₀ : kSpecialization} {a b : MString} {a₂ : kKappa} {a₃ : kEvidence} : MString.rw_star a b →
      (approximate a₀ a a₂ a₃).rw_star (approximate a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_approximate₁ h)
    | .refl h => .refl (eqe.eqe_approximate (kSpecialization.eqe_refl a₀) h (kKappa.eqe_refl a₂) (kEvidence.eqe_refl a₃))
    | .trans h₀ h₁ => .trans (rw_star_sub_approximate₁ h₀) (rw_star_sub_approximate₁ h₁)
  theorem rw_star_sub_approximate₂ {a₀ : kSpecialization} {a₁ : MString} {a b : kKappa} {a₃ : kEvidence} : a.rw_star b →
      (approximate a₀ a₁ a a₃).rw_star (approximate a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_approximate₂ h)
    | .refl h => .refl (eqe.eqe_approximate (kSpecialization.eqe_refl a₀) rfl h (kEvidence.eqe_refl a₃))
    | .trans h₀ h₁ => .trans (rw_star_sub_approximate₂ h₀) (rw_star_sub_approximate₂ h₁)
  theorem rw_star_sub_approximate₃ {a₀ : kSpecialization} {a₁ : MString} {a₂ : kKappa} {a b : kEvidence} : a.rw_star b →
      (approximate a₀ a₁ a₂ a).rw_star (approximate a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_approximate₃ h)
    | .refl h => .refl (eqe.eqe_approximate (kSpecialization.eqe_refl a₀) rfl (kKappa.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_approximate₃ h₀) (rw_star_sub_approximate₃ h₁)
  theorem rw_star_sub_at₀ {a b : kDeclarationSeq} {a₁ : MRat} : a.rw_star b →
      («at» a a₁).rw_star («at» b a₁)
    | .step h => .step (rw_one.sub_at₀ h)
    | .refl h => .refl (eqe.eqe_at h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₀ h₀) (rw_star_sub_at₀ h₁)
  theorem rw_star_sub_at₁ {a₀ : kDeclarationSeq} {a b : MRat} : MRat.rw_star a b →
      («at» a₀ a).rw_star («at» a₀ b)
    | .step h => .step (rw_one.sub_at₁ h)
    | .refl h => .refl (eqe.eqe_at (kDeclarationSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₁ h₀) (rw_star_sub_at₁ h₁)
  theorem rw_star_sub_partitioned₀ {a b : kSpecialization} {a₁ : MString} {a₂ : kCodeSeq} {a₃ : kKappaPartSeq} {a₄ : kEvidence} : a.rw_star b →
      (partitioned a a₁ a₂ a₃ a₄).rw_star (partitioned b a₁ a₂ a₃ a₄)
    | .step h => .step (rw_one.sub_partitioned₀ h)
    | .refl h => .refl (eqe.eqe_partitioned h rfl (kCodeSeq.eqe_refl a₂) (kKappaPartSeq.eqe_refl a₃) (kEvidence.eqe_refl a₄))
    | .trans h₀ h₁ => .trans (rw_star_sub_partitioned₀ h₀) (rw_star_sub_partitioned₀ h₁)
  theorem rw_star_sub_partitioned₁ {a₀ : kSpecialization} {a b : MString} {a₂ : kCodeSeq} {a₃ : kKappaPartSeq} {a₄ : kEvidence} : MString.rw_star a b →
      (partitioned a₀ a a₂ a₃ a₄).rw_star (partitioned a₀ b a₂ a₃ a₄)
    | .step h => .step (rw_one.sub_partitioned₁ h)
    | .refl h => .refl (eqe.eqe_partitioned (kSpecialization.eqe_refl a₀) h (kCodeSeq.eqe_refl a₂) (kKappaPartSeq.eqe_refl a₃) (kEvidence.eqe_refl a₄))
    | .trans h₀ h₁ => .trans (rw_star_sub_partitioned₁ h₀) (rw_star_sub_partitioned₁ h₁)
  theorem rw_star_sub_partitioned₂ {a₀ : kSpecialization} {a₁ : MString} {a b : kCodeSeq} {a₃ : kKappaPartSeq} {a₄ : kEvidence} : a.rw_star b →
      (partitioned a₀ a₁ a a₃ a₄).rw_star (partitioned a₀ a₁ b a₃ a₄)
    | .step h => .step (rw_one.sub_partitioned₂ h)
    | .refl h => .refl (eqe.eqe_partitioned (kSpecialization.eqe_refl a₀) rfl h (kKappaPartSeq.eqe_refl a₃) (kEvidence.eqe_refl a₄))
    | .trans h₀ h₁ => .trans (rw_star_sub_partitioned₂ h₀) (rw_star_sub_partitioned₂ h₁)
  theorem rw_star_sub_partitioned₃ {a₀ : kSpecialization} {a₁ : MString} {a₂ : kCodeSeq} {a b : kKappaPartSeq} {a₄ : kEvidence} : a.rw_star b →
      (partitioned a₀ a₁ a₂ a a₄).rw_star (partitioned a₀ a₁ a₂ b a₄)
    | .step h => .step (rw_one.sub_partitioned₃ h)
    | .refl h => .refl (eqe.eqe_partitioned (kSpecialization.eqe_refl a₀) rfl (kCodeSeq.eqe_refl a₂) h (kEvidence.eqe_refl a₄))
    | .trans h₀ h₁ => .trans (rw_star_sub_partitioned₃ h₀) (rw_star_sub_partitioned₃ h₁)
  theorem rw_star_sub_partitioned₄ {a₀ : kSpecialization} {a₁ : MString} {a₂ : kCodeSeq} {a₃ : kKappaPartSeq} {a b : kEvidence} : a.rw_star b →
      (partitioned a₀ a₁ a₂ a₃ a).rw_star (partitioned a₀ a₁ a₂ a₃ b)
    | .step h => .step (rw_one.sub_partitioned₄ h)
    | .refl h => .refl (eqe.eqe_partitioned (kSpecialization.eqe_refl a₀) rfl (kCodeSeq.eqe_refl a₂) (kKappaPartSeq.eqe_refl a₃) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_partitioned₄ h₀) (rw_star_sub_partitioned₄ h₁)
end kDeclaration

namespace kEvidence
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kEvidence} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kEvidence} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kEvidence} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kEvidence} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
end kEvidence

namespace kKappaPart
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kKappaPart} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kKappaPart} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kKappaPart} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kKappaPart} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_kappaPart₀ {a b : kCodeSeq} {a₁ : kKappa} : a.rw_star b →
      (kappaPart a a₁).rw_star (kappaPart b a₁)
    | .step h => .step (rw_one.sub_kappaPart₀ h)
    | .refl h => .refl (eqe.eqe_kappaPart h (kKappa.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_kappaPart₀ h₀) (rw_star_sub_kappaPart₀ h₁)
  theorem rw_star_sub_kappaPart₁ {a₀ : kCodeSeq} {a b : kKappa} : a.rw_star b →
      (kappaPart a₀ a).rw_star (kappaPart a₀ b)
    | .step h => .step (rw_one.sub_kappaPart₁ h)
    | .refl h => .refl (eqe.eqe_kappaPart (kCodeSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_kappaPart₁ h₀) (rw_star_sub_kappaPart₁ h₁)
  theorem rw_star_sub_at₀ {a b : kKappaPartSeq} {a₁ : MRat} : a.rw_star b →
      («at» a a₁).rw_star («at» b a₁)
    | .step h => .step (rw_one.sub_at₀ h)
    | .refl h => .refl (eqe.eqe_at h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₀ h₀) (rw_star_sub_at₀ h₁)
  theorem rw_star_sub_at₁ {a₀ : kKappaPartSeq} {a b : MRat} : MRat.rw_star a b →
      («at» a₀ a).rw_star («at» a₀ b)
    | .step h => .step (rw_one.sub_at₁ h)
    | .refl h => .refl (eqe.eqe_at (kKappaPartSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₁ h₀) (rw_star_sub_at₁ h₁)
end kKappaPart

namespace kArityEntry
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kArityEntry} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kArityEntry} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kArityEntry} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kArityEntry} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_entry₀ {a b : MString} {a₁ : MRat} : MString.rw_star a b →
      (entry a a₁).rw_star (entry b a₁)
    | .step h => .step (rw_one.sub_entry₀ h)
    | .refl h => .refl (eqe.eqe_entry h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_entry₀ h₀) (rw_star_sub_entry₀ h₁)
  theorem rw_star_sub_entry₁ {a₀ : MString} {a b : MRat} : MRat.rw_star a b →
      (entry a₀ a).rw_star (entry a₀ b)
    | .step h => .step (rw_one.sub_entry₁ h)
    | .refl h => .refl (eqe.eqe_entry rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_entry₁ h₀) (rw_star_sub_entry₁ h₁)
  theorem rw_star_sub_at₀ {a b : kArityTable} {a₁ : MRat} : a.rw_star b →
      («at» a a₁).rw_star («at» b a₁)
    | .step h => .step (rw_one.sub_at₀ h)
    | .refl h => .refl (eqe.eqe_at h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₀ h₀) (rw_star_sub_at₀ h₁)
  theorem rw_star_sub_at₁ {a₀ : kArityTable} {a b : MRat} : MRat.rw_star a b →
      («at» a₀ a).rw_star («at» a₀ b)
    | .step h => .step (rw_one.sub_at₁ h)
    | .refl h => .refl (eqe.eqe_at (kArityTable.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₁ h₀) (rw_star_sub_at₁ h₁)
end kArityEntry

namespace kKappaPartSeq
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kKappaPartSeq} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kKappaPartSeq} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kKappaPartSeq} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kKappaPartSeq} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_kcons₀ {a b : kKappaPart} {a₁ : kKappaPartSeq} : a.rw_star b →
      (kcons a a₁).rw_star (kcons b a₁)
    | .step h => .step (rw_one.sub_kcons₀ h)
    | .refl h => .refl (eqe.eqe_kcons h (kKappaPartSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_kcons₀ h₀) (rw_star_sub_kcons₀ h₁)
  theorem rw_star_sub_kcons₁ {a₀ : kKappaPart} {a b : kKappaPartSeq} : a.rw_star b →
      (kcons a₀ a).rw_star (kcons a₀ b)
    | .step h => .step (rw_one.sub_kcons₁ h)
    | .refl h => .refl (eqe.eqe_kcons (kKappaPart.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_kcons₁ h₀) (rw_star_sub_kcons₁ h₁)
end kKappaPartSeq

namespace kPartitionSeq
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kPartitionSeq} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kPartitionSeq} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kPartitionSeq} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kPartitionSeq} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_pcons₀ {a b : kCodeSeq} {a₁ : kPartitionSeq} : a.rw_star b →
      (pcons a a₁).rw_star (pcons b a₁)
    | .step h => .step (rw_one.sub_pcons₀ h)
    | .refl h => .refl (eqe.eqe_pcons h (kPartitionSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_pcons₀ h₀) (rw_star_sub_pcons₀ h₁)
  theorem rw_star_sub_pcons₁ {a₀ : kCodeSeq} {a b : kPartitionSeq} : a.rw_star b →
      (pcons a₀ a).rw_star (pcons a₀ b)
    | .step h => .step (rw_one.sub_pcons₁ h)
    | .refl h => .refl (eqe.eqe_pcons (kCodeSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_pcons₁ h₀) (rw_star_sub_pcons₁ h₁)
  theorem rw_star_sub_partRegions {a b : kKappaPartSeq} : a.rw_star b →
      (partRegions a).rw_star (partRegions b)
    | .step h => .step (rw_one.sub_partRegions h)
    | .refl h => .refl (eqe.eqe_partRegions h)
    | .trans h₀ h₁ => .trans (rw_star_sub_partRegions h₀) (rw_star_sub_partRegions h₁)
end kPartitionSeq

namespace kDeclarationSeq
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kDeclarationSeq} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kDeclarationSeq} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kDeclarationSeq} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kDeclarationSeq} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_dcons₀ {a b : kDeclaration} {a₁ : kDeclarationSeq} : a.rw_star b →
      (dcons a a₁).rw_star (dcons b a₁)
    | .step h => .step (rw_one.sub_dcons₀ h)
    | .refl h => .refl (eqe.eqe_dcons h (kDeclarationSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_dcons₀ h₀) (rw_star_sub_dcons₀ h₁)
  theorem rw_star_sub_dcons₁ {a₀ : kDeclaration} {a b : kDeclarationSeq} : a.rw_star b →
      (dcons a₀ a).rw_star (dcons a₀ b)
    | .step h => .step (rw_one.sub_dcons₁ h)
    | .refl h => .refl (eqe.eqe_dcons (kDeclaration.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_dcons₁ h₀) (rw_star_sub_dcons₁ h₁)
end kDeclarationSeq

namespace kSpecializationSeq
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kSpecializationSeq} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kSpecializationSeq} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kSpecializationSeq} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kSpecializationSeq} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_scons₀ {a b : kSpecialization} {a₁ : kSpecializationSeq} : a.rw_star b →
      (scons a a₁).rw_star (scons b a₁)
    | .step h => .step (rw_one.sub_scons₀ h)
    | .refl h => .refl (eqe.eqe_scons h (kSpecializationSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_scons₀ h₀) (rw_star_sub_scons₀ h₁)
  theorem rw_star_sub_scons₁ {a₀ : kSpecialization} {a b : kSpecializationSeq} : a.rw_star b →
      (scons a₀ a).rw_star (scons a₀ b)
    | .step h => .step (rw_one.sub_scons₁ h)
    | .refl h => .refl (eqe.eqe_scons (kSpecialization.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_scons₁ h₀) (rw_star_sub_scons₁ h₁)
end kSpecializationSeq

namespace kClassEnum
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kClassEnum} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kClassEnum} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kClassEnum} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kClassEnum} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_Class₀ {a b : kFormat} {a₁ : MRat} : a.rw_star b →
      (Class a a₁).rw_star (Class b a₁)
    | .step h => .step (rw_one.sub_Class₀ h)
    | .refl h => .refl (eqe.eqe_Class h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_Class₀ h₀) (rw_star_sub_Class₀ h₁)
  theorem rw_star_sub_Class₁ {a₀ : kFormat} {a b : MRat} : MRat.rw_star a b →
      (Class a₀ a).rw_star (Class a₀ b)
    | .step h => .step (rw_one.sub_Class₁ h)
    | .refl h => .refl (eqe.eqe_Class (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Class₁ h₀) (rw_star_sub_Class₁ h₁)
  theorem rw_star_sub_ifthenelsefi₀ {a b : kBool} {a₁ a₂ : kClassEnum} : a.rw_star b →
      (ifthenelsefi a a₁ a₂).rw_star (ifthenelsefi b a₁ a₂)
    | .step h => .step (rw_one.sub_ifthenelsefi₀ h)
    | .refl h => .refl (eqe.eqe_ifthenelsefi h (kClassEnum.eqe_refl a₁) (kClassEnum.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_ifthenelsefi₀ h₀) (rw_star_sub_ifthenelsefi₀ h₁)
  theorem rw_star_sub_ifthenelsefi₁ {a₀ : kBool} {a b a₂ : kClassEnum} : a.rw_star b →
      (ifthenelsefi a₀ a a₂).rw_star (ifthenelsefi a₀ b a₂)
    | .step h => .step (rw_one.sub_ifthenelsefi₁ h)
    | .refl h => .refl (eqe.eqe_ifthenelsefi (kBool.eqe_refl a₀) h (kClassEnum.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_ifthenelsefi₁ h₀) (rw_star_sub_ifthenelsefi₁ h₁)
  theorem rw_star_sub_ifthenelsefi₂ {a₀ : kBool} {a₁ a b : kClassEnum} : a.rw_star b →
      (ifthenelsefi a₀ a₁ a).rw_star (ifthenelsefi a₀ a₁ b)
    | .step h => .step (rw_one.sub_ifthenelsefi₂ h)
    | .refl h => .refl (eqe.eqe_ifthenelsefi (kBool.eqe_refl a₀) (kClassEnum.eqe_refl a₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ifthenelsefi₂ h₀) (rw_star_sub_ifthenelsefi₂ h₁)
end kClassEnum

namespace kObservationSeq
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kObservationSeq} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kObservationSeq} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kObservationSeq} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kObservationSeq} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_ocons₀ {a b : kObservation} {a₁ : kObservationSeq} : a.rw_star b →
      (ocons a a₁).rw_star (ocons b a₁)
    | .step h => .step (rw_one.sub_ocons₀ h)
    | .refl h => .refl (eqe.eqe_ocons h (kObservationSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_ocons₀ h₀) (rw_star_sub_ocons₀ h₁)
  theorem rw_star_sub_ocons₁ {a₀ : kObservation} {a b : kObservationSeq} : a.rw_star b →
      (ocons a₀ a).rw_star (ocons a₀ b)
    | .step h => .step (rw_one.sub_ocons₁ h)
    | .refl h => .refl (eqe.eqe_ocons (kObservation.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ocons₁ h₀) (rw_star_sub_ocons₁ h₁)
end kObservationSeq

namespace kArityTable
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kArityTable} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kArityTable} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kArityTable} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kArityTable} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_acons₀ {a b : kArityEntry} {a₁ : kArityTable} : a.rw_star b →
      (acons a a₁).rw_star (acons b a₁)
    | .step h => .step (rw_one.sub_acons₀ h)
    | .refl h => .refl (eqe.eqe_acons h (kArityTable.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_acons₀ h₀) (rw_star_sub_acons₀ h₁)
  theorem rw_star_sub_acons₁ {a₀ : kArityEntry} {a b : kArityTable} : a.rw_star b →
      (acons a₀ a).rw_star (acons a₀ b)
    | .step h => .step (rw_one.sub_acons₁ h)
    | .refl h => .refl (eqe.eqe_acons (kArityEntry.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_acons₁ h₀) (rw_star_sub_acons₁ h₁)
end kArityTable

end Maude
