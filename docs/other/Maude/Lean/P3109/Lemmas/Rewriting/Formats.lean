-- Extracted from ../spec2.lean, lines 11923-12257.
-- See PLAN.md and manifest.json for provenance.
import P3109.Lemmas.Rewriting.XReal

namespace Maude
namespace kFormat
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kFormat} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kFormat} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kFormat} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kFormat} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_Binary₀ {a b a₁ : MRat} {a₂ : kSignedness} {a₃ : kDomain} : MRat.rw_star a b →
      (Binary a a₁ a₂ a₃).rw_star (Binary b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_Binary₀ h)
    | .refl h => .refl (eqe.eqe_Binary h rfl (kSignedness.eqe_refl a₂) (kDomain.eqe_refl a₃))
    | .trans h₀ h₁ => .trans (rw_star_sub_Binary₀ h₀) (rw_star_sub_Binary₀ h₁)
  theorem rw_star_sub_Binary₁ {a₀ a b : MRat} {a₂ : kSignedness} {a₃ : kDomain} : MRat.rw_star a b →
      (Binary a₀ a a₂ a₃).rw_star (Binary a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_Binary₁ h)
    | .refl h => .refl (eqe.eqe_Binary rfl h (kSignedness.eqe_refl a₂) (kDomain.eqe_refl a₃))
    | .trans h₀ h₁ => .trans (rw_star_sub_Binary₁ h₀) (rw_star_sub_Binary₁ h₁)
  theorem rw_star_sub_Binary₂ {a₀ a₁ : MRat} {a b : kSignedness} {a₃ : kDomain} : a.rw_star b →
      (Binary a₀ a₁ a a₃).rw_star (Binary a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_Binary₂ h)
    | .refl h => .refl (eqe.eqe_Binary rfl rfl h (kDomain.eqe_refl a₃))
    | .trans h₀ h₁ => .trans (rw_star_sub_Binary₂ h₀) (rw_star_sub_Binary₂ h₁)
  theorem rw_star_sub_Binary₃ {a₀ a₁ : MRat} {a₂ : kSignedness} {a b : kDomain} : a.rw_star b →
      (Binary a₀ a₁ a₂ a).rw_star (Binary a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_Binary₃ h)
    | .refl h => .refl (eqe.eqe_Binary rfl rfl (kSignedness.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_Binary₃ h₀) (rw_star_sub_Binary₃ h₁)
  theorem rw_star_sub_at₀ {a b : kFormatSeq} {a₁ : MRat} : a.rw_star b →
      («at» a a₁).rw_star («at» b a₁)
    | .step h => .step (rw_one.sub_at₀ h)
    | .refl h => .refl (eqe.eqe_at h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₀ h₀) (rw_star_sub_at₀ h₁)
  theorem rw_star_sub_at₁ {a₀ : kFormatSeq} {a b : MRat} : MRat.rw_star a b →
      («at» a₀ a).rw_star («at» a₀ b)
    | .step h => .step (rw_one.sub_at₁ h)
    | .refl h => .refl (eqe.eqe_at (kFormatSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₁ h₀) (rw_star_sub_at₁ h₁)
end kFormat

namespace kSignedness
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kSignedness} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kSignedness} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kSignedness} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kSignedness} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_SignednessOf {a b : kFormat} : a.rw_star b →
      (SignednessOf a).rw_star (SignednessOf b)
    | .step h => .step (rw_one.sub_SignednessOf h)
    | .refl h => .refl (eqe.eqe_SignednessOf h)
    | .trans h₀ h₁ => .trans (rw_star_sub_SignednessOf h₀) (rw_star_sub_SignednessOf h₁)
end kSignedness

namespace kDomain
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kDomain} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kDomain} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kDomain} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kDomain} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_DomainOf {a b : kFormat} : a.rw_star b →
      (DomainOf a).rw_star (DomainOf b)
    | .step h => .step (rw_one.sub_DomainOf h)
    | .refl h => .refl (eqe.eqe_DomainOf h)
    | .trans h₀ h₁ => .trans (rw_star_sub_DomainOf h₀) (rw_star_sub_DomainOf h₁)
end kDomain

namespace kBoundQuery
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kBoundQuery} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kBoundQuery} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kBoundQuery} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kBoundQuery} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
end kBoundQuery

namespace kRandomSeq
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kRandomSeq} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kRandomSeq} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kRandomSeq} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kRandomSeq} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_rcons₀ {a b : MRat} {a₁ : kRandomSeq} : MRat.rw_star a b →
      (rcons a a₁).rw_star (rcons b a₁)
    | .step h => .step (rw_one.sub_rcons₀ h)
    | .refl h => .refl (eqe.eqe_rcons h (kRandomSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_rcons₀ h₀) (rw_star_sub_rcons₀ h₁)
  theorem rw_star_sub_rcons₁ {a₀ : MRat} {a b : kRandomSeq} : a.rw_star b →
      (rcons a₀ a).rw_star (rcons a₀ b)
    | .step h => .step (rw_one.sub_rcons₁ h)
    | .refl h => .refl (eqe.eqe_rcons rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_rcons₁ h₀) (rw_star_sub_rcons₁ h₁)
end kRandomSeq

namespace kBlockRoundMode
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kBlockRoundMode} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kBlockRoundMode} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kBlockRoundMode} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kBlockRoundMode} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_StochasticA₀ {a b a₁ : MRat} : MRat.rw_star a b →
      (StochasticA a a₁).rw_star (StochasticA b a₁)
    | .step h => .step (rw_one.sub_StochasticA₀ h)
    | .refl h => .refl (eqe.eqe_StochasticA h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_StochasticA₀ h₀) (rw_star_sub_StochasticA₀ h₁)
  theorem rw_star_sub_StochasticA₁ {a₀ a b : MRat} : MRat.rw_star a b →
      (StochasticA a₀ a).rw_star (StochasticA a₀ b)
    | .step h => .step (rw_one.sub_StochasticA₁ h)
    | .refl h => .refl (eqe.eqe_StochasticA rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_StochasticA₁ h₀) (rw_star_sub_StochasticA₁ h₁)
  theorem rw_star_sub_StochasticB₀ {a b a₁ : MRat} : MRat.rw_star a b →
      (StochasticB a a₁).rw_star (StochasticB b a₁)
    | .step h => .step (rw_one.sub_StochasticB₀ h)
    | .refl h => .refl (eqe.eqe_StochasticB h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_StochasticB₀ h₀) (rw_star_sub_StochasticB₀ h₁)
  theorem rw_star_sub_StochasticB₁ {a₀ a b : MRat} : MRat.rw_star a b →
      (StochasticB a₀ a).rw_star (StochasticB a₀ b)
    | .step h => .step (rw_one.sub_StochasticB₁ h)
    | .refl h => .refl (eqe.eqe_StochasticB rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_StochasticB₁ h₀) (rw_star_sub_StochasticB₁ h₁)
  theorem rw_star_sub_StochasticC₀ {a b a₁ : MRat} : MRat.rw_star a b →
      (StochasticC a a₁).rw_star (StochasticC b a₁)
    | .step h => .step (rw_one.sub_StochasticC₀ h)
    | .refl h => .refl (eqe.eqe_StochasticC h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_StochasticC₀ h₀) (rw_star_sub_StochasticC₀ h₁)
  theorem rw_star_sub_StochasticC₁ {a₀ a b : MRat} : MRat.rw_star a b →
      (StochasticC a₀ a).rw_star (StochasticC a₀ b)
    | .step h => .step (rw_one.sub_StochasticC₁ h)
    | .refl h => .refl (eqe.eqe_StochasticC rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_StochasticC₁ h₀) (rw_star_sub_StochasticC₁ h₁)
  theorem rw_star_sub_BlockStochasticA₀ {a b : MRat} {a₁ : kRandomSeq} : MRat.rw_star a b →
      (BlockStochasticA a a₁).rw_star (BlockStochasticA b a₁)
    | .step h => .step (rw_one.sub_BlockStochasticA₀ h)
    | .refl h => .refl (eqe.eqe_BlockStochasticA h (kRandomSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockStochasticA₀ h₀) (rw_star_sub_BlockStochasticA₀ h₁)
  theorem rw_star_sub_BlockStochasticA₁ {a₀ : MRat} {a b : kRandomSeq} : a.rw_star b →
      (BlockStochasticA a₀ a).rw_star (BlockStochasticA a₀ b)
    | .step h => .step (rw_one.sub_BlockStochasticA₁ h)
    | .refl h => .refl (eqe.eqe_BlockStochasticA rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockStochasticA₁ h₀) (rw_star_sub_BlockStochasticA₁ h₁)
  theorem rw_star_sub_BlockStochasticB₀ {a b : MRat} {a₁ : kRandomSeq} : MRat.rw_star a b →
      (BlockStochasticB a a₁).rw_star (BlockStochasticB b a₁)
    | .step h => .step (rw_one.sub_BlockStochasticB₀ h)
    | .refl h => .refl (eqe.eqe_BlockStochasticB h (kRandomSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockStochasticB₀ h₀) (rw_star_sub_BlockStochasticB₀ h₁)
  theorem rw_star_sub_BlockStochasticB₁ {a₀ : MRat} {a b : kRandomSeq} : a.rw_star b →
      (BlockStochasticB a₀ a).rw_star (BlockStochasticB a₀ b)
    | .step h => .step (rw_one.sub_BlockStochasticB₁ h)
    | .refl h => .refl (eqe.eqe_BlockStochasticB rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockStochasticB₁ h₀) (rw_star_sub_BlockStochasticB₁ h₁)
  theorem rw_star_sub_BlockStochasticC₀ {a b : MRat} {a₁ : kRandomSeq} : MRat.rw_star a b →
      (BlockStochasticC a a₁).rw_star (BlockStochasticC b a₁)
    | .step h => .step (rw_one.sub_BlockStochasticC₀ h)
    | .refl h => .refl (eqe.eqe_BlockStochasticC h (kRandomSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockStochasticC₀ h₀) (rw_star_sub_BlockStochasticC₀ h₁)
  theorem rw_star_sub_BlockStochasticC₁ {a₀ : MRat} {a b : kRandomSeq} : a.rw_star b →
      (BlockStochasticC a₀ a).rw_star (BlockStochasticC a₀ b)
    | .step h => .step (rw_one.sub_BlockStochasticC₁ h)
    | .refl h => .refl (eqe.eqe_BlockStochasticC rfl h)
    | .trans h₀ h₁ => .trans (rw_star_sub_BlockStochasticC₁ h₀) (rw_star_sub_BlockStochasticC₁ h₁)
  theorem rw_star_sub_RoundOf {a b : kProjSpec} : a.rw_star b →
      (RoundOf a).rw_star (RoundOf b)
    | .step h => .step (rw_one.sub_RoundOf h)
    | .refl h => .refl (eqe.eqe_RoundOf h)
    | .trans h₀ h₁ => .trans (rw_star_sub_RoundOf h₀) (rw_star_sub_RoundOf h₁)
end kBlockRoundMode

namespace kSatMode
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kSatMode} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kSatMode} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kSatMode} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kSatMode} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_SatOf {a b : kProjSpec} : a.rw_star b →
      (SatOf a).rw_star (SatOf b)
    | .step h => .step (rw_one.sub_SatOf h)
    | .refl h => .refl (eqe.eqe_SatOf h)
    | .trans h₀ h₁ => .trans (rw_star_sub_SatOf h₀) (rw_star_sub_SatOf h₁)
end kSatMode

namespace kProjSpec
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kProjSpec} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kProjSpec} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kProjSpec} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kProjSpec} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_proj₀ {a b : kBlockRoundMode} {a₁ : kSatMode} : a.rw_star b →
      (proj a a₁).rw_star (proj b a₁)
    | .step h => .step (rw_one.sub_proj₀ h)
    | .refl h => .refl (eqe.eqe_proj h (kSatMode.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_proj₀ h₀) (rw_star_sub_proj₀ h₁)
  theorem rw_star_sub_proj₁ {a₀ : kBlockRoundMode} {a b : kSatMode} : a.rw_star b →
      (proj a₀ a).rw_star (proj a₀ b)
    | .step h => .step (rw_one.sub_proj₁ h)
    | .refl h => .refl (eqe.eqe_proj (kBlockRoundMode.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_proj₁ h₀) (rw_star_sub_proj₁ h₁)
  theorem rw_star_sub_projectionAt₀ {a b : kBlockProjSpec} {a₁ : MRat} : a.rw_star b →
      (projectionAt a a₁).rw_star (projectionAt b a₁)
    | .step h => .step (rw_one.sub_projectionAt₀ h)
    | .refl h => .refl (eqe.eqe_projectionAt h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_projectionAt₀ h₀) (rw_star_sub_projectionAt₀ h₁)
  theorem rw_star_sub_projectionAt₁ {a₀ : kBlockProjSpec} {a b : MRat} : MRat.rw_star a b →
      (projectionAt a₀ a).rw_star (projectionAt a₀ b)
    | .step h => .step (rw_one.sub_projectionAt₁ h)
    | .refl h => .refl (eqe.eqe_projectionAt (kBlockProjSpec.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_projectionAt₁ h₀) (rw_star_sub_projectionAt₁ h₁)
end kProjSpec

namespace kBlockProjSpec
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kBlockProjSpec} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kBlockProjSpec} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kBlockProjSpec} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kBlockProjSpec} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_bproj₀ {a b : kBlockRoundMode} {a₁ : kSatMode} : a.rw_star b →
      (bproj a a₁).rw_star (bproj b a₁)
    | .step h => .step (rw_one.sub_bproj₀ h)
    | .refl h => .refl (eqe.eqe_bproj h (kSatMode.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_bproj₀ h₀) (rw_star_sub_bproj₀ h₁)
  theorem rw_star_sub_bproj₁ {a₀ : kBlockRoundMode} {a b : kSatMode} : a.rw_star b →
      (bproj a₀ a).rw_star (bproj a₀ b)
    | .step h => .step (rw_one.sub_bproj₁ h)
    | .refl h => .refl (eqe.eqe_bproj (kBlockRoundMode.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_bproj₁ h₀) (rw_star_sub_bproj₁ h₁)
  theorem rw_star_sub_singletonLift {a b : kProjSpec} : a.rw_star b →
      (singletonLift a).rw_star (singletonLift b)
    | .step h => .step (rw_one.sub_singletonLift h)
    | .refl h => .refl (eqe.eqe_singletonLift h)
    | .trans h₀ h₁ => .trans (rw_star_sub_singletonLift h₀) (rw_star_sub_singletonLift h₁)
end kBlockProjSpec

end Maude
