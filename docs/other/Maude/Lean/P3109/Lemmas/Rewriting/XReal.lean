-- Extracted from ../spec2.lean, lines 11233-11922.
-- See PLAN.md and manifest.json for provenance.
import P3109.Lemmas.Rewriting.Bool

namespace Maude
namespace kXReal
  -- Congruence lemmas
  @[congr] theorem eqe_rw_one_congr {a b c d : kXReal} : a.eqe b → c.eqe d → (a.rw_one c) = (b.rw_one d)
    := generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm
  @[congr] theorem eqa_rw_one_congr {a b c d : kXReal} : a.eqa b → c.eqa d → (a.rw_one c) = (b.rw_one d)
    := generic_congr (λ {x y z} => (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm
  @[congr] theorem eqe_rw_star_congr {a b c d : kXReal} : a.eqe b → c.eqe d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm
  @[congr] theorem eqa_rw_star_congr {a b c d : kXReal} : a.eqa b → c.eqa d → (a.rw_star c) = (b.rw_star d)
    := generic_congr (λ {x y z} => (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] rw_star.refl rw_star.trans

  -- Lemmas for subterm rewriting with =>*
  theorem rw_star_sub_fin {a b : MRat} : MRat.rw_star a b →
      (fin a).rw_star (fin b)
    | .step h => .step (rw_one.sub_fin h)
    | .refl h => .refl (eqe.eqe_fin h)
    | .trans h₀ h₁ => .trans (rw_star_sub_fin h₀) (rw_star_sub_fin h₁)
  theorem rw_star_sub_externalDecode₀ {a b : kFormat} {a₁ : MRat} : a.rw_star b →
      (externalDecode a a₁).rw_star (externalDecode b a₁)
    | .step h => .step (rw_one.sub_externalDecode₀ h)
    | .refl h => .refl (eqe.eqe_externalDecode h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_externalDecode₀ h₀) (rw_star_sub_externalDecode₀ h₁)
  theorem rw_star_sub_externalDecode₁ {a₀ : kFormat} {a b : MRat} : MRat.rw_star a b →
      (externalDecode a₀ a).rw_star (externalDecode a₀ b)
    | .step h => .step (rw_one.sub_externalDecode₁ h)
    | .refl h => .refl (eqe.eqe_externalDecode (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_externalDecode₁ h₀) (rw_star_sub_externalDecode₁ h₁)
  theorem rw_star_sub_decode₀ {a b : kFormat} {a₁ : MRat} : a.rw_star b →
      (decode a a₁).rw_star (decode b a₁)
    | .step h => .step (rw_one.sub_decode₀ h)
    | .refl h => .refl (eqe.eqe_decode h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_decode₀ h₀) (rw_star_sub_decode₀ h₁)
  theorem rw_star_sub_decode₁ {a₀ : kFormat} {a b : MRat} : MRat.rw_star a b →
      (decode a₀ a).rw_star (decode a₀ b)
    | .step h => .step (rw_one.sub_decode₁ h)
    | .refl h => .refl (eqe.eqe_decode (kFormat.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_decode₁ h₀) (rw_star_sub_decode₁ h₁)
  theorem rw_star_sub_roundToPrecision₀ {a b a₁ : MRat} {a₂ : kBlockRoundMode} {a₃ : kXReal} : MRat.rw_star a b →
      (roundToPrecision a a₁ a₂ a₃).rw_star (roundToPrecision b a₁ a₂ a₃)
    | .step h => .step (rw_one.sub_roundToPrecision₀ h)
    | .refl h => .refl (eqe.eqe_roundToPrecision h rfl (kBlockRoundMode.eqe_refl a₂) (kXReal.eqe_refl a₃))
    | .trans h₀ h₁ => .trans (rw_star_sub_roundToPrecision₀ h₀) (rw_star_sub_roundToPrecision₀ h₁)
  theorem rw_star_sub_roundToPrecision₁ {a₀ a b : MRat} {a₂ : kBlockRoundMode} {a₃ : kXReal} : MRat.rw_star a b →
      (roundToPrecision a₀ a a₂ a₃).rw_star (roundToPrecision a₀ b a₂ a₃)
    | .step h => .step (rw_one.sub_roundToPrecision₁ h)
    | .refl h => .refl (eqe.eqe_roundToPrecision rfl h (kBlockRoundMode.eqe_refl a₂) (kXReal.eqe_refl a₃))
    | .trans h₀ h₁ => .trans (rw_star_sub_roundToPrecision₁ h₀) (rw_star_sub_roundToPrecision₁ h₁)
  theorem rw_star_sub_roundToPrecision₂ {a₀ a₁ : MRat} {a b : kBlockRoundMode} {a₃ : kXReal} : a.rw_star b →
      (roundToPrecision a₀ a₁ a a₃).rw_star (roundToPrecision a₀ a₁ b a₃)
    | .step h => .step (rw_one.sub_roundToPrecision₂ h)
    | .refl h => .refl (eqe.eqe_roundToPrecision rfl rfl h (kXReal.eqe_refl a₃))
    | .trans h₀ h₁ => .trans (rw_star_sub_roundToPrecision₂ h₀) (rw_star_sub_roundToPrecision₂ h₁)
  theorem rw_star_sub_roundToPrecision₃ {a₀ a₁ : MRat} {a₂ : kBlockRoundMode} {a b : kXReal} : a.rw_star b →
      (roundToPrecision a₀ a₁ a₂ a).rw_star (roundToPrecision a₀ a₁ a₂ b)
    | .step h => .step (rw_one.sub_roundToPrecision₃ h)
    | .refl h => .refl (eqe.eqe_roundToPrecision rfl rfl (kBlockRoundMode.eqe_refl a₂) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_roundToPrecision₃ h₀) (rw_star_sub_roundToPrecision₃ h₁)
  theorem rw_star_sub_saturate₀ {a b a₁ : MRat} {a₂ : kSatMode} {a₃ : kBlockRoundMode} {a₄ : kXReal} {a₅ : kSignedness} {a₆ : kDomain} : MRat.rw_star a b →
      (saturate a a₁ a₂ a₃ a₄ a₅ a₆).rw_star (saturate b a₁ a₂ a₃ a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_saturate₀ h)
    | .refl h => .refl (eqe.eqe_saturate h rfl (kSatMode.eqe_refl a₂) (kBlockRoundMode.eqe_refl a₃) (kXReal.eqe_refl a₄) (kSignedness.eqe_refl a₅) (kDomain.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_saturate₀ h₀) (rw_star_sub_saturate₀ h₁)
  theorem rw_star_sub_saturate₁ {a₀ a b : MRat} {a₂ : kSatMode} {a₃ : kBlockRoundMode} {a₄ : kXReal} {a₅ : kSignedness} {a₆ : kDomain} : MRat.rw_star a b →
      (saturate a₀ a a₂ a₃ a₄ a₅ a₆).rw_star (saturate a₀ b a₂ a₃ a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_saturate₁ h)
    | .refl h => .refl (eqe.eqe_saturate rfl h (kSatMode.eqe_refl a₂) (kBlockRoundMode.eqe_refl a₃) (kXReal.eqe_refl a₄) (kSignedness.eqe_refl a₅) (kDomain.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_saturate₁ h₀) (rw_star_sub_saturate₁ h₁)
  theorem rw_star_sub_saturate₂ {a₀ a₁ : MRat} {a b : kSatMode} {a₃ : kBlockRoundMode} {a₄ : kXReal} {a₅ : kSignedness} {a₆ : kDomain} : a.rw_star b →
      (saturate a₀ a₁ a a₃ a₄ a₅ a₆).rw_star (saturate a₀ a₁ b a₃ a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_saturate₂ h)
    | .refl h => .refl (eqe.eqe_saturate rfl rfl h (kBlockRoundMode.eqe_refl a₃) (kXReal.eqe_refl a₄) (kSignedness.eqe_refl a₅) (kDomain.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_saturate₂ h₀) (rw_star_sub_saturate₂ h₁)
  theorem rw_star_sub_saturate₃ {a₀ a₁ : MRat} {a₂ : kSatMode} {a b : kBlockRoundMode} {a₄ : kXReal} {a₅ : kSignedness} {a₆ : kDomain} : a.rw_star b →
      (saturate a₀ a₁ a₂ a a₄ a₅ a₆).rw_star (saturate a₀ a₁ a₂ b a₄ a₅ a₆)
    | .step h => .step (rw_one.sub_saturate₃ h)
    | .refl h => .refl (eqe.eqe_saturate rfl rfl (kSatMode.eqe_refl a₂) h (kXReal.eqe_refl a₄) (kSignedness.eqe_refl a₅) (kDomain.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_saturate₃ h₀) (rw_star_sub_saturate₃ h₁)
  theorem rw_star_sub_saturate₄ {a₀ a₁ : MRat} {a₂ : kSatMode} {a₃ : kBlockRoundMode} {a b : kXReal} {a₅ : kSignedness} {a₆ : kDomain} : a.rw_star b →
      (saturate a₀ a₁ a₂ a₃ a a₅ a₆).rw_star (saturate a₀ a₁ a₂ a₃ b a₅ a₆)
    | .step h => .step (rw_one.sub_saturate₄ h)
    | .refl h => .refl (eqe.eqe_saturate rfl rfl (kSatMode.eqe_refl a₂) (kBlockRoundMode.eqe_refl a₃) h (kSignedness.eqe_refl a₅) (kDomain.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_saturate₄ h₀) (rw_star_sub_saturate₄ h₁)
  theorem rw_star_sub_saturate₅ {a₀ a₁ : MRat} {a₂ : kSatMode} {a₃ : kBlockRoundMode} {a₄ : kXReal} {a b : kSignedness} {a₆ : kDomain} : a.rw_star b →
      (saturate a₀ a₁ a₂ a₃ a₄ a a₆).rw_star (saturate a₀ a₁ a₂ a₃ a₄ b a₆)
    | .step h => .step (rw_one.sub_saturate₅ h)
    | .refl h => .refl (eqe.eqe_saturate rfl rfl (kSatMode.eqe_refl a₂) (kBlockRoundMode.eqe_refl a₃) (kXReal.eqe_refl a₄) h (kDomain.eqe_refl a₆))
    | .trans h₀ h₁ => .trans (rw_star_sub_saturate₅ h₀) (rw_star_sub_saturate₅ h₁)
  theorem rw_star_sub_saturate₆ {a₀ a₁ : MRat} {a₂ : kSatMode} {a₃ : kBlockRoundMode} {a₄ : kXReal} {a₅ : kSignedness} {a b : kDomain} : a.rw_star b →
      (saturate a₀ a₁ a₂ a₃ a₄ a₅ a).rw_star (saturate a₀ a₁ a₂ a₃ a₄ a₅ b)
    | .step h => .step (rw_one.sub_saturate₆ h)
    | .refl h => .refl (eqe.eqe_saturate rfl rfl (kSatMode.eqe_refl a₂) (kBlockRoundMode.eqe_refl a₃) (kXReal.eqe_refl a₄) (kSignedness.eqe_refl a₅) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_saturate₆ h₀) (rw_star_sub_saturate₆ h₁)
  theorem rw_star_sub_overflow₀ {a b : kSignedness} {a₁ : kDomain} {a₂ : kBool} : a.rw_star b →
      (overflow a a₁ a₂).rw_star (overflow b a₁ a₂)
    | .step h => .step (rw_one.sub_overflow₀ h)
    | .refl h => .refl (eqe.eqe_overflow h (kDomain.eqe_refl a₁) (kBool.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_overflow₀ h₀) (rw_star_sub_overflow₀ h₁)
  theorem rw_star_sub_overflow₁ {a₀ : kSignedness} {a b : kDomain} {a₂ : kBool} : a.rw_star b →
      (overflow a₀ a a₂).rw_star (overflow a₀ b a₂)
    | .step h => .step (rw_one.sub_overflow₁ h)
    | .refl h => .refl (eqe.eqe_overflow (kSignedness.eqe_refl a₀) h (kBool.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_overflow₁ h₀) (rw_star_sub_overflow₁ h₁)
  theorem rw_star_sub_overflow₂ {a₀ : kSignedness} {a₁ : kDomain} {a b : kBool} : a.rw_star b →
      (overflow a₀ a₁ a).rw_star (overflow a₀ a₁ b)
    | .step h => .step (rw_one.sub_overflow₂ h)
    | .refl h => .refl (eqe.eqe_overflow (kSignedness.eqe_refl a₀) (kDomain.eqe_refl a₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_overflow₂ h₀) (rw_star_sub_overflow₂ h₁)
  theorem rw_star_sub_omegaConvert {a b : kXReal} : a.rw_star b →
      (omegaConvert a).rw_star (omegaConvert b)
    | .step h => .step (rw_one.sub_omegaConvert h)
    | .refl h => .refl (eqe.eqe_omegaConvert h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaConvert h₀) (rw_star_sub_omegaConvert h₁)
  theorem rw_star_sub_omegaAbs {a b : kXReal} : a.rw_star b →
      (omegaAbs a).rw_star (omegaAbs b)
    | .step h => .step (rw_one.sub_omegaAbs h)
    | .refl h => .refl (eqe.eqe_omegaAbs h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaAbs h₀) (rw_star_sub_omegaAbs h₁)
  theorem rw_star_sub_omegaNegate {a b : kXReal} : a.rw_star b →
      (omegaNegate a).rw_star (omegaNegate b)
    | .step h => .step (rw_one.sub_omegaNegate h)
    | .refl h => .refl (eqe.eqe_omegaNegate h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaNegate h₀) (rw_star_sub_omegaNegate h₁)
  theorem rw_star_sub_omegaRecip {a b : kXReal} : a.rw_star b →
      (omegaRecip a).rw_star (omegaRecip b)
    | .step h => .step (rw_one.sub_omegaRecip h)
    | .refl h => .refl (eqe.eqe_omegaRecip h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaRecip h₀) (rw_star_sub_omegaRecip h₁)
  theorem rw_star_sub_omegaCopySign₀ {a b a₁ : kXReal} : a.rw_star b →
      (omegaCopySign a a₁).rw_star (omegaCopySign b a₁)
    | .step h => .step (rw_one.sub_omegaCopySign₀ h)
    | .refl h => .refl (eqe.eqe_omegaCopySign h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaCopySign₀ h₀) (rw_star_sub_omegaCopySign₀ h₁)
  theorem rw_star_sub_omegaCopySign₁ {a₀ a b : kXReal} : a.rw_star b →
      (omegaCopySign a₀ a).rw_star (omegaCopySign a₀ b)
    | .step h => .step (rw_one.sub_omegaCopySign₁ h)
    | .refl h => .refl (eqe.eqe_omegaCopySign (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaCopySign₁ h₀) (rw_star_sub_omegaCopySign₁ h₁)
  theorem rw_star_sub_omegaAdd₀ {a b a₁ : kXReal} : a.rw_star b →
      (omegaAdd a a₁).rw_star (omegaAdd b a₁)
    | .step h => .step (rw_one.sub_omegaAdd₀ h)
    | .refl h => .refl (eqe.eqe_omegaAdd h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaAdd₀ h₀) (rw_star_sub_omegaAdd₀ h₁)
  theorem rw_star_sub_omegaAdd₁ {a₀ a b : kXReal} : a.rw_star b →
      (omegaAdd a₀ a).rw_star (omegaAdd a₀ b)
    | .step h => .step (rw_one.sub_omegaAdd₁ h)
    | .refl h => .refl (eqe.eqe_omegaAdd (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaAdd₁ h₀) (rw_star_sub_omegaAdd₁ h₁)
  theorem rw_star_sub_omegaSubtract₀ {a b a₁ : kXReal} : a.rw_star b →
      (omegaSubtract a a₁).rw_star (omegaSubtract b a₁)
    | .step h => .step (rw_one.sub_omegaSubtract₀ h)
    | .refl h => .refl (eqe.eqe_omegaSubtract h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaSubtract₀ h₀) (rw_star_sub_omegaSubtract₀ h₁)
  theorem rw_star_sub_omegaSubtract₁ {a₀ a b : kXReal} : a.rw_star b →
      (omegaSubtract a₀ a).rw_star (omegaSubtract a₀ b)
    | .step h => .step (rw_one.sub_omegaSubtract₁ h)
    | .refl h => .refl (eqe.eqe_omegaSubtract (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaSubtract₁ h₀) (rw_star_sub_omegaSubtract₁ h₁)
  theorem rw_star_sub_omegaMultiply₀ {a b a₁ : kXReal} : a.rw_star b →
      (omegaMultiply a a₁).rw_star (omegaMultiply b a₁)
    | .step h => .step (rw_one.sub_omegaMultiply₀ h)
    | .refl h => .refl (eqe.eqe_omegaMultiply h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMultiply₀ h₀) (rw_star_sub_omegaMultiply₀ h₁)
  theorem rw_star_sub_omegaMultiply₁ {a₀ a b : kXReal} : a.rw_star b →
      (omegaMultiply a₀ a).rw_star (omegaMultiply a₀ b)
    | .step h => .step (rw_one.sub_omegaMultiply₁ h)
    | .refl h => .refl (eqe.eqe_omegaMultiply (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMultiply₁ h₀) (rw_star_sub_omegaMultiply₁ h₁)
  theorem rw_star_sub_omegaDivide₀ {a b a₁ : kXReal} : a.rw_star b →
      (omegaDivide a a₁).rw_star (omegaDivide b a₁)
    | .step h => .step (rw_one.sub_omegaDivide₀ h)
    | .refl h => .refl (eqe.eqe_omegaDivide h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaDivide₀ h₀) (rw_star_sub_omegaDivide₀ h₁)
  theorem rw_star_sub_omegaDivide₁ {a₀ a b : kXReal} : a.rw_star b →
      (omegaDivide a₀ a).rw_star (omegaDivide a₀ b)
    | .step h => .step (rw_one.sub_omegaDivide₁ h)
    | .refl h => .refl (eqe.eqe_omegaDivide (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaDivide₁ h₀) (rw_star_sub_omegaDivide₁ h₁)
  theorem rw_star_sub_omegaFMA₀ {a b a₁ a₂ : kXReal} : a.rw_star b →
      (omegaFMA a a₁ a₂).rw_star (omegaFMA b a₁ a₂)
    | .step h => .step (rw_one.sub_omegaFMA₀ h)
    | .refl h => .refl (eqe.eqe_omegaFMA h (kXReal.eqe_refl a₁) (kXReal.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaFMA₀ h₀) (rw_star_sub_omegaFMA₀ h₁)
  theorem rw_star_sub_omegaFMA₁ {a₀ a b a₂ : kXReal} : a.rw_star b →
      (omegaFMA a₀ a a₂).rw_star (omegaFMA a₀ b a₂)
    | .step h => .step (rw_one.sub_omegaFMA₁ h)
    | .refl h => .refl (eqe.eqe_omegaFMA (kXReal.eqe_refl a₀) h (kXReal.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaFMA₁ h₀) (rw_star_sub_omegaFMA₁ h₁)
  theorem rw_star_sub_omegaFMA₂ {a₀ a₁ a b : kXReal} : a.rw_star b →
      (omegaFMA a₀ a₁ a).rw_star (omegaFMA a₀ a₁ b)
    | .step h => .step (rw_one.sub_omegaFMA₂ h)
    | .refl h => .refl (eqe.eqe_omegaFMA (kXReal.eqe_refl a₀) (kXReal.eqe_refl a₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaFMA₂ h₀) (rw_star_sub_omegaFMA₂ h₁)
  theorem rw_star_sub_omegaFAA₀ {a b a₁ a₂ : kXReal} : a.rw_star b →
      (omegaFAA a a₁ a₂).rw_star (omegaFAA b a₁ a₂)
    | .step h => .step (rw_one.sub_omegaFAA₀ h)
    | .refl h => .refl (eqe.eqe_omegaFAA h (kXReal.eqe_refl a₁) (kXReal.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaFAA₀ h₀) (rw_star_sub_omegaFAA₀ h₁)
  theorem rw_star_sub_omegaFAA₁ {a₀ a b a₂ : kXReal} : a.rw_star b →
      (omegaFAA a₀ a a₂).rw_star (omegaFAA a₀ b a₂)
    | .step h => .step (rw_one.sub_omegaFAA₁ h)
    | .refl h => .refl (eqe.eqe_omegaFAA (kXReal.eqe_refl a₀) h (kXReal.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaFAA₁ h₀) (rw_star_sub_omegaFAA₁ h₁)
  theorem rw_star_sub_omegaFAA₂ {a₀ a₁ a b : kXReal} : a.rw_star b →
      (omegaFAA a₀ a₁ a).rw_star (omegaFAA a₀ a₁ b)
    | .step h => .step (rw_one.sub_omegaFAA₂ h)
    | .refl h => .refl (eqe.eqe_omegaFAA (kXReal.eqe_refl a₀) (kXReal.eqe_refl a₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaFAA₂ h₀) (rw_star_sub_omegaFAA₂ h₁)
  theorem rw_star_sub_at₀ {a b : kXSeq} {a₁ : MRat} : a.rw_star b →
      («at» a a₁).rw_star («at» b a₁)
    | .step h => .step (rw_one.sub_at₀ h)
    | .refl h => .refl (eqe.eqe_at h rfl)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₀ h₀) (rw_star_sub_at₀ h₁)
  theorem rw_star_sub_at₁ {a₀ : kXSeq} {a b : MRat} : MRat.rw_star a b →
      («at» a₀ a).rw_star («at» a₀ b)
    | .step h => .step (rw_one.sub_at₁ h)
    | .refl h => .refl (eqe.eqe_at (kXSeq.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_at₁ h₀) (rw_star_sub_at₁ h₁)
  theorem rw_star_sub_normalizeElement₀ {a b a₁ : kXReal} : a.rw_star b →
      (normalizeElement a a₁).rw_star (normalizeElement b a₁)
    | .step h => .step (rw_one.sub_normalizeElement₀ h)
    | .refl h => .refl (eqe.eqe_normalizeElement h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_normalizeElement₀ h₀) (rw_star_sub_normalizeElement₀ h₁)
  theorem rw_star_sub_normalizeElement₁ {a₀ a b : kXReal} : a.rw_star b →
      (normalizeElement a₀ a).rw_star (normalizeElement a₀ b)
    | .step h => .step (rw_one.sub_normalizeElement₁ h)
    | .refl h => .refl (eqe.eqe_normalizeElement (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_normalizeElement₁ h₀) (rw_star_sub_normalizeElement₁ h₁)
  theorem rw_star_sub_omegaMinimum₀ {a b a₁ : kXReal} : a.rw_star b →
      (omegaMinimum a a₁).rw_star (omegaMinimum b a₁)
    | .step h => .step (rw_one.sub_omegaMinimum₀ h)
    | .refl h => .refl (eqe.eqe_omegaMinimum h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMinimum₀ h₀) (rw_star_sub_omegaMinimum₀ h₁)
  theorem rw_star_sub_omegaMinimum₁ {a₀ a b : kXReal} : a.rw_star b →
      (omegaMinimum a₀ a).rw_star (omegaMinimum a₀ b)
    | .step h => .step (rw_one.sub_omegaMinimum₁ h)
    | .refl h => .refl (eqe.eqe_omegaMinimum (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMinimum₁ h₀) (rw_star_sub_omegaMinimum₁ h₁)
  theorem rw_star_sub_omegaMaximum₀ {a b a₁ : kXReal} : a.rw_star b →
      (omegaMaximum a a₁).rw_star (omegaMaximum b a₁)
    | .step h => .step (rw_one.sub_omegaMaximum₀ h)
    | .refl h => .refl (eqe.eqe_omegaMaximum h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMaximum₀ h₀) (rw_star_sub_omegaMaximum₀ h₁)
  theorem rw_star_sub_omegaMaximum₁ {a₀ a b : kXReal} : a.rw_star b →
      (omegaMaximum a₀ a).rw_star (omegaMaximum a₀ b)
    | .step h => .step (rw_one.sub_omegaMaximum₁ h)
    | .refl h => .refl (eqe.eqe_omegaMaximum (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMaximum₁ h₀) (rw_star_sub_omegaMaximum₁ h₁)
  theorem rw_star_sub_omegaMinimumNumber₀ {a b a₁ : kXReal} : a.rw_star b →
      (omegaMinimumNumber a a₁).rw_star (omegaMinimumNumber b a₁)
    | .step h => .step (rw_one.sub_omegaMinimumNumber₀ h)
    | .refl h => .refl (eqe.eqe_omegaMinimumNumber h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMinimumNumber₀ h₀) (rw_star_sub_omegaMinimumNumber₀ h₁)
  theorem rw_star_sub_omegaMinimumNumber₁ {a₀ a b : kXReal} : a.rw_star b →
      (omegaMinimumNumber a₀ a).rw_star (omegaMinimumNumber a₀ b)
    | .step h => .step (rw_one.sub_omegaMinimumNumber₁ h)
    | .refl h => .refl (eqe.eqe_omegaMinimumNumber (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMinimumNumber₁ h₀) (rw_star_sub_omegaMinimumNumber₁ h₁)
  theorem rw_star_sub_omegaMaximumNumber₀ {a b a₁ : kXReal} : a.rw_star b →
      (omegaMaximumNumber a a₁).rw_star (omegaMaximumNumber b a₁)
    | .step h => .step (rw_one.sub_omegaMaximumNumber₀ h)
    | .refl h => .refl (eqe.eqe_omegaMaximumNumber h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMaximumNumber₀ h₀) (rw_star_sub_omegaMaximumNumber₀ h₁)
  theorem rw_star_sub_omegaMaximumNumber₁ {a₀ a b : kXReal} : a.rw_star b →
      (omegaMaximumNumber a₀ a).rw_star (omegaMaximumNumber a₀ b)
    | .step h => .step (rw_one.sub_omegaMaximumNumber₁ h)
    | .refl h => .refl (eqe.eqe_omegaMaximumNumber (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMaximumNumber₁ h₀) (rw_star_sub_omegaMaximumNumber₁ h₁)
  theorem rw_star_sub_omegaMinimumMagnitude₀ {a b a₁ : kXReal} : a.rw_star b →
      (omegaMinimumMagnitude a a₁).rw_star (omegaMinimumMagnitude b a₁)
    | .step h => .step (rw_one.sub_omegaMinimumMagnitude₀ h)
    | .refl h => .refl (eqe.eqe_omegaMinimumMagnitude h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMinimumMagnitude₀ h₀) (rw_star_sub_omegaMinimumMagnitude₀ h₁)
  theorem rw_star_sub_omegaMinimumMagnitude₁ {a₀ a b : kXReal} : a.rw_star b →
      (omegaMinimumMagnitude a₀ a).rw_star (omegaMinimumMagnitude a₀ b)
    | .step h => .step (rw_one.sub_omegaMinimumMagnitude₁ h)
    | .refl h => .refl (eqe.eqe_omegaMinimumMagnitude (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMinimumMagnitude₁ h₀) (rw_star_sub_omegaMinimumMagnitude₁ h₁)
  theorem rw_star_sub_omegaMaximumMagnitude₀ {a b a₁ : kXReal} : a.rw_star b →
      (omegaMaximumMagnitude a a₁).rw_star (omegaMaximumMagnitude b a₁)
    | .step h => .step (rw_one.sub_omegaMaximumMagnitude₀ h)
    | .refl h => .refl (eqe.eqe_omegaMaximumMagnitude h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMaximumMagnitude₀ h₀) (rw_star_sub_omegaMaximumMagnitude₀ h₁)
  theorem rw_star_sub_omegaMaximumMagnitude₁ {a₀ a b : kXReal} : a.rw_star b →
      (omegaMaximumMagnitude a₀ a).rw_star (omegaMaximumMagnitude a₀ b)
    | .step h => .step (rw_one.sub_omegaMaximumMagnitude₁ h)
    | .refl h => .refl (eqe.eqe_omegaMaximumMagnitude (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMaximumMagnitude₁ h₀) (rw_star_sub_omegaMaximumMagnitude₁ h₁)
  theorem rw_star_sub_omegaMinimumMagnitudeNumber₀ {a b a₁ : kXReal} : a.rw_star b →
      (omegaMinimumMagnitudeNumber a a₁).rw_star (omegaMinimumMagnitudeNumber b a₁)
    | .step h => .step (rw_one.sub_omegaMinimumMagnitudeNumber₀ h)
    | .refl h => .refl (eqe.eqe_omegaMinimumMagnitudeNumber h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMinimumMagnitudeNumber₀ h₀) (rw_star_sub_omegaMinimumMagnitudeNumber₀ h₁)
  theorem rw_star_sub_omegaMinimumMagnitudeNumber₁ {a₀ a b : kXReal} : a.rw_star b →
      (omegaMinimumMagnitudeNumber a₀ a).rw_star (omegaMinimumMagnitudeNumber a₀ b)
    | .step h => .step (rw_one.sub_omegaMinimumMagnitudeNumber₁ h)
    | .refl h => .refl (eqe.eqe_omegaMinimumMagnitudeNumber (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMinimumMagnitudeNumber₁ h₀) (rw_star_sub_omegaMinimumMagnitudeNumber₁ h₁)
  theorem rw_star_sub_omegaMaximumMagnitudeNumber₀ {a b a₁ : kXReal} : a.rw_star b →
      (omegaMaximumMagnitudeNumber a a₁).rw_star (omegaMaximumMagnitudeNumber b a₁)
    | .step h => .step (rw_one.sub_omegaMaximumMagnitudeNumber₀ h)
    | .refl h => .refl (eqe.eqe_omegaMaximumMagnitudeNumber h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMaximumMagnitudeNumber₀ h₀) (rw_star_sub_omegaMaximumMagnitudeNumber₀ h₁)
  theorem rw_star_sub_omegaMaximumMagnitudeNumber₁ {a₀ a b : kXReal} : a.rw_star b →
      (omegaMaximumMagnitudeNumber a₀ a).rw_star (omegaMaximumMagnitudeNumber a₀ b)
    | .step h => .step (rw_one.sub_omegaMaximumMagnitudeNumber₁ h)
    | .refl h => .refl (eqe.eqe_omegaMaximumMagnitudeNumber (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMaximumMagnitudeNumber₁ h₀) (rw_star_sub_omegaMaximumMagnitudeNumber₁ h₁)
  theorem rw_star_sub_omegaMinimumFinite₀ {a b a₁ : kXReal} : a.rw_star b →
      (omegaMinimumFinite a a₁).rw_star (omegaMinimumFinite b a₁)
    | .step h => .step (rw_one.sub_omegaMinimumFinite₀ h)
    | .refl h => .refl (eqe.eqe_omegaMinimumFinite h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMinimumFinite₀ h₀) (rw_star_sub_omegaMinimumFinite₀ h₁)
  theorem rw_star_sub_omegaMinimumFinite₁ {a₀ a b : kXReal} : a.rw_star b →
      (omegaMinimumFinite a₀ a).rw_star (omegaMinimumFinite a₀ b)
    | .step h => .step (rw_one.sub_omegaMinimumFinite₁ h)
    | .refl h => .refl (eqe.eqe_omegaMinimumFinite (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMinimumFinite₁ h₀) (rw_star_sub_omegaMinimumFinite₁ h₁)
  theorem rw_star_sub_omegaMaximumFinite₀ {a b a₁ : kXReal} : a.rw_star b →
      (omegaMaximumFinite a a₁).rw_star (omegaMaximumFinite b a₁)
    | .step h => .step (rw_one.sub_omegaMaximumFinite₀ h)
    | .refl h => .refl (eqe.eqe_omegaMaximumFinite h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMaximumFinite₀ h₀) (rw_star_sub_omegaMaximumFinite₀ h₁)
  theorem rw_star_sub_omegaMaximumFinite₁ {a₀ a b : kXReal} : a.rw_star b →
      (omegaMaximumFinite a₀ a).rw_star (omegaMaximumFinite a₀ b)
    | .step h => .step (rw_one.sub_omegaMaximumFinite₁ h)
    | .refl h => .refl (eqe.eqe_omegaMaximumFinite (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaMaximumFinite₁ h₀) (rw_star_sub_omegaMaximumFinite₁ h₁)
  theorem rw_star_sub_omegaClamp₀ {a b a₁ a₂ : kXReal} : a.rw_star b →
      (omegaClamp a a₁ a₂).rw_star (omegaClamp b a₁ a₂)
    | .step h => .step (rw_one.sub_omegaClamp₀ h)
    | .refl h => .refl (eqe.eqe_omegaClamp h (kXReal.eqe_refl a₁) (kXReal.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaClamp₀ h₀) (rw_star_sub_omegaClamp₀ h₁)
  theorem rw_star_sub_omegaClamp₁ {a₀ a b a₂ : kXReal} : a.rw_star b →
      (omegaClamp a₀ a a₂).rw_star (omegaClamp a₀ b a₂)
    | .step h => .step (rw_one.sub_omegaClamp₁ h)
    | .refl h => .refl (eqe.eqe_omegaClamp (kXReal.eqe_refl a₀) h (kXReal.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaClamp₁ h₀) (rw_star_sub_omegaClamp₁ h₁)
  theorem rw_star_sub_omegaClamp₂ {a₀ a₁ a b : kXReal} : a.rw_star b →
      (omegaClamp a₀ a₁ a).rw_star (omegaClamp a₀ a₁ b)
    | .step h => .step (rw_one.sub_omegaClamp₂ h)
    | .refl h => .refl (eqe.eqe_omegaClamp (kXReal.eqe_refl a₀) (kXReal.eqe_refl a₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaClamp₂ h₀) (rw_star_sub_omegaClamp₂ h₁)
  theorem rw_star_sub_foldAdd₀ {a b : kXReal} {a₁ : kXSeq} : a.rw_star b →
      (foldAdd a a₁).rw_star (foldAdd b a₁)
    | .step h => .step (rw_one.sub_foldAdd₀ h)
    | .refl h => .refl (eqe.eqe_foldAdd h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_foldAdd₀ h₀) (rw_star_sub_foldAdd₀ h₁)
  theorem rw_star_sub_foldAdd₁ {a₀ : kXReal} {a b : kXSeq} : a.rw_star b →
      (foldAdd a₀ a).rw_star (foldAdd a₀ b)
    | .step h => .step (rw_one.sub_foldAdd₁ h)
    | .refl h => .refl (eqe.eqe_foldAdd (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_foldAdd₁ h₀) (rw_star_sub_foldAdd₁ h₁)
  theorem rw_star_sub_foldMultiply₀ {a b : kXReal} {a₁ : kXSeq} : a.rw_star b →
      (foldMultiply a a₁).rw_star (foldMultiply b a₁)
    | .step h => .step (rw_one.sub_foldMultiply₀ h)
    | .refl h => .refl (eqe.eqe_foldMultiply h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_foldMultiply₀ h₀) (rw_star_sub_foldMultiply₀ h₁)
  theorem rw_star_sub_foldMultiply₁ {a₀ : kXReal} {a b : kXSeq} : a.rw_star b →
      (foldMultiply a₀ a).rw_star (foldMultiply a₀ b)
    | .step h => .step (rw_one.sub_foldMultiply₁ h)
    | .refl h => .refl (eqe.eqe_foldMultiply (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_foldMultiply₁ h₀) (rw_star_sub_foldMultiply₁ h₁)
  theorem rw_star_sub_foldMaximumFinite₀ {a b : kXReal} {a₁ : kXSeq} : a.rw_star b →
      (foldMaximumFinite a a₁).rw_star (foldMaximumFinite b a₁)
    | .step h => .step (rw_one.sub_foldMaximumFinite₀ h)
    | .refl h => .refl (eqe.eqe_foldMaximumFinite h (kXSeq.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_foldMaximumFinite₀ h₀) (rw_star_sub_foldMaximumFinite₀ h₁)
  theorem rw_star_sub_foldMaximumFinite₁ {a₀ : kXReal} {a b : kXSeq} : a.rw_star b →
      (foldMaximumFinite a₀ a).rw_star (foldMaximumFinite a₀ b)
    | .step h => .step (rw_one.sub_foldMaximumFinite₁ h)
    | .refl h => .refl (eqe.eqe_foldMaximumFinite (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_foldMaximumFinite₁ h₀) (rw_star_sub_foldMaximumFinite₁ h₁)
  theorem rw_star_sub_realAdd₀ {a b a₁ : kXReal} : a.rw_star b →
      (realAdd a a₁).rw_star (realAdd b a₁)
    | .step h => .step (rw_one.sub_realAdd₀ h)
    | .refl h => .refl (eqe.eqe_realAdd h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_realAdd₀ h₀) (rw_star_sub_realAdd₀ h₁)
  theorem rw_star_sub_realAdd₁ {a₀ a b : kXReal} : a.rw_star b →
      (realAdd a₀ a).rw_star (realAdd a₀ b)
    | .step h => .step (rw_one.sub_realAdd₁ h)
    | .refl h => .refl (eqe.eqe_realAdd (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_realAdd₁ h₀) (rw_star_sub_realAdd₁ h₁)
  theorem rw_star_sub_realMultiply₀ {a b a₁ : kXReal} : a.rw_star b →
      (realMultiply a a₁).rw_star (realMultiply b a₁)
    | .step h => .step (rw_one.sub_realMultiply₀ h)
    | .refl h => .refl (eqe.eqe_realMultiply h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_realMultiply₀ h₀) (rw_star_sub_realMultiply₀ h₁)
  theorem rw_star_sub_realMultiply₁ {a₀ a b : kXReal} : a.rw_star b →
      (realMultiply a₀ a).rw_star (realMultiply a₀ b)
    | .step h => .step (rw_one.sub_realMultiply₁ h)
    | .refl h => .refl (eqe.eqe_realMultiply (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_realMultiply₁ h₀) (rw_star_sub_realMultiply₁ h₁)
  theorem rw_star_sub_realNegate {a b : kXReal} : a.rw_star b →
      (realNegate a).rw_star (realNegate b)
    | .step h => .step (rw_one.sub_realNegate h)
    | .refl h => .refl (eqe.eqe_realNegate h)
    | .trans h₀ h₁ => .trans (rw_star_sub_realNegate h₀) (rw_star_sub_realNegate h₁)
  theorem rw_star_sub_realAbs {a b : kXReal} : a.rw_star b →
      (realAbs a).rw_star (realAbs b)
    | .step h => .step (rw_one.sub_realAbs h)
    | .refl h => .refl (eqe.eqe_realAbs h)
    | .trans h₀ h₁ => .trans (rw_star_sub_realAbs h₀) (rw_star_sub_realAbs h₁)
  theorem rw_star_sub_realDivide₀ {a b a₁ : kXReal} : a.rw_star b →
      (realDivide a a₁).rw_star (realDivide b a₁)
    | .step h => .step (rw_one.sub_realDivide₀ h)
    | .refl h => .refl (eqe.eqe_realDivide h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_realDivide₀ h₀) (rw_star_sub_realDivide₀ h₁)
  theorem rw_star_sub_realDivide₁ {a₀ a b : kXReal} : a.rw_star b →
      (realDivide a₀ a).rw_star (realDivide a₀ b)
    | .step h => .step (rw_one.sub_realDivide₁ h)
    | .refl h => .refl (eqe.eqe_realDivide (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_realDivide₁ h₀) (rw_star_sub_realDivide₁ h₁)
  theorem rw_star_sub_piMultiple {a b : MRat} : MRat.rw_star a b →
      (piMultiple a).rw_star (piMultiple b)
    | .step h => .step (rw_one.sub_piMultiple h)
    | .refl h => .refl (eqe.eqe_piMultiple h)
    | .trans h₀ h₁ => .trans (rw_star_sub_piMultiple h₀) (rw_star_sub_piMultiple h₁)
  theorem rw_star_sub_omegaHypot₀ {a b a₁ : kXReal} : a.rw_star b →
      (omegaHypot a a₁).rw_star (omegaHypot b a₁)
    | .step h => .step (rw_one.sub_omegaHypot₀ h)
    | .refl h => .refl (eqe.eqe_omegaHypot h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaHypot₀ h₀) (rw_star_sub_omegaHypot₀ h₁)
  theorem rw_star_sub_omegaHypot₁ {a₀ a b : kXReal} : a.rw_star b →
      (omegaHypot a₀ a).rw_star (omegaHypot a₀ b)
    | .step h => .step (rw_one.sub_omegaHypot₁ h)
    | .refl h => .refl (eqe.eqe_omegaHypot (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaHypot₁ h₀) (rw_star_sub_omegaHypot₁ h₁)
  theorem rw_star_sub_omegaArcTan2₀ {a b a₁ : kXReal} : a.rw_star b →
      (omegaArcTan2 a a₁).rw_star (omegaArcTan2 b a₁)
    | .step h => .step (rw_one.sub_omegaArcTan2₀ h)
    | .refl h => .refl (eqe.eqe_omegaArcTan2 h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaArcTan2₀ h₀) (rw_star_sub_omegaArcTan2₀ h₁)
  theorem rw_star_sub_omegaArcTan2₁ {a₀ a b : kXReal} : a.rw_star b →
      (omegaArcTan2 a₀ a).rw_star (omegaArcTan2 a₀ b)
    | .step h => .step (rw_one.sub_omegaArcTan2₁ h)
    | .refl h => .refl (eqe.eqe_omegaArcTan2 (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaArcTan2₁ h₀) (rw_star_sub_omegaArcTan2₁ h₁)
  theorem rw_star_sub_omegaArcTan2Pi₀ {a b a₁ : kXReal} : a.rw_star b →
      (omegaArcTan2Pi a a₁).rw_star (omegaArcTan2Pi b a₁)
    | .step h => .step (rw_one.sub_omegaArcTan2Pi₀ h)
    | .refl h => .refl (eqe.eqe_omegaArcTan2Pi h (kXReal.eqe_refl a₁))
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaArcTan2Pi₀ h₀) (rw_star_sub_omegaArcTan2Pi₀ h₁)
  theorem rw_star_sub_omegaArcTan2Pi₁ {a₀ a b : kXReal} : a.rw_star b →
      (omegaArcTan2Pi a₀ a).rw_star (omegaArcTan2Pi a₀ b)
    | .step h => .step (rw_one.sub_omegaArcTan2Pi₁ h)
    | .refl h => .refl (eqe.eqe_omegaArcTan2Pi (kXReal.eqe_refl a₀) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaArcTan2Pi₁ h₀) (rw_star_sub_omegaArcTan2Pi₁ h₁)
  theorem rw_star_sub_omegaSqrt {a b : kXReal} : a.rw_star b →
      (omegaSqrt a).rw_star (omegaSqrt b)
    | .step h => .step (rw_one.sub_omegaSqrt h)
    | .refl h => .refl (eqe.eqe_omegaSqrt h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaSqrt h₀) (rw_star_sub_omegaSqrt h₁)
  theorem rw_star_sub_omegaRSqrt {a b : kXReal} : a.rw_star b →
      (omegaRSqrt a).rw_star (omegaRSqrt b)
    | .step h => .step (rw_one.sub_omegaRSqrt h)
    | .refl h => .refl (eqe.eqe_omegaRSqrt h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaRSqrt h₀) (rw_star_sub_omegaRSqrt h₁)
  theorem rw_star_sub_omegaExp {a b : kXReal} : a.rw_star b →
      (omegaExp a).rw_star (omegaExp b)
    | .step h => .step (rw_one.sub_omegaExp h)
    | .refl h => .refl (eqe.eqe_omegaExp h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaExp h₀) (rw_star_sub_omegaExp h₁)
  theorem rw_star_sub_omegaExp2 {a b : kXReal} : a.rw_star b →
      (omegaExp2 a).rw_star (omegaExp2 b)
    | .step h => .step (rw_one.sub_omegaExp2 h)
    | .refl h => .refl (eqe.eqe_omegaExp2 h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaExp2 h₀) (rw_star_sub_omegaExp2 h₁)
  theorem rw_star_sub_omegaLog {a b : kXReal} : a.rw_star b →
      (omegaLog a).rw_star (omegaLog b)
    | .step h => .step (rw_one.sub_omegaLog h)
    | .refl h => .refl (eqe.eqe_omegaLog h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaLog h₀) (rw_star_sub_omegaLog h₁)
  theorem rw_star_sub_omegaLog2 {a b : kXReal} : a.rw_star b →
      (omegaLog2 a).rw_star (omegaLog2 b)
    | .step h => .step (rw_one.sub_omegaLog2 h)
    | .refl h => .refl (eqe.eqe_omegaLog2 h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaLog2 h₀) (rw_star_sub_omegaLog2 h₁)
  theorem rw_star_sub_omegaLogOnePlus {a b : kXReal} : a.rw_star b →
      (omegaLogOnePlus a).rw_star (omegaLogOnePlus b)
    | .step h => .step (rw_one.sub_omegaLogOnePlus h)
    | .refl h => .refl (eqe.eqe_omegaLogOnePlus h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaLogOnePlus h₀) (rw_star_sub_omegaLogOnePlus h₁)
  theorem rw_star_sub_omegaExpMinusOne {a b : kXReal} : a.rw_star b →
      (omegaExpMinusOne a).rw_star (omegaExpMinusOne b)
    | .step h => .step (rw_one.sub_omegaExpMinusOne h)
    | .refl h => .refl (eqe.eqe_omegaExpMinusOne h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaExpMinusOne h₀) (rw_star_sub_omegaExpMinusOne h₁)
  theorem rw_star_sub_omegaSin {a b : kXReal} : a.rw_star b →
      (omegaSin a).rw_star (omegaSin b)
    | .step h => .step (rw_one.sub_omegaSin h)
    | .refl h => .refl (eqe.eqe_omegaSin h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaSin h₀) (rw_star_sub_omegaSin h₁)
  theorem rw_star_sub_omegaCos {a b : kXReal} : a.rw_star b →
      (omegaCos a).rw_star (omegaCos b)
    | .step h => .step (rw_one.sub_omegaCos h)
    | .refl h => .refl (eqe.eqe_omegaCos h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaCos h₀) (rw_star_sub_omegaCos h₁)
  theorem rw_star_sub_omegaTan {a b : kXReal} : a.rw_star b →
      (omegaTan a).rw_star (omegaTan b)
    | .step h => .step (rw_one.sub_omegaTan h)
    | .refl h => .refl (eqe.eqe_omegaTan h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaTan h₀) (rw_star_sub_omegaTan h₁)
  theorem rw_star_sub_omegaArcSin {a b : kXReal} : a.rw_star b →
      (omegaArcSin a).rw_star (omegaArcSin b)
    | .step h => .step (rw_one.sub_omegaArcSin h)
    | .refl h => .refl (eqe.eqe_omegaArcSin h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaArcSin h₀) (rw_star_sub_omegaArcSin h₁)
  theorem rw_star_sub_omegaArcCos {a b : kXReal} : a.rw_star b →
      (omegaArcCos a).rw_star (omegaArcCos b)
    | .step h => .step (rw_one.sub_omegaArcCos h)
    | .refl h => .refl (eqe.eqe_omegaArcCos h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaArcCos h₀) (rw_star_sub_omegaArcCos h₁)
  theorem rw_star_sub_omegaArcTan {a b : kXReal} : a.rw_star b →
      (omegaArcTan a).rw_star (omegaArcTan b)
    | .step h => .step (rw_one.sub_omegaArcTan h)
    | .refl h => .refl (eqe.eqe_omegaArcTan h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaArcTan h₀) (rw_star_sub_omegaArcTan h₁)
  theorem rw_star_sub_omegaSinh {a b : kXReal} : a.rw_star b →
      (omegaSinh a).rw_star (omegaSinh b)
    | .step h => .step (rw_one.sub_omegaSinh h)
    | .refl h => .refl (eqe.eqe_omegaSinh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaSinh h₀) (rw_star_sub_omegaSinh h₁)
  theorem rw_star_sub_omegaCosh {a b : kXReal} : a.rw_star b →
      (omegaCosh a).rw_star (omegaCosh b)
    | .step h => .step (rw_one.sub_omegaCosh h)
    | .refl h => .refl (eqe.eqe_omegaCosh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaCosh h₀) (rw_star_sub_omegaCosh h₁)
  theorem rw_star_sub_omegaTanh {a b : kXReal} : a.rw_star b →
      (omegaTanh a).rw_star (omegaTanh b)
    | .step h => .step (rw_one.sub_omegaTanh h)
    | .refl h => .refl (eqe.eqe_omegaTanh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaTanh h₀) (rw_star_sub_omegaTanh h₁)
  theorem rw_star_sub_omegaArcSinh {a b : kXReal} : a.rw_star b →
      (omegaArcSinh a).rw_star (omegaArcSinh b)
    | .step h => .step (rw_one.sub_omegaArcSinh h)
    | .refl h => .refl (eqe.eqe_omegaArcSinh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaArcSinh h₀) (rw_star_sub_omegaArcSinh h₁)
  theorem rw_star_sub_omegaArcCosh {a b : kXReal} : a.rw_star b →
      (omegaArcCosh a).rw_star (omegaArcCosh b)
    | .step h => .step (rw_one.sub_omegaArcCosh h)
    | .refl h => .refl (eqe.eqe_omegaArcCosh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaArcCosh h₀) (rw_star_sub_omegaArcCosh h₁)
  theorem rw_star_sub_omegaArcTanh {a b : kXReal} : a.rw_star b →
      (omegaArcTanh a).rw_star (omegaArcTanh b)
    | .step h => .step (rw_one.sub_omegaArcTanh h)
    | .refl h => .refl (eqe.eqe_omegaArcTanh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaArcTanh h₀) (rw_star_sub_omegaArcTanh h₁)
  theorem rw_star_sub_omegaSinPi {a b : kXReal} : a.rw_star b →
      (omegaSinPi a).rw_star (omegaSinPi b)
    | .step h => .step (rw_one.sub_omegaSinPi h)
    | .refl h => .refl (eqe.eqe_omegaSinPi h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaSinPi h₀) (rw_star_sub_omegaSinPi h₁)
  theorem rw_star_sub_omegaCosPi {a b : kXReal} : a.rw_star b →
      (omegaCosPi a).rw_star (omegaCosPi b)
    | .step h => .step (rw_one.sub_omegaCosPi h)
    | .refl h => .refl (eqe.eqe_omegaCosPi h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaCosPi h₀) (rw_star_sub_omegaCosPi h₁)
  theorem rw_star_sub_omegaTanPi {a b : kXReal} : a.rw_star b →
      (omegaTanPi a).rw_star (omegaTanPi b)
    | .step h => .step (rw_one.sub_omegaTanPi h)
    | .refl h => .refl (eqe.eqe_omegaTanPi h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaTanPi h₀) (rw_star_sub_omegaTanPi h₁)
  theorem rw_star_sub_omegaArcSinPi {a b : kXReal} : a.rw_star b →
      (omegaArcSinPi a).rw_star (omegaArcSinPi b)
    | .step h => .step (rw_one.sub_omegaArcSinPi h)
    | .refl h => .refl (eqe.eqe_omegaArcSinPi h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaArcSinPi h₀) (rw_star_sub_omegaArcSinPi h₁)
  theorem rw_star_sub_omegaArcCosPi {a b : kXReal} : a.rw_star b →
      (omegaArcCosPi a).rw_star (omegaArcCosPi b)
    | .step h => .step (rw_one.sub_omegaArcCosPi h)
    | .refl h => .refl (eqe.eqe_omegaArcCosPi h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaArcCosPi h₀) (rw_star_sub_omegaArcCosPi h₁)
  theorem rw_star_sub_omegaArcTanPi {a b : kXReal} : a.rw_star b →
      (omegaArcTanPi a).rw_star (omegaArcTanPi b)
    | .step h => .step (rw_one.sub_omegaArcTanPi h)
    | .refl h => .refl (eqe.eqe_omegaArcTanPi h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaArcTanPi h₀) (rw_star_sub_omegaArcTanPi h₁)
  theorem rw_star_sub_omegaSoftplus {a b : kXReal} : a.rw_star b →
      (omegaSoftplus a).rw_star (omegaSoftplus b)
    | .step h => .step (rw_one.sub_omegaSoftplus h)
    | .refl h => .refl (eqe.eqe_omegaSoftplus h)
    | .trans h₀ h₁ => .trans (rw_star_sub_omegaSoftplus h₀) (rw_star_sub_omegaSoftplus h₁)
  theorem rw_star_sub_exprSqrt {a b : kXReal} : a.rw_star b →
      (exprSqrt a).rw_star (exprSqrt b)
    | .step h => .step (rw_one.sub_exprSqrt h)
    | .refl h => .refl (eqe.eqe_exprSqrt h)
    | .trans h₀ h₁ => .trans (rw_star_sub_exprSqrt h₀) (rw_star_sub_exprSqrt h₁)
  theorem rw_star_sub_exprExp {a b : kXReal} : a.rw_star b →
      (exprExp a).rw_star (exprExp b)
    | .step h => .step (rw_one.sub_exprExp h)
    | .refl h => .refl (eqe.eqe_exprExp h)
    | .trans h₀ h₁ => .trans (rw_star_sub_exprExp h₀) (rw_star_sub_exprExp h₁)
  theorem rw_star_sub_exprExp2 {a b : kXReal} : a.rw_star b →
      (exprExp2 a).rw_star (exprExp2 b)
    | .step h => .step (rw_one.sub_exprExp2 h)
    | .refl h => .refl (eqe.eqe_exprExp2 h)
    | .trans h₀ h₁ => .trans (rw_star_sub_exprExp2 h₀) (rw_star_sub_exprExp2 h₁)
  theorem rw_star_sub_exprLog {a b : kXReal} : a.rw_star b →
      (exprLog a).rw_star (exprLog b)
    | .step h => .step (rw_one.sub_exprLog h)
    | .refl h => .refl (eqe.eqe_exprLog h)
    | .trans h₀ h₁ => .trans (rw_star_sub_exprLog h₀) (rw_star_sub_exprLog h₁)
  theorem rw_star_sub_exprLog2 {a b : kXReal} : a.rw_star b →
      (exprLog2 a).rw_star (exprLog2 b)
    | .step h => .step (rw_one.sub_exprLog2 h)
    | .refl h => .refl (eqe.eqe_exprLog2 h)
    | .trans h₀ h₁ => .trans (rw_star_sub_exprLog2 h₀) (rw_star_sub_exprLog2 h₁)
  theorem rw_star_sub_exprSin {a b : kXReal} : a.rw_star b →
      (exprSin a).rw_star (exprSin b)
    | .step h => .step (rw_one.sub_exprSin h)
    | .refl h => .refl (eqe.eqe_exprSin h)
    | .trans h₀ h₁ => .trans (rw_star_sub_exprSin h₀) (rw_star_sub_exprSin h₁)
  theorem rw_star_sub_exprCos {a b : kXReal} : a.rw_star b →
      (exprCos a).rw_star (exprCos b)
    | .step h => .step (rw_one.sub_exprCos h)
    | .refl h => .refl (eqe.eqe_exprCos h)
    | .trans h₀ h₁ => .trans (rw_star_sub_exprCos h₀) (rw_star_sub_exprCos h₁)
  theorem rw_star_sub_exprTan {a b : kXReal} : a.rw_star b →
      (exprTan a).rw_star (exprTan b)
    | .step h => .step (rw_one.sub_exprTan h)
    | .refl h => .refl (eqe.eqe_exprTan h)
    | .trans h₀ h₁ => .trans (rw_star_sub_exprTan h₀) (rw_star_sub_exprTan h₁)
  theorem rw_star_sub_exprArcSin {a b : kXReal} : a.rw_star b →
      (exprArcSin a).rw_star (exprArcSin b)
    | .step h => .step (rw_one.sub_exprArcSin h)
    | .refl h => .refl (eqe.eqe_exprArcSin h)
    | .trans h₀ h₁ => .trans (rw_star_sub_exprArcSin h₀) (rw_star_sub_exprArcSin h₁)
  theorem rw_star_sub_exprArcCos {a b : kXReal} : a.rw_star b →
      (exprArcCos a).rw_star (exprArcCos b)
    | .step h => .step (rw_one.sub_exprArcCos h)
    | .refl h => .refl (eqe.eqe_exprArcCos h)
    | .trans h₀ h₁ => .trans (rw_star_sub_exprArcCos h₀) (rw_star_sub_exprArcCos h₁)
  theorem rw_star_sub_exprArcTan {a b : kXReal} : a.rw_star b →
      (exprArcTan a).rw_star (exprArcTan b)
    | .step h => .step (rw_one.sub_exprArcTan h)
    | .refl h => .refl (eqe.eqe_exprArcTan h)
    | .trans h₀ h₁ => .trans (rw_star_sub_exprArcTan h₀) (rw_star_sub_exprArcTan h₁)
  theorem rw_star_sub_exprSinh {a b : kXReal} : a.rw_star b →
      (exprSinh a).rw_star (exprSinh b)
    | .step h => .step (rw_one.sub_exprSinh h)
    | .refl h => .refl (eqe.eqe_exprSinh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_exprSinh h₀) (rw_star_sub_exprSinh h₁)
  theorem rw_star_sub_exprCosh {a b : kXReal} : a.rw_star b →
      (exprCosh a).rw_star (exprCosh b)
    | .step h => .step (rw_one.sub_exprCosh h)
    | .refl h => .refl (eqe.eqe_exprCosh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_exprCosh h₀) (rw_star_sub_exprCosh h₁)
  theorem rw_star_sub_exprTanh {a b : kXReal} : a.rw_star b →
      (exprTanh a).rw_star (exprTanh b)
    | .step h => .step (rw_one.sub_exprTanh h)
    | .refl h => .refl (eqe.eqe_exprTanh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_exprTanh h₀) (rw_star_sub_exprTanh h₁)
  theorem rw_star_sub_exprArcSinh {a b : kXReal} : a.rw_star b →
      (exprArcSinh a).rw_star (exprArcSinh b)
    | .step h => .step (rw_one.sub_exprArcSinh h)
    | .refl h => .refl (eqe.eqe_exprArcSinh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_exprArcSinh h₀) (rw_star_sub_exprArcSinh h₁)
  theorem rw_star_sub_exprArcCosh {a b : kXReal} : a.rw_star b →
      (exprArcCosh a).rw_star (exprArcCosh b)
    | .step h => .step (rw_one.sub_exprArcCosh h)
    | .refl h => .refl (eqe.eqe_exprArcCosh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_exprArcCosh h₀) (rw_star_sub_exprArcCosh h₁)
  theorem rw_star_sub_exprArcTanh {a b : kXReal} : a.rw_star b →
      (exprArcTanh a).rw_star (exprArcTanh b)
    | .step h => .step (rw_one.sub_exprArcTanh h)
    | .refl h => .refl (eqe.eqe_exprArcTanh h)
    | .trans h₀ h₁ => .trans (rw_star_sub_exprArcTanh h₀) (rw_star_sub_exprArcTanh h₁)
  theorem rw_star_sub_ifthenelsefi₀ {a b : kBool} {a₁ a₂ : kXReal} : a.rw_star b →
      (ifthenelsefi a a₁ a₂).rw_star (ifthenelsefi b a₁ a₂)
    | .step h => .step (rw_one.sub_ifthenelsefi₀ h)
    | .refl h => .refl (eqe.eqe_ifthenelsefi h (kXReal.eqe_refl a₁) (kXReal.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_ifthenelsefi₀ h₀) (rw_star_sub_ifthenelsefi₀ h₁)
  theorem rw_star_sub_ifthenelsefi₁ {a₀ : kBool} {a b a₂ : kXReal} : a.rw_star b →
      (ifthenelsefi a₀ a a₂).rw_star (ifthenelsefi a₀ b a₂)
    | .step h => .step (rw_one.sub_ifthenelsefi₁ h)
    | .refl h => .refl (eqe.eqe_ifthenelsefi (kBool.eqe_refl a₀) h (kXReal.eqe_refl a₂))
    | .trans h₀ h₁ => .trans (rw_star_sub_ifthenelsefi₁ h₀) (rw_star_sub_ifthenelsefi₁ h₁)
  theorem rw_star_sub_ifthenelsefi₂ {a₀ : kBool} {a₁ a b : kXReal} : a.rw_star b →
      (ifthenelsefi a₀ a₁ a).rw_star (ifthenelsefi a₀ a₁ b)
    | .step h => .step (rw_one.sub_ifthenelsefi₂ h)
    | .refl h => .refl (eqe.eqe_ifthenelsefi (kBool.eqe_refl a₀) (kXReal.eqe_refl a₁) h)
    | .trans h₀ h₁ => .trans (rw_star_sub_ifthenelsefi₂ h₀) (rw_star_sub_ifthenelsefi₂ h₁)
end kXReal

end Maude
