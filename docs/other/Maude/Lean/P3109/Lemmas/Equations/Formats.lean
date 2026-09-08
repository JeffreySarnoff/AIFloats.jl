-- Extracted from ../spec2.lean, lines 8979-9266.
-- See PLAN.md and manifest.json for provenance.
import P3109.Lemmas.Equations.XReal

namespace Maude
namespace kFormat
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kFormat) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kFormat} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kFormat} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kFormat} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev Binary_decl := @has_sort.Binary_decl
  abbrev binary64_decl := @has_sort.binary64_decl
  abbrev binary32_decl := @has_sort.binary32_decl
  abbrev binary16_decl := @has_sort.binary16_decl
  abbrev BFloat16_decl := @has_sort.BFloat16_decl
  abbrev eqa_Binary := @eqa.eqa_Binary
  abbrev eqe_Binary := @eqe.eqe_Binary
  abbrev eqa_at := @eqa.eqa_at
  abbrev eqe_at := @eqe.eqe_at
  abbrev eq_p31zero9_sequences_zerozero3 := @eqe.eq_p31zero9_sequences_zerozero3
  abbrev eq_p31zero9_sequences_zerozero4 := @eqe.eq_p31zero9_sequences_zerozero4

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_Binary eqe.eqe_Binary eqa.eqa_at eqe.eqe_at
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.Binary_decl has_sort.binary64_decl has_sort.binary32_decl has_sort.binary16_decl has_sort.BFloat16_decl eqe.eq_p31zero9_sequences_zerozero3 eqe.eq_p31zero9_sequences_zerozero4
end kFormat

namespace kSignedness
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kSignedness) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kSignedness} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kSignedness} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kSignedness} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev Signed_decl := @has_sort.Signed_decl
  abbrev Unsigned_decl := @has_sort.Unsigned_decl
  abbrev eqa_SignednessOf := @eqa.eqa_SignednessOf
  abbrev eqe_SignednessOf := @eqe.eqe_SignednessOf
  abbrev eq_p31zero9_format_core_zerozero5 := @eqe.eq_p31zero9_format_core_zerozero5
  abbrev eq_p31zero9_format_core_zero2zero := @eqe.eq_p31zero9_format_core_zero2zero
  abbrev eq_p31zero9_format_core_zero28 := @eqe.eq_p31zero9_format_core_zero28
  abbrev eq_p31zero9_format_core_zero36 := @eqe.eq_p31zero9_format_core_zero36
  abbrev eq_p31zero9_format_core_zero44 := @eqe.eq_p31zero9_format_core_zero44

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_SignednessOf eqe.eqe_SignednessOf
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.Signed_decl has_sort.Unsigned_decl eqe.eq_p31zero9_format_core_zerozero5 eqe.eq_p31zero9_format_core_zero2zero eqe.eq_p31zero9_format_core_zero28 eqe.eq_p31zero9_format_core_zero36 eqe.eq_p31zero9_format_core_zero44
end kSignedness

namespace kDomain
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kDomain) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kDomain} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kDomain} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kDomain} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev Finite_decl := @has_sort.Finite_decl
  abbrev Extended_decl := @has_sort.Extended_decl
  abbrev eqa_DomainOf := @eqa.eqa_DomainOf
  abbrev eqe_DomainOf := @eqe.eqe_DomainOf
  abbrev eq_p31zero9_format_core_zerozero6 := @eqe.eq_p31zero9_format_core_zerozero6
  abbrev eq_p31zero9_format_core_zero21 := @eqe.eq_p31zero9_format_core_zero21
  abbrev eq_p31zero9_format_core_zero29 := @eqe.eq_p31zero9_format_core_zero29
  abbrev eq_p31zero9_format_core_zero37 := @eqe.eq_p31zero9_format_core_zero37
  abbrev eq_p31zero9_format_core_zero45 := @eqe.eq_p31zero9_format_core_zero45

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_DomainOf eqe.eqe_DomainOf
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.Finite_decl has_sort.Extended_decl eqe.eq_p31zero9_format_core_zerozero6 eqe.eq_p31zero9_format_core_zero21 eqe.eq_p31zero9_format_core_zero29 eqe.eq_p31zero9_format_core_zero37 eqe.eq_p31zero9_format_core_zero45
end kDomain

namespace kBoundQuery
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kBoundQuery) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kBoundQuery} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kBoundQuery} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kBoundQuery} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev maxFiniteQuery_decl := @has_sort.maxFiniteQuery_decl
  abbrev minFiniteQuery_decl := @has_sort.minFiniteQuery_decl
  abbrev minPositiveQuery_decl := @has_sort.minPositiveQuery_decl
  abbrev maxSubnormalQuery_decl := @has_sort.maxSubnormalQuery_decl
  abbrev minNormalQuery_decl := @has_sort.minNormalQuery_decl

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.maxFiniteQuery_decl has_sort.minFiniteQuery_decl has_sort.minPositiveQuery_decl has_sort.maxSubnormalQuery_decl has_sort.minNormalQuery_decl
end kBoundQuery

namespace kRandomSeq
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kRandomSeq) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kRandomSeq} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kRandomSeq} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kRandomSeq} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev rnil_decl := @has_sort.rnil_decl
  abbrev rcons_decl := @has_sort.rcons_decl
  abbrev eqa_rcons := @eqa.eqa_rcons
  abbrev eqe_rcons := @eqe.eqe_rcons

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_rcons eqe.eqe_rcons
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.rnil_decl has_sort.rcons_decl
end kRandomSeq

namespace kBlockRoundMode
  -- Sort membership lemmas
  theorem subsort_roundmode_blockroundmode {t : kBlockRoundMode} : t.has_sort MSort.RoundMode →
    t.has_sort MSort.BlockRoundMode := by apply has_sort.subsort; simp [subsort]

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kBlockRoundMode) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kBlockRoundMode} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kBlockRoundMode} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kBlockRoundMode} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev NearestTiesToEven_decl := @has_sort.NearestTiesToEven_decl
  abbrev NearestTiesToAway_decl := @has_sort.NearestTiesToAway_decl
  abbrev TowardPositive_decl := @has_sort.TowardPositive_decl
  abbrev TowardNegative_decl := @has_sort.TowardNegative_decl
  abbrev TowardZero_decl := @has_sort.TowardZero_decl
  abbrev ToOdd_decl := @has_sort.ToOdd_decl
  abbrev StochasticA_decl := @has_sort.StochasticA_decl
  abbrev StochasticB_decl := @has_sort.StochasticB_decl
  abbrev StochasticC_decl := @has_sort.StochasticC_decl
  abbrev BlockStochasticA_decl := @has_sort.BlockStochasticA_decl
  abbrev BlockStochasticB_decl := @has_sort.BlockStochasticB_decl
  abbrev BlockStochasticC_decl := @has_sort.BlockStochasticC_decl
  abbrev eqa_StochasticA := @eqa.eqa_StochasticA
  abbrev eqe_StochasticA := @eqe.eqe_StochasticA
  abbrev eqa_StochasticB := @eqa.eqa_StochasticB
  abbrev eqe_StochasticB := @eqe.eqe_StochasticB
  abbrev eqa_StochasticC := @eqa.eqa_StochasticC
  abbrev eqe_StochasticC := @eqe.eqe_StochasticC
  abbrev eqa_BlockStochasticA := @eqa.eqa_BlockStochasticA
  abbrev eqe_BlockStochasticA := @eqe.eqe_BlockStochasticA
  abbrev eqa_BlockStochasticB := @eqa.eqa_BlockStochasticB
  abbrev eqe_BlockStochasticB := @eqe.eqe_BlockStochasticB
  abbrev eqa_BlockStochasticC := @eqa.eqa_BlockStochasticC
  abbrev eqe_BlockStochasticC := @eqe.eqe_BlockStochasticC
  abbrev eqa_RoundOf := @eqa.eqa_RoundOf
  abbrev eqe_RoundOf := @eqe.eqe_RoundOf
  abbrev eq_p31zero9_projection_spec_zero29 := @eqe.eq_p31zero9_projection_spec_zero29

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_StochasticA eqe.eqe_StochasticA eqa.eqa_StochasticB eqe.eqe_StochasticB eqa.eqa_StochasticC eqe.eqe_StochasticC eqa.eqa_BlockStochasticA eqe.eqe_BlockStochasticA eqa.eqa_BlockStochasticB eqe.eqe_BlockStochasticB eqa.eqa_BlockStochasticC eqe.eqe_BlockStochasticC eqa.eqa_RoundOf eqe.eqe_RoundOf
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.NearestTiesToEven_decl has_sort.NearestTiesToAway_decl has_sort.TowardPositive_decl has_sort.TowardNegative_decl has_sort.TowardZero_decl has_sort.ToOdd_decl has_sort.StochasticA_decl has_sort.StochasticB_decl has_sort.StochasticC_decl has_sort.BlockStochasticA_decl has_sort.BlockStochasticB_decl has_sort.BlockStochasticC_decl eqe.eq_p31zero9_projection_spec_zero29 subsort_roundmode_blockroundmode
end kBlockRoundMode

namespace kSatMode
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kSatMode) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kSatMode} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kSatMode} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kSatMode} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev SatNone_decl := @has_sort.SatNone_decl
  abbrev SatFinite_decl := @has_sort.SatFinite_decl
  abbrev SatPropagate_decl := @has_sort.SatPropagate_decl
  abbrev eqa_SatOf := @eqa.eqa_SatOf
  abbrev eqe_SatOf := @eqe.eqe_SatOf
  abbrev eq_p31zero9_projection_spec_zero3zero := @eqe.eq_p31zero9_projection_spec_zero3zero

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_SatOf eqe.eqe_SatOf
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.SatNone_decl has_sort.SatFinite_decl has_sort.SatPropagate_decl eqe.eq_p31zero9_projection_spec_zero3zero
end kSatMode

namespace kProjSpec
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kProjSpec) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kProjSpec} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kProjSpec} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kProjSpec} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev proj_decl := @has_sort.proj_decl
  abbrev eqa_proj := @eqa.eqa_proj
  abbrev eqe_proj := @eqe.eqe_proj
  abbrev eqa_projectionAt := @eqa.eqa_projectionAt
  abbrev eqe_projectionAt := @eqe.eqe_projectionAt
  abbrev eq_p31zero9_projection_spec_zero16 := @eqe.eq_p31zero9_projection_spec_zero16
  abbrev eq_p31zero9_projection_spec_zero21 := @eqe.eq_p31zero9_projection_spec_zero21
  abbrev eq_p31zero9_projection_spec_zero26 := @eqe.eq_p31zero9_projection_spec_zero26
  abbrev eq_p31zero9_projection_spec_zero34 := @eqe.eq_p31zero9_projection_spec_zero34

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_proj eqe.eqe_proj eqa.eqa_projectionAt eqe.eqe_projectionAt
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.proj_decl eqe.eq_p31zero9_projection_spec_zero16 eqe.eq_p31zero9_projection_spec_zero21 eqe.eq_p31zero9_projection_spec_zero26 eqe.eq_p31zero9_projection_spec_zero34
end kProjSpec

namespace kBlockProjSpec
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kBlockProjSpec) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kBlockProjSpec} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kBlockProjSpec} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kBlockProjSpec} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev bproj_decl := @has_sort.bproj_decl
  abbrev eqa_bproj := @eqa.eqa_bproj
  abbrev eqe_bproj := @eqe.eqe_bproj
  abbrev eqa_singletonLift := @eqa.eqa_singletonLift
  abbrev eqe_singletonLift := @eqe.eqe_singletonLift
  abbrev eq_p31zero9_projection_spec_zero17 := @eqe.eq_p31zero9_projection_spec_zero17
  abbrev eq_p31zero9_projection_spec_zero22 := @eqe.eq_p31zero9_projection_spec_zero22
  abbrev eq_p31zero9_projection_spec_zero27 := @eqe.eq_p31zero9_projection_spec_zero27
  abbrev eq_p31zero9_projection_spec_zero35 := @eqe.eq_p31zero9_projection_spec_zero35

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_bproj eqe.eqe_bproj eqa.eqa_singletonLift eqe.eqe_singletonLift
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.bproj_decl eqe.eq_p31zero9_projection_spec_zero17 eqe.eq_p31zero9_projection_spec_zero22 eqe.eq_p31zero9_projection_spec_zero27 eqe.eq_p31zero9_projection_spec_zero35
end kBlockProjSpec

end Maude
