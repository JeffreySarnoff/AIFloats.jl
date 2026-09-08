-- Extracted from ../spec2.lean, lines 9764-10250.
-- See PLAN.md and manifest.json for provenance.
import P3109.Lemmas.Equations.SequencesAndBlocks

namespace Maude
namespace kFormatSeq
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kFormatSeq) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kFormatSeq} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kFormatSeq} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kFormatSeq} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev fnil_decl := @has_sort.fnil_decl
  abbrev fcons_decl := @has_sort.fcons_decl
  abbrev eqa_fcons := @eqa.eqa_fcons
  abbrev eqe_fcons := @eqe.eqe_fcons

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_fcons eqe.eqe_fcons
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.fnil_decl has_sort.fcons_decl
end kFormatSeq

namespace kSpecialization
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kSpecialization) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kSpecialization} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kSpecialization} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kSpecialization} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev numeric_decl := @has_sort.numeric_decl
  abbrev plain_decl := @has_sort.plain_decl
  abbrev blockElements_decl := @has_sort.blockElements_decl
  abbrev blockReduction_decl := @has_sort.blockReduction_decl
  abbrev blockScale_decl := @has_sort.blockScale_decl
  abbrev declaredIdentity_decl := @has_sort.declaredIdentity_decl
  abbrev eqa_numeric := @eqa.eqa_numeric
  abbrev eqe_numeric := @eqe.eqe_numeric
  abbrev eqa_plain := @eqa.eqa_plain
  abbrev eqe_plain := @eqe.eqe_plain
  abbrev eqa_blockElements := @eqa.eqa_blockElements
  abbrev eqe_blockElements := @eqe.eqe_blockElements
  abbrev eqa_blockReduction := @eqa.eqa_blockReduction
  abbrev eqe_blockReduction := @eqe.eqe_blockReduction
  abbrev eqa_blockScale := @eqa.eqa_blockScale
  abbrev eqe_blockScale := @eqe.eqe_blockScale
  abbrev eqa_at := @eqa.eqa_at
  abbrev eqe_at := @eqe.eqe_at
  abbrev eqa_declaredIdentity := @eqa.eqa_declaredIdentity
  abbrev eqe_declaredIdentity := @eqe.eqe_declaredIdentity
  abbrev eq_p31zero9_sequences_zerozero3 := @eqe.eq_p31zero9_sequences_zerozero3
  abbrev eq_p31zero9_sequences_zerozero4 := @eqe.eq_p31zero9_sequences_zerozero4
  abbrev eq_p31zero9_declared_exact := @eqe.eq_p31zero9_declared_exact
  abbrev eq_p31zero9_declared_approximate := @eqe.eq_p31zero9_declared_approximate
  abbrev eq_p31zero9_decl_partitioned_identity := @eqe.eq_p31zero9_decl_partitioned_identity

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_numeric eqe.eqe_numeric eqa.eqa_plain eqe.eqe_plain eqa.eqa_blockElements eqe.eqe_blockElements eqa.eqa_blockReduction eqe.eqe_blockReduction eqa.eqa_blockScale eqe.eqe_blockScale eqa.eqa_at eqe.eqe_at eqa.eqa_declaredIdentity eqe.eqe_declaredIdentity
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.numeric_decl has_sort.plain_decl has_sort.blockElements_decl has_sort.blockReduction_decl has_sort.blockScale_decl has_sort.declaredIdentity_decl eqe.eq_p31zero9_sequences_zerozero3 eqe.eq_p31zero9_sequences_zerozero4 eqe.eq_p31zero9_declared_exact eqe.eq_p31zero9_declared_approximate eqe.eq_p31zero9_decl_partitioned_identity
end kSpecialization

namespace kKappa
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kKappa) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kKappa} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kKappa} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kKappa} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev steps_decl := @has_sort.steps_decl
  abbrev kNaN_decl := @has_sort.kNaN_decl
  abbrev kInfinity_decl := @has_sort.kInfinity_decl
  abbrev partBound_decl := @has_sort.partBound_decl
  abbrev mergeKappa_decl := @has_sort.mergeKappa_decl
  abbrev eqa_steps := @eqa.eqa_steps
  abbrev eqe_steps := @eqe.eqe_steps
  abbrev eqa_partBound := @eqa.eqa_partBound
  abbrev eqe_partBound := @eqe.eqe_partBound
  abbrev eqa_declarationKappa := @eqa.eqa_declarationKappa
  abbrev eqe_declarationKappa := @eqe.eqe_declarationKappa
  abbrev eqa_observationKappa := @eqa.eqa_observationKappa
  abbrev eqe_observationKappa := @eqe.eqe_observationKappa
  abbrev eqa_batchKappa := @eqa.eqa_batchKappa
  abbrev eqe_batchKappa := @eqe.eqe_batchKappa
  abbrev eqa_mergeKappa := @eqa.eqa_mergeKappa
  abbrev eqe_mergeKappa := @eqe.eqe_mergeKappa
  abbrev eq_p31zero9_conformance_zero4zero := @eqe.eq_p31zero9_conformance_zero4zero
  abbrev eq_p31zero9_conformance_zero41 := @eqe.eq_p31zero9_conformance_zero41
  abbrev eq_p31zero9_conformance_zero42 := @eqe.eq_p31zero9_conformance_zero42
  abbrev eq_p31zero9_conformance_zero43 := @eqe.eq_p31zero9_conformance_zero43
  abbrev eq_p31zero9_conformance_zero44 := @eqe.eq_p31zero9_conformance_zero44
  abbrev eq_p31zero9_conformance_zero45 := @eqe.eq_p31zero9_conformance_zero45
  abbrev eq_p31zero9_conformance_zero46 := @eqe.eq_p31zero9_conformance_zero46
  abbrev eq_p31zero9_conformance_zero47 := @eqe.eq_p31zero9_conformance_zero47
  abbrev eq_p31zero9_conformance_zero48 := @eqe.eq_p31zero9_conformance_zero48
  abbrev eq_p31zero9_conformance_zero49 := @eqe.eq_p31zero9_conformance_zero49
  abbrev eq_p31zero9_conformance_zero5zero := @eqe.eq_p31zero9_conformance_zero5zero
  abbrev eq_p31zero9_conformance_zero51 := @eqe.eq_p31zero9_conformance_zero51
  abbrev eq_p31zero9_conformance_zero52 := @eqe.eq_p31zero9_conformance_zero52
  abbrev eq_p31zero9_conformance_zero53 := @eqe.eq_p31zero9_conformance_zero53
  abbrev eq_p31zero9_part_bound_empty := @eqe.eq_p31zero9_part_bound_empty
  abbrev eq_p31zero9_part_bound_cons := @eqe.eq_p31zero9_part_bound_cons
  abbrev eq_p31zero9_decl_exact_kappa := @eqe.eq_p31zero9_decl_exact_kappa
  abbrev eq_p31zero9_decl_approx_kappa := @eqe.eq_p31zero9_decl_approx_kappa
  abbrev eq_p31zero9_decl_partition_kappa := @eqe.eq_p31zero9_decl_partition_kappa

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_steps eqe.eqe_steps eqa.eqa_partBound eqe.eqe_partBound eqa.eqa_declarationKappa eqe.eqe_declarationKappa eqa.eqa_observationKappa eqe.eqe_observationKappa eqa.eqa_batchKappa eqe.eqe_batchKappa eqa.eqa_mergeKappa eqe.eqe_mergeKappa
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.steps_decl has_sort.kNaN_decl has_sort.kInfinity_decl has_sort.partBound_decl has_sort.mergeKappa_decl eqe.eq_p31zero9_conformance_zero4zero eqe.eq_p31zero9_conformance_zero41 eqe.eq_p31zero9_conformance_zero42 eqe.eq_p31zero9_conformance_zero43 eqe.eq_p31zero9_conformance_zero44 eqe.eq_p31zero9_conformance_zero45 eqe.eq_p31zero9_conformance_zero46 eqe.eq_p31zero9_conformance_zero47 eqe.eq_p31zero9_conformance_zero48 eqe.eq_p31zero9_conformance_zero49 eqe.eq_p31zero9_conformance_zero5zero eqe.eq_p31zero9_conformance_zero51 eqe.eq_p31zero9_conformance_zero52 eqe.eq_p31zero9_conformance_zero53 eqe.eq_p31zero9_part_bound_empty eqe.eq_p31zero9_part_bound_cons eqe.eq_p31zero9_decl_exact_kappa eqe.eq_p31zero9_decl_approx_kappa eqe.eq_p31zero9_decl_partition_kappa
end kKappa

namespace kObservation
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kObservation) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kObservation} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kObservation} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kObservation} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev observation_decl := @has_sort.observation_decl
  abbrev eqa_observation := @eqa.eqa_observation
  abbrev eqe_observation := @eqe.eqe_observation
  abbrev eqa_at := @eqa.eqa_at
  abbrev eqe_at := @eqe.eqe_at
  abbrev eq_p31zero9_sequences_zerozero3 := @eqe.eq_p31zero9_sequences_zerozero3
  abbrev eq_p31zero9_sequences_zerozero4 := @eqe.eq_p31zero9_sequences_zerozero4

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_observation eqe.eqe_observation eqa.eqa_at eqe.eqe_at
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.observation_decl eqe.eq_p31zero9_sequences_zerozero3 eqe.eq_p31zero9_sequences_zerozero4
end kObservation

namespace kDeclaration
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kDeclaration) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kDeclaration} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kDeclaration} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kDeclaration} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev exact_decl := @has_sort.exact_decl
  abbrev approximate_decl := @has_sort.approximate_decl
  abbrev partitioned_decl := @has_sort.partitioned_decl
  abbrev eqa_exact := @eqa.eqa_exact
  abbrev eqe_exact := @eqe.eqe_exact
  abbrev eqa_approximate := @eqa.eqa_approximate
  abbrev eqe_approximate := @eqe.eqe_approximate
  abbrev eqa_at := @eqa.eqa_at
  abbrev eqe_at := @eqe.eqe_at
  abbrev eqa_partitioned := @eqa.eqa_partitioned
  abbrev eqe_partitioned := @eqe.eqe_partitioned
  abbrev eq_p31zero9_sequences_zerozero3 := @eqe.eq_p31zero9_sequences_zerozero3
  abbrev eq_p31zero9_sequences_zerozero4 := @eqe.eq_p31zero9_sequences_zerozero4

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_exact eqe.eqe_exact eqa.eqa_approximate eqe.eqe_approximate eqa.eqa_at eqe.eqe_at eqa.eqa_partitioned eqe.eqe_partitioned
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.exact_decl has_sort.approximate_decl has_sort.partitioned_decl eqe.eq_p31zero9_sequences_zerozero3 eqe.eq_p31zero9_sequences_zerozero4
end kDeclaration

namespace kEvidence
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kEvidence) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kEvidence} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kEvidence} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kEvidence} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev pendingEvidence_decl := @has_sort.pendingEvidence_decl
  abbrev sampleEvidence_decl := @has_sort.sampleEvidence_decl
  abbrev exhaustiveEvidence_decl := @has_sort.exhaustiveEvidence_decl
  abbrev proofEvidence_decl := @has_sort.proofEvidence_decl

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.pendingEvidence_decl has_sort.sampleEvidence_decl has_sort.exhaustiveEvidence_decl has_sort.proofEvidence_decl
end kEvidence

namespace kKappaPart
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kKappaPart) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kKappaPart} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kKappaPart} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kKappaPart} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev kappaPart_decl := @has_sort.kappaPart_decl
  abbrev eqa_kappaPart := @eqa.eqa_kappaPart
  abbrev eqe_kappaPart := @eqe.eqe_kappaPart
  abbrev eqa_at := @eqa.eqa_at
  abbrev eqe_at := @eqe.eqe_at
  abbrev eq_p31zero9_sequences_zerozero3 := @eqe.eq_p31zero9_sequences_zerozero3
  abbrev eq_p31zero9_sequences_zerozero4 := @eqe.eq_p31zero9_sequences_zerozero4

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_kappaPart eqe.eqe_kappaPart eqa.eqa_at eqe.eqe_at
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.kappaPart_decl eqe.eq_p31zero9_sequences_zerozero3 eqe.eq_p31zero9_sequences_zerozero4
end kKappaPart

namespace kArityEntry
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kArityEntry) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kArityEntry} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kArityEntry} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kArityEntry} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev entry_decl := @has_sort.entry_decl
  abbrev eqa_entry := @eqa.eqa_entry
  abbrev eqe_entry := @eqe.eqe_entry
  abbrev eqa_at := @eqa.eqa_at
  abbrev eqe_at := @eqe.eqe_at
  abbrev eq_p31zero9_sequences_zerozero3 := @eqe.eq_p31zero9_sequences_zerozero3
  abbrev eq_p31zero9_sequences_zerozero4 := @eqe.eq_p31zero9_sequences_zerozero4

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_entry eqe.eqe_entry eqa.eqa_at eqe.eqe_at
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.entry_decl eqe.eq_p31zero9_sequences_zerozero3 eqe.eq_p31zero9_sequences_zerozero4
end kArityEntry

namespace kKappaPartSeq
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kKappaPartSeq) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kKappaPartSeq} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kKappaPartSeq} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kKappaPartSeq} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev knil_decl := @has_sort.knil_decl
  abbrev kcons_decl := @has_sort.kcons_decl
  abbrev eqa_kcons := @eqa.eqa_kcons
  abbrev eqe_kcons := @eqe.eqe_kcons

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_kcons eqe.eqe_kcons
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.knil_decl has_sort.kcons_decl
end kKappaPartSeq

namespace kPartitionSeq
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kPartitionSeq) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kPartitionSeq} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kPartitionSeq} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kPartitionSeq} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev pnil_decl := @has_sort.pnil_decl
  abbrev pcons_decl := @has_sort.pcons_decl
  abbrev partRegions_decl := @has_sort.partRegions_decl
  abbrev eqa_pcons := @eqa.eqa_pcons
  abbrev eqe_pcons := @eqe.eqe_pcons
  abbrev eqa_partRegions := @eqa.eqa_partRegions
  abbrev eqe_partRegions := @eqe.eqe_partRegions
  abbrev eq_p31zero9_part_regions_empty := @eqe.eq_p31zero9_part_regions_empty
  abbrev eq_p31zero9_part_regions_cons := @eqe.eq_p31zero9_part_regions_cons

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_pcons eqe.eqe_pcons eqa.eqa_partRegions eqe.eqe_partRegions
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.pnil_decl has_sort.pcons_decl has_sort.partRegions_decl eqe.eq_p31zero9_part_regions_empty eqe.eq_p31zero9_part_regions_cons
end kPartitionSeq

namespace kDeclarationSeq
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kDeclarationSeq) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kDeclarationSeq} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kDeclarationSeq} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kDeclarationSeq} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev dnil_decl := @has_sort.dnil_decl
  abbrev dcons_decl := @has_sort.dcons_decl
  abbrev eqa_dcons := @eqa.eqa_dcons
  abbrev eqe_dcons := @eqe.eqe_dcons

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_dcons eqe.eqe_dcons
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.dnil_decl has_sort.dcons_decl
end kDeclarationSeq

namespace kSpecializationSeq
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kSpecializationSeq) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kSpecializationSeq} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kSpecializationSeq} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kSpecializationSeq} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev snil_decl := @has_sort.snil_decl
  abbrev scons_decl := @has_sort.scons_decl
  abbrev eqa_scons := @eqa.eqa_scons
  abbrev eqe_scons := @eqe.eqe_scons

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_scons eqe.eqe_scons
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.snil_decl has_sort.scons_decl
end kSpecializationSeq

namespace kClassEnum
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kClassEnum) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kClassEnum} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kClassEnum} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kClassEnum} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev ClsNaN_decl := @has_sort.ClsNaN_decl
  abbrev ClsNegativeInfinity_decl := @has_sort.ClsNegativeInfinity_decl
  abbrev ClsNegativeNormal_decl := @has_sort.ClsNegativeNormal_decl
  abbrev ClsNegativeSubnormal_decl := @has_sort.ClsNegativeSubnormal_decl
  abbrev ClsZero_decl := @has_sort.ClsZero_decl
  abbrev ClsPositiveSubnormal_decl := @has_sort.ClsPositiveSubnormal_decl
  abbrev ClsPositiveNormal_decl := @has_sort.ClsPositiveNormal_decl
  abbrev ClsPositiveInfinity_decl := @has_sort.ClsPositiveInfinity_decl
  abbrev ifthenelsefi_decl₁ := @has_sort.ifthenelsefi_decl₁
  abbrev eqa_Class := @eqa.eqa_Class
  abbrev eqe_Class := @eqe.eqe_Class
  abbrev eqa_ifthenelsefi := @eqa.eqa_ifthenelsefi
  abbrev eqe_ifthenelsefi := @eqe.eqe_ifthenelsefi
  abbrev eq_p31zero9_predicates_zero15 := @eqe.eq_p31zero9_predicates_zero15
  abbrev eq_p31zero9_predicates_zero16 := @eqe.eq_p31zero9_predicates_zero16
  abbrev eq_p31zero9_predicates_zero17 := @eqe.eq_p31zero9_predicates_zero17
  abbrev eq_p31zero9_predicates_zero18 := @eqe.eq_p31zero9_predicates_zero18
  abbrev eq_p31zero9_predicates_zero19 := @eqe.eq_p31zero9_predicates_zero19
  abbrev eq_itet := @eqe.eq_itet
  abbrev eq_itef := @eqe.eq_itef

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_Class eqe.eqe_Class eqa.eqa_ifthenelsefi eqe.eqe_ifthenelsefi
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.ClsNaN_decl has_sort.ClsNegativeInfinity_decl has_sort.ClsNegativeNormal_decl has_sort.ClsNegativeSubnormal_decl has_sort.ClsZero_decl has_sort.ClsPositiveSubnormal_decl has_sort.ClsPositiveNormal_decl has_sort.ClsPositiveInfinity_decl has_sort.ifthenelsefi_decl₁ eqe.eq_p31zero9_predicates_zero15 eqe.eq_p31zero9_predicates_zero16 eqe.eq_p31zero9_predicates_zero17 eqe.eq_p31zero9_predicates_zero18 eqe.eq_p31zero9_predicates_zero19 eqe.eq_itet eqe.eq_itef
end kClassEnum

namespace kObservationSeq
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kObservationSeq) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kObservationSeq} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kObservationSeq} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kObservationSeq} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev onil_decl := @has_sort.onil_decl
  abbrev ocons_decl := @has_sort.ocons_decl
  abbrev eqa_ocons := @eqa.eqa_ocons
  abbrev eqe_ocons := @eqe.eqe_ocons

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_ocons eqe.eqe_ocons
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.onil_decl has_sort.ocons_decl
end kObservationSeq

namespace kArityTable
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kArityTable) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kArityTable} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kArityTable} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kArityTable} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev anil_decl := @has_sort.anil_decl
  abbrev acons_decl := @has_sort.acons_decl
  abbrev numericArityTable_decl := @has_sort.numericArityTable_decl
  abbrev plainArityTable_decl := @has_sort.plainArityTable_decl
  abbrev blockElementArityTable_decl := @has_sort.blockElementArityTable_decl
  abbrev eqa_acons := @eqa.eqa_acons
  abbrev eqe_acons := @eqe.eqe_acons
  abbrev eq_p31zero9_decl_numeric_table := @eqe.eq_p31zero9_decl_numeric_table
  abbrev eq_p31zero9_decl_plain_table := @eqe.eq_p31zero9_decl_plain_table
  abbrev eq_p31zero9_block_element_arity_table := @eqe.eq_p31zero9_block_element_arity_table

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_acons eqe.eqe_acons
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.anil_decl has_sort.acons_decl has_sort.numericArityTable_decl has_sort.plainArityTable_decl has_sort.blockElementArityTable_decl eqe.eq_p31zero9_decl_numeric_table eqe.eq_p31zero9_decl_plain_table eqe.eq_p31zero9_block_element_arity_table
end kArityTable

end Maude
