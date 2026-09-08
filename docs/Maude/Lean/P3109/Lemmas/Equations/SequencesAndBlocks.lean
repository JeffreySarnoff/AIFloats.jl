-- Extracted from ../spec2.lean, lines 9267-9763.
-- See PLAN.md and manifest.json for provenance.
import P3109.Lemmas.Equations.Formats

namespace Maude
namespace kXSeq
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kXSeq) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kXSeq} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kXSeq} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kXSeq} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev xnil_decl := @has_sort.xnil_decl
  abbrev xcons_decl := @has_sort.xcons_decl
  abbrev eqa_xcons := @eqa.eqa_xcons
  abbrev eqe_xcons := @eqe.eqe_xcons
  abbrev eqa_decodeElements := @eqa.eqa_decodeElements
  abbrev eqe_decodeElements := @eqe.eqe_decodeElements
  abbrev eqa_multiplyElements := @eqa.eqa_multiplyElements
  abbrev eqe_multiplyElements := @eqe.eqe_multiplyElements
  abbrev eqa_blockDecode := @eqa.eqa_blockDecode
  abbrev eqe_blockDecode := @eqe.eqe_blockDecode
  abbrev eqa_absElements := @eqa.eqa_absElements
  abbrev eqe_absElements := @eqe.eqe_absElements
  abbrev eqa_pairProducts := @eqa.eqa_pairProducts
  abbrev eqe_pairProducts := @eqe.eqe_pairProducts
  abbrev eqa_mapConvert := @eqa.eqa_mapConvert
  abbrev eqe_mapConvert := @eqe.eqe_mapConvert
  abbrev eqa_mapAbs := @eqa.eqa_mapAbs
  abbrev eqe_mapAbs := @eqe.eqe_mapAbs
  abbrev eqa_mapNegate := @eqa.eqa_mapNegate
  abbrev eqe_mapNegate := @eqe.eqe_mapNegate
  abbrev eqa_mapCopySign := @eqa.eqa_mapCopySign
  abbrev eqe_mapCopySign := @eqe.eqe_mapCopySign
  abbrev eqa_mapAdd := @eqa.eqa_mapAdd
  abbrev eqe_mapAdd := @eqe.eqe_mapAdd
  abbrev eqa_mapSubtract := @eqa.eqa_mapSubtract
  abbrev eqe_mapSubtract := @eqe.eqe_mapSubtract
  abbrev eqa_mapMultiply := @eqa.eqa_mapMultiply
  abbrev eqe_mapMultiply := @eqe.eqe_mapMultiply
  abbrev eqa_mapDivide := @eqa.eqa_mapDivide
  abbrev eqe_mapDivide := @eqe.eqe_mapDivide
  abbrev eqa_mapFMA := @eqa.eqa_mapFMA
  abbrev eqe_mapFMA := @eqe.eqe_mapFMA
  abbrev eqa_mapFAA := @eqa.eqa_mapFAA
  abbrev eqe_mapFAA := @eqe.eqe_mapFAA
  abbrev eqa_mapRecip := @eqa.eqa_mapRecip
  abbrev eqe_mapRecip := @eqe.eqe_mapRecip
  abbrev eqa_mapMinimum := @eqa.eqa_mapMinimum
  abbrev eqe_mapMinimum := @eqe.eqe_mapMinimum
  abbrev eqa_mapMaximum := @eqa.eqa_mapMaximum
  abbrev eqe_mapMaximum := @eqe.eqe_mapMaximum
  abbrev eqa_mapMinimumNumber := @eqa.eqa_mapMinimumNumber
  abbrev eqe_mapMinimumNumber := @eqe.eqe_mapMinimumNumber
  abbrev eqa_mapMaximumNumber := @eqa.eqa_mapMaximumNumber
  abbrev eqe_mapMaximumNumber := @eqe.eqe_mapMaximumNumber
  abbrev eqa_mapMinimumMagnitude := @eqa.eqa_mapMinimumMagnitude
  abbrev eqe_mapMinimumMagnitude := @eqe.eqe_mapMinimumMagnitude
  abbrev eqa_mapMaximumMagnitude := @eqa.eqa_mapMaximumMagnitude
  abbrev eqe_mapMaximumMagnitude := @eqe.eqe_mapMaximumMagnitude
  abbrev eqa_mapMinimumMagnitudeNumber := @eqa.eqa_mapMinimumMagnitudeNumber
  abbrev eqe_mapMinimumMagnitudeNumber := @eqe.eqe_mapMinimumMagnitudeNumber
  abbrev eqa_mapMaximumMagnitudeNumber := @eqa.eqa_mapMaximumMagnitudeNumber
  abbrev eqe_mapMaximumMagnitudeNumber := @eqe.eqe_mapMaximumMagnitudeNumber
  abbrev eqa_mapMinimumFinite := @eqa.eqa_mapMinimumFinite
  abbrev eqe_mapMinimumFinite := @eqe.eqe_mapMinimumFinite
  abbrev eqa_mapMaximumFinite := @eqa.eqa_mapMaximumFinite
  abbrev eqe_mapMaximumFinite := @eqe.eqe_mapMaximumFinite
  abbrev eqa_mapClamp := @eqa.eqa_mapClamp
  abbrev eqe_mapClamp := @eqe.eqe_mapClamp
  abbrev eqa_mapSqrt := @eqa.eqa_mapSqrt
  abbrev eqe_mapSqrt := @eqe.eqe_mapSqrt
  abbrev eqa_mapRSqrt := @eqa.eqa_mapRSqrt
  abbrev eqe_mapRSqrt := @eqe.eqe_mapRSqrt
  abbrev eqa_mapExp := @eqa.eqa_mapExp
  abbrev eqe_mapExp := @eqe.eqe_mapExp
  abbrev eqa_mapExp2 := @eqa.eqa_mapExp2
  abbrev eqe_mapExp2 := @eqe.eqe_mapExp2
  abbrev eqa_mapLog := @eqa.eqa_mapLog
  abbrev eqe_mapLog := @eqe.eqe_mapLog
  abbrev eqa_mapLog2 := @eqa.eqa_mapLog2
  abbrev eqe_mapLog2 := @eqe.eqe_mapLog2
  abbrev eqa_mapLogOnePlus := @eqa.eqa_mapLogOnePlus
  abbrev eqe_mapLogOnePlus := @eqe.eqe_mapLogOnePlus
  abbrev eqa_mapExpMinusOne := @eqa.eqa_mapExpMinusOne
  abbrev eqe_mapExpMinusOne := @eqe.eqe_mapExpMinusOne
  abbrev eqa_mapSin := @eqa.eqa_mapSin
  abbrev eqe_mapSin := @eqe.eqe_mapSin
  abbrev eqa_mapCos := @eqa.eqa_mapCos
  abbrev eqe_mapCos := @eqe.eqe_mapCos
  abbrev eqa_mapTan := @eqa.eqa_mapTan
  abbrev eqe_mapTan := @eqe.eqe_mapTan
  abbrev eqa_mapArcSin := @eqa.eqa_mapArcSin
  abbrev eqe_mapArcSin := @eqe.eqe_mapArcSin
  abbrev eqa_mapArcCos := @eqa.eqa_mapArcCos
  abbrev eqe_mapArcCos := @eqe.eqe_mapArcCos
  abbrev eqa_mapArcTan := @eqa.eqa_mapArcTan
  abbrev eqe_mapArcTan := @eqe.eqe_mapArcTan
  abbrev eqa_mapSinh := @eqa.eqa_mapSinh
  abbrev eqe_mapSinh := @eqe.eqe_mapSinh
  abbrev eqa_mapCosh := @eqa.eqa_mapCosh
  abbrev eqe_mapCosh := @eqe.eqe_mapCosh
  abbrev eqa_mapTanh := @eqa.eqa_mapTanh
  abbrev eqe_mapTanh := @eqe.eqe_mapTanh
  abbrev eqa_mapArcSinh := @eqa.eqa_mapArcSinh
  abbrev eqe_mapArcSinh := @eqe.eqe_mapArcSinh
  abbrev eqa_mapArcCosh := @eqa.eqa_mapArcCosh
  abbrev eqe_mapArcCosh := @eqe.eqe_mapArcCosh
  abbrev eqa_mapArcTanh := @eqa.eqa_mapArcTanh
  abbrev eqe_mapArcTanh := @eqe.eqe_mapArcTanh
  abbrev eqa_mapSinPi := @eqa.eqa_mapSinPi
  abbrev eqe_mapSinPi := @eqe.eqe_mapSinPi
  abbrev eqa_mapCosPi := @eqa.eqa_mapCosPi
  abbrev eqe_mapCosPi := @eqe.eqe_mapCosPi
  abbrev eqa_mapTanPi := @eqa.eqa_mapTanPi
  abbrev eqe_mapTanPi := @eqe.eqe_mapTanPi
  abbrev eqa_mapArcSinPi := @eqa.eqa_mapArcSinPi
  abbrev eqe_mapArcSinPi := @eqe.eqe_mapArcSinPi
  abbrev eqa_mapArcCosPi := @eqa.eqa_mapArcCosPi
  abbrev eqe_mapArcCosPi := @eqe.eqe_mapArcCosPi
  abbrev eqa_mapArcTanPi := @eqa.eqa_mapArcTanPi
  abbrev eqe_mapArcTanPi := @eqe.eqe_mapArcTanPi
  abbrev eqa_mapSoftplus := @eqa.eqa_mapSoftplus
  abbrev eqe_mapSoftplus := @eqe.eqe_mapSoftplus
  abbrev eqa_mapHypot := @eqa.eqa_mapHypot
  abbrev eqe_mapHypot := @eqe.eqe_mapHypot
  abbrev eqa_mapArcTan2 := @eqa.eqa_mapArcTan2
  abbrev eqe_mapArcTan2 := @eqe.eqe_mapArcTan2
  abbrev eqa_mapArcTan2Pi := @eqa.eqa_mapArcTan2Pi
  abbrev eqe_mapArcTan2Pi := @eqe.eqe_mapArcTan2Pi
  abbrev eq_p31zero9_block_core_zerozero4 := @eqe.eq_p31zero9_block_core_zerozero4
  abbrev eq_p31zero9_block_core_zerozero5 := @eqe.eq_p31zero9_block_core_zerozero5
  abbrev eq_p31zero9_block_core_zerozero6 := @eqe.eq_p31zero9_block_core_zerozero6
  abbrev eq_p31zero9_block_core_zerozero7 := @eqe.eq_p31zero9_block_core_zerozero7
  abbrev eq_p31zero9_block_core_zerozero8 := @eqe.eq_p31zero9_block_core_zerozero8
  abbrev eq_p31zero9_block_ops_zerozero7 := @eqe.eq_p31zero9_block_ops_zerozero7
  abbrev eq_p31zero9_block_ops_zerozero8 := @eqe.eq_p31zero9_block_ops_zerozero8
  abbrev eq_p31zero9_block_ops_zerozero9 := @eqe.eq_p31zero9_block_ops_zerozero9
  abbrev eq_p31zero9_block_ops_zero1zero := @eqe.eq_p31zero9_block_ops_zero1zero
  abbrev eq_p31zero9_map_Convert_nil := @eqe.eq_p31zero9_map_Convert_nil
  abbrev eq_p31zero9_map_Convert_cons := @eqe.eq_p31zero9_map_Convert_cons
  abbrev eq_p31zero9_map_Abs_nil := @eqe.eq_p31zero9_map_Abs_nil
  abbrev eq_p31zero9_map_Abs_cons := @eqe.eq_p31zero9_map_Abs_cons
  abbrev eq_p31zero9_map_Negate_nil := @eqe.eq_p31zero9_map_Negate_nil
  abbrev eq_p31zero9_map_Negate_cons := @eqe.eq_p31zero9_map_Negate_cons
  abbrev eq_p31zero9_map_CopySign_nil := @eqe.eq_p31zero9_map_CopySign_nil
  abbrev eq_p31zero9_map_CopySign_cons := @eqe.eq_p31zero9_map_CopySign_cons
  abbrev eq_p31zero9_map_Add_nil := @eqe.eq_p31zero9_map_Add_nil
  abbrev eq_p31zero9_map_Add_cons := @eqe.eq_p31zero9_map_Add_cons
  abbrev eq_p31zero9_map_Subtract_nil := @eqe.eq_p31zero9_map_Subtract_nil
  abbrev eq_p31zero9_map_Subtract_cons := @eqe.eq_p31zero9_map_Subtract_cons
  abbrev eq_p31zero9_map_Multiply_nil := @eqe.eq_p31zero9_map_Multiply_nil
  abbrev eq_p31zero9_map_Multiply_cons := @eqe.eq_p31zero9_map_Multiply_cons
  abbrev eq_p31zero9_map_Divide_nil := @eqe.eq_p31zero9_map_Divide_nil
  abbrev eq_p31zero9_map_Divide_cons := @eqe.eq_p31zero9_map_Divide_cons
  abbrev eq_p31zero9_map_FMA_nil := @eqe.eq_p31zero9_map_FMA_nil
  abbrev eq_p31zero9_map_FMA_cons := @eqe.eq_p31zero9_map_FMA_cons
  abbrev eq_p31zero9_map_FAA_nil := @eqe.eq_p31zero9_map_FAA_nil
  abbrev eq_p31zero9_map_FAA_cons := @eqe.eq_p31zero9_map_FAA_cons
  abbrev eq_p31zero9_map_Recip_nil := @eqe.eq_p31zero9_map_Recip_nil
  abbrev eq_p31zero9_map_Recip_cons := @eqe.eq_p31zero9_map_Recip_cons
  abbrev eq_p31zero9_map_Minimum_nil := @eqe.eq_p31zero9_map_Minimum_nil
  abbrev eq_p31zero9_map_Minimum_cons := @eqe.eq_p31zero9_map_Minimum_cons
  abbrev eq_p31zero9_map_Maximum_nil := @eqe.eq_p31zero9_map_Maximum_nil
  abbrev eq_p31zero9_map_Maximum_cons := @eqe.eq_p31zero9_map_Maximum_cons
  abbrev eq_p31zero9_map_MinimumNumber_nil := @eqe.eq_p31zero9_map_MinimumNumber_nil
  abbrev eq_p31zero9_map_MinimumNumber_cons := @eqe.eq_p31zero9_map_MinimumNumber_cons
  abbrev eq_p31zero9_map_MaximumNumber_nil := @eqe.eq_p31zero9_map_MaximumNumber_nil
  abbrev eq_p31zero9_map_MaximumNumber_cons := @eqe.eq_p31zero9_map_MaximumNumber_cons
  abbrev eq_p31zero9_map_MinimumMagnitude_nil := @eqe.eq_p31zero9_map_MinimumMagnitude_nil
  abbrev eq_p31zero9_map_MinimumMagnitude_cons := @eqe.eq_p31zero9_map_MinimumMagnitude_cons
  abbrev eq_p31zero9_map_MaximumMagnitude_nil := @eqe.eq_p31zero9_map_MaximumMagnitude_nil
  abbrev eq_p31zero9_map_MaximumMagnitude_cons := @eqe.eq_p31zero9_map_MaximumMagnitude_cons
  abbrev eq_p31zero9_map_MinimumMagnitudeNumber_nil := @eqe.eq_p31zero9_map_MinimumMagnitudeNumber_nil
  abbrev eq_p31zero9_map_MinimumMagnitudeNumber_cons := @eqe.eq_p31zero9_map_MinimumMagnitudeNumber_cons
  abbrev eq_p31zero9_map_MaximumMagnitudeNumber_nil := @eqe.eq_p31zero9_map_MaximumMagnitudeNumber_nil
  abbrev eq_p31zero9_map_MaximumMagnitudeNumber_cons := @eqe.eq_p31zero9_map_MaximumMagnitudeNumber_cons
  abbrev eq_p31zero9_map_MinimumFinite_nil := @eqe.eq_p31zero9_map_MinimumFinite_nil
  abbrev eq_p31zero9_map_MinimumFinite_cons := @eqe.eq_p31zero9_map_MinimumFinite_cons
  abbrev eq_p31zero9_map_MaximumFinite_nil := @eqe.eq_p31zero9_map_MaximumFinite_nil
  abbrev eq_p31zero9_map_MaximumFinite_cons := @eqe.eq_p31zero9_map_MaximumFinite_cons
  abbrev eq_p31zero9_map_Clamp_nil := @eqe.eq_p31zero9_map_Clamp_nil
  abbrev eq_p31zero9_map_Clamp_cons := @eqe.eq_p31zero9_map_Clamp_cons
  abbrev eq_p31zero9_map_Sqrt_nil := @eqe.eq_p31zero9_map_Sqrt_nil
  abbrev eq_p31zero9_map_Sqrt_cons := @eqe.eq_p31zero9_map_Sqrt_cons
  abbrev eq_p31zero9_map_RSqrt_nil := @eqe.eq_p31zero9_map_RSqrt_nil
  abbrev eq_p31zero9_map_RSqrt_cons := @eqe.eq_p31zero9_map_RSqrt_cons
  abbrev eq_p31zero9_map_Exp_nil := @eqe.eq_p31zero9_map_Exp_nil
  abbrev eq_p31zero9_map_Exp_cons := @eqe.eq_p31zero9_map_Exp_cons
  abbrev eq_p31zero9_map_Exp2_nil := @eqe.eq_p31zero9_map_Exp2_nil
  abbrev eq_p31zero9_map_Exp2_cons := @eqe.eq_p31zero9_map_Exp2_cons
  abbrev eq_p31zero9_map_Log_nil := @eqe.eq_p31zero9_map_Log_nil
  abbrev eq_p31zero9_map_Log_cons := @eqe.eq_p31zero9_map_Log_cons
  abbrev eq_p31zero9_map_Log2_nil := @eqe.eq_p31zero9_map_Log2_nil
  abbrev eq_p31zero9_map_Log2_cons := @eqe.eq_p31zero9_map_Log2_cons
  abbrev eq_p31zero9_map_LogOnePlus_nil := @eqe.eq_p31zero9_map_LogOnePlus_nil
  abbrev eq_p31zero9_map_LogOnePlus_cons := @eqe.eq_p31zero9_map_LogOnePlus_cons
  abbrev eq_p31zero9_map_ExpMinusOne_nil := @eqe.eq_p31zero9_map_ExpMinusOne_nil
  abbrev eq_p31zero9_map_ExpMinusOne_cons := @eqe.eq_p31zero9_map_ExpMinusOne_cons
  abbrev eq_p31zero9_map_Sin_nil := @eqe.eq_p31zero9_map_Sin_nil
  abbrev eq_p31zero9_map_Sin_cons := @eqe.eq_p31zero9_map_Sin_cons
  abbrev eq_p31zero9_map_Cos_nil := @eqe.eq_p31zero9_map_Cos_nil
  abbrev eq_p31zero9_map_Cos_cons := @eqe.eq_p31zero9_map_Cos_cons
  abbrev eq_p31zero9_map_Tan_nil := @eqe.eq_p31zero9_map_Tan_nil
  abbrev eq_p31zero9_map_Tan_cons := @eqe.eq_p31zero9_map_Tan_cons
  abbrev eq_p31zero9_map_ArcSin_nil := @eqe.eq_p31zero9_map_ArcSin_nil
  abbrev eq_p31zero9_map_ArcSin_cons := @eqe.eq_p31zero9_map_ArcSin_cons
  abbrev eq_p31zero9_map_ArcCos_nil := @eqe.eq_p31zero9_map_ArcCos_nil
  abbrev eq_p31zero9_map_ArcCos_cons := @eqe.eq_p31zero9_map_ArcCos_cons
  abbrev eq_p31zero9_map_ArcTan_nil := @eqe.eq_p31zero9_map_ArcTan_nil
  abbrev eq_p31zero9_map_ArcTan_cons := @eqe.eq_p31zero9_map_ArcTan_cons
  abbrev eq_p31zero9_map_Sinh_nil := @eqe.eq_p31zero9_map_Sinh_nil
  abbrev eq_p31zero9_map_Sinh_cons := @eqe.eq_p31zero9_map_Sinh_cons
  abbrev eq_p31zero9_map_Cosh_nil := @eqe.eq_p31zero9_map_Cosh_nil
  abbrev eq_p31zero9_map_Cosh_cons := @eqe.eq_p31zero9_map_Cosh_cons
  abbrev eq_p31zero9_map_Tanh_nil := @eqe.eq_p31zero9_map_Tanh_nil
  abbrev eq_p31zero9_map_Tanh_cons := @eqe.eq_p31zero9_map_Tanh_cons
  abbrev eq_p31zero9_map_ArcSinh_nil := @eqe.eq_p31zero9_map_ArcSinh_nil
  abbrev eq_p31zero9_map_ArcSinh_cons := @eqe.eq_p31zero9_map_ArcSinh_cons
  abbrev eq_p31zero9_map_ArcCosh_nil := @eqe.eq_p31zero9_map_ArcCosh_nil
  abbrev eq_p31zero9_map_ArcCosh_cons := @eqe.eq_p31zero9_map_ArcCosh_cons
  abbrev eq_p31zero9_map_ArcTanh_nil := @eqe.eq_p31zero9_map_ArcTanh_nil
  abbrev eq_p31zero9_map_ArcTanh_cons := @eqe.eq_p31zero9_map_ArcTanh_cons
  abbrev eq_p31zero9_map_SinPi_nil := @eqe.eq_p31zero9_map_SinPi_nil
  abbrev eq_p31zero9_map_SinPi_cons := @eqe.eq_p31zero9_map_SinPi_cons
  abbrev eq_p31zero9_map_CosPi_nil := @eqe.eq_p31zero9_map_CosPi_nil
  abbrev eq_p31zero9_map_CosPi_cons := @eqe.eq_p31zero9_map_CosPi_cons
  abbrev eq_p31zero9_map_TanPi_nil := @eqe.eq_p31zero9_map_TanPi_nil
  abbrev eq_p31zero9_map_TanPi_cons := @eqe.eq_p31zero9_map_TanPi_cons
  abbrev eq_p31zero9_map_ArcSinPi_nil := @eqe.eq_p31zero9_map_ArcSinPi_nil
  abbrev eq_p31zero9_map_ArcSinPi_cons := @eqe.eq_p31zero9_map_ArcSinPi_cons
  abbrev eq_p31zero9_map_ArcCosPi_nil := @eqe.eq_p31zero9_map_ArcCosPi_nil
  abbrev eq_p31zero9_map_ArcCosPi_cons := @eqe.eq_p31zero9_map_ArcCosPi_cons
  abbrev eq_p31zero9_map_ArcTanPi_nil := @eqe.eq_p31zero9_map_ArcTanPi_nil
  abbrev eq_p31zero9_map_ArcTanPi_cons := @eqe.eq_p31zero9_map_ArcTanPi_cons
  abbrev eq_p31zero9_map_Softplus_nil := @eqe.eq_p31zero9_map_Softplus_nil
  abbrev eq_p31zero9_map_Softplus_cons := @eqe.eq_p31zero9_map_Softplus_cons
  abbrev eq_p31zero9_map_Hypot_nil := @eqe.eq_p31zero9_map_Hypot_nil
  abbrev eq_p31zero9_map_Hypot_cons := @eqe.eq_p31zero9_map_Hypot_cons
  abbrev eq_p31zero9_map_ArcTan2_nil := @eqe.eq_p31zero9_map_ArcTan2_nil
  abbrev eq_p31zero9_map_ArcTan2_cons := @eqe.eq_p31zero9_map_ArcTan2_cons
  abbrev eq_p31zero9_map_ArcTan2Pi_nil := @eqe.eq_p31zero9_map_ArcTan2Pi_nil
  abbrev eq_p31zero9_map_ArcTan2Pi_cons := @eqe.eq_p31zero9_map_ArcTan2Pi_cons

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_xcons eqe.eqe_xcons eqa.eqa_decodeElements eqe.eqe_decodeElements eqa.eqa_multiplyElements eqe.eqe_multiplyElements eqa.eqa_blockDecode eqe.eqe_blockDecode eqa.eqa_absElements eqe.eqe_absElements eqa.eqa_pairProducts eqe.eqe_pairProducts eqa.eqa_mapConvert eqe.eqe_mapConvert eqa.eqa_mapAbs eqe.eqe_mapAbs eqa.eqa_mapNegate eqe.eqe_mapNegate eqa.eqa_mapCopySign eqe.eqe_mapCopySign eqa.eqa_mapAdd eqe.eqe_mapAdd eqa.eqa_mapSubtract eqe.eqe_mapSubtract eqa.eqa_mapMultiply eqe.eqe_mapMultiply eqa.eqa_mapDivide eqe.eqe_mapDivide eqa.eqa_mapFMA eqe.eqe_mapFMA eqa.eqa_mapFAA eqe.eqe_mapFAA eqa.eqa_mapRecip eqe.eqe_mapRecip eqa.eqa_mapMinimum eqe.eqe_mapMinimum eqa.eqa_mapMaximum eqe.eqe_mapMaximum eqa.eqa_mapMinimumNumber eqe.eqe_mapMinimumNumber eqa.eqa_mapMaximumNumber eqe.eqe_mapMaximumNumber eqa.eqa_mapMinimumMagnitude eqe.eqe_mapMinimumMagnitude eqa.eqa_mapMaximumMagnitude eqe.eqe_mapMaximumMagnitude eqa.eqa_mapMinimumMagnitudeNumber eqe.eqe_mapMinimumMagnitudeNumber eqa.eqa_mapMaximumMagnitudeNumber eqe.eqe_mapMaximumMagnitudeNumber eqa.eqa_mapMinimumFinite eqe.eqe_mapMinimumFinite eqa.eqa_mapMaximumFinite eqe.eqe_mapMaximumFinite eqa.eqa_mapClamp eqe.eqe_mapClamp eqa.eqa_mapSqrt eqe.eqe_mapSqrt eqa.eqa_mapRSqrt eqe.eqe_mapRSqrt eqa.eqa_mapExp eqe.eqe_mapExp eqa.eqa_mapExp2 eqe.eqe_mapExp2 eqa.eqa_mapLog eqe.eqe_mapLog eqa.eqa_mapLog2 eqe.eqe_mapLog2 eqa.eqa_mapLogOnePlus eqe.eqe_mapLogOnePlus eqa.eqa_mapExpMinusOne eqe.eqe_mapExpMinusOne eqa.eqa_mapSin eqe.eqe_mapSin eqa.eqa_mapCos eqe.eqe_mapCos eqa.eqa_mapTan eqe.eqe_mapTan eqa.eqa_mapArcSin eqe.eqe_mapArcSin eqa.eqa_mapArcCos eqe.eqe_mapArcCos eqa.eqa_mapArcTan eqe.eqe_mapArcTan eqa.eqa_mapSinh eqe.eqe_mapSinh eqa.eqa_mapCosh eqe.eqe_mapCosh eqa.eqa_mapTanh eqe.eqe_mapTanh eqa.eqa_mapArcSinh eqe.eqe_mapArcSinh eqa.eqa_mapArcCosh eqe.eqe_mapArcCosh eqa.eqa_mapArcTanh eqe.eqe_mapArcTanh eqa.eqa_mapSinPi eqe.eqe_mapSinPi eqa.eqa_mapCosPi eqe.eqe_mapCosPi eqa.eqa_mapTanPi eqe.eqe_mapTanPi eqa.eqa_mapArcSinPi eqe.eqe_mapArcSinPi eqa.eqa_mapArcCosPi eqe.eqe_mapArcCosPi eqa.eqa_mapArcTanPi eqe.eqe_mapArcTanPi eqa.eqa_mapSoftplus eqe.eqe_mapSoftplus eqa.eqa_mapHypot eqe.eqe_mapHypot eqa.eqa_mapArcTan2 eqe.eqe_mapArcTan2 eqa.eqa_mapArcTan2Pi eqe.eqe_mapArcTan2Pi
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.xnil_decl has_sort.xcons_decl eqe.eq_p31zero9_block_core_zerozero4 eqe.eq_p31zero9_block_core_zerozero5 eqe.eq_p31zero9_block_core_zerozero6 eqe.eq_p31zero9_block_core_zerozero7 eqe.eq_p31zero9_block_core_zerozero8 eqe.eq_p31zero9_block_ops_zerozero7 eqe.eq_p31zero9_block_ops_zerozero8 eqe.eq_p31zero9_block_ops_zerozero9 eqe.eq_p31zero9_block_ops_zero1zero eqe.eq_p31zero9_map_Convert_nil eqe.eq_p31zero9_map_Convert_cons eqe.eq_p31zero9_map_Abs_nil eqe.eq_p31zero9_map_Abs_cons eqe.eq_p31zero9_map_Negate_nil eqe.eq_p31zero9_map_Negate_cons eqe.eq_p31zero9_map_CopySign_nil eqe.eq_p31zero9_map_CopySign_cons eqe.eq_p31zero9_map_Add_nil eqe.eq_p31zero9_map_Add_cons eqe.eq_p31zero9_map_Subtract_nil eqe.eq_p31zero9_map_Subtract_cons eqe.eq_p31zero9_map_Multiply_nil eqe.eq_p31zero9_map_Multiply_cons eqe.eq_p31zero9_map_Divide_nil eqe.eq_p31zero9_map_Divide_cons eqe.eq_p31zero9_map_FMA_nil eqe.eq_p31zero9_map_FMA_cons eqe.eq_p31zero9_map_FAA_nil eqe.eq_p31zero9_map_FAA_cons eqe.eq_p31zero9_map_Recip_nil eqe.eq_p31zero9_map_Recip_cons eqe.eq_p31zero9_map_Minimum_nil eqe.eq_p31zero9_map_Minimum_cons eqe.eq_p31zero9_map_Maximum_nil eqe.eq_p31zero9_map_Maximum_cons eqe.eq_p31zero9_map_MinimumNumber_nil eqe.eq_p31zero9_map_MinimumNumber_cons eqe.eq_p31zero9_map_MaximumNumber_nil eqe.eq_p31zero9_map_MaximumNumber_cons eqe.eq_p31zero9_map_MinimumMagnitude_nil eqe.eq_p31zero9_map_MinimumMagnitude_cons eqe.eq_p31zero9_map_MaximumMagnitude_nil eqe.eq_p31zero9_map_MaximumMagnitude_cons eqe.eq_p31zero9_map_MinimumMagnitudeNumber_nil eqe.eq_p31zero9_map_MinimumMagnitudeNumber_cons eqe.eq_p31zero9_map_MaximumMagnitudeNumber_nil eqe.eq_p31zero9_map_MaximumMagnitudeNumber_cons eqe.eq_p31zero9_map_MinimumFinite_nil eqe.eq_p31zero9_map_MinimumFinite_cons eqe.eq_p31zero9_map_MaximumFinite_nil eqe.eq_p31zero9_map_MaximumFinite_cons eqe.eq_p31zero9_map_Clamp_nil eqe.eq_p31zero9_map_Clamp_cons eqe.eq_p31zero9_map_Sqrt_nil eqe.eq_p31zero9_map_Sqrt_cons eqe.eq_p31zero9_map_RSqrt_nil eqe.eq_p31zero9_map_RSqrt_cons eqe.eq_p31zero9_map_Exp_nil eqe.eq_p31zero9_map_Exp_cons eqe.eq_p31zero9_map_Exp2_nil eqe.eq_p31zero9_map_Exp2_cons eqe.eq_p31zero9_map_Log_nil eqe.eq_p31zero9_map_Log_cons eqe.eq_p31zero9_map_Log2_nil eqe.eq_p31zero9_map_Log2_cons eqe.eq_p31zero9_map_LogOnePlus_nil eqe.eq_p31zero9_map_LogOnePlus_cons eqe.eq_p31zero9_map_ExpMinusOne_nil eqe.eq_p31zero9_map_ExpMinusOne_cons eqe.eq_p31zero9_map_Sin_nil eqe.eq_p31zero9_map_Sin_cons eqe.eq_p31zero9_map_Cos_nil eqe.eq_p31zero9_map_Cos_cons eqe.eq_p31zero9_map_Tan_nil eqe.eq_p31zero9_map_Tan_cons eqe.eq_p31zero9_map_ArcSin_nil eqe.eq_p31zero9_map_ArcSin_cons eqe.eq_p31zero9_map_ArcCos_nil eqe.eq_p31zero9_map_ArcCos_cons eqe.eq_p31zero9_map_ArcTan_nil eqe.eq_p31zero9_map_ArcTan_cons eqe.eq_p31zero9_map_Sinh_nil eqe.eq_p31zero9_map_Sinh_cons eqe.eq_p31zero9_map_Cosh_nil eqe.eq_p31zero9_map_Cosh_cons eqe.eq_p31zero9_map_Tanh_nil eqe.eq_p31zero9_map_Tanh_cons eqe.eq_p31zero9_map_ArcSinh_nil eqe.eq_p31zero9_map_ArcSinh_cons eqe.eq_p31zero9_map_ArcCosh_nil eqe.eq_p31zero9_map_ArcCosh_cons eqe.eq_p31zero9_map_ArcTanh_nil eqe.eq_p31zero9_map_ArcTanh_cons eqe.eq_p31zero9_map_SinPi_nil eqe.eq_p31zero9_map_SinPi_cons eqe.eq_p31zero9_map_CosPi_nil eqe.eq_p31zero9_map_CosPi_cons eqe.eq_p31zero9_map_TanPi_nil eqe.eq_p31zero9_map_TanPi_cons eqe.eq_p31zero9_map_ArcSinPi_nil eqe.eq_p31zero9_map_ArcSinPi_cons eqe.eq_p31zero9_map_ArcCosPi_nil eqe.eq_p31zero9_map_ArcCosPi_cons eqe.eq_p31zero9_map_ArcTanPi_nil eqe.eq_p31zero9_map_ArcTanPi_cons eqe.eq_p31zero9_map_Softplus_nil eqe.eq_p31zero9_map_Softplus_cons eqe.eq_p31zero9_map_Hypot_nil eqe.eq_p31zero9_map_Hypot_cons eqe.eq_p31zero9_map_ArcTan2_nil eqe.eq_p31zero9_map_ArcTan2_cons eqe.eq_p31zero9_map_ArcTan2Pi_nil eqe.eq_p31zero9_map_ArcTan2Pi_cons
end kXSeq

namespace kCodeSeq
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kCodeSeq) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kCodeSeq} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kCodeSeq} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kCodeSeq} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev cnil_decl := @has_sort.cnil_decl
  abbrev ccons_decl := @has_sort.ccons_decl
  abbrev partitionUnion_decl := @has_sort.partitionUnion_decl
  abbrev appendCodes_decl := @has_sort.appendCodes_decl
  abbrev eqa_ccons := @eqa.eqa_ccons
  abbrev eqe_ccons := @eqe.eqe_ccons
  abbrev eqa_blockProject := @eqa.eqa_blockProject
  abbrev eqe_blockProject := @eqe.eqe_blockProject
  abbrev eqa_projectElements := @eqa.eqa_projectElements
  abbrev eqe_projectElements := @eqe.eqe_projectElements
  abbrev eqa_projectUnscaled := @eqa.eqa_projectUnscaled
  abbrev eqe_projectUnscaled := @eqe.eqe_projectUnscaled
  abbrev eqa_at := @eqa.eqa_at
  abbrev eqe_at := @eqe.eqe_at
  abbrev eqa_partitionUnion := @eqa.eqa_partitionUnion
  abbrev eqe_partitionUnion := @eqe.eqe_partitionUnion
  abbrev eqa_appendCodes := @eqa.eqa_appendCodes
  abbrev eqe_appendCodes := @eqe.eqe_appendCodes
  abbrev eqa_ConvertFromBlock := @eqa.eqa_ConvertFromBlock
  abbrev eqe_ConvertFromBlock := @eqe.eqe_ConvertFromBlock
  abbrev eqa_ConvertToBlock := @eqa.eqa_ConvertToBlock
  abbrev eqe_ConvertToBlock := @eqe.eqe_ConvertToBlock
  abbrev eq_p31zero9_block_core_zero14 := @eqe.eq_p31zero9_block_core_zero14
  abbrev eq_p31zero9_block_core_zero15 := @eqe.eq_p31zero9_block_core_zero15
  abbrev eq_p31zero9_block_core_zero16 := @eqe.eq_p31zero9_block_core_zero16
  abbrev eq_p31zero9_block_core_zero17 := @eqe.eq_p31zero9_block_core_zero17
  abbrev eq_p31zero9_block_core_zero18 := @eqe.eq_p31zero9_block_core_zero18
  abbrev eq_p31zero9_sequences_zerozero3 := @eqe.eq_p31zero9_sequences_zerozero3
  abbrev eq_p31zero9_sequences_zerozero4 := @eqe.eq_p31zero9_sequences_zerozero4
  abbrev eq_p31zero9_conformance_zero6zero := @eqe.eq_p31zero9_conformance_zero6zero
  abbrev eq_p31zero9_conformance_zero61 := @eqe.eq_p31zero9_conformance_zero61
  abbrev eq_p31zero9_partition_union_empty := @eqe.eq_p31zero9_partition_union_empty
  abbrev eq_p31zero9_partition_union_cons := @eqe.eq_p31zero9_partition_union_cons
  abbrev eq_p31zero9_block_ops_zero11 := @eqe.eq_p31zero9_block_ops_zero11
  abbrev eq_p31zero9_block_ops_zero12 := @eqe.eq_p31zero9_block_ops_zero12

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_ccons eqe.eqe_ccons eqa.eqa_blockProject eqe.eqe_blockProject eqa.eqa_projectElements eqe.eqe_projectElements eqa.eqa_projectUnscaled eqe.eqe_projectUnscaled eqa.eqa_at eqe.eqe_at eqa.eqa_partitionUnion eqe.eqe_partitionUnion eqa.eqa_appendCodes eqe.eqe_appendCodes eqa.eqa_ConvertFromBlock eqe.eqe_ConvertFromBlock eqa.eqa_ConvertToBlock eqe.eqe_ConvertToBlock
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.cnil_decl has_sort.ccons_decl has_sort.partitionUnion_decl has_sort.appendCodes_decl eqe.eq_p31zero9_block_core_zero14 eqe.eq_p31zero9_block_core_zero15 eqe.eq_p31zero9_block_core_zero16 eqe.eq_p31zero9_block_core_zero17 eqe.eq_p31zero9_block_core_zero18 eqe.eq_p31zero9_sequences_zerozero3 eqe.eq_p31zero9_sequences_zerozero4 eqe.eq_p31zero9_conformance_zero6zero eqe.eq_p31zero9_conformance_zero61 eqe.eq_p31zero9_partition_union_empty eqe.eq_p31zero9_partition_union_cons eqe.eq_p31zero9_block_ops_zero11 eqe.eq_p31zero9_block_ops_zero12
end kCodeSeq

namespace kBlock
  -- Sort membership lemmas

  -- Reflexivity and congruence lemmas
  @[simp] theorem eqe_refl (a : kBlock) : a.eqe a := eqe.from_eqa eqa.refl
  theorem eqa_congr {a b c d : kBlock} : a.eqa b → c.eqa d → (a.eqa c) = (b.eqa d)
    := generic_congr @eqa.trans @eqa.trans @eqa.symm
  theorem eqe_congr {a b c d : kBlock} : a.eqe b → c.eqe d → (a.eqe c) = (b.eqe d)
    := generic_congr @eqe.trans @eqe.trans @eqe.symm
  theorem eqa_eqe_congr {a b c d : kBlock} : a.eqa b → c.eqa d → (a.eqe c) = (b.eqe d)
    := generic_congr (λ {x y z} => (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))
      (λ {x y z h} => (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm

  -- Aliases
  abbrev block_decl := @has_sort.block_decl
  abbrev eqa_block := @eqa.eqa_block
  abbrev eqe_block := @eqe.eqe_block
  abbrev eqa_ConvertToBlockMaxAbsFinite := @eqa.eqa_ConvertToBlockMaxAbsFinite
  abbrev eqe_ConvertToBlockMaxAbsFinite := @eqe.eqe_ConvertToBlockMaxAbsFinite
  abbrev eqa_computedBlock := @eqa.eqa_computedBlock
  abbrev eqe_computedBlock := @eqe.eqe_computedBlock
  abbrev eqa_BlockConvert := @eqa.eqa_BlockConvert
  abbrev eqe_BlockConvert := @eqe.eqe_BlockConvert
  abbrev eqa_BlockAbs := @eqa.eqa_BlockAbs
  abbrev eqe_BlockAbs := @eqe.eqe_BlockAbs
  abbrev eqa_BlockNegate := @eqa.eqa_BlockNegate
  abbrev eqe_BlockNegate := @eqe.eqe_BlockNegate
  abbrev eqa_BlockCopySign := @eqa.eqa_BlockCopySign
  abbrev eqe_BlockCopySign := @eqe.eqe_BlockCopySign
  abbrev eqa_BlockAdd := @eqa.eqa_BlockAdd
  abbrev eqe_BlockAdd := @eqe.eqe_BlockAdd
  abbrev eqa_BlockSubtract := @eqa.eqa_BlockSubtract
  abbrev eqe_BlockSubtract := @eqe.eqe_BlockSubtract
  abbrev eqa_BlockMultiply := @eqa.eqa_BlockMultiply
  abbrev eqe_BlockMultiply := @eqe.eqe_BlockMultiply
  abbrev eqa_BlockDivide := @eqa.eqa_BlockDivide
  abbrev eqe_BlockDivide := @eqe.eqe_BlockDivide
  abbrev eqa_BlockFMA := @eqa.eqa_BlockFMA
  abbrev eqe_BlockFMA := @eqe.eqe_BlockFMA
  abbrev eqa_BlockFAA := @eqa.eqa_BlockFAA
  abbrev eqe_BlockFAA := @eqe.eqe_BlockFAA
  abbrev eqa_BlockRecip := @eqa.eqa_BlockRecip
  abbrev eqe_BlockRecip := @eqe.eqe_BlockRecip
  abbrev eqa_BlockMinimum := @eqa.eqa_BlockMinimum
  abbrev eqe_BlockMinimum := @eqe.eqe_BlockMinimum
  abbrev eqa_BlockMaximum := @eqa.eqa_BlockMaximum
  abbrev eqe_BlockMaximum := @eqe.eqe_BlockMaximum
  abbrev eqa_BlockMinimumNumber := @eqa.eqa_BlockMinimumNumber
  abbrev eqe_BlockMinimumNumber := @eqe.eqe_BlockMinimumNumber
  abbrev eqa_BlockMaximumNumber := @eqa.eqa_BlockMaximumNumber
  abbrev eqe_BlockMaximumNumber := @eqe.eqe_BlockMaximumNumber
  abbrev eqa_BlockMinimumMagnitude := @eqa.eqa_BlockMinimumMagnitude
  abbrev eqe_BlockMinimumMagnitude := @eqe.eqe_BlockMinimumMagnitude
  abbrev eqa_BlockMaximumMagnitude := @eqa.eqa_BlockMaximumMagnitude
  abbrev eqe_BlockMaximumMagnitude := @eqe.eqe_BlockMaximumMagnitude
  abbrev eqa_BlockMinimumMagnitudeNumber := @eqa.eqa_BlockMinimumMagnitudeNumber
  abbrev eqe_BlockMinimumMagnitudeNumber := @eqe.eqe_BlockMinimumMagnitudeNumber
  abbrev eqa_BlockMaximumMagnitudeNumber := @eqa.eqa_BlockMaximumMagnitudeNumber
  abbrev eqe_BlockMaximumMagnitudeNumber := @eqe.eqe_BlockMaximumMagnitudeNumber
  abbrev eqa_BlockMinimumFinite := @eqa.eqa_BlockMinimumFinite
  abbrev eqe_BlockMinimumFinite := @eqe.eqe_BlockMinimumFinite
  abbrev eqa_BlockMaximumFinite := @eqa.eqa_BlockMaximumFinite
  abbrev eqe_BlockMaximumFinite := @eqe.eqe_BlockMaximumFinite
  abbrev eqa_BlockClamp := @eqa.eqa_BlockClamp
  abbrev eqe_BlockClamp := @eqe.eqe_BlockClamp
  abbrev eqa_BlockSqrt := @eqa.eqa_BlockSqrt
  abbrev eqe_BlockSqrt := @eqe.eqe_BlockSqrt
  abbrev eqa_BlockRSqrt := @eqa.eqa_BlockRSqrt
  abbrev eqe_BlockRSqrt := @eqe.eqe_BlockRSqrt
  abbrev eqa_BlockExp := @eqa.eqa_BlockExp
  abbrev eqe_BlockExp := @eqe.eqe_BlockExp
  abbrev eqa_BlockExp2 := @eqa.eqa_BlockExp2
  abbrev eqe_BlockExp2 := @eqe.eqe_BlockExp2
  abbrev eqa_BlockLog := @eqa.eqa_BlockLog
  abbrev eqe_BlockLog := @eqe.eqe_BlockLog
  abbrev eqa_BlockLog2 := @eqa.eqa_BlockLog2
  abbrev eqe_BlockLog2 := @eqe.eqe_BlockLog2
  abbrev eqa_BlockLogOnePlus := @eqa.eqa_BlockLogOnePlus
  abbrev eqe_BlockLogOnePlus := @eqe.eqe_BlockLogOnePlus
  abbrev eqa_BlockExpMinusOne := @eqa.eqa_BlockExpMinusOne
  abbrev eqe_BlockExpMinusOne := @eqe.eqe_BlockExpMinusOne
  abbrev eqa_BlockSin := @eqa.eqa_BlockSin
  abbrev eqe_BlockSin := @eqe.eqe_BlockSin
  abbrev eqa_BlockCos := @eqa.eqa_BlockCos
  abbrev eqe_BlockCos := @eqe.eqe_BlockCos
  abbrev eqa_BlockTan := @eqa.eqa_BlockTan
  abbrev eqe_BlockTan := @eqe.eqe_BlockTan
  abbrev eqa_BlockArcSin := @eqa.eqa_BlockArcSin
  abbrev eqe_BlockArcSin := @eqe.eqe_BlockArcSin
  abbrev eqa_BlockArcCos := @eqa.eqa_BlockArcCos
  abbrev eqe_BlockArcCos := @eqe.eqe_BlockArcCos
  abbrev eqa_BlockArcTan := @eqa.eqa_BlockArcTan
  abbrev eqe_BlockArcTan := @eqe.eqe_BlockArcTan
  abbrev eqa_BlockSinh := @eqa.eqa_BlockSinh
  abbrev eqe_BlockSinh := @eqe.eqe_BlockSinh
  abbrev eqa_BlockCosh := @eqa.eqa_BlockCosh
  abbrev eqe_BlockCosh := @eqe.eqe_BlockCosh
  abbrev eqa_BlockTanh := @eqa.eqa_BlockTanh
  abbrev eqe_BlockTanh := @eqe.eqe_BlockTanh
  abbrev eqa_BlockArcSinh := @eqa.eqa_BlockArcSinh
  abbrev eqe_BlockArcSinh := @eqe.eqe_BlockArcSinh
  abbrev eqa_BlockArcCosh := @eqa.eqa_BlockArcCosh
  abbrev eqe_BlockArcCosh := @eqe.eqe_BlockArcCosh
  abbrev eqa_BlockArcTanh := @eqa.eqa_BlockArcTanh
  abbrev eqe_BlockArcTanh := @eqe.eqe_BlockArcTanh
  abbrev eqa_BlockSinPi := @eqa.eqa_BlockSinPi
  abbrev eqe_BlockSinPi := @eqe.eqe_BlockSinPi
  abbrev eqa_BlockCosPi := @eqa.eqa_BlockCosPi
  abbrev eqe_BlockCosPi := @eqe.eqe_BlockCosPi
  abbrev eqa_BlockTanPi := @eqa.eqa_BlockTanPi
  abbrev eqe_BlockTanPi := @eqe.eqe_BlockTanPi
  abbrev eqa_BlockArcSinPi := @eqa.eqa_BlockArcSinPi
  abbrev eqe_BlockArcSinPi := @eqe.eqe_BlockArcSinPi
  abbrev eqa_BlockArcCosPi := @eqa.eqa_BlockArcCosPi
  abbrev eqe_BlockArcCosPi := @eqe.eqe_BlockArcCosPi
  abbrev eqa_BlockArcTanPi := @eqa.eqa_BlockArcTanPi
  abbrev eqe_BlockArcTanPi := @eqe.eqe_BlockArcTanPi
  abbrev eqa_BlockSoftplus := @eqa.eqa_BlockSoftplus
  abbrev eqe_BlockSoftplus := @eqe.eqe_BlockSoftplus
  abbrev eqa_BlockHypot := @eqa.eqa_BlockHypot
  abbrev eqe_BlockHypot := @eqe.eqe_BlockHypot
  abbrev eqa_BlockArcTan2 := @eqa.eqa_BlockArcTan2
  abbrev eqe_BlockArcTan2 := @eqe.eqe_BlockArcTan2
  abbrev eqa_BlockArcTan2Pi := @eqa.eqa_BlockArcTan2Pi
  abbrev eqe_BlockArcTan2Pi := @eqe.eqe_BlockArcTan2Pi
  abbrev eq_p31zero9_block_ops_zero13 := @eqe.eq_p31zero9_block_ops_zero13
  abbrev eq_p31zero9_block_ops_zero14 := @eqe.eq_p31zero9_block_ops_zero14
  abbrev eq_p31zero9_block_Convert := @eqe.eq_p31zero9_block_Convert
  abbrev eq_p31zero9_block_Abs := @eqe.eq_p31zero9_block_Abs
  abbrev eq_p31zero9_block_Negate := @eqe.eq_p31zero9_block_Negate
  abbrev eq_p31zero9_block_CopySign := @eqe.eq_p31zero9_block_CopySign
  abbrev eq_p31zero9_block_Add := @eqe.eq_p31zero9_block_Add
  abbrev eq_p31zero9_block_Subtract := @eqe.eq_p31zero9_block_Subtract
  abbrev eq_p31zero9_block_Multiply := @eqe.eq_p31zero9_block_Multiply
  abbrev eq_p31zero9_block_Divide := @eqe.eq_p31zero9_block_Divide
  abbrev eq_p31zero9_block_FMA := @eqe.eq_p31zero9_block_FMA
  abbrev eq_p31zero9_block_FAA := @eqe.eq_p31zero9_block_FAA
  abbrev eq_p31zero9_block_Recip := @eqe.eq_p31zero9_block_Recip
  abbrev eq_p31zero9_block_Minimum := @eqe.eq_p31zero9_block_Minimum
  abbrev eq_p31zero9_block_Maximum := @eqe.eq_p31zero9_block_Maximum
  abbrev eq_p31zero9_block_MinimumNumber := @eqe.eq_p31zero9_block_MinimumNumber
  abbrev eq_p31zero9_block_MaximumNumber := @eqe.eq_p31zero9_block_MaximumNumber
  abbrev eq_p31zero9_block_MinimumMagnitude := @eqe.eq_p31zero9_block_MinimumMagnitude
  abbrev eq_p31zero9_block_MaximumMagnitude := @eqe.eq_p31zero9_block_MaximumMagnitude
  abbrev eq_p31zero9_block_MinimumMagnitudeNumber := @eqe.eq_p31zero9_block_MinimumMagnitudeNumber
  abbrev eq_p31zero9_block_MaximumMagnitudeNumber := @eqe.eq_p31zero9_block_MaximumMagnitudeNumber
  abbrev eq_p31zero9_block_MinimumFinite := @eqe.eq_p31zero9_block_MinimumFinite
  abbrev eq_p31zero9_block_MaximumFinite := @eqe.eq_p31zero9_block_MaximumFinite
  abbrev eq_p31zero9_block_Clamp := @eqe.eq_p31zero9_block_Clamp
  abbrev eq_p31zero9_block_Sqrt := @eqe.eq_p31zero9_block_Sqrt
  abbrev eq_p31zero9_block_RSqrt := @eqe.eq_p31zero9_block_RSqrt
  abbrev eq_p31zero9_block_Exp := @eqe.eq_p31zero9_block_Exp
  abbrev eq_p31zero9_block_Exp2 := @eqe.eq_p31zero9_block_Exp2
  abbrev eq_p31zero9_block_Log := @eqe.eq_p31zero9_block_Log
  abbrev eq_p31zero9_block_Log2 := @eqe.eq_p31zero9_block_Log2
  abbrev eq_p31zero9_block_LogOnePlus := @eqe.eq_p31zero9_block_LogOnePlus
  abbrev eq_p31zero9_block_ExpMinusOne := @eqe.eq_p31zero9_block_ExpMinusOne
  abbrev eq_p31zero9_block_Sin := @eqe.eq_p31zero9_block_Sin
  abbrev eq_p31zero9_block_Cos := @eqe.eq_p31zero9_block_Cos
  abbrev eq_p31zero9_block_Tan := @eqe.eq_p31zero9_block_Tan
  abbrev eq_p31zero9_block_ArcSin := @eqe.eq_p31zero9_block_ArcSin
  abbrev eq_p31zero9_block_ArcCos := @eqe.eq_p31zero9_block_ArcCos
  abbrev eq_p31zero9_block_ArcTan := @eqe.eq_p31zero9_block_ArcTan
  abbrev eq_p31zero9_block_Sinh := @eqe.eq_p31zero9_block_Sinh
  abbrev eq_p31zero9_block_Cosh := @eqe.eq_p31zero9_block_Cosh
  abbrev eq_p31zero9_block_Tanh := @eqe.eq_p31zero9_block_Tanh
  abbrev eq_p31zero9_block_ArcSinh := @eqe.eq_p31zero9_block_ArcSinh
  abbrev eq_p31zero9_block_ArcCosh := @eqe.eq_p31zero9_block_ArcCosh
  abbrev eq_p31zero9_block_ArcTanh := @eqe.eq_p31zero9_block_ArcTanh
  abbrev eq_p31zero9_block_SinPi := @eqe.eq_p31zero9_block_SinPi
  abbrev eq_p31zero9_block_CosPi := @eqe.eq_p31zero9_block_CosPi
  abbrev eq_p31zero9_block_TanPi := @eqe.eq_p31zero9_block_TanPi
  abbrev eq_p31zero9_block_ArcSinPi := @eqe.eq_p31zero9_block_ArcSinPi
  abbrev eq_p31zero9_block_ArcCosPi := @eqe.eq_p31zero9_block_ArcCosPi
  abbrev eq_p31zero9_block_ArcTanPi := @eqe.eq_p31zero9_block_ArcTanPi
  abbrev eq_p31zero9_block_Softplus := @eqe.eq_p31zero9_block_Softplus
  abbrev eq_p31zero9_block_Hypot := @eqe.eq_p31zero9_block_Hypot
  abbrev eq_p31zero9_block_ArcTan2 := @eqe.eq_p31zero9_block_ArcTan2
  abbrev eq_p31zero9_block_ArcTan2Pi := @eqe.eq_p31zero9_block_ArcTan2Pi

  -- Attributes for the Lean simplifier and machinery
  attribute [simp] eqa.refl eqa.trans eqe.trans
  attribute [simp] eqa.eqa_block eqe.eqe_block eqa.eqa_ConvertToBlockMaxAbsFinite eqe.eqe_ConvertToBlockMaxAbsFinite eqa.eqa_computedBlock eqe.eqe_computedBlock eqa.eqa_BlockConvert eqe.eqe_BlockConvert eqa.eqa_BlockAbs eqe.eqe_BlockAbs eqa.eqa_BlockNegate eqe.eqe_BlockNegate eqa.eqa_BlockCopySign eqe.eqe_BlockCopySign eqa.eqa_BlockAdd eqe.eqe_BlockAdd eqa.eqa_BlockSubtract eqe.eqe_BlockSubtract eqa.eqa_BlockMultiply eqe.eqe_BlockMultiply eqa.eqa_BlockDivide eqe.eqe_BlockDivide eqa.eqa_BlockFMA eqe.eqe_BlockFMA eqa.eqa_BlockFAA eqe.eqe_BlockFAA eqa.eqa_BlockRecip eqe.eqe_BlockRecip eqa.eqa_BlockMinimum eqe.eqe_BlockMinimum eqa.eqa_BlockMaximum eqe.eqe_BlockMaximum eqa.eqa_BlockMinimumNumber eqe.eqe_BlockMinimumNumber eqa.eqa_BlockMaximumNumber eqe.eqe_BlockMaximumNumber eqa.eqa_BlockMinimumMagnitude eqe.eqe_BlockMinimumMagnitude eqa.eqa_BlockMaximumMagnitude eqe.eqe_BlockMaximumMagnitude eqa.eqa_BlockMinimumMagnitudeNumber eqe.eqe_BlockMinimumMagnitudeNumber eqa.eqa_BlockMaximumMagnitudeNumber eqe.eqe_BlockMaximumMagnitudeNumber eqa.eqa_BlockMinimumFinite eqe.eqe_BlockMinimumFinite eqa.eqa_BlockMaximumFinite eqe.eqe_BlockMaximumFinite eqa.eqa_BlockClamp eqe.eqe_BlockClamp eqa.eqa_BlockSqrt eqe.eqe_BlockSqrt eqa.eqa_BlockRSqrt eqe.eqe_BlockRSqrt eqa.eqa_BlockExp eqe.eqe_BlockExp eqa.eqa_BlockExp2 eqe.eqe_BlockExp2 eqa.eqa_BlockLog eqe.eqe_BlockLog eqa.eqa_BlockLog2 eqe.eqe_BlockLog2 eqa.eqa_BlockLogOnePlus eqe.eqe_BlockLogOnePlus eqa.eqa_BlockExpMinusOne eqe.eqe_BlockExpMinusOne eqa.eqa_BlockSin eqe.eqe_BlockSin eqa.eqa_BlockCos eqe.eqe_BlockCos eqa.eqa_BlockTan eqe.eqe_BlockTan eqa.eqa_BlockArcSin eqe.eqe_BlockArcSin eqa.eqa_BlockArcCos eqe.eqe_BlockArcCos eqa.eqa_BlockArcTan eqe.eqe_BlockArcTan eqa.eqa_BlockSinh eqe.eqe_BlockSinh eqa.eqa_BlockCosh eqe.eqe_BlockCosh eqa.eqa_BlockTanh eqe.eqe_BlockTanh eqa.eqa_BlockArcSinh eqe.eqe_BlockArcSinh eqa.eqa_BlockArcCosh eqe.eqe_BlockArcCosh eqa.eqa_BlockArcTanh eqe.eqe_BlockArcTanh eqa.eqa_BlockSinPi eqe.eqe_BlockSinPi eqa.eqa_BlockCosPi eqe.eqe_BlockCosPi eqa.eqa_BlockTanPi eqe.eqe_BlockTanPi eqa.eqa_BlockArcSinPi eqe.eqe_BlockArcSinPi eqa.eqa_BlockArcCosPi eqe.eqe_BlockArcCosPi eqa.eqa_BlockArcTanPi eqe.eqe_BlockArcTanPi eqa.eqa_BlockSoftplus eqe.eqe_BlockSoftplus eqa.eqa_BlockHypot eqe.eqe_BlockHypot eqa.eqa_BlockArcTan2 eqe.eqe_BlockArcTan2 eqa.eqa_BlockArcTan2Pi eqe.eqe_BlockArcTan2Pi
  attribute [congr] eqa_congr eqe_congr eqa_eqe_congr
  attribute [simp] has_sort.block_decl eqe.eq_p31zero9_block_ops_zero13 eqe.eq_p31zero9_block_ops_zero14 eqe.eq_p31zero9_block_Convert eqe.eq_p31zero9_block_Abs eqe.eq_p31zero9_block_Negate eqe.eq_p31zero9_block_CopySign eqe.eq_p31zero9_block_Add eqe.eq_p31zero9_block_Subtract eqe.eq_p31zero9_block_Multiply eqe.eq_p31zero9_block_Divide eqe.eq_p31zero9_block_FMA eqe.eq_p31zero9_block_FAA eqe.eq_p31zero9_block_Recip eqe.eq_p31zero9_block_Minimum eqe.eq_p31zero9_block_Maximum eqe.eq_p31zero9_block_MinimumNumber eqe.eq_p31zero9_block_MaximumNumber eqe.eq_p31zero9_block_MinimumMagnitude eqe.eq_p31zero9_block_MaximumMagnitude eqe.eq_p31zero9_block_MinimumMagnitudeNumber eqe.eq_p31zero9_block_MaximumMagnitudeNumber eqe.eq_p31zero9_block_MinimumFinite eqe.eq_p31zero9_block_MaximumFinite eqe.eq_p31zero9_block_Clamp eqe.eq_p31zero9_block_Sqrt eqe.eq_p31zero9_block_RSqrt eqe.eq_p31zero9_block_Exp eqe.eq_p31zero9_block_Exp2 eqe.eq_p31zero9_block_Log eqe.eq_p31zero9_block_Log2 eqe.eq_p31zero9_block_LogOnePlus eqe.eq_p31zero9_block_ExpMinusOne eqe.eq_p31zero9_block_Sin eqe.eq_p31zero9_block_Cos eqe.eq_p31zero9_block_Tan eqe.eq_p31zero9_block_ArcSin eqe.eq_p31zero9_block_ArcCos eqe.eq_p31zero9_block_ArcTan eqe.eq_p31zero9_block_Sinh eqe.eq_p31zero9_block_Cosh eqe.eq_p31zero9_block_Tanh eqe.eq_p31zero9_block_ArcSinh eqe.eq_p31zero9_block_ArcCosh eqe.eq_p31zero9_block_ArcTanh eqe.eq_p31zero9_block_SinPi eqe.eq_p31zero9_block_CosPi eqe.eq_p31zero9_block_TanPi eqe.eq_p31zero9_block_ArcSinPi eqe.eq_p31zero9_block_ArcCosPi eqe.eq_p31zero9_block_ArcTanPi eqe.eq_p31zero9_block_Softplus eqe.eq_p31zero9_block_Hypot eqe.eq_p31zero9_block_ArcTan2 eqe.eq_p31zero9_block_ArcTan2Pi
end kBlock

end Maude
