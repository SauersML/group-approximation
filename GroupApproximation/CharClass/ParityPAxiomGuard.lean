import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.CharClass.ParityPCoeffBridge
import GroupApproximation.CharClass.ParityPSlice
import GroupApproximation.CharClass.ParityPTwo
import GroupApproximation.CharClass.ParityPWuCartan

/-!
# Gating axiom audit for the even side mod `p`

Lane `sp-evenside`.  Every declaration this lane owns, checked with `#audit_axioms`
(`GroupApproximation/Meta/AxiomGuard.lean`), which prints the same report as
`#print axioms` and then **throws** unless the closure is exactly
`[propext, Classical.choice, Quot.sound]`.

The point is that the verdict is a build error rather than a line in a log.  A `Built` line
on this module *is* the certificate, so there is nothing to grep — which retires a trap that
bit this lane: three of the twenty-four `#print axioms` lines in the older
`ParityPAxiomCheck.lean` wrap across three log lines, so a one-line grep under-reports them
as `[propext,` and reads like a violation.  With the gating command the wrap is irrelevant.

Pointed out by `sp-evenside-n`, 2026-09-10.  This module supersedes
`CharClass/ParityPAxiomCheck.lean`, which is in the pending landing batch and therefore not
edited; the older file should be deleted once the batch is in.

`#audit_closed_axioms` is deliberately **not** used here.  It additionally rejects a
declaration whose type starts with a binder, and every theorem in this lane is a conditional
one — the whole point of `ParityPData` is that it takes its hypotheses as fields.  The
unconditional endpoints of this program live at the C*-side, not here.
-/

namespace GroupApproximation.CharClass

/-! ### `ParityPData.lean` -/

#audit_axioms ParityP.aProd
#audit_axioms ParityP.aProd_nil
#audit_axioms ParityP.aProd_cons
#audit_axioms ParityP.bPart
#audit_axioms ParityP.bPart_nil
#audit_axioms ParityP.bPart_cons
#audit_axioms ParityP.aProd_eq_zero_of_mem
#audit_axioms ParityP.dvd_listSum
#audit_axioms ParityP.one_le_listSum
#audit_axioms ParityP.bPart_eq_zero
#audit_axioms ParityP.gammaProd
#audit_axioms ParityP.gammaProd_nil
#audit_axioms ParityP.gammaProd_cons
#audit_axioms ParityP.IsDecomposable.sum
#audit_axioms ParityP.IsDecomposable.pair
#audit_axioms ParityP.Instability
#audit_axioms ParityP.pR_b_succ_of_instability
#audit_axioms ParityP.pH_z_mul_of_cartan
#audit_axioms ParityPData.gammaProd_eq
#audit_axioms ParityPData.exists_iota_of_isDecomposable
#audit_axioms ParityPData.b_step
#audit_axioms ParityPData.b_eq_zero
#audit_axioms ParityPData.b_eq_zero_of_mod
#audit_axioms ParityPData.gamma_eq_zero
#audit_axioms ParityPData.gamma_rank_eq_zero

/-! ### `ParityPSlice.lean` -/

#audit_axioms ParityP.coeff_pow_expChar_eq_zero
#audit_axioms ParityP.sliceClass_eq_pow
#audit_axioms ParityP.sliceClass_coeff_eq_zero_of_not_dvd
#audit_axioms ParityPData.gamma_top_eq_zero_of_slice

/-! ### `ParityPTwo.lean` -/

#audit_axioms ParityData.iota_sqR_zero
#audit_axioms ParityData.iota_b_zero
#audit_axioms ParityData.gamma_zero
#audit_axioms ParityData.toParityPData
#audit_axioms ParityData.b_odd_eq_zero'
#audit_axioms ParityData.gamma_top_eq_zero'

/-! ### `ParityPWuCartan.lean` -/

#audit_axioms ParityP.wuMonomialP
#audit_axioms ParityP.wuMonomialP_def
#audit_axioms ParityP.wuMonomialP_zero
#audit_axioms ParityP.wuMonomialP_empty_of_pos
#audit_axioms ParityP.wuMonomialP_insert
#audit_axioms ParityP.wuRHSP
#audit_axioms ParityP.wuRHSP_def
#audit_axioms ParityP.wuRHSP_eq_sum_wuMonomialP
#audit_axioms ParityP.PowerData.pShift
#audit_axioms ParityP.PowerData.pShift_zero
#audit_axioms ParityP.PowerData.pShift_succ
#audit_axioms ParityP.PowerData.p_mul_y
#audit_axioms ParityP.PowerData.p_one_eq_zero
#audit_axioms ParityP.PowerData.p_prod
#audit_axioms ParityP.PowerData.gamma
#audit_axioms ParityP.PowerData.gamma_def
#audit_axioms ParityP.PowerData.gamma_zero
#audit_axioms ParityP.PowerData.p_gamma_succ
#audit_axioms ParityP.PowerData.p_gamma_succ_eq_smul

/-! ### `ParityPSymmetric.lean` -/

#audit_axioms ParityP.esymmSub
#audit_axioms ParityP.eExpand
#audit_axioms ParityP.eExpand_esymmSub
#audit_axioms ParityP.eExpand_mul
#audit_axioms ParityP.eExpand_add
#audit_axioms ParityP.eExpand_neg
#audit_axioms ParityP.eExpand_zero
#audit_axioms ParityP.eLin
#audit_axioms ParityP.eCoeff
#audit_axioms ParityP.eLin_esymmSub_self
#audit_axioms ParityP.eCoeff_esymmSub_self
#audit_axioms ParityP.eLin_esymmSub_fst
#audit_axioms ParityP.eCoeff_mul_eq_zero
#audit_axioms ParityP.eLin_mul_fst

/-! ### `ParityPNewton.lean` -/

#audit_axioms ParityP.eLinHom
#audit_axioms ParityP.eLinHom_apply
#audit_axioms ParityP.constantCoeff_esymm
#audit_axioms ParityP.aeval_zero_eExpand
#audit_axioms ParityP.eLin_fst
#audit_axioms ParityP.eLin_fst_esymm
#audit_axioms ParityP.eLin_fst_psum
#audit_axioms ParityP.eCoeff_add
#audit_axioms ParityP.eCoeff_zero
#audit_axioms ParityP.eCoeff_neg
#audit_axioms ParityP.eCoeff_sub
#audit_axioms ParityP.eCoeff_sum

/-! ### `ParityPNewtonValue.lean` -/

#audit_axioms ParityP.psumSub
#audit_axioms ParityP.psumSub_coe
#audit_axioms ParityP.esymmSub_coe
#audit_axioms ParityP.eCoeff_smul
#audit_axioms ParityP.newtonIdx
#audit_axioms ParityP.newtonIdx_mem
#audit_axioms ParityP.psumSub_eq_newton
#audit_axioms ParityP.eCoeff_psumSub

/-! ### `ParityPTwist.lean` -/

#audit_axioms ParityP.twist
#audit_axioms ParityP.twist_X
#audit_axioms ParityP.twist_psum
#audit_axioms ParityP.twist_psum_weight

/-! ### `ParityPHomog.lean` -/

#audit_axioms ParityP.esymm_isHomogeneous
#audit_axioms ParityP.eWeight
#audit_axioms ParityP.eWeight_apply
#audit_axioms ParityP.isHomogeneous_esymmAeval

/-! ### `ParityPHomogConverse.lean` -/

#audit_axioms ParityP.esymmAeval_injective
#audit_axioms ParityP.homogeneousComponent_eq_zero_of_ne
#audit_axioms ParityP.isHomogeneous_aeval_component
#audit_axioms ParityP.eExpand_isWeightedHomogeneous

/-! ### `ParityPCoeffBridge.lean` -/

#audit_axioms ParityP.epsSub
#audit_axioms ParityP.epsSub_self
#audit_axioms ParityP.epsSub_of_ne
#audit_axioms ParityP.snd_prod_eq_zero_of_ne
#audit_axioms ParityP.eLin_snd_eq_coeff
#audit_axioms ParityP.eCoeff_eq_coeff_eExpand
#audit_axioms ParityP.eCoeff_eq_zero_of_degree_ne
end GroupApproximation.CharClass
