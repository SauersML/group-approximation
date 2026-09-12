import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.CharClass.ParityPSplitStepD

/-!
# Gating axiom audit for L4a and the splitting interface of Step D mod `p`

Lane `lix-evenside`.  Every endpoint-facing declaration of `ParityPTwistSymm`, `ParityPWuValue`,
`ParityPDecomposable`, `ParityPWuComponent`, `ParityPWuTransport` and `ParityPSplitStepD`,
checked with `#audit_axioms`, which throws unless the closure is exactly
`[propext, Classical.choice, Quot.sound]`.  A `Built` line for this module is the certificate.

`#audit_closed_axioms` is not used: every declaration here is conditional, taking its
hypotheses as binders or record fields.
-/

namespace GroupApproximation.CharClass

/-! ### `ParityPTwistSymm.lean` -/

#audit_axioms ParityP.rename_twist
#audit_axioms ParityP.twist_isSymmetric
#audit_axioms ParityP.twistSub
#audit_axioms ParityP.aeval_zero_twist
#audit_axioms ParityP.eLin_twistSub_fst

/-! ### `ParityPWuValue.lean` -/

#audit_axioms ParityP.neg_one_pow_add_two_mul_pow_add_two
#audit_axioms ParityP.eCoeff_esymmSub_of_ne
#audit_axioms ParityP.eCoeff_psumSub_of_ne
#audit_axioms ParityP.eCoeff_psumSub_self
#audit_axioms ParityP.twistSub_psumSub
#audit_axioms ParityP.eCoeff_twistSub_psumSub
#audit_axioms ParityP.eCoeff_twistSub_psumSub_succ
#audit_axioms ParityP.eCoeff_twistSub_esymmSub_succ_mul
#audit_axioms ParityP.eCoeff_twistSub_esymmSub_succ

/-! ### `ParityPDecomposable.lean` -/

#audit_axioms ParityP.gammaProd_append
#audit_axioms ParityP.gammaProd_replicate
#audit_axioms ParityP.gammaProd_map
#audit_axioms ParityP.IsDecomposable.map
#audit_axioms ParityP.IsDecomposable.congr
#audit_axioms ParityP.IsDecomposable.sub
#audit_axioms ParityP.IsDecomposable.intCast_mul
#audit_axioms ParityP.exists_list_of_finsupp
#audit_axioms ParityP.two_le_degree_of_ne
#audit_axioms ParityP.isDecomposable_eval₂_of_isWeightedHomogeneous
#audit_axioms ParityP.isDecomposable_of_eCoeff_eq_zero

/-! ### `ParityPWuComponent.lean` -/

#audit_axioms ParityP.isSymmetric_homogeneousComponent
#audit_axioms ParityP.compSub
#audit_axioms ParityP.eCoeff_eq_eCoeff_compSub
#audit_axioms ParityP.eCoeff_C_mul
#audit_axioms ParityP.wuComp
#audit_axioms ParityP.wuCompSub
#audit_axioms ParityP.wuCoeff
#audit_axioms ParityP.isHomogeneous_wuTerm
#audit_axioms ParityP.wuDeg_eq_iff
#audit_axioms ParityP.wuComp_eq_wuRHSP
#audit_axioms ParityP.eCoeff_wuCompSub
#audit_axioms ParityP.isDecomposable_wuComp
#audit_axioms ParityP.isDecomposable_wuRHSP
#audit_axioms ParityP.wuCoeff_cast_eq
#audit_axioms ParityP.isUnit_wuCoeff_cast

/-! ### `ParityPWuTransport.lean` -/

#audit_axioms ParityP.esymmOn_map
#audit_axioms ParityP.esymmOn_congr
#audit_axioms ParityP.esymmOn_eq_of_subset
#audit_axioms ParityP.esymmOn_attach
#audit_axioms ParityP.wuMonomialP_map
#audit_axioms ParityP.wuMonomialP_eq_zero_of_mem
#audit_axioms ParityP.wuRHSP_eq_of_subset
#audit_axioms ParityP.wuRHSP_map
#audit_axioms ParityP.wuRHSP_congr
#audit_axioms ParityP.wuRHSP_attach
#audit_axioms ParityP.exists_pad
#audit_axioms ParityP.eval₂Hom_esymm
#audit_axioms ParityP.eval₂Hom_wuRHSP
#audit_axioms ParityP.IsDecomposable.exists_lift
#audit_axioms ParityP.wu_isDecomposable_of_splitting
#audit_axioms ParityP.wu_field_of_splitting
#audit_axioms ParityP.isUnit_wuLeading

/-! ### `ParityPSplitStepD.lean` -/

#audit_axioms ParityP.HasSplittingP
#audit_axioms SplitStepDData
#audit_axioms SplitStepDData.toParityPData
#audit_axioms SplitStepDData.gamma_top_eq_zero

end GroupApproximation.CharClass
