import GroupApproximation.CharClass.ParityPSlice
import GroupApproximation.CharClass.ParityPSymmetric
import GroupApproximation.CharClass.ParityPTwo
import GroupApproximation.CharClass.ParityPWuCartan

/-!
# Axiom check for the even side mod `p`

Lane `sp-evenside`.  The program note's protocol requires `#print axioms` on every
endpoint-facing theorem, with `[propext, Classical.choice, Quot.sound]` and nothing else.
This module has no content; it exists so that one probe of one target prints the whole
list.  It is a leaf and nothing imports it.
-/

namespace GroupApproximation.CharClass

#print axioms ParityP.bPart_eq_zero
#print axioms ParityP.IsDecomposable.sum
#print axioms ParityP.IsDecomposable.pair
#print axioms ParityP.pR_b_succ_of_instability
#print axioms ParityP.pH_z_mul_of_cartan
#print axioms ParityPData.b_step
#print axioms ParityPData.b_eq_zero
#print axioms ParityPData.b_eq_zero_of_mod
#print axioms ParityPData.gamma_eq_zero
#print axioms ParityPData.gamma_rank_eq_zero
#print axioms ParityP.coeff_pow_expChar_eq_zero
#print axioms ParityP.sliceClass_coeff_eq_zero_of_not_dvd
#print axioms ParityPData.gamma_top_eq_zero_of_slice
#print axioms ParityData.gamma_zero
#print axioms ParityData.toParityPData
#print axioms ParityData.b_odd_eq_zero'
#print axioms ParityData.gamma_top_eq_zero'

/-! ### L4a: the Cartan half and the coefficient functional -/

#print axioms ParityP.wuRHSP_eq_sum_wuMonomialP
#print axioms ParityP.PowerData.p_one_eq_zero
#print axioms ParityP.PowerData.p_prod
#print axioms ParityP.PowerData.p_gamma_succ
#print axioms ParityP.PowerData.p_gamma_succ_eq_smul
#print axioms ParityP.eCoeff_esymmSub_self
#print axioms ParityP.eCoeff_mul_eq_zero

end GroupApproximation.CharClass
