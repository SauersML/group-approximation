import GroupApproximation.CharClass.LIXStepDGenData
import GroupApproximation.Meta.AxiomGuard

/-!
# Axiom gate for Step D at rank `n`

Lane `sp-evenside-n`.  The programme note's protocol requires the axiom closure of every
endpoint-facing declaration to be `[propext, Classical.choice, Quot.sound]` and nothing
else.

`#audit_axioms` rather than `#print axioms`: the repository's own command
(`Meta/AxiomGuard.lean`) prints the same report and then **throws** if the closure leaves
the classical allowlist, so a green build of this module *is* the certificate.  A
`#print axioms` file would instead put the verdict in the log, where the known trap that
axiom lists wrap across lines makes a line-oriented check under-report.

This module has no content and nothing imports it: it is a leaf, so it must be named on the
probe command explicitly — a closure gate is blind to a leaf.  Note the fleet rule that a
replayed `#audit_axioms` line is not evidence: the log this module's verdict is cited from
must show `Built` for it.
-/

namespace GroupApproximation.CharClass

/-! ### The abstract even side at the rank-`n` index -/

#audit_axioms Gen.gamma_top_rank_eq_zero
#audit_axioms Gen.gamma_top_rank_eq_zero_of_slice

/-! ### The sphere generator in any degree, and the two Künneth helpers -/

#audit_axioms Gen.sphereClass
#audit_axioms Gen.sphereClass_eq_tClass
#audit_axioms Gen.sphereClass_eq_xClass
#audit_axioms Gen.sphereClass_eq_of
#audit_axioms Gen.sq_b_of_grading
#audit_axioms Gen.tx_inj_of_degreewise

/-! ### The even side at the rank-`n` objects -/

#audit_axioms Gen.parityData_of
#audit_axioms Gen.gamma_top_eq_zero_of_slice_totalH
#audit_axioms Gen.gamma_top_eq_zero_of_hasSplitting

/-! ### Step D at the real objects -/

#audit_axioms Gen.WuStepDData.gamma_top_eq_zero
#audit_axioms Gen.stepD_of_wu
#audit_axioms Gen.stepD_of_wu_stage

/-! ### The rank-two bridges -/

#audit_axioms Gen.gamma_top_eq_zero_of_hasSplitting_two
#audit_axioms Gen.ofRankTwo
#audit_axioms Gen.toRankTwo
#audit_axioms stepD_of_wu_of_gen

end GroupApproximation.CharClass
