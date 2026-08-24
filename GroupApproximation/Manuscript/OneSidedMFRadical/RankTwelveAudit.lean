import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration
import GroupApproximation.Meta.AxiomGuard

/-!
# Closed-axiom audit for the rank-twelve defect

This is the audit backing the `prop:defect` row of
`metadata/ONE_SIDED_MF_CLAIMS.md`.  It deliberately stops before
`prop:simple`: the declarations below cover only the explicit `EL₁₂`
compressor, its nontrivial normally generating defect, and the consequent full
MF radical.  No simplicity hypothesis or normal-subgroup theorem enters these
checks.  Every audited name is defined by `RankTwelveEndpoints` or
`RankTwelveConfiguration`; there are no conditional endpoint declarations in
this list.
-/

open GroupApproximation
open GroupApproximation.Manuscript.OneSidedMFRadical

#audit_closed_axioms RankTwelveEndpoint.defect_ne_one
#audit_closed_axioms RankTwelveEndpoint.normalClosure_defect_eq_top
#audit_closed_axioms RankTwelveEndpoint.printedTauGL_mem
#audit_closed_axioms RankTwelveEndpoint.corner_hasKazhdanPropertyT
#audit_closed_axioms RankTwelveEndpoint.tau_c_commutator_ell
#audit_closed_axioms RankTwelveEndpoint.printedDefectConfiguration
#audit_closed_axioms RankTwelveEndpoint.manuscriptPropositionDefect
#audit_closed_axioms RankTwelveEndpoint.rankTwelve_actualCoronaMFResidual_eq_top
