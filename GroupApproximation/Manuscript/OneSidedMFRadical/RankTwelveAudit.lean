import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration
import GroupApproximation.Meta.AxiomGuard

/-!
# Closed-axiom audit for the rank-twelve defect

This is the focused audit backing the `prop:defect` row of
`metadata/ONE_SIDED_MF_CLAIMS.md`.  The declarations below cover only the
explicit `EL₁₂` compressor, its nontrivial normally generating defect, and
the consequent full MF radical.  No simplicity hypothesis or normal-subgroup
theorem enters these checks.  The separately closed `prop:simple` and headline
audits live in `PrintedAudit` and `Endpoint/OneSidedTransportAudit`.  Every name
in this focused list is defined by `RankTwelveEndpoints` or
`RankTwelveConfiguration`; there are no conditional endpoint declarations.
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
