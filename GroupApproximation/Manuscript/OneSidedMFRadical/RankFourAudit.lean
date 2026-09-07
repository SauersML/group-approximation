import GroupApproximation.Manuscript.OneSidedMFRadical.ReducedCStarConsequenceRankFour
import GroupApproximation.Manuscript.OneSidedMFRadical.RankFourEJZInstance
import GroupApproximation.Meta.AxiomGuard

/-!
# Closed-axiom audit for the rank-four headline

This is the audit backing every printed endpoint of `thm:headline` at
`H = EL₄(L_{𝔽₂}(1,2))`, the group the manuscript now names.

The list is in printed order: the defect data of the compression step, the two
Ershov--Jaikin-Zapirain uses, simplicity, the full radical, the two C⋆-algebra
clauses, and the printed theorem as a single proposition.  Every name is
defined by `RankFourEndpoints`, `RankFourConfiguration`, `RankFourSimplicity`,
`RankFourEJZInstance`, `HeadlineTheoremRankFour` or
`ReducedCStarConsequenceRankFour`; there are no conditional endpoint
declarations among them.

Two kinds of statement are deliberately absent, because `#audit_closed_axioms`
refuses an advertised endpoint whose elaborated type is a pi type: the
centrality of the mark and the compression of the corner are stated as
`∀ γ ∈ L, …`.  Both are conjuncts of `manuscriptPropositionDefect`, which is
audited, so neither escapes the check.
-/

open GroupApproximation
open GroupApproximation.Manuscript.OneSidedMFRadical

/-! ## The compression step of the printed proof -/

#audit_closed_axioms RankFourEndpoint.defect_ne_one
#audit_closed_axioms RankFourEndpoint.normalClosure_defect_eq_top
#audit_closed_axioms RankFourEndpoint.c_val
#audit_closed_axioms RankFourEndpoint.u_conj_c
#audit_closed_axioms RankFourEndpoint.u_c_commutator_ell
#audit_closed_axioms RankFourEndpoint.printedDefectConfiguration
#audit_closed_axioms RankFourEndpoint.manuscriptPropositionDefect

/-! ## Strictness of the compression, for the maximal-C⋆ clause -/

#audit_closed_axioms RankFourEndpoint.ell_not_mem_u_conj_corner
#audit_closed_axioms RankFourEndpoint.u_conj_corner_lt

/-! ## Property (T) at the two printed ranks, and finite generation -/

#audit_closed_axioms RankFourEndpoint.finitelyGenerated
#audit_closed_axioms RankFourEndpoint.hasKazhdanPropertyT
#audit_closed_axioms RankFourEndpoint.corner_hasKazhdanPropertyT
#audit_closed_axioms RankFourEndpoint.printedBothGroupsHaveKazhdanPropertyT

/-! ## Simplicity and the full radical -/

#audit_closed_axioms RankFourEndpoint.manuscriptPropositionSimple
#audit_closed_axioms RankFourEndpoint.rankFour_actualCoronaMFResidual_eq_top
#audit_closed_axioms manuscriptBinaryLeavittFullRadicalRankFour
#audit_closed_axioms manuscriptBinaryLeavittHeadlineRankFour

/-! ## The two C⋆-algebra clauses, and the printed theorem -/

#audit_closed_axioms manuscriptReducedCStarConsequenceRankFour
#audit_closed_axioms manuscriptMaximalCStarNotFiniteRankFour
#audit_closed_axioms manuscriptSeparableStablyFiniteNonMFCStarAlgebraExistsRankFour
#audit_closed_axioms manuscriptNotEverySeparableStablyFiniteCStarAlgebraIsMFRankFour
#audit_closed_axioms manuscriptPrintedHeadlineRankFour
