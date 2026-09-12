import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Sofic.LiteralSignFreeQuotient

/-!
# Closed audit for the sign-free compression endpoint

This is the audit surface for the second, analytically independent non-MF
construction.  Its group is the quotient of the literal finite presentation
by the single relation killing the old central sign.  The obstruction that
survives is instead the unsquared two-lamp commutator supplied by the
involutive-compression witness.

The endpoint does not import or invoke
`LiteralNonMFEndpoint.literal_not_isOperatorMF`.  The declarations below are
closed: no group, property-(T), small-cancellation, literature, or compiler
hypothesis is accepted at the endpoint.
-/

#audit_closed_axioms GroupApproximation.LiteralSignFreeQuotient.markSubgroup_eq_normalClosure_singleton
#audit_closed_axioms GroupApproximation.LiteralSignFreeQuotient.signFreeQuotient_finitelyPresented
#audit_closed_axioms GroupApproximation.LiteralSignFreeQuotient.signFree_collapse
#audit_closed_axioms GroupApproximation.LiteralSignFreeQuotient.signFreeQuotient_not_isOperatorMF
#audit_closed_axioms GroupApproximation.LiteralSignFreeQuotient.exists_finitelyPresented_signFree_not_isOperatorMF

