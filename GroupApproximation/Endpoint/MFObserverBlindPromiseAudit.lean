import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Computability.MFObserverBlindPromise

/-!
# Trust audit for the observer-blind promise problem

These checks reject both nonclassical axioms and a hidden leading declaration
input.  In particular, the compiler, the halting equivalence, and the
non-enumerability result are closed theorems rather than consequences of a
caller-supplied non-MF witness or reduction.
-/

#audit_closed_axioms GroupApproximation.MFObserverBlindPromise.closed_package
#audit_closed_axioms GroupApproximation.MFObserverBlindPromise.trivial_re
#audit_closed_axioms GroupApproximation.MFObserverBlindPromise.nontrivial_not_re
#audit_closed_axioms GroupApproximation.MFObserverBlindPromise.trivial_not_computable
#audit_closed_axioms GroupApproximation.MFObserverBlindPromise.no_triviality_decider
#audit_closed_axioms GroupApproximation.MFObserverBlindPromise.strictlyObserverBlind_not_re
