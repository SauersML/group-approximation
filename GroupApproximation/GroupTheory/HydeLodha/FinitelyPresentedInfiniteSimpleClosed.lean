import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitelyPresented
import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationStabK
import GroupApproximation.Meta.AxiomGuard

/-!
# hW: `FinitelyPresentedInfiniteSimpleStatement` over Lemma 4.6

Hyde–Lodha, proof of Theorem 1.1: "`Q_n` is simple from Proposition [simplicity], and of type `F_∞` from
Theorem 4.8."  At `n = 2`, in the finite-presentation form the Fournier-Facio paragraph needs.

The chain, with its one open leaf:

* Lemma 4.6: `UpsilonFinitelyPresented` (`QTwoFinitePresentationStabK`), with the pieces of its proof
  in `QTwoLemmaFourSixStatements`;
* Proposition 4.7: `isFinitelyPresented_stabK_of_upsilon`, packaged here as
  `stabKFinitelyPresented_of_upsilon`;
* Theorem 4.8 and simplicity: `finitelyPresentedInfiniteSimpleStatement_of_stabK`
  (`QTwoFinitelyPresented`).

When Lemma 4.6 closes, the closed `finitelyPresentedInfiniteSimple_closed` is added here.
-/

namespace GroupApproximation
namespace HydeLodha

open Manuscript.NonMF.TorsionFreePrinted

/-- **Hyde–Lodha, Proposition 4.7**, in the form Theorem 4.8 consumes, from Lemma 4.6. -/
theorem stabKFinitelyPresented_of_upsilon (hU : UpsilonFinitelyPresented)
    {Γ : Subgroup (Equiv.Perm ℚ)} (hQ : qTwo ≤ Γ) (hΓ : Γ ≤ gammaTwo) : StabKFinitelyPresented Γ :=
  fun _ hKfin hKne hKgrid => isFinitelyPresented_stabK_of_upsilon hU hQ hΓ hKfin hKne hKgrid

/-- **hW over Lemma 4.6**: a finitely presented, power-torsion-free, infinite simple group. -/
theorem finitelyPresentedInfiniteSimpleStatement_of_upsilon (hU : UpsilonFinitelyPresented) :
    FinitelyPresentedInfiniteSimpleStatement :=
  finitelyPresentedInfiniteSimpleStatement_of_stabK
    (stabKFinitelyPresented_of_upsilon hU le_rfl qTwo_le_gammaTwo)

#audit_axioms GroupApproximation.HydeLodha.stabKFinitelyPresented_of_upsilon
#audit_axioms GroupApproximation.HydeLodha.finitelyPresentedInfiniteSimpleStatement_of_upsilon

end HydeLodha
end GroupApproximation
