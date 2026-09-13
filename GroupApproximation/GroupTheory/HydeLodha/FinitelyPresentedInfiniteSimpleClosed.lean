import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitelyPresented
import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationStabK
import GroupApproximation.GroupTheory.HydeLodha.QTwoLemmaFourSixAssembly
import GroupApproximation.GroupTheory.HydeLodha.QTwoLemmaFourSixDynamics
import GroupApproximation.Meta.AxiomGuard

/-!
# hW: `FinitelyPresentedInfiniteSimpleStatement`, closed

Hyde–Lodha, Theorem 1.1 at `n = 2`: `Q₂` is simple and of type `F_∞` (by Theorem 4.8), in the
finite-presentation form the Fournier-Facio paragraph needs.

The chain:

* the dynamics in the proof of Lemma 4.6: `lemmaFourSixDynamics` (`QTwoLemmaFourSixDynamics`);
* Lemma 4.6: `UpsilonFinitelyPresented` (`QTwoFinitePresentationStabK`), from the dynamics by
  `upsilonFinitelyPresented_of_dynamics` (`QTwoLemmaFourSixAssembly`);
* Proposition 4.7: `isFinitelyPresented_stabK_of_upsilon`, packaged here as
  `stabKFinitelyPresented_of_upsilon`;
* Theorem 4.8 and simplicity: `finitelyPresentedInfiniteSimpleStatement_of_stabK`
  (`QTwoFinitelyPresented`);
* `finitelyPresentedInfiniteSimple_closed`: hW.
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

/-- **hW over the dynamics of Lemma 4.6**: a finitely presented, power-torsion-free, infinite simple
group. -/
theorem finitelyPresentedInfiniteSimpleStatement_of_dynamics (hdyn : LemmaFourSixDynamicsStatement) :
    FinitelyPresentedInfiniteSimpleStatement :=
  finitelyPresentedInfiniteSimpleStatement_of_upsilon (upsilonFinitelyPresented_of_dynamics hdyn)

/-- **hW**: a finitely presented, power-torsion-free, infinite simple group, `Q₂ = [Γ₂, Γ₂]`
(Hyde–Lodha, Theorem 1.1 at `n = 2`). -/
theorem finitelyPresentedInfiniteSimple_closed : FinitelyPresentedInfiniteSimpleStatement :=
  finitelyPresentedInfiniteSimpleStatement_of_dynamics lemmaFourSixDynamics

#audit_axioms GroupApproximation.HydeLodha.stabKFinitelyPresented_of_upsilon
#audit_axioms GroupApproximation.HydeLodha.finitelyPresentedInfiniteSimpleStatement_of_upsilon
#audit_axioms GroupApproximation.HydeLodha.finitelyPresentedInfiniteSimpleStatement_of_dynamics
#audit_closed_axioms GroupApproximation.HydeLodha.finitelyPresentedInfiniteSimple_closed

end HydeLodha
end GroupApproximation
