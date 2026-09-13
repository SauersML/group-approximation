import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitelyPresented
import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationStabK
import GroupApproximation.GroupTheory.HydeLodha.QTwoLemmaFourSixAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# hW: `FinitelyPresentedInfiniteSimpleStatement` over Lemma 4.6

Hyde–Lodha, proof of Theorem 1.1: "`Q_n` is simple from Proposition [simplicity], and of type `F_∞` from
Theorem 4.8."  At `n = 2`, in the finite-presentation form the Fournier-Facio paragraph needs.

The chain, with its one open leaf:

* the dynamics in the proof of Lemma 4.6: `LemmaFourSixDynamicsStatement` (`QTwoLemmaFourSixStatements`),
  the open leaf;
* Lemma 4.6: `UpsilonFinitelyPresented` (`QTwoFinitePresentationStabK`), from the dynamics by
  `upsilonFinitelyPresented_of_dynamics` (`QTwoLemmaFourSixAssembly`);
* Proposition 4.7: `isFinitelyPresented_stabK_of_upsilon`, packaged here as
  `stabKFinitelyPresented_of_upsilon`;
* Theorem 4.8 and simplicity: `finitelyPresentedInfiniteSimpleStatement_of_stabK`
  (`QTwoFinitelyPresented`).

When `LemmaFourSixDynamicsStatement` closes, the closed `finitelyPresentedInfiniteSimple_closed` is added
here.
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

#audit_axioms GroupApproximation.HydeLodha.stabKFinitelyPresented_of_upsilon
#audit_axioms GroupApproximation.HydeLodha.finitelyPresentedInfiniteSimpleStatement_of_upsilon
#audit_axioms GroupApproximation.HydeLodha.finitelyPresentedInfiniteSimpleStatement_of_dynamics

end HydeLodha
end GroupApproximation
