import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitelyPresented
import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationStabK
import GroupApproximation.Meta.AxiomGuard

/-!
# `FinitelyPresentedInfiniteSimpleStatement` over its open leaves

The manuscript's Fournier-Facio paragraph (`non_mf_groups_exist.tex`, line 1679) takes "a subgroup
`J ≤ G_0` isomorphic to a finitely presented infinite simple group".  The consumers in `Manuscript/NonMF`
take it as `hW : FinitelyPresentedInfiniteSimpleStatement`, witnessed by Hyde–Lodha's `Q₂ = [Γ₂, Γ₂]`.

This module is the single integration point for `hW`.  `FinitelyPresentedInfiniteSimpleLeaves` is exactly
the conjunction of the hypotheses still open on `main`, and `finitelyPresentedInfiniteSimpleStatement_of_leaves`
gives `hW` from it, so the top endpoints consume one stable name while the leaves are discharged.

Closed inputs: simplicity (`isSimpleGroup_qTwo_closed`), torsion-freeness (`qTwo_torsionFree`), infinitude
(`infinite_qTwo`), Theorem 4.8's Brown criterion and its triangle count (`vertexHTriangle`), and
Proposition 4.7 from Lemma 4.6 (`isFinitelyPresented_stabK_of_upsilon`).

Open leaf:
* `UpsilonFinitelyPresented`: Hyde–Lodha, Lemma 4.6, "For all `Γ` satisfying `Q_n ≤ Γ ≤ Γ_n` and
  `I = [a, b] ⊂ ℝ` with `|I| ≤ 1`, `Υ_Γ(I)` is of type `F_∞`".
-/

namespace GroupApproximation
namespace HydeLodha

open Manuscript.NonMF.TorsionFreePrinted

/-- **The open leaves of `FinitelyPresentedInfiniteSimpleStatement`**: Hyde–Lodha, Lemma 4.6. -/
def FinitelyPresentedInfiniteSimpleLeaves : Prop :=
  UpsilonFinitelyPresented

/-- **A finitely presented torsion-free infinite simple group, from the open leaves.** -/
theorem finitelyPresentedInfiniteSimpleStatement_of_leaves
    (hL : FinitelyPresentedInfiniteSimpleLeaves) : FinitelyPresentedInfiniteSimpleStatement :=
  finitelyPresentedInfiniteSimpleStatement_of_stabK fun _ hKfin hKne hKgrid =>
    isFinitelyPresented_stabK_of_upsilon hL le_rfl qTwo_le_gammaTwo hKfin hKne hKgrid

#audit_axioms GroupApproximation.HydeLodha.finitelyPresentedInfiniteSimpleStatement_of_leaves

end HydeLodha
end GroupApproximation
