import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitelyPresented
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
(`infinite_qTwo`), Theorem 4.8's Brown criterion and its triangle count (`vertexHTriangle`).

Open leaf:
* `StabKFinitelyPresented qTwo`: Hyde–Lodha, Proposition 4.7, "For `Γ` so that `Q_n ≤ Γ ≤ Γ_n` and every
  nonempty finite set `K ⊂ ℤ[1/η_n]`, `Γ_K = Γ_{K+ℤ}` is of type `F_∞`", at `Γ = Q₂`.
-/

namespace GroupApproximation
namespace HydeLodha

open Manuscript.NonMF.TorsionFreePrinted

/-- **The open leaves of `FinitelyPresentedInfiniteSimpleStatement`**: Hyde–Lodha, Proposition 4.7, at
`Γ = Q₂`. -/
def FinitelyPresentedInfiniteSimpleLeaves : Prop :=
  StabKFinitelyPresented qTwo

/-- **A finitely presented torsion-free infinite simple group, from the open leaves.** -/
theorem finitelyPresentedInfiniteSimpleStatement_of_leaves
    (hL : FinitelyPresentedInfiniteSimpleLeaves) : FinitelyPresentedInfiniteSimpleStatement :=
  finitelyPresentedInfiniteSimpleStatement_of_stabK hL

#audit_axioms GroupApproximation.HydeLodha.finitelyPresentedInfiniteSimpleStatement_of_leaves

end HydeLodha
end GroupApproximation
