import GroupApproximation.CharClass.OddPProductAW
import GroupApproximation.CharClass.OddPDiagonalSrc
import GroupApproximation.Meta.AxiomGuard

/-!
# The degree-`0` value of the slotwise Alexander–Whitney map

`awTup_diagPt`: the constant tuple of a point goes to the constant tuple of that point, at twice
the arity.  This is its own module so that `OddPProductAW` does not import the equivariant
diagonal's source layer (`OddPDiagonalSrc`, which reaches `OddPDiagonalAug`), and so the
Alexander–Whitney layer compiles on its own.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Simplicial
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

variable (K : Type) [CommRing K] (X : TopCat.{0})

/-- **The degree-`0` value**: the constant tuple of a point goes to the constant tuple of that
point, at twice the arity. -/
theorem awTup_diagPt (r : ℕ) (x : stdSimplexTop 0 ⟶ X) :
    awTup K X r 0 (Finsupp.single (diagPt X r x) (1 : K))
      = Finsupp.single (diagPt X (2 * r) x) (1 : K) := by
  apply tupIncl_injective K X 0
  have h := LinearMap.congr_fun (tupIncl_comp_awTup K X r 0) (Finsupp.single (diagPt X r x) 1)
  simp only [LinearMap.comp_apply] at h
  rw [h, tupIncl_single, tupIncl_single, awTupAll_single]
  have hcuts : awCuts (diagPt X r x).1 = {fun _ => 0} := by
    show (Fintype.piFinset fun _ : Fin r => Finset.range (0 + 1)) = {fun _ => 0}
    rw [zero_add, Finset.range_one]
    exact Fintype.piFinset_singleton (fun _ => 0)
  rw [hcuts, Finset.sum_singleton]
  congr 1
  funext s
  simp only [awTupOf, tupInterleave]
  split_ifs
  · exact vtx_id_self _
  · exact (TopPow.vtx_congr _ _ monotone_id (by rfl) fun j _ => by simp).trans (vtx_id_self _)

#audit_axioms awTup_diagPt

end

end GroupApproximation.CharClass
