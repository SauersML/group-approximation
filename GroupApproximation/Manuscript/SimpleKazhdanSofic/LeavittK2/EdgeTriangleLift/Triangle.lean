import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.EdgeConj
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Weyl.Braid
import GroupApproximation.Meta.AxiomGuard

/-!
# Edge and triangle lifts V: the triangle relation (lane sk-leavitt-13)

Khanh (arXiv:2609.08428), proof of Theorem 5.1.  Let `σ : J → St_4(L)` lift the roots
(`Criterion.LiftsRoots`).  Brown's triangle relation `T σ(h) T = σ(h) T σ(h)`, with
`h = swapMid = 1 + E₂₁ · 1 + E₁₂ · 1 + E₂₁` and `T = w₃₂`, holds as follows.

* `h` is a product of three root matrices in `J`, so `σ(h) = x₂₁(1) x₁₂(1) x₂₁(1) = w₂₁`
  (`sigma_swapMid`).
* The relation is then the braid relation `w₃₂ w₂₁ w₃₂ = w₂₁ w₃₂ w₂₁` (lane 01, `weyl_braid`,
  characteristic two).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Criterion

/-- `h = swapMid` is the product of three elementary matrices. -/
theorem swapMid_eq :
    swapMid = GroupApproximation.elementaryUnit (2 : Fin 4) 1 midIdx_ne (1 : BinL) *
      GroupApproximation.elementaryUnit (1 : Fin 4) 2 midIdx_ne.symm (1 : BinL) *
      GroupApproximation.elementaryUnit (2 : Fin 4) 1 midIdx_ne (1 : BinL) := by
  simp only [swapMid, LeavittK2.weyl, map_mul, Subgroup.coe_mul, projection_x, elementaryRoot_val]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.swapMid_eq

/-- **A root lift sends `h` to `w₂₁`.** -/
theorem sigma_swapMid (σ : vertexStab →* St 4 BinL) (hσ : LiftsRoots σ) (j : vertexStab)
    (hj : (j : GLFour) = swapMid) :
    σ j = LeavittK2.weyl (R := BinL) (2 : Fin 4) 1 midIdx_ne := by
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have hA := elementaryUnit_mem_vertexStab (2 : Fin 4) 1 midIdx_ne h13 (1 : BinL)
  have hB := elementaryUnit_mem_vertexStab (1 : Fin 4) 2 midIdx_ne.symm h23 (1 : BinL)
  have hj' : j = (⟨GroupApproximation.elementaryUnit (2 : Fin 4) 1 midIdx_ne (1 : BinL), hA⟩ :
      vertexStab) * ⟨GroupApproximation.elementaryUnit (1 : Fin 4) 2 midIdx_ne.symm (1 : BinL), hB⟩ *
      ⟨GroupApproximation.elementaryUnit (2 : Fin 4) 1 midIdx_ne (1 : BinL), hA⟩ :=
    Subtype.ext (hj.trans swapMid_eq)
  rw [hj', map_mul, map_mul, hσ (2 : Fin 4) 1 midIdx_ne h13 (1 : BinL),
    hσ (1 : Fin 4) 2 midIdx_ne.symm h23 (1 : BinL)]
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.sigma_swapMid

/-- **Brown's triangle relation for a root lift** (`T = w₃₂`). -/
theorem triangleRelation_of_liftsRoots (σ : vertexStab →* St 4 BinL) (hσ : LiftsRoots σ) :
    TriangleRelation σ weylLast := by
  intro j hj
  rw [sigma_swapMid σ hσ j hj]
  exact weyl_braid (n := 4) two_eq_zero_binL (by decide) lastIdx_ne midIdx_ne
    (show (3 : Fin 4) ≠ 1 by decide)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.triangleRelation_of_liftsRoots

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift
