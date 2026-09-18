import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVAssembly.Retraction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVAssembly.WeylBraid

/-!
# Characteristic two and Brown's triangle relation (glue for `K₂(4, L) = ⊥`)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735.  This is part of the proof of
Khanh (arXiv:2609.08428), Thm 5.1.  Let `σ : J → St_4(L)` lift the roots (`LiftsRoots`).

* `two_eq_zero_binL`: `L = L_{𝔽₂}(1,2)` has characteristic two.
* `swapMid_eq`: `h = (1 + E₂₁)(1 + E₁₂)(1 + E₂₁)` is a product of root matrices in `J`.
* `sigma_swapMid`: `σ(h) = w₂₁`.
* `triangleRelation_of_liftsRoots`: `w₃₂ σ(h) w₃₂ = σ(h) w₃₂ σ(h)`, which is the braid relation
  `weyl_braid`.

This ports the unwired foreign draft `LeavittK2/EdgeTriangleLift/Triangle.lean`.
-/

namespace GroupApproximation.Full.LVAssembly

open GroupApproximation.SteinbergGroup

/-- **`L = L_{𝔽₂}(1,2)` has characteristic two** (tex l.733-735). -/
theorem two_eq_zero_binL : (2 : BinL) = 0 := by
  have h : (1 + 1 : ZMod 2) = 0 := by decide
  have h2 := congrArg (algebraMap (ZMod 2) BinL) h
  rw [map_add, map_one, map_zero, one_add_one_eq_two] at h2
  exact h2

/-- `h = swapMid` is a product of three elementary matrices. -/
theorem swapMid_eq :
    swapMid = GroupApproximation.elementaryUnit (2 : Fin 4) 1 midIdx_ne (1 : BinL) *
      GroupApproximation.elementaryUnit (1 : Fin 4) 2 midIdx_ne.symm (1 : BinL) *
      GroupApproximation.elementaryUnit (2 : Fin 4) 1 midIdx_ne (1 : BinL) := by
  simp only [swapMid, GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl, map_mul,
    Subgroup.coe_mul, projection_x, elementaryRoot_val]

/-- **A root lift sends `h` to `w₂₁`** (Khanh, Thm 5.1). -/
theorem sigma_swapMid (σ : vertexStab →* GroupApproximation.SteinbergGroup (Fin 4) BinL)
    (hσ : LiftsRoots σ) (j : vertexStab) (hj : (j : GLFour) = swapMid) :
    σ j = GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl (R := BinL)
      (2 : Fin 4) 1 midIdx_ne := by
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have hA := elementaryUnit_mem_vertexStab (2 : Fin 4) 1 midIdx_ne h13 (1 : BinL)
  have hB := elementaryUnit_mem_vertexStab (1 : Fin 4) 2 midIdx_ne.symm h23 (1 : BinL)
  have hj' : j =
      (⟨GroupApproximation.elementaryUnit (2 : Fin 4) 1 midIdx_ne (1 : BinL), hA⟩ :
        vertexStab) *
      ⟨GroupApproximation.elementaryUnit (1 : Fin 4) 2 midIdx_ne.symm (1 : BinL), hB⟩ *
      ⟨GroupApproximation.elementaryUnit (2 : Fin 4) 1 midIdx_ne (1 : BinL), hA⟩ :=
    Subtype.ext (hj.trans swapMid_eq)
  rw [hj', map_mul, map_mul, hσ (2 : Fin 4) 1 midIdx_ne h13 (1 : BinL),
    hσ (1 : Fin 4) 2 midIdx_ne.symm h23 (1 : BinL)]
  rfl

/-- **Brown's triangle relation for a root lift**, with `T = w₃₂` (Khanh, Thm 5.1;
tex l.733-735). -/
theorem triangleRelation_of_liftsRoots
    (σ : vertexStab →* GroupApproximation.SteinbergGroup (Fin 4) BinL) (hσ : LiftsRoots σ) :
    TriangleRelation σ weylLast := by
  intro j hj
  rw [sigma_swapMid σ hσ j hj]
  exact weyl_braid (n := 4) two_eq_zero_binL (by decide) lastIdx_ne midIdx_ne
    (show (3 : Fin 4) ≠ 1 by decide)

end GroupApproximation.Full.LVAssembly
