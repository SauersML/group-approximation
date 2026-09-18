import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVAssembly.FrameAction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVEGen.GLEqElementary

/-!
# The swaps `τ`, `h` on the base frame (glue for `K₂(4, L) = ⊥`)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735.  This is part of the proof of
Khanh (arXiv:2609.08428), Thm 5.1.  These are the group-theoretic inputs of Brown's criterion
`GroupApproximation.Full.LVBrown.brown_lift` for `GL_4(L)` acting on the frame complex, with base
edge `(e₃, e₂)`, `τ = swapLast` (the image of `w₃₂`) and `h = swapMid` (the image of `w₂₁`).

* `swapLast_smul_base`, `swapLast_smul_next`: `τ e₃ = e₂` and `τ e₂ = e₃`.
* `swapMid_smul_base`: `h e₃ = e₃`.
* `swapLast_mul_self`, `swapMid_mul_self`, `swap_braid`: `τ² = 1`, `h² = 1`, `τhτ = hτh`,
  as images of the Weyl relations in `St_4(L)`.
* `stabilizer_eq_vertexStab`: the stabilizer of `e₃` is `J`.
* `closure_stabilizer_swapLast`: `J` and `τ` generate `GL_4(L)`, using `GL_4(L) = E_4(L)`
  (leaf T1a, `Full/LVEGen/GLEqElementary`).
-/

namespace GroupApproximation.Full.LVAssembly

open scoped Matrix
open GroupApproximation.Full.LVFrame

/-- `τ = swapLast` is a product of three elementary matrices. -/
theorem swapLast_eq :
    swapLast = GroupApproximation.elementaryUnit (3 : Fin 4) 2 lastIdx_ne (1 : BinL) *
      GroupApproximation.elementaryUnit (2 : Fin 4) 3 lastIdx_ne.symm (1 : BinL) *
      GroupApproximation.elementaryUnit (3 : Fin 4) 2 lastIdx_ne (1 : BinL) := by
  simp only [swapLast, weylLast_eq, map_mul, Subgroup.coe_mul,
    GroupApproximation.SteinbergGroup.projection_x, GroupApproximation.elementaryRoot_val]

/-- **`τ e₃ = e₂`** (Khanh, Thm 5.1). -/
theorem swapLast_smul_base : swapLast • baseVertex = nextVertex := by
  refine Subtype.ext ?_
  show (swapLast : Matrix (Fin 4) (Fin 4) BinL) *ᵥ Pi.single 3 1 = Pi.single 2 1
  rw [swapLast_eq, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    fix_single 3 2 lastIdx_ne (show (2 : Fin 4) ≠ 3 by decide), add_single 2 3 lastIdx_ne.symm,
    cancel_single 3 2 lastIdx_ne]

/-- **`τ e₂ = e₃`** (Khanh, Thm 5.1). -/
theorem swapLast_smul_next : swapLast • nextVertex = baseVertex := by
  refine Subtype.ext ?_
  show (swapLast : Matrix (Fin 4) (Fin 4) BinL) *ᵥ Pi.single 2 1 = Pi.single 3 1
  rw [swapLast_eq, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    add_single 3 2 lastIdx_ne, cancel_single 2 3 lastIdx_ne.symm,
    fix_single 3 2 lastIdx_ne (show (2 : Fin 4) ≠ 3 by decide)]

/-- **`h e₃ = e₃`** (Khanh, Thm 5.1). -/
theorem swapMid_smul_base : swapMid • baseVertex = baseVertex := by
  refine Subtype.ext ?_
  show (swapMid : Matrix (Fin 4) (Fin 4) BinL) *ᵥ Pi.single 3 1 = Pi.single 3 1
  rw [swapMid_eq, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    fix_single 2 1 midIdx_ne (show (1 : Fin 4) ≠ 3 by decide),
    fix_single 1 2 midIdx_ne.symm (show (2 : Fin 4) ≠ 3 by decide),
    fix_single 2 1 midIdx_ne (show (1 : Fin 4) ≠ 3 by decide)]

/-- `w₃₂² = 1` in `St_4(L)`, in characteristic two. -/
theorem weylLast_mul_self : weylLast * weylLast = 1 :=
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_mul_self (I := Fin 4)
    (R := BinL) two_eq_zero_binL (3 : Fin 4) 2 lastIdx_ne

/-- **`τ² = 1`** (Khanh, Thm 5.1). -/
theorem swapLast_mul_self : swapLast * swapLast = 1 := by
  have hc := congrArg
    (fun g => ((GroupApproximation.SteinbergGroup.projection g :
      GroupApproximation.elementaryGroup (Fin 4) BinL) : GLFour)) weylLast_mul_self
  simp only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one] at hc
  exact hc

/-- **`h² = 1`** (Khanh, Thm 5.1). -/
theorem swapMid_mul_self : swapMid * swapMid = 1 := by
  have hc := congrArg
    (fun g => ((GroupApproximation.SteinbergGroup.projection g :
      GroupApproximation.elementaryGroup (Fin 4) BinL) : GLFour))
    (GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_mul_self (I := Fin 4)
      (R := BinL) two_eq_zero_binL (2 : Fin 4) 1 midIdx_ne)
  simp only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one] at hc
  exact hc

/-- **The braid relation `τ h τ = h τ h`** (Khanh, Thm 5.1). -/
theorem swap_braid : swapLast * swapMid * swapLast = swapMid * swapLast * swapMid := by
  have hc := congrArg
    (fun g => ((GroupApproximation.SteinbergGroup.projection g :
      GroupApproximation.elementaryGroup (Fin 4) BinL) : GLFour))
    (weyl_braid (R := BinL) (n := 4) two_eq_zero_binL (by decide) lastIdx_ne midIdx_ne
      (show (3 : Fin 4) ≠ 1 by decide))
  simp only [map_mul, Subgroup.coe_mul] at hc
  exact hc

/-- **The stabilizer of the base vertex `e₃` is `J`** (Khanh, Thm 5.1). -/
theorem stabilizer_eq_vertexStab : MulAction.stabilizer GLFour baseVertex = vertexStab := by
  ext g
  rw [MulAction.mem_stabilizer_iff, mem_vertexStab]
  exact Subtype.ext_iff

/-- **`J` and `τ` generate `GL_4(L)`** (Khanh, Thm 5.1; tex l.733-735).  Every matrix is the
image of a Steinberg element (`GL_4(L) = E_4(L)`), and `St_4(L)` is generated by the roots of `J`
and `w₃₂` (`steinberg_eq_top_of_mem`). -/
theorem closure_stabilizer_swapLast :
    Subgroup.closure ((MulAction.stabilizer GLFour baseVertex : Set GLFour) ∪ {swapLast}) = ⊤ := by
  rw [stabilizer_eq_vertexStab]
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨s, rfl⟩ := GroupApproximation.Full.LVEGen.steinbergToGL_surjective (ZMod 2)
    (show 2 ≤ 4 by decide) g
  have hcomap : (Subgroup.closure ((vertexStab : Set GLFour) ∪ {swapLast})).comap
      (GroupApproximation.Full.LVEGen.steinbergToGL (ZMod 2) 4) = ⊤ := by
    refine steinberg_eq_top_of_mem _ ?_ ?_
    · intro i j hij hj a
      rw [Subgroup.mem_comap]
      show ((GroupApproximation.SteinbergGroup.projection
          (GroupApproximation.SteinbergGroup.x i j hij a) :
            GroupApproximation.elementaryGroup (Fin 4) BinL) : GLFour) ∈ _
      rw [GroupApproximation.SteinbergGroup.projection_x, GroupApproximation.elementaryRoot_val]
      exact Subgroup.subset_closure
        (Set.mem_union_left _ (elementaryUnit_mem_vertexStab i j hij hj a))
    · rw [Subgroup.mem_comap]
      exact Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton_iff.mpr rfl))
  have hs : s ∈ (Subgroup.closure ((vertexStab : Set GLFour) ∪ {swapLast})).comap
      (GroupApproximation.Full.LVEGen.steinbergToGL (ZMod 2) 4) := by
    rw [hcomap]
    exact Subgroup.mem_top s
  exact Subgroup.mem_comap.mp hs

end GroupApproximation.Full.LVAssembly
