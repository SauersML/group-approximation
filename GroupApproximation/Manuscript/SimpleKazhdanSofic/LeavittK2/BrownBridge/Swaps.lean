import Mathlib.Data.Matrix.PEquiv
import GroupApproximation.Leavitt.ElementaryWeylMonomial
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.Endpoint
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Frame.Swap
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown bridge III: lane 14's Weyl swaps are lane 07's permutation units (lane sk-leavitt-20)

Lane 14 (`Criterion`) names two elements of `GL₄(L)`, `L = L₂(𝔽₂)`: `swapLast`, the image of
the Steinberg Weyl element `w₃₂`, and `swapMid`, the image of `w₂₁`.  Lane 07's Brown setting
`frameBrownSetting L 1` uses `τ = frameTau L 2` (permutation unit of `swap(3, 2)`) and
`h = frameHSwap L 1` (permutation unit of `swap(2, 1)`).

Route.
* `pequiv_single_toMatrix`: `(PEquiv.single i j).toMatrix = Matrix.single i j 1`.
* `weylUnit_val_eq_swap`: in characteristic two, `w_{uv} = 1 - E_uu - E_vv + E_uv - E_vu`
  (`ElementaryWeyl.weylUnit_val`) is Mathlib's `PEquiv.toMatrix_swap` form of the permutation
  matrix of `swap(u, v)`, since `-E_vu = E_vu`.
* `swapLast_eq_frameTau`, `swapMid_eq_frameHSwap`: lane 06's `projection_weyl` and lane 06's
  `swapMid_eq` identify the two swaps with Weyl units; `Units.ext` finishes.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Criterion

theorem pequiv_single_toMatrix {ι S : Type*} [DecidableEq ι] [Ring S] (i j : ι) :
    ((PEquiv.single i j).toMatrix : Matrix ι ι S) = Matrix.single i j 1 := by
  ext r s
  simp only [PEquiv.toMatrix_apply, Matrix.single_apply, PEquiv.mem_single_iff]
  exact if_congr ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩ rfl rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.pequiv_single_toMatrix

/-- In characteristic two the Weyl unit `w_{uv}` is the permutation matrix of `swap(u, v)`. -/
theorem weylUnit_val_eq_swap {ι S : Type*} [Fintype ι] [DecidableEq ι] [Ring S]
    (h2 : (2 : S) = 0) (u v : ι) (huv : u ≠ v) :
    (ElementaryWeyl.weylUnit (S := S) u v huv : Matrix ι ι S) =
      (Equiv.swap u v).toPEquiv.toMatrix := by
  have hn : -Matrix.single v u (1 : S) = Matrix.single v u 1 := by
    rw [Matrix.single_neg, WeylCalc.neg_self_of_two_eq_zero h2]
  rw [ElementaryWeyl.weylUnit_val, PEquiv.toMatrix_swap, pequiv_single_toMatrix,
    pequiv_single_toMatrix, pequiv_single_toMatrix, pequiv_single_toMatrix,
    sub_eq_add_neg _ (Matrix.single v u (1 : S)), hn]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.weylUnit_val_eq_swap

/-- Lane 14's `swapLast` is lane 07's `τ` for `GL₄(L)`. -/
theorem swapLast_eq_frameTau : swapLast = frameTau BinL (1 + 1) := by
  have h : swapLast = ElementaryWeyl.weylUnit (S := BinL) (3 : Fin 4) 2 lastIdx_ne :=
    EdgeTriangleLift.projection_weyl
  rw [h]
  exact Units.ext (weylUnit_val_eq_swap EdgeTriangleLift.two_eq_zero_binL 3 2 lastIdx_ne)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.swapLast_eq_frameTau

/-- Lane 14's `swapMid` is lane 07's `h` for `GL₄(L)`. -/
theorem swapMid_eq_frameHSwap : swapMid = frameHSwap BinL 1 := by
  have hw : swapMid = ElementaryWeyl.weylUnit (S := BinL) (2 : Fin 4) 1 midIdx_ne := by
    rw [EdgeTriangleLift.swapMid_eq, ElementaryWeyl.weylUnit,
      WeylCalc.neg_self_of_two_eq_zero EdgeTriangleLift.two_eq_zero_binL]
  rw [hw]
  exact Units.ext (weylUnit_val_eq_swap EdgeTriangleLift.two_eq_zero_binL 2 1 midIdx_ne)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.swapMid_eq_frameHSwap

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge
