import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFrame.UnitAlgebra
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFrame.Coordinate
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFrame.Comb
import Mathlib.GroupTheory.Perm.Fin
import GroupApproximation.Meta.AxiomGuard

/-!
# Frame cone: the scalar core completion

Khanh (arXiv:2609.08428), proof of Prop. `prop:frame-cone`:

> For `i ∈ E`, `f_i = (w_i, σ_i)` is a basis; let `ρ_i` be the coordinate onto `σ_i`, …
> put `y_i = ρ_i v`, `b_i = η_i^*`. Then `b_iy_i = 1` … so `(v, w_i)` is a frame.

Scalarized through the left-comb leaves `d_j = s_{1^j0}`, `d_3 = s_{111}` of `A ≅ A^4`, in the
frame basis (`f` is the standard frame `d_0, …, d_{k-1}`), the statement becomes `cone_core`:
if `k ≤ 2`, `η ≠ []` and `η^* t_{1^k} p = 1`, then some unit `W` sends `d_0 ↦ p` and
`d_{j+1} ↦ d_j` for `j < k`. The unit is `W = T · Ẑ · P`:

* `P` permutes the leaves by `π = (cycleRange k)⁻¹`: `d_0 ↦ d_k = σ s_0`, `d_{j+1} ↦ d_j`;
* `Ẑ` is the corner unit on `σ A` (`σ = s_{1^k}`, `ρ = t_{1^k}`) of the coordinate unit `Z`
  with `Z s_0 = ρ p` (`exists_coordinate_unit`), fixing `ker ρ ∋ d_j` (`j < k`);
* `T = 1 + (1 - σρ) p η^* ρ` sends `σ ρ p ↦ p` and fixes `ker ρ`.
-/

namespace GroupApproximation.Full.LVFrame


variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- The left-comb matrix family of rank four. -/
def combFamily : CompleteMatrixFamily A (Fin 4) :=
  L.prefixMatrixFamily (leftCombCode 3) (L.leftCombCode_complete 3)

#audit_axioms GroupApproximation.Full.LVFrame.combFamily

theorem combFamily_left (j : Fin 4) : (combFamily L).left j = L.wordS (leftCombWord 3 j) := rfl

#audit_axioms GroupApproximation.Full.LVFrame.combFamily_left

theorem combFamily_right (j : Fin 4) :
    (combFamily L).right j = L.wordT (leftCombWord 3 j) := rfl

#audit_axioms GroupApproximation.Full.LVFrame.combFamily_right

theorem combPerm_left (π : Equiv.Perm (Fin 4)) (j : Fin 4) :
    (permUnit (combFamily L) π : A) * L.wordS (leftCombWord 3 j) =
      L.wordS (leftCombWord 3 (π j)) :=
  permUnit_mul_left (combFamily L) π j

#audit_axioms GroupApproximation.Full.LVFrame.combPerm_left

theorem cycleRange_symm_succ_of_lt (k j : ℕ) (hk : k ≤ 2) (hj : j < k) :
    (Fin.cycleRange (⟨k, by omega⟩ : Fin 4)).symm ⟨j + 1, by omega⟩ = ⟨j, by omega⟩ :=
  (Equiv.symm_apply_eq _).mpr
    (Fin.ext (Fin.coe_cycleRange_of_lt (Fin.mk_lt_mk.mpr hj : (⟨j, by omega⟩ : Fin 4) <
      ⟨k, by omega⟩)).symm)

#audit_axioms
  GroupApproximation.Full.LVFrame.cycleRange_symm_succ_of_lt

/-- **Core completion.** For `k ≤ 2`, a nonempty word `η` and `p` with `η^* t_{1^k} p = 1`,
there is a unit `W` with `W d_0 = p` and `W d_{j+1} = d_j` for `j < k`. -/
theorem cone_core (k : ℕ) (hk : k ≤ 2) (η : List (Fin 2)) (hη : η ≠ []) (p : A)
    (hp : L.wordT η * (L.wordT (List.replicate k 1) * p) = 1) :
    ∃ W : Aˣ, (W : A) * L.wordS (leftCombWord 3 0) = p ∧
      ∀ (j : ℕ) (hj : j < k),
        (W : A) * L.wordS (leftCombWord 3 ⟨j + 1, by omega⟩) =
          L.wordS (leftCombWord 3 ⟨j, by omega⟩) := by
  have hρσ : L.wordT (List.replicate k 1) * L.wordS (List.replicate k 1) = 1 :=
    L.wordT_mul_wordS_self _
  obtain ⟨Z, hZ⟩ := exists_coordinate_unit L η hη hp
  refine ⟨shearUnit (cone_shear_orth hρσ (L.wordT η) p) * cornerUnit hρσ Z *
    permUnit (combFamily L) (Fin.cycleRange (⟨k, by omega⟩ : Fin 4)).symm, ?_, ?_⟩
  · simp only [Units.val_mul, mul_assoc]
    rw [combPerm_left, Fin.cycleRange_symm_zero, comb_left_self L k hk,
      cornerUnit_mul_sigma, hZ, cone_shear_sigma hρσ (L.wordT η) p hp]
  · intro j hj
    simp only [Units.val_mul, mul_assoc]
    rw [combPerm_left, cycleRange_symm_succ_of_lt k j hk hj,
      cornerUnit_mul_of_rho hρσ Z (comb_rho_left L k hk ⟨j, by omega⟩ hj),
      cone_shear_of_rho hρσ (L.wordT η) p (comb_rho_left L k hk ⟨j, by omega⟩ hj)]

#audit_axioms GroupApproximation.Full.LVFrame.cone_core

end GroupApproximation.Full.LVFrame
