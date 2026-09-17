import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Conjugating column and row vectors by one padded root (lane sk-leavitt-02)

Let `z = x_{castSucc i, castSucc j}(c)` with `i ≠ j`.  Then

* `z · colVec a · z⁻¹ = colVec (a + Function.update 0 i (c * a j))`, which is `(1 + c E_ij) *ᵥ a`;
* `z · rowVec b · z⁻¹ = rowVec (b + Function.update 0 j (b i * -c))`, which is
  `b ᵥ* (1 + (-c) E_ij)`.

The proof splits off the coordinate that `z` does not commute with (`colVec_split`), uses the
adjacent-root commutator relation on that factor, and uses `x_commute_of_ne` on the rest
(`RowColumn.conj_split`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open SteinbergGroup RowColumn
open scoped commutatorElement

variable {n : ℕ} {R : Type*} [Ring R]

theorem x_conj_colVec (i j : Fin n) (hij : i ≠ j) (c : R) (a : Fin n → R) :
    x i.castSucc j.castSucc (fun h ↦ hij (Fin.castSucc_inj.mp h)) c * colVec a *
        (x i.castSucc j.castSucc (fun h ↦ hij (Fin.castSucc_inj.mp h)) c)⁻¹ =
      colVec (a + Function.update (0 : Fin n → R) i (c * a j)) := by
  have hz : i.castSucc ≠ j.castSucc := fun h ↦ hij (Fin.castSucc_inj.mp h)
  have hcomm : Commute (x i.castSucc j.castSucc hz c) (colVec (Function.update a j 0)) := by
    apply colVec_commute
    intro k
    by_cases hk : k = j
    · rw [hk, Function.update_self, colRoot_zero]
      exact Commute.one_right _
    · rw [Function.update_of_ne hk]
      exact x_commute_of_ne i.castSucc j.castSucc k.castSucc (Fin.last n) hz
        (Fin.castSucc_ne_last k) (fun h ↦ hk (Fin.castSucc_inj.mp h).symm)
        (Fin.castSucc_ne_last i).symm c (a k)
  have hc : ⁅x i.castSucc j.castSucc hz c, colRoot j (a j)⁆ = colRoot i (c * a j) :=
    x_commutator i.castSucc j.castSucc (Fin.last n) hz (Fin.castSucc_ne_last j)
      (Fin.castSucc_ne_last i) c (a j)
  have hconj :
    x i.castSucc j.castSucc hz c * colRoot j (a j) * (x i.castSucc j.castSucc hz c)⁻¹ =
      colRoot i (c * a j) * colRoot j (a j) := by
    rw [← hc, commutatorElement_def, inv_mul_cancel_right]
  rw [conj_split _ _ _ _ _ (colVec_split a j) hconj hcomm, add_comm a, colVec_add,
    colVec_update_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.x_conj_colVec

theorem x_conj_rowVec (i j : Fin n) (hij : i ≠ j) (c : R) (b : Fin n → R) :
    x i.castSucc j.castSucc (fun h ↦ hij (Fin.castSucc_inj.mp h)) c * rowVec b *
        (x i.castSucc j.castSucc (fun h ↦ hij (Fin.castSucc_inj.mp h)) c)⁻¹ =
      rowVec (b + Function.update (0 : Fin n → R) j (b i * -c)) := by
  have hz : i.castSucc ≠ j.castSucc := fun h ↦ hij (Fin.castSucc_inj.mp h)
  have hcomm : Commute (x i.castSucc j.castSucc hz c) (rowVec (Function.update b i 0)) := by
    apply rowVec_commute
    intro k
    by_cases hk : k = i
    · rw [hk, Function.update_self, rowRoot_zero]
      exact Commute.one_right _
    · rw [Function.update_of_ne hk]
      exact x_commute_of_ne i.castSucc j.castSucc (Fin.last n) k.castSucc hz
        (Fin.castSucc_ne_last k).symm (Fin.castSucc_ne_last j)
        (fun h ↦ hk (Fin.castSucc_inj.mp h)) c (b k)
  have hc : ⁅rowRoot i (b i), x i.castSucc j.castSucc hz c⁆ = rowRoot j (b i * c) :=
    x_commutator (Fin.last n) i.castSucc j.castSucc (Fin.castSucc_ne_last i).symm hz
      (Fin.castSucc_ne_last j).symm (b i) c
  have hneg : rowRoot j (b i * -c) = (rowRoot j (b i * c))⁻¹ := by
    rw [mul_neg]
    exact x_neg _ _ _ _
  have hconj :
    x i.castSucc j.castSucc hz c * rowRoot i (b i) * (x i.castSucc j.castSucc hz c)⁻¹ =
      rowRoot j (b i * -c) * rowRoot i (b i) := by
    rw [hneg, ← hc, commutatorElement_def]
    group
  rw [conj_split _ _ _ _ _ (rowVec_split b i) hconj hcomm, add_comm b, rowVec_add,
    rowVec_update_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.x_conj_rowVec

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
