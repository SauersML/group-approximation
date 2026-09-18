import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Frame.Stab
import Mathlib.Data.Fin.SuccPred
import Mathlib.Algebra.Group.End
import GroupApproximation.Meta.AxiomGuard

/-!
# The swap `h ∈ J` and the braid relation `τ h τ = h τ h`

Lane `sk-leavitt-07` (carto `sk-leavitt`).  Khanh (arXiv:2609.08428v1), proof of Theorem 5.1:
`h ∈ J` with `(v_0, v_1, h v_1)` a triangle, and the relation `T h T = h T h`.

Last-index convention in `A^{m+3}`: `v_0 = e_last`, `v_1 = e_{cs last}`, `h v_1 = e_{cs cs last}`.

* `frameHSwap A m`: the permutation unit of `swap(cs last, cs cs last)`.
* `frameHSwap_mem_frameVertexStab`: `h ∈ J`.
* `frameHSwap_smul_castSucc`, `frameHSwap_smul_castSucc_castSucc`, `frameHSwap_mul_self`.
* `frameTau_frameHSwap_braid`: `τ h τ = h τ h` (with `τ = frameTau A (m + 1)`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

variable {A : Type*} [Ring A] {m : ℕ}

/-- `h`: the permutation unit exchanging `e_{cs last}` and `e_{cs cs last}` in `A^{m+3}`. -/
def frameHSwap (A : Type*) [Ring A] (m : ℕ) :
    (Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) A)ˣ :=
  framePermUnit (Equiv.swap (Fin.castSucc (Fin.last (m + 1)))
    (Fin.castSucc (Fin.castSucc (Fin.last m))))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameHSwap

theorem frameHSwap_smul_last :
    frameHSwap A m • (Pi.single (Fin.last (m + 1 + 1)) 1 : Fin (m + 1 + 1 + 1) → A) =
      Pi.single (Fin.last (m + 1 + 1)) 1 := by
  rw [frameHSwap, framePermUnit_smul_single, Equiv.symm_swap,
    Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_ne_last _).symm (Fin.castSucc_ne_last _).symm]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameHSwap_smul_last

/-- `h ∈ J`. -/
theorem frameHSwap_mem_frameVertexStab : frameHSwap A m ∈ frameVertexStab A (m + 1 + 1) :=
  frameHSwap_smul_last

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameHSwap_mem_frameVertexStab

theorem frameHSwap_smul_castSucc :
    frameHSwap A m • (Pi.single (Fin.castSucc (Fin.last (m + 1))) 1 : Fin (m + 1 + 1 + 1) → A) =
      Pi.single (Fin.castSucc (Fin.castSucc (Fin.last m))) 1 := by
  rw [frameHSwap, framePermUnit_smul_single, Equiv.symm_swap, Equiv.swap_apply_left]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameHSwap_smul_castSucc

theorem frameHSwap_smul_castSucc_castSucc :
    frameHSwap A m •
        (Pi.single (Fin.castSucc (Fin.castSucc (Fin.last m))) 1 : Fin (m + 1 + 1 + 1) → A) =
      Pi.single (Fin.castSucc (Fin.last (m + 1))) 1 := by
  rw [frameHSwap, framePermUnit_smul_single, Equiv.symm_swap, Equiv.swap_apply_right]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameHSwap_smul_castSucc_castSucc

theorem frameHSwap_mul_self : frameHSwap A m * frameHSwap A m = 1 :=
  framePermUnit_mul_self_of_mul_self (Equiv.swap_mul_self _ _)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameHSwap_mul_self

/-- The braid relation for transpositions sharing one point. -/
theorem perm_swap_braid {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    Equiv.swap a b * (Equiv.swap b c * Equiv.swap a b) =
      Equiv.swap b c * (Equiv.swap a b * Equiv.swap b c) := by
  calc Equiv.swap a b * (Equiv.swap b c * Equiv.swap a b)
        = Equiv.swap b a * Equiv.swap c b * Equiv.swap b a := by
          rw [← mul_assoc, Equiv.swap_comm a b, Equiv.swap_comm b c]
    _ = Equiv.swap a c := Equiv.swap_mul_swap_mul_swap hbc.symm hac.symm
    _ = Equiv.swap c a := Equiv.swap_comm a c
    _ = Equiv.swap b c * Equiv.swap a b * Equiv.swap b c :=
          (Equiv.swap_mul_swap_mul_swap hab hac).symm
    _ = Equiv.swap b c * (Equiv.swap a b * Equiv.swap b c) := mul_assoc _ _ _

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.perm_swap_braid

/-- The braid relation `τ h τ = h τ h`. -/
theorem frameTau_frameHSwap_braid :
    frameTau A (m + 1) * frameHSwap A m * frameTau A (m + 1) =
      frameHSwap A m * frameTau A (m + 1) * frameHSwap A m := by
  have hab : Fin.last (m + 1 + 1) ≠ Fin.castSucc (Fin.last (m + 1)) :=
    (Fin.castSucc_ne_last _).symm
  have hac : Fin.last (m + 1 + 1) ≠ Fin.castSucc (Fin.castSucc (Fin.last m)) :=
    (Fin.castSucc_ne_last _).symm
  have hbc : Fin.castSucc (Fin.last (m + 1)) ≠ Fin.castSucc (Fin.castSucc (Fin.last m)) :=
    (Fin.castSucc_injective _).ne (Fin.castSucc_ne_last _).symm
  rw [frameTau, frameHSwap, ← framePermUnit_mul, ← framePermUnit_mul, ← framePermUnit_mul,
    ← framePermUnit_mul, perm_swap_braid hab hac hbc]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTau_frameHSwap_braid

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
