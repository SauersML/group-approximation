import GroupApproximation.GGT.VanKampen.PermOrbitSum
import GroupApproximation.GGT.VanKampen.CactusTopology
import GroupApproximation.Meta.AxiomGuard

/-!
# Cutting one finite cycle into two

Swapping the successors at the starts of two nonempty consecutive blocks
turns the long rotation into the two separate block rotations. The actual
conjugation and the resulting two-orbit count are proved here. This is the
local face calculation for an edge inserted across a face.
-/

namespace GroupApproximation.GGT.VanKampen.FiniteCycleSplit

open Equiv

theorem rotate_val {n : ℕ} (i : Fin n) :
    (finRotate n i).val = if i.val + 1 = n then 0 else i.val + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  rw [coe_finRotate]
  by_cases hi : i = Fin.last m
  · simp only [hi, Fin.val_last]
  · have hlt := Fin.val_lt_last hi
    rw [if_neg hi, if_neg (by omega)]

def cut (k l : ℕ) (hk : 0 < k) (hl : 0 < l) : Perm (Fin (k + l)) :=
  Equiv.swap ⟨0, by omega⟩ ⟨k, by omega⟩ * finRotate (k + l)

theorem cut_left {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (i : Fin k) :
    cut k l hk hl (Fin.castAdd l i) = Fin.castAdd l (finRotate k i) := by
  have hi := i.isLt
  have hr : (finRotate (k + l) (Fin.castAdd l i)).val = i.val + 1 := by
    rw [rotate_val]
    change (if i.val + 1 = k + l then 0 else i.val + 1) = _
    rw [if_neg (by omega)]
  rw [cut, Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs with hzero hpivot
  · have hv := congrArg Fin.val hzero
    rw [hr] at hv
    change i.val + 1 = 0 at hv
    omega
  · have hv := congrArg Fin.val hpivot
    rw [hr] at hv
    change i.val + 1 = k at hv
    apply Fin.ext
    change 0 = (finRotate k i).val
    rw [rotate_val, if_pos hv]
  · have hnot : i.val + 1 ≠ k := by
      intro heq
      apply hpivot
      apply Fin.ext
      exact hr.trans heq
    apply Fin.ext
    change (finRotate (k + l) (Fin.castAdd l i)).val = (finRotate k i).val
    rw [hr, rotate_val, if_neg hnot]

theorem cut_right {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (i : Fin l) :
    cut k l hk hl (Fin.natAdd k i) = Fin.natAdd k (finRotate l i) := by
  have hi := i.isLt
  by_cases hlast : i.val + 1 = l
  · have hr : finRotate (k + l) (Fin.natAdd k i) = (⟨0, by omega⟩ : Fin (k + l)) := by
      apply Fin.ext
      rw [rotate_val]
      change (if k + i.val + 1 = k + l then 0 else k + i.val + 1) = 0
      rw [if_pos (by omega)]
    rw [cut, Perm.mul_apply, hr, Equiv.swap_apply_left]
    apply Fin.ext
    change k = k + (finRotate l i).val
    rw [rotate_val, if_pos hlast, Nat.add_zero]
  · have hr : (finRotate (k + l) (Fin.natAdd k i)).val = k + i.val + 1 := by
      rw [rotate_val]
      change (if k + i.val + 1 = k + l then 0 else k + i.val + 1) = _
      rw [if_neg (by omega)]
    rw [cut, Perm.mul_apply, Equiv.swap_apply_def]
    split_ifs with hzero hpivot
    · have hv := congrArg Fin.val hzero
      rw [hr] at hv
      change k + i.val + 1 = 0 at hv
      omega
    · have hv := congrArg Fin.val hpivot
      rw [hr] at hv
      change k + i.val + 1 = k at hv
      omega
    · apply Fin.ext
      change (finRotate (k + l) (Fin.natAdd k i)).val = k + (finRotate l i).val
      rw [hr, rotate_val, if_neg hlast]
      omega

/-- The cut rotation is exactly the two block rotations in consecutive
coordinates, including blocks of length one. -/
theorem cut_eq (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    cut k l hk hl = (finSumFinEquiv : Fin k ⊕ Fin l ≃ Fin (k + l)).permCongr
      (Equiv.sumCongr (finRotate k) (finRotate l)) := by
  apply Equiv.ext
  intro z
  obtain ⟨x, rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin l ≃ Fin (k + l)).surjective z
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  cases x with
  | inl i => exact cut_left hk hl i
  | inr i => exact cut_right hk hl i

theorem orbit_card_cut (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    Nat.card (CombMap.Orbit (cut k l hk hl)) = 2 := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  letI : Nonempty (Fin l) := Fin.pos_iff_nonempty.mp hl
  rw [cut_eq]
  let e := (orbitPermCongr (finSumFinEquiv : Fin k ⊕ Fin l ≃ Fin (k + l))
    (Equiv.sumCongr (finRotate k) (finRotate l))).symm.trans
      ((orbitSumCongr (finRotate k) (finRotate l)).trans
        (Equiv.sumCongr (orbitEquivPUnit (finRotate k) (CactusShape.finRotate_sameCycle hk))
          (orbitEquivPUnit (finRotate l) (CactusShape.finRotate_sameCycle hl))))
  have h := Nat.card_congr e
  simpa using h

end GroupApproximation.GGT.VanKampen.FiniteCycleSplit

#audit_axioms GroupApproximation.GGT.VanKampen.FiniteCycleSplit.cut_eq
#audit_axioms GroupApproximation.GGT.VanKampen.FiniteCycleSplit.orbit_card_cut
