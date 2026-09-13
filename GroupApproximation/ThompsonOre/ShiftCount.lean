import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

/-!
# The dimension count in the shift argument

There are `multichoose L n` sorted words of length `n` in `L` letters.  When `L ≤ 2c + 3`, each
extra letter multiplies this number by at most `3`.  So with `N ≥ (D + 1) 3^D`, the words of
lengths `c, …, c + D` are fewer than `N + 1` copies of the words of length `c`.  This replaces
the induction of Guba's Theorem 3 in the proof of Theorem 3.18.
-/

namespace GroupApproximation.ThompsonOre

theorem multichoose_succ_le_three_mul {L k : ℕ} (hL : 1 ≤ L) (h : L ≤ 2 * k + 3) :
    Nat.multichoose L (k + 1) ≤ 3 * Nat.multichoose L k := by
  rw [Nat.multichoose_eq, Nat.multichoose_eq]
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  rw [show n + 1 + (k + 1) - 1 = n + k + 1 by omega, show n + 1 + k - 1 = n + k by omega]
  have key := Nat.add_one_mul_choose_eq (n + k) k
  refine Nat.le_of_mul_le_mul_right (c := k + 1) ?_ (by omega)
  rw [← key]
  calc (n + k + 1) * (n + k).choose k ≤ (3 * (k + 1)) * (n + k).choose k :=
        Nat.mul_le_mul_right _ (by omega)
    _ = 3 * (n + k).choose k * (k + 1) := by ring

theorem multichoose_add_le_pow_mul {L c : ℕ} (hL : 1 ≤ L) (h : L ≤ 2 * c + 3) :
    ∀ d : ℕ, Nat.multichoose L (c + d) ≤ 3 ^ d * Nat.multichoose L c
  | 0 => by simp
  | d + 1 => by
    calc Nat.multichoose L (c + (d + 1)) = Nat.multichoose L (c + d + 1) := rfl
      _ ≤ 3 * Nat.multichoose L (c + d) := multichoose_succ_le_three_mul hL (by omega)
      _ ≤ 3 * (3 ^ d * Nat.multichoose L c) :=
        Nat.mul_le_mul_left 3 (multichoose_add_le_pow_mul hL h d)
      _ = 3 ^ (d + 1) * Nat.multichoose L c := by ring

/-- The count: words of lengths `c, …, c + D` are fewer than `N + 1` copies of words of
length `c`. -/
theorem sum_multichoose_lt {L c D N : ℕ} (hL : 1 ≤ L) (h : L ≤ 2 * c + 3)
    (hN : (D + 1) * 3 ^ D ≤ N) :
    ∑ d ∈ Finset.range (D + 1), Nat.multichoose L (c + d) < (N + 1) * Nat.multichoose L c := by
  have hpos : 0 < Nat.multichoose L c := by
    rw [Nat.multichoose_eq]; exact Nat.choose_pos (by omega)
  calc ∑ d ∈ Finset.range (D + 1), Nat.multichoose L (c + d)
      ≤ ∑ _d ∈ Finset.range (D + 1), 3 ^ D * Nat.multichoose L c := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hd' : d ≤ D := by have := Finset.mem_range.mp hd; omega
        exact (multichoose_add_le_pow_mul hL h d).trans
          (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hd'))
    _ = (D + 1) * 3 ^ D * Nat.multichoose L c := by
        rw [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, Nat.mul_assoc]
    _ < (N + 1) * Nat.multichoose L c :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_of_le hN) hpos

end GroupApproximation.ThompsonOre
