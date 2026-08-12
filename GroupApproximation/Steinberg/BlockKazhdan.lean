import GroupApproximation.Steinberg.BlockA2
import GroupApproximation.Steinberg.A2Kazhdan

/-!
# Kazhdan subsets from the three-block Steinberg system

In positive characteristic, each rectangular block root is still an additive
root and therefore has bounded exponent.  The generic magic-graph theorem
then makes the union of the six block roots a Kazhdan subset.
-/

namespace GroupApproximation
namespace SteinbergBlockRoot

open SteinbergGroup

variable {R κ : Type*} [Ring R] [Fintype κ] [DecidableEq κ]

theorem rowToTail_pow (F : CompleteMatrixFamily R κ) (p : Fin 2)
    (a : R) (n : ℕ) : rowToTail F p a ^ n = rowToTail F p (n • a) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← rowToTail_add, succ_nsmul]

theorem tailToRow_pow (F : CompleteMatrixFamily R κ) (p : Fin 2)
    (a : R) (n : ℕ) : tailToRow F p a ^ n = tailToRow F p (n • a) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← tailToRow_add, succ_nsmul]

theorem rowToTail_pow_char (F : CompleteMatrixFamily R κ) (p : ℕ)
    [CharP R p] (i : Fin 2) (a : R) : rowToTail F i a ^ p = 1 := by
  rw [rowToTail_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul,
    rowToTail_zero]

theorem tailToRow_pow_char (F : CompleteMatrixFamily R κ) (p : ℕ)
    [CharP R p] (i : Fin 2) (a : R) : tailToRow F i a ^ p = 1 := by
  rw [tailToRow_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul,
    tailToRow_zero]

theorem blockRootSubgroup_pow_char (F : CompleteMatrixFamily R κ)
    (p : ℕ) [CharP R p] :
    ∀ (i j : Fin 3) (hij : i ≠ j),
      ∀ g ∈ blockRootSubgroup F i j hij, g ^ p = 1 := by
  intro i j hij g hg
  by_cases hi : i = 2
  · subst i
    have hj : j ≠ 2 := by omega
    simp [blockRootSubgroup, singletonOfNotTail] at hg
    obtain ⟨a, rfl⟩ := hg
    exact tailToRow_pow_char F p _ a
  · by_cases hj : j = 2
    · subst j
      simp [blockRootSubgroup, singletonOfNotTail, hi] at hg
      obtain ⟨a, rfl⟩ := hg
      exact rowToTail_pow_char F p _ a
    · simp [blockRootSubgroup, singletonOfNotTail, smallRootSubgroup,
        hi, hj] at hg
      obtain ⟨a, rfl⟩ := hg
      exact x_pow_char p _ _ _ a

/-- The union of the six three-block roots is a Kazhdan subset whenever the
coefficient ring has positive characteristic. -/
theorem blockA2_exists_rootSet_isKazhdan (F : CompleteMatrixFamily R κ)
    (p : ℕ) (hp : 0 < p) [CharP R p] :
    ∃ kappa : ℝ,
      IsKazhdanSubset (SteinbergGroup (Fin 2 ⊕ κ) R)
        (blockA2System F).rootSet kappa := by
  exact A2MagicHilbert.exists_rootSet_isKazhdan
    (blockA2System F) p hp (blockRootSubgroup_pow_char F p)

end SteinbergBlockRoot
end GroupApproximation
