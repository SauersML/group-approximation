import GroupApproximation.Matching.FinitePartialBijection
import Mathlib.Data.Fintype.Sum

/-!
# Encoding a partial bijection by an involution

A partial bijection between finite models is the same data as an involution
of their disjoint union which swaps every matched pair and fixes every
unmatched point.  This converts partial-arrow composition questions into
ordinary finite permutation questions.
-/

namespace GroupApproximation
namespace FinitePartialBijection

variable {Y Z W : FiniteModel}

/-- Disjoint union of two finite models. -/
abbrev sumModel (Y Z : FiniteModel) : FiniteModel where
  carrier := Y ⊕ Z
  fintype := by
    letI : Fintype Y.carrier := Y.fintype
    letI : Fintype Z.carrier := Z.fintype
    exact inferInstance
  decidableEq := by
    letI : DecidableEq Y.carrier := Y.decidableEq
    letI : DecidableEq Z.carrier := Z.decidableEq
    exact inferInstance

/-- The involution which swaps the graph pairs of `b` and fixes all
unmatched points. -/
def swapPerm (b : FinitePartialBijection Y Z) :
    Equiv.Perm (sumModel Y Z) where
  toFun
    | Sum.inl y => if hy : y ∈ b.source then Sum.inr (b.apply y hy) else Sum.inl y
    | Sum.inr z => if hz : z ∈ b.target then Sum.inl (b.symm.apply z hz) else Sum.inr z
  invFun
    | Sum.inl y => if hy : y ∈ b.source then Sum.inr (b.apply y hy) else Sum.inl y
    | Sum.inr z => if hz : z ∈ b.target then Sum.inl (b.symm.apply z hz) else Sum.inr z
  left_inv := by
    intro x
    cases x with
    | inl y =>
        by_cases hy : y ∈ b.source
        · simp only [hy, dite_true]
          rw [dif_pos (b.apply_mem_target y hy)]
          simp
        · simp [hy]
    | inr z =>
        by_cases hz : z ∈ b.target
        · simp only [hz, dite_true]
          have hy : b.symm.apply z hz ∈ b.source :=
            b.symm.apply_mem_target z hz
          rw [dif_pos hy]
          exact congrArg Sum.inr (b.apply_symm_apply z hz)
        · simp [hz]
  right_inv := by
    intro x
    cases x with
    | inl y =>
        by_cases hy : y ∈ b.source
        · simp only [hy, dite_true]
          rw [dif_pos (b.apply_mem_target y hy)]
          simp
        · simp [hy]
    | inr z =>
        by_cases hz : z ∈ b.target
        · simp only [hz, dite_true]
          have hy : b.symm.apply z hz ∈ b.source :=
            b.symm.apply_mem_target z hz
          rw [dif_pos hy]
          exact congrArg Sum.inr (b.apply_symm_apply z hz)
        · simp [hz]

@[simp] theorem swapPerm_inl_of_mem
    (b : FinitePartialBijection Y Z) (y : Y) (hy : y ∈ b.source) :
    b.swapPerm (Sum.inl y) = Sum.inr (b.apply y hy) := by
  simp [swapPerm, hy]

@[simp] theorem swapPerm_inl_of_not_mem
    (b : FinitePartialBijection Y Z) (y : Y) (hy : y ∉ b.source) :
    b.swapPerm (Sum.inl y) = Sum.inl y := by
  simp [swapPerm, hy]

@[simp] theorem swapPerm_inr_of_mem
    (b : FinitePartialBijection Y Z) (z : Z) (hz : z ∈ b.target) :
    b.swapPerm (Sum.inr z) = Sum.inl (b.symm.apply z hz) := by
  simp [swapPerm, hz]

@[simp] theorem swapPerm_inr_of_not_mem
    (b : FinitePartialBijection Y Z) (z : Z) (hz : z ∉ b.target) :
    b.swapPerm (Sum.inr z) = Sum.inr z := by
  simp [swapPerm, hz]

@[simp] theorem swapPerm_inv_inr_of_mem
    (b : FinitePartialBijection Y Z) (z : Z) (hz : z ∈ b.target) :
    b.swapPerm⁻¹ (Sum.inr z) = Sum.inl (b.symm.apply z hz) := by
  simp [swapPerm, hz]

theorem swapPerm_mul_self (b : FinitePartialBijection Y Z) :
    b.swapPerm * b.swapPerm = 1 := by
  apply Equiv.ext
  intro x
  exact b.swapPerm.left_inv x

end FinitePartialBijection
end GroupApproximation
