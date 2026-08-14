import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Order

/-!
# Finite gluing along a common marginal

Compatible probability laws on the two edges `A-B` and `A-C` glue to a law
on `A-B-C`.  This is the conditional-product step used to glue the three
classical transport contexts in the robust paired-quotient program.
-/

namespace GroupApproximation
namespace FiniteTreeCoupling

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-- Conditional-product gluing over a common first-coordinate marginal.
Zero marginal fibers are assigned zero mass. -/
def glueAlongFirst
    (μAB : A → B → ℝ) (μAC : A → C → ℝ) (α : A → ℝ) :
    A → B → C → ℝ :=
  fun a b c ↦
    if α a = 0 then 0 else μAB a b * μAC a c / α a

/-- A nonnegative finite row with sum zero vanishes pointwise. -/
theorem eq_zero_of_nonnegative_sum_eq_zero
    {X : Type*} [Fintype X] (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hsum : ∑ x, f x = 0) (x : X) :
    f x = 0 := by
  have hle : f x ≤ ∑ y, f y :=
    Finset.single_le_sum (fun y _ ↦ hf y) (Finset.mem_univ x)
  rw [hsum] at hle
  exact le_antisymm hle (hf x)

theorem glueAlongFirst_nonnegative
    (μAB : A → B → ℝ) (μAC : A → C → ℝ) (α : A → ℝ)
    (hAB : ∀ a b, 0 ≤ μAB a b)
    (hAC : ∀ a c, 0 ≤ μAC a c)
    (hα : ∀ a, 0 ≤ α a) :
    ∀ a b c, 0 ≤ glueAlongFirst μAB μAC α a b c := by
  intro a b c
  by_cases ha : α a = 0
  · simp [glueAlongFirst, ha]
  · simp only [glueAlongFirst, if_neg ha]
    exact div_nonneg (mul_nonneg (hAB a b) (hAC a c)) (hα a)

/-- Summing out `C` recovers the `A-B` law. -/
theorem sum_glueAlongFirst_right
    (μAB : A → B → ℝ) (μAC : A → C → ℝ) (α : A → ℝ)
    (hABnonneg : ∀ a b, 0 ≤ μAB a b)
    (hABmarginal : ∀ a, ∑ b, μAB a b = α a)
    (hACmarginal : ∀ a, ∑ c, μAC a c = α a)
    (a : A) (b : B) :
    ∑ c, glueAlongFirst μAB μAC α a b c = μAB a b := by
  by_cases ha : α a = 0
  · have hab : μAB a b = 0 :=
      eq_zero_of_nonnegative_sum_eq_zero (μAB a)
        (hABnonneg a) ((hABmarginal a).trans ha) b
    simp [glueAlongFirst, ha, hab]
  · simp_rw [glueAlongFirst, if_neg ha]
    rw [← Finset.sum_div, ← Finset.mul_sum, hACmarginal,
      mul_div_cancel_right₀ _ ha]

/-- Summing out `B` recovers the `A-C` law. -/
theorem sum_glueAlongFirst_left
    (μAB : A → B → ℝ) (μAC : A → C → ℝ) (α : A → ℝ)
    (hACnonneg : ∀ a c, 0 ≤ μAC a c)
    (hABmarginal : ∀ a, ∑ b, μAB a b = α a)
    (hACmarginal : ∀ a, ∑ c, μAC a c = α a)
    (a : A) (c : C) :
    ∑ b, glueAlongFirst μAB μAC α a b c = μAC a c := by
  by_cases ha : α a = 0
  · have hac : μAC a c = 0 :=
      eq_zero_of_nonnegative_sum_eq_zero (μAC a)
        (hACnonneg a) ((hACmarginal a).trans ha) c
    simp [glueAlongFirst, ha, hac]
  · simp_rw [glueAlongFirst, if_neg ha]
    rw [show (∑ b, μAB a b * μAC a c / α a) =
        (∑ b, μAB a b) * μAC a c / α a by
          rw [← Finset.sum_div, Finset.sum_mul]],
      hABmarginal]
    rw [mul_comm (α a) (μAC a c), mul_div_cancel_right₀ _ ha]

/-- The glued law is normalized whenever either input pair-law is. -/
theorem sum_glueAlongFirst
    (μAB : A → B → ℝ) (μAC : A → C → ℝ) (α : A → ℝ)
    (hABnonneg : ∀ a b, 0 ≤ μAB a b)
    (hABmarginal : ∀ a, ∑ b, μAB a b = α a)
    (hACmarginal : ∀ a, ∑ c, μAC a c = α a)
    (hABtotal : ∑ a, ∑ b, μAB a b = 1) :
    ∑ a, ∑ b, ∑ c, glueAlongFirst μAB μAC α a b c = 1 := by
  simp_rw [sum_glueAlongFirst_right μAB μAC α hABnonneg
    hABmarginal hACmarginal]
  exact hABtotal

/-- Existence form of finite marginal gluing. -/
theorem exists_gluing
    (μAB : A → B → ℝ) (μAC : A → C → ℝ) (α : A → ℝ)
    (hABnonneg : ∀ a b, 0 ≤ μAB a b)
    (hACnonneg : ∀ a c, 0 ≤ μAC a c)
    (hαnonneg : ∀ a, 0 ≤ α a)
    (hABmarginal : ∀ a, ∑ b, μAB a b = α a)
    (hACmarginal : ∀ a, ∑ c, μAC a c = α a)
    (hABtotal : ∑ a, ∑ b, μAB a b = 1) :
    ∃ μABC : A → B → C → ℝ,
      (∀ a b c, 0 ≤ μABC a b c) ∧
      (∀ a b, ∑ c, μABC a b c = μAB a b) ∧
      (∀ a c, ∑ b, μABC a b c = μAC a c) ∧
      ∑ a, ∑ b, ∑ c, μABC a b c = 1 := by
  refine ⟨glueAlongFirst μAB μAC α,
    glueAlongFirst_nonnegative μAB μAC α hABnonneg hACnonneg hαnonneg,
    ?_, ?_, ?_⟩
  · exact sum_glueAlongFirst_right μAB μAC α hABnonneg
      hABmarginal hACmarginal
  · exact sum_glueAlongFirst_left μAB μAC α hACnonneg
      hABmarginal hACmarginal
  · exact sum_glueAlongFirst μAB μAC α hABnonneg
      hABmarginal hACmarginal hABtotal

end FiniteTreeCoupling
end GroupApproximation
