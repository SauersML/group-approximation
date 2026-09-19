import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Finite gluing along a common marginal

Compatible probability laws on the two edges `A-B` and `A-C` glue to a law
on `A-B-C`.  This is the conditional-product step used to glue the three
classical transport contexts in the robust paired-quotient program.
-/

namespace GroupApproximation
namespace FiniteTreeCoupling

noncomputable section

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

omit [Fintype A] [Fintype B] [Fintype C] in
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

omit [Fintype A] in
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

omit [Fintype A] in
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
    have hsum : (∑ b, μAB a b * μAC a c / α a) =
        (∑ b, μAB a b) * μAC a c / α a := by
      rw [← Finset.sum_div, Finset.sum_mul]
    rw [hsum, hABmarginal]
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

/-! ## The three-edge transport path

The paired-quotient obstruction uses the contexts `A₀-B₀`, `A₀-B₁`,
and `A₁-B₁`.  Their context graph is a path.  The construction below
performs both conditional-product gluings explicitly. -/

section TransportPath

variable {A₀ A₁ B₀ B₁ : Type*}
  [Fintype A₀] [Fintype A₁] [Fintype B₀] [Fintype B₁]

/-- The inner law on `A₀-B₀-B₁`, re-indexed with `B₁` first for
the second gluing. -/
def innerTransportLaw
    (μ₀₀ : A₀ → B₀ → ℝ) (μ₀₁ : A₀ → B₁ → ℝ) (α₀ : A₀ → ℝ) :
    B₁ → (A₀ × B₀) → ℝ :=
  fun b₁ p ↦ glueAlongFirst μ₀₀ μ₀₁ α₀ p.1 p.2 b₁

/-- Conditional-product gluing of compatible laws on the path
`B₀-A₀-B₁-A₁`. -/
def glueTransportPath
    (μ₀₀ : A₀ → B₀ → ℝ) (μ₀₁ : A₀ → B₁ → ℝ)
    (μ₁₁ : A₁ → B₁ → ℝ) (α₀ : A₀ → ℝ) (β₁ : B₁ → ℝ) :
    A₀ → A₁ → B₀ → B₁ → ℝ :=
  fun a₀ a₁ b₀ b₁ ↦
    glueAlongFirst
      (innerTransportLaw μ₀₀ μ₀₁ α₀)
      (fun b₁ a₁ ↦ μ₁₁ a₁ b₁) β₁
      b₁ (a₀, b₀) a₁

/-- The inner law has the shared `B₁` marginal. -/
theorem sum_innerTransportLaw
    (μ₀₀ : A₀ → B₀ → ℝ) (μ₀₁ : A₀ → B₁ → ℝ)
    (α₀ : A₀ → ℝ) (β₁ : B₁ → ℝ)
    (h₀₁nonneg : ∀ a₀ b₁, 0 ≤ μ₀₁ a₀ b₁)
    (h₀₀row : ∀ a₀, ∑ b₀, μ₀₀ a₀ b₀ = α₀ a₀)
    (h₀₁row : ∀ a₀, ∑ b₁, μ₀₁ a₀ b₁ = α₀ a₀)
    (h₀₁col : ∀ b₁, ∑ a₀, μ₀₁ a₀ b₁ = β₁ b₁)
    (b₁ : B₁) :
    ∑ p, innerTransportLaw μ₀₀ μ₀₁ α₀ b₁ p = β₁ b₁ := by
  rw [Fintype.sum_prod_type]
  simp_rw [innerTransportLaw,
    sum_glueAlongFirst_left μ₀₀ μ₀₁ α₀ h₀₁nonneg
      h₀₀row h₀₁row]
  exact h₀₁col b₁

omit [Fintype A₀] [Fintype A₁] [Fintype B₀] [Fintype B₁] in
/-- The path law is nonnegative whenever its three edge laws and two shared
marginals are nonnegative. -/
theorem glueTransportPath_nonnegative
    (μ₀₀ : A₀ → B₀ → ℝ) (μ₀₁ : A₀ → B₁ → ℝ)
    (μ₁₁ : A₁ → B₁ → ℝ) (α₀ : A₀ → ℝ) (β₁ : B₁ → ℝ)
    (h₀₀nonneg : ∀ a₀ b₀, 0 ≤ μ₀₀ a₀ b₀)
    (h₀₁nonneg : ∀ a₀ b₁, 0 ≤ μ₀₁ a₀ b₁)
    (h₁₁nonneg : ∀ a₁ b₁, 0 ≤ μ₁₁ a₁ b₁)
    (hα₀nonneg : ∀ a₀, 0 ≤ α₀ a₀) (hβ₁nonneg : ∀ b₁, 0 ≤ β₁ b₁) :
    ∀ a₀ a₁ b₀ b₁,
      0 ≤ glueTransportPath μ₀₀ μ₀₁ μ₁₁ α₀ β₁ a₀ a₁ b₀ b₁ := by
  intro a₀ a₁ b₀ b₁
  exact glueAlongFirst_nonnegative
    (innerTransportLaw μ₀₀ μ₀₁ α₀)
    (fun b₁ a₁ ↦ μ₁₁ a₁ b₁) β₁
    (fun b₁' p ↦ glueAlongFirst_nonnegative μ₀₀ μ₀₁ α₀
      h₀₀nonneg h₀₁nonneg hα₀nonneg p.1 p.2 b₁')
    (fun b₁' a₁' ↦ h₁₁nonneg a₁' b₁') hβ₁nonneg
    b₁ (a₀, b₀) a₁

/-- The four-variable path law recovers the `A₀-B₀` edge. -/
theorem sum_glueTransportPath_00
    (μ₀₀ : A₀ → B₀ → ℝ) (μ₀₁ : A₀ → B₁ → ℝ)
    (μ₁₁ : A₁ → B₁ → ℝ) (α₀ : A₀ → ℝ) (β₁ : B₁ → ℝ)
    (h₀₀nonneg : ∀ a₀ b₀, 0 ≤ μ₀₀ a₀ b₀)
    (h₀₁nonneg : ∀ a₀ b₁, 0 ≤ μ₀₁ a₀ b₁)
    (h₀₀row : ∀ a₀, ∑ b₀, μ₀₀ a₀ b₀ = α₀ a₀)
    (h₀₁row : ∀ a₀, ∑ b₁, μ₀₁ a₀ b₁ = α₀ a₀)
    (h₀₁col : ∀ b₁, ∑ a₀, μ₀₁ a₀ b₁ = β₁ b₁)
    (h₁₁col : ∀ b₁, ∑ a₁, μ₁₁ a₁ b₁ = β₁ b₁)
    (a₀ : A₀) (b₀ : B₀) :
    ∑ a₁, ∑ b₁, glueTransportPath μ₀₀ μ₀₁ μ₁₁ α₀ β₁ a₀ a₁ b₀ b₁ =
      μ₀₀ a₀ b₀ := by
  rw [Finset.sum_comm]
  simp_rw [glueTransportPath,
    sum_glueAlongFirst_right
      (innerTransportLaw μ₀₀ μ₀₁ α₀)
      (fun b₁ a₁ ↦ μ₁₁ a₁ b₁) β₁
      (fun b₁' p ↦ glueAlongFirst_nonnegative μ₀₀ μ₀₁ α₀
        h₀₀nonneg h₀₁nonneg (fun a₀' ↦ by
          rw [← h₀₀row a₀']
          exact Finset.sum_nonneg fun b₀' _ ↦ h₀₀nonneg a₀' b₀') p.1 p.2 b₁')
      (sum_innerTransportLaw μ₀₀ μ₀₁ α₀ β₁ h₀₁nonneg
        h₀₀row h₀₁row h₀₁col)
      h₁₁col]
  exact sum_glueAlongFirst_right μ₀₀ μ₀₁ α₀ h₀₀nonneg
    h₀₀row h₀₁row a₀ b₀

/-- The four-variable path law recovers the `A₀-B₁` edge. -/
theorem sum_glueTransportPath_01
    (μ₀₀ : A₀ → B₀ → ℝ) (μ₀₁ : A₀ → B₁ → ℝ)
    (μ₁₁ : A₁ → B₁ → ℝ) (α₀ : A₀ → ℝ) (β₁ : B₁ → ℝ)
    (h₀₀nonneg : ∀ a₀ b₀, 0 ≤ μ₀₀ a₀ b₀)
    (h₀₁nonneg : ∀ a₀ b₁, 0 ≤ μ₀₁ a₀ b₁)
    (h₀₀row : ∀ a₀, ∑ b₀, μ₀₀ a₀ b₀ = α₀ a₀)
    (h₀₁row : ∀ a₀, ∑ b₁, μ₀₁ a₀ b₁ = α₀ a₀)
    (h₀₁col : ∀ b₁, ∑ a₀, μ₀₁ a₀ b₁ = β₁ b₁)
    (h₁₁col : ∀ b₁, ∑ a₁, μ₁₁ a₁ b₁ = β₁ b₁)
    (a₀ : A₀) (b₁ : B₁) :
    ∑ a₁, ∑ b₀, glueTransportPath μ₀₀ μ₀₁ μ₁₁ α₀ β₁ a₀ a₁ b₀ b₁ =
      μ₀₁ a₀ b₁ := by
  rw [Finset.sum_comm]
  simp_rw [glueTransportPath,
    sum_glueAlongFirst_right
      (innerTransportLaw μ₀₀ μ₀₁ α₀)
      (fun b₁ a₁ ↦ μ₁₁ a₁ b₁) β₁
      (fun b₁' p ↦ glueAlongFirst_nonnegative μ₀₀ μ₀₁ α₀
        h₀₀nonneg h₀₁nonneg (fun a₀' ↦ by
          rw [← h₀₀row a₀']
          exact Finset.sum_nonneg fun b₀' _ ↦ h₀₀nonneg a₀' b₀') p.1 p.2 b₁')
      (sum_innerTransportLaw μ₀₀ μ₀₁ α₀ β₁ h₀₁nonneg
        h₀₀row h₀₁row h₀₁col)
      h₁₁col]
  exact sum_glueAlongFirst_left μ₀₀ μ₀₁ α₀ h₀₁nonneg
    h₀₀row h₀₁row a₀ b₁

/-- The four-variable path law recovers the `A₁-B₁` edge. -/
theorem sum_glueTransportPath_11
    (μ₀₀ : A₀ → B₀ → ℝ) (μ₀₁ : A₀ → B₁ → ℝ)
    (μ₁₁ : A₁ → B₁ → ℝ) (α₀ : A₀ → ℝ) (β₁ : B₁ → ℝ)
    (h₀₁nonneg : ∀ a₀ b₁, 0 ≤ μ₀₁ a₀ b₁)
    (h₀₀row : ∀ a₀, ∑ b₀, μ₀₀ a₀ b₀ = α₀ a₀)
    (h₀₁row : ∀ a₀, ∑ b₁, μ₀₁ a₀ b₁ = α₀ a₀)
    (h₀₁col : ∀ b₁, ∑ a₀, μ₀₁ a₀ b₁ = β₁ b₁)
    (h₁₁nonneg : ∀ a₁ b₁, 0 ≤ μ₁₁ a₁ b₁)
    (h₁₁col : ∀ b₁, ∑ a₁, μ₁₁ a₁ b₁ = β₁ b₁)
    (a₁ : A₁) (b₁ : B₁) :
    ∑ a₀, ∑ b₀, glueTransportPath μ₀₀ μ₀₁ μ₁₁ α₀ β₁ a₀ a₁ b₀ b₁ =
      μ₁₁ a₁ b₁ := by
  simpa only [glueTransportPath, Fintype.sum_prod_type] using
    (sum_glueAlongFirst_left
    (innerTransportLaw μ₀₀ μ₀₁ α₀)
    (fun b₁ a₁ ↦ μ₁₁ a₁ b₁) β₁
      (fun b₁ a₁ ↦ h₁₁nonneg a₁ b₁)
    (sum_innerTransportLaw μ₀₀ μ₀₁ α₀ β₁ h₀₁nonneg
      h₀₀row h₀₁row h₀₁col)
    h₁₁col b₁ a₁)

end TransportPath

end
end FiniteTreeCoupling
end GroupApproximation
