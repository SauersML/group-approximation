import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import GroupApproximation.Meta.AxiomGuard

/-!
# The swap involution of two orthogonal equivalent idempotents

Let `e, f` be orthogonal idempotents in a ring `R`, and let `a ∈ fRe`, `b ∈ eRf` with `ba = e` and `ab = f`.  Then

`w = (1 - e - f) + a + b`

satisfies `w² = 1`, and `w ≠ 1` as soon as `e ≠ 0`.  So `R^×` contains a nontrivial element of finite order.

This is the elementary mechanism behind the sentence of `non_mf_groups_exist.tex` (tex 292): "Every example above
has torsion".  Two producers are given:

* `SwapData.ofIsometry`: a one-sided inverse pair `ts = 1` with `e = 1 - st`, `f = s e t`, `a = s e`, `b = e t`;
* `SwapData.ofOrthogonalIsometries`: two orthogonal isometries `w_i v_j = δ_ij`, with `e = v₀w₀`, `f = v₁w₁`,
  `a = v₁w₀`, `b = v₀w₁`.
-/

namespace GroupApproximation
namespace IdempotentSwap

variable {R : Type*} [Ring R]

/-- Two orthogonal idempotents `e, f` with `a ∈ fRe`, `b ∈ eRf`, `ba = e` and `ab = f`. -/
structure SwapData (R : Type*) [Ring R] where
  /-- The first idempotent. -/
  e : R
  /-- The second idempotent. -/
  f : R
  /-- The element carrying `e` to `f`. -/
  a : R
  /-- The element carrying `f` back to `e`. -/
  b : R
  e_mul_e : e * e = e
  f_mul_f : f * f = f
  e_mul_f : e * f = 0
  f_mul_e : f * e = 0
  b_mul_a : b * a = e
  a_mul_b : a * b = f
  f_a_e : f * a * e = a
  e_b_f : e * b * f = b

namespace SwapData

variable (D : SwapData R)

/-- The complement `1 - e - f`. -/
def c : R := 1 - D.e - D.f

/-- The swap `1 - e - f + a + b`. -/
def swap : R := D.c + D.a + D.b

theorem e_mul_a : D.e * D.a = 0 := by
  calc D.e * D.a = D.e * (D.f * D.a * D.e) := by rw [D.f_a_e]
    _ = D.e * D.f * D.a * D.e := by simp only [mul_assoc]
    _ = 0 := by rw [D.e_mul_f, zero_mul, zero_mul]

theorem f_mul_a : D.f * D.a = D.a := by
  calc D.f * D.a = D.f * (D.f * D.a * D.e) := by rw [D.f_a_e]
    _ = D.f * D.f * D.a * D.e := by simp only [mul_assoc]
    _ = D.a := by rw [D.f_mul_f, D.f_a_e]

theorem a_mul_e : D.a * D.e = D.a := by
  calc D.a * D.e = D.f * D.a * D.e * D.e := by rw [D.f_a_e]
    _ = D.f * D.a * (D.e * D.e) := by simp only [mul_assoc]
    _ = D.a := by rw [D.e_mul_e, D.f_a_e]

theorem a_mul_f : D.a * D.f = 0 := by
  calc D.a * D.f = D.f * D.a * D.e * D.f := by rw [D.f_a_e]
    _ = D.f * D.a * (D.e * D.f) := by simp only [mul_assoc]
    _ = 0 := by rw [D.e_mul_f, mul_zero]

theorem e_mul_b : D.e * D.b = D.b := by
  calc D.e * D.b = D.e * (D.e * D.b * D.f) := by rw [D.e_b_f]
    _ = D.e * D.e * D.b * D.f := by simp only [mul_assoc]
    _ = D.b := by rw [D.e_mul_e, D.e_b_f]

theorem f_mul_b : D.f * D.b = 0 := by
  calc D.f * D.b = D.f * (D.e * D.b * D.f) := by rw [D.e_b_f]
    _ = D.f * D.e * D.b * D.f := by simp only [mul_assoc]
    _ = 0 := by rw [D.f_mul_e, zero_mul, zero_mul]

theorem b_mul_f : D.b * D.f = D.b := by
  calc D.b * D.f = D.e * D.b * D.f * D.f := by rw [D.e_b_f]
    _ = D.e * D.b * (D.f * D.f) := by simp only [mul_assoc]
    _ = D.b := by rw [D.f_mul_f, D.e_b_f]

theorem b_mul_e : D.b * D.e = 0 := by
  calc D.b * D.e = D.e * D.b * D.f * D.e := by rw [D.e_b_f]
    _ = D.e * D.b * (D.f * D.e) := by simp only [mul_assoc]
    _ = 0 := by rw [D.f_mul_e, mul_zero]

theorem a_mul_a : D.a * D.a = 0 := by
  calc D.a * D.a = D.a * D.f * D.a := by rw [mul_assoc, D.f_mul_a]
    _ = 0 := by rw [D.a_mul_f, zero_mul]

theorem b_mul_b : D.b * D.b = 0 := by
  calc D.b * D.b = D.b * D.e * D.b := by rw [mul_assoc, D.e_mul_b]
    _ = 0 := by rw [D.b_mul_e, zero_mul]

theorem c_mul_c : D.c * D.c = D.c := by
  simp only [c, sub_mul, mul_sub, one_mul, mul_one, D.e_mul_e, D.f_mul_f, D.e_mul_f, D.f_mul_e]
  abel

theorem c_mul_a : D.c * D.a = 0 := by
  simp only [c, sub_mul, one_mul, D.e_mul_a, D.f_mul_a, sub_zero, sub_self]

theorem a_mul_c : D.a * D.c = 0 := by
  simp only [c, mul_sub, mul_one, D.a_mul_e, D.a_mul_f, sub_self]

theorem c_mul_b : D.c * D.b = 0 := by
  simp only [c, sub_mul, one_mul, D.e_mul_b, D.f_mul_b, sub_self]

theorem b_mul_c : D.b * D.c = 0 := by
  simp only [c, mul_sub, mul_one, D.b_mul_e, D.b_mul_f, sub_zero, sub_self]

/-- **`w² = 1`.** -/
theorem swap_mul_swap : D.swap * D.swap = 1 := by
  simp only [swap, add_mul, mul_add, D.c_mul_c, D.c_mul_a, D.c_mul_b, D.a_mul_c, D.a_mul_a,
    D.a_mul_b, D.b_mul_c, D.b_mul_a, D.b_mul_b, add_zero, zero_add]
  simp only [c]
  abel

/-- **`w ≠ 1` when `e ≠ 0`**: `e w e = 0`, while `e 1 e = e`. -/
theorem swap_ne_one (he : D.e ≠ 0) : D.swap ≠ 1 := by
  intro h
  have h1 : D.e * D.swap * D.e = D.e := by rw [h, mul_one, D.e_mul_e]
  have h2 : D.e * D.swap * D.e = 0 := by
    have hl : D.e * D.swap = D.b := by
      simp only [swap, c, mul_add, mul_sub, mul_one, D.e_mul_e, D.e_mul_f, D.e_mul_a, D.e_mul_b,
        sub_self, zero_add, add_zero]
    rw [hl, D.b_mul_e]
  exact he (h1.symm.trans h2)

/-- The swap as a unit. -/
def swapUnit : Rˣ := ⟨D.swap, D.swap, D.swap_mul_swap, D.swap_mul_swap⟩

theorem swapUnit_sq : D.swapUnit ^ 2 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, pow_two, Units.val_one]
  exact D.swap_mul_swap

theorem swapUnit_isOfFinOrder : IsOfFinOrder D.swapUnit :=
  isOfFinOrder_iff_pow_eq_one.2 ⟨2, two_pos, D.swapUnit_sq⟩

theorem swapUnit_ne_one (he : D.e ≠ 0) : D.swapUnit ≠ 1 := by
  intro h
  exact D.swap_ne_one he (congrArg Units.val h)

/-! ## Producers -/

/-- **From a one-sided inverse pair `ts = 1`**: `e = 1 - st`, `f = s e t`, `a = s e`, `b = e t`. -/
def ofIsometry (s t : R) (hts : t * s = 1) : SwapData R where
  e := 1 - s * t
  f := s * (1 - s * t) * t
  a := s * (1 - s * t)
  b := (1 - s * t) * t
  e_mul_e := by
    have hes : (1 - s * t) * s = 0 := by rw [sub_mul, one_mul, mul_assoc, hts, mul_one, sub_self]
    rw [mul_sub, mul_one, ← mul_assoc, hes, zero_mul, sub_zero]
  f_mul_f := by
    have hts' : ∀ x : R, t * (s * x) = x := fun x ↦ by rw [← mul_assoc, hts, one_mul]
    have hee' : ∀ x : R, (1 - s * t) * ((1 - s * t) * x) = (1 - s * t) * x := fun x ↦ by
      have hes : (1 - s * t) * s = 0 := by rw [sub_mul, one_mul, mul_assoc, hts, mul_one, sub_self]
      rw [← mul_assoc, mul_sub, mul_one, ← mul_assoc, hes, zero_mul, sub_zero]
    simp only [mul_assoc, hts', hee']
  e_mul_f := by
    have hes' : ∀ x : R, (1 - s * t) * (s * x) = 0 := fun x ↦ by
      rw [← mul_assoc, sub_mul, one_mul, mul_assoc, hts, mul_one, sub_self, zero_mul]
    simp only [mul_assoc, hes']
  f_mul_e := by
    have hte : t * (1 - s * t) = 0 := by rw [mul_sub, mul_one, ← mul_assoc, hts, one_mul, sub_self]
    simp only [mul_assoc, hte, mul_zero]
  b_mul_a := by
    have hts' : ∀ x : R, t * (s * x) = x := fun x ↦ by rw [← mul_assoc, hts, one_mul]
    have hes : (1 - s * t) * s = 0 := by rw [sub_mul, one_mul, mul_assoc, hts, mul_one, sub_self]
    simp only [mul_assoc, hts']
    rw [mul_sub, mul_one, ← mul_assoc, hes, zero_mul, sub_zero]
  a_mul_b := by
    have hee' : ∀ x : R, (1 - s * t) * ((1 - s * t) * x) = (1 - s * t) * x := fun x ↦ by
      have hes : (1 - s * t) * s = 0 := by rw [sub_mul, one_mul, mul_assoc, hts, mul_one, sub_self]
      rw [← mul_assoc, mul_sub, mul_one, ← mul_assoc, hes, zero_mul, sub_zero]
    simp only [mul_assoc, hee']
  f_a_e := by
    have hts' : ∀ x : R, t * (s * x) = x := fun x ↦ by rw [← mul_assoc, hts, one_mul]
    have hes : (1 - s * t) * s = 0 := by rw [sub_mul, one_mul, mul_assoc, hts, mul_one, sub_self]
    have hee : (1 - s * t) * (1 - s * t) = 1 - s * t := by
      rw [mul_sub, mul_one, ← mul_assoc, hes, zero_mul, sub_zero]
    simp only [mul_assoc, hts', hee]
  e_b_f := by
    have hts' : ∀ x : R, t * (s * x) = x := fun x ↦ by rw [← mul_assoc, hts, one_mul]
    have hes : (1 - s * t) * s = 0 := by rw [sub_mul, one_mul, mul_assoc, hts, mul_one, sub_self]
    have hee : (1 - s * t) * (1 - s * t) = 1 - s * t := by
      rw [mul_sub, mul_one, ← mul_assoc, hes, zero_mul, sub_zero]
    have hee' : ∀ x : R, (1 - s * t) * ((1 - s * t) * x) = (1 - s * t) * x := fun x ↦ by
      rw [← mul_assoc, hee]
    simp only [mul_assoc, hts', hee']

/-- **From two orthogonal isometries** `w₀v₀ = w₁v₁ = 1`, `w₀v₁ = w₁v₀ = 0`: `e = v₀w₀`, `f = v₁w₁`, `a = v₁w₀`,
`b = v₀w₁`. -/
def ofOrthogonalIsometries (v₀ v₁ w₀ w₁ : R) (h₀₀ : w₀ * v₀ = 1) (h₀₁ : w₀ * v₁ = 0)
    (h₁₀ : w₁ * v₀ = 0) (h₁₁ : w₁ * v₁ = 1) : SwapData R where
  e := v₀ * w₀
  f := v₁ * w₁
  a := v₁ * w₀
  b := v₀ * w₁
  e_mul_e := by
    have h : ∀ x : R, w₀ * (v₀ * x) = x := fun x ↦ by rw [← mul_assoc, h₀₀, one_mul]
    simp only [mul_assoc, h]
  f_mul_f := by
    have h : ∀ x : R, w₁ * (v₁ * x) = x := fun x ↦ by rw [← mul_assoc, h₁₁, one_mul]
    simp only [mul_assoc, h]
  e_mul_f := by
    have h : ∀ x : R, w₀ * (v₁ * x) = 0 := fun x ↦ by rw [← mul_assoc, h₀₁, zero_mul]
    simp only [mul_assoc, h, mul_zero]
  f_mul_e := by
    have h : ∀ x : R, w₁ * (v₀ * x) = 0 := fun x ↦ by rw [← mul_assoc, h₁₀, zero_mul]
    simp only [mul_assoc, h, mul_zero]
  b_mul_a := by
    have h : ∀ x : R, w₁ * (v₁ * x) = x := fun x ↦ by rw [← mul_assoc, h₁₁, one_mul]
    simp only [mul_assoc, h]
  a_mul_b := by
    have h : ∀ x : R, w₀ * (v₀ * x) = x := fun x ↦ by rw [← mul_assoc, h₀₀, one_mul]
    simp only [mul_assoc, h]
  f_a_e := by
    have h0 : ∀ x : R, w₀ * (v₀ * x) = x := fun x ↦ by rw [← mul_assoc, h₀₀, one_mul]
    have h1 : ∀ x : R, w₁ * (v₁ * x) = x := fun x ↦ by rw [← mul_assoc, h₁₁, one_mul]
    simp only [mul_assoc, h0, h1]
  e_b_f := by
    have h0 : ∀ x : R, w₀ * (v₀ * x) = x := fun x ↦ by rw [← mul_assoc, h₀₀, one_mul]
    have h1 : ∀ x : R, w₁ * (v₁ * x) = x := fun x ↦ by rw [← mul_assoc, h₁₁, one_mul]
    simp only [mul_assoc, h0, h1]

theorem ofOrthogonalIsometries_e_ne_zero [Nontrivial R] (v₀ v₁ w₀ w₁ : R) (h₀₀ : w₀ * v₀ = 1)
    (h₀₁ : w₀ * v₁ = 0) (h₁₀ : w₁ * v₀ = 0) (h₁₁ : w₁ * v₁ = 1) :
    (ofOrthogonalIsometries v₀ v₁ w₀ w₁ h₀₀ h₀₁ h₁₀ h₁₁).e ≠ 0 := by
  intro h
  have h' : w₀ * (v₀ * w₀) * v₀ = 1 := by rw [← mul_assoc, h₀₀, one_mul, h₀₀]
  change v₀ * w₀ = 0 at h
  rw [h, mul_zero, zero_mul] at h'
  exact zero_ne_one h'

end SwapData

/-- **A ring with a one-sided inverse pair `ts = 1`, `st ≠ 1`, has a nontrivial unit of finite order.** -/
theorem exists_isOfFinOrder_ne_one_of_isometry (s t : R) (hts : t * s = 1) (hst : (1 : R) - s * t ≠ 0) :
    ∃ g : Rˣ, g ≠ 1 ∧ IsOfFinOrder g :=
  ⟨(SwapData.ofIsometry s t hts).swapUnit, (SwapData.ofIsometry s t hts).swapUnit_ne_one hst,
    (SwapData.ofIsometry s t hts).swapUnit_isOfFinOrder⟩

/-- **A nontrivial ring with two orthogonal isometries has a nontrivial unit of finite order.** -/
theorem exists_isOfFinOrder_ne_one_of_orthogonalIsometries [Nontrivial R] (v₀ v₁ w₀ w₁ : R)
    (h₀₀ : w₀ * v₀ = 1) (h₀₁ : w₀ * v₁ = 0) (h₁₀ : w₁ * v₀ = 0) (h₁₁ : w₁ * v₁ = 1) :
    ∃ g : Rˣ, g ≠ 1 ∧ IsOfFinOrder g :=
  ⟨(SwapData.ofOrthogonalIsometries v₀ v₁ w₀ w₁ h₀₀ h₀₁ h₁₀ h₁₁).swapUnit,
    (SwapData.ofOrthogonalIsometries v₀ v₁ w₀ w₁ h₀₀ h₀₁ h₁₀ h₁₁).swapUnit_ne_one
      (SwapData.ofOrthogonalIsometries_e_ne_zero v₀ v₁ w₀ w₁ h₀₀ h₀₁ h₁₀ h₁₁),
    (SwapData.ofOrthogonalIsometries v₀ v₁ w₀ w₁ h₀₀ h₀₁ h₁₀ h₁₁).swapUnit_isOfFinOrder⟩

end IdempotentSwap
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.IdempotentSwap.SwapData.swap_mul_swap
#audit_axioms GroupApproximation.IdempotentSwap.SwapData.swap_ne_one
#audit_axioms GroupApproximation.IdempotentSwap.exists_isOfFinOrder_ne_one_of_isometry
#audit_axioms GroupApproximation.IdempotentSwap.exists_isOfFinOrder_ne_one_of_orthogonalIsometries
