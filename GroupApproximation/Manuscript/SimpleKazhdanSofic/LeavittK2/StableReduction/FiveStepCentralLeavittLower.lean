import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStepCentralLeavittSpread
import GroupApproximation.Meta.AxiomGuard

/-!
# The lower corner `ψ₁` commutes with the corner root `x_{pq}(s₀t₀)` (lane sk-leavitt-35, part 2)

Let `R` be a ring with a Leavitt family, `p₀ = s₀ t₀` and `p₁ = s₁ t₁`.  The *lower corner
homomorphism* `ψ₁ : St_n(R) → St_n(R)` is `x_{ij}(a) ↦ x_{ij}(s₁ a t₁)`
(`fiveStepCentralLeavittLowerHom`).  It respects the Steinberg relations because
`(s₁ a t₁)(s₁ b t₁) = s₁ (a b) t₁` (from `t₁ s₁ = 1`).

The main result is unconditional, for `n ≥ 3`: every element of the image of `ψ₁` commutes
with `x_{pq}(p₀)` (`fiveStepCentralLeavitt_commute_lowerHom`).  On generators:
* a root `(i, j)` with `i ≠ q` and `j ≠ p` commutes by the Steinberg relation;
* for `(q, j)` with `j ≠ p` the commutator is `x_{pj}(p₀ · s₁ a t₁) = x_{pj}(0)`;
* for `(i, p)` with `i ≠ q` the commutator is `x_{iq}(s₁ a t₁ · p₀) = x_{iq}(0)`;
* for the opposite root `(q, p)` write `x_{qp}(s₁ a t₁) = ⁅x_{qm}(s₁ a), x_{mp}(t₁)⁆`.  Here
  `x_{pq}(p₀)` commutes with both factors, since `p₀ s₁ = 0` and `t₁ p₀ = 0`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

theorem fiveStepCentralLeavitt_p0_mul_s1 {R : Type*} [Ring R] (L : LeavittFamily R) (a : R) :
    L.s0 * L.t0 * (L.s1 * a) = 0 := by
  calc L.s0 * L.t0 * (L.s1 * a) = L.s0 * ((L.t0 * L.s1) * a) := by simp only [mul_assoc]
    _ = 0 := by rw [L.t0_s1, zero_mul, mul_zero]

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentralLeavitt_p0_mul_s1

theorem fiveStepCentralLeavitt_p0_mul_lower {R : Type*} [Ring R] (L : LeavittFamily R) (a : R) :
    L.s0 * L.t0 * (L.s1 * a * L.t1) = 0 := by
  calc L.s0 * L.t0 * (L.s1 * a * L.t1) = L.s0 * ((L.t0 * L.s1) * (a * L.t1)) := by
        simp only [mul_assoc]
    _ = 0 := by rw [L.t0_s1, zero_mul, mul_zero]

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentralLeavitt_p0_mul_lower

theorem fiveStepCentralLeavitt_lower_mul_p0 {R : Type*} [Ring R] (L : LeavittFamily R) (a : R) :
    L.s1 * a * L.t1 * (L.s0 * L.t0) = 0 := by
  calc L.s1 * a * L.t1 * (L.s0 * L.t0) = L.s1 * (a * ((L.t1 * L.s0) * L.t0)) := by
        simp only [mul_assoc]
    _ = 0 := by rw [L.t1_s0, zero_mul, mul_zero, mul_zero]

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentralLeavitt_lower_mul_p0

theorem fiveStepCentralLeavitt_t1_mul_p0 {R : Type*} [Ring R] (L : LeavittFamily R) :
    L.t1 * (L.s0 * L.t0) = 0 := by
  rw [← mul_assoc, L.t1_s0, zero_mul]

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentralLeavitt_t1_mul_p0

/-- The lower corner is multiplicative: `(s₁ a t₁)(s₁ b t₁) = s₁ (a b) t₁`. -/
theorem fiveStepCentralLeavitt_lower_mul {R : Type*} [Ring R] (L : LeavittFamily R) (a b : R) :
    L.s1 * a * L.t1 * (L.s1 * b * L.t1) = L.s1 * (a * b) * L.t1 := by
  calc L.s1 * a * L.t1 * (L.s1 * b * L.t1)
      = L.s1 * (a * ((L.t1 * L.s1) * (b * L.t1))) := by simp only [mul_assoc]
    _ = L.s1 * (a * b) * L.t1 := by rw [L.t1_s1, one_mul, mul_assoc, mul_assoc]

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentralLeavitt_lower_mul

/-- Adjacent roots with vanishing coefficient product commute, over any ring. -/
theorem fiveStepCentralLeavitt_commute_of_mul_eq_zero {R : Type*} [Ring R] {n : ℕ}
    {p q j : Fin n} (hpq : p ≠ q) (hqj : q ≠ j) (hpj : p ≠ j) {c d : R} (h : c * d = 0) :
    Commute (x p q hpq c) (x q j hqj d) := by
  rw [← commutatorElement_eq_one_iff_commute, x_commutator p q j hpq hqj hpj, h, x_zero]

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentralLeavitt_commute_of_mul_eq_zero

/-- **The opposite root.**  `x_{pq}(s₀ t₀)` commutes with `x_{qp}(s₁ a t₁)`, for `n ≥ 3`. -/
theorem fiveStepCentralLeavitt_commute_lower_opp {R : Type*} [Ring R] (L : LeavittFamily R)
    {n : ℕ} (hn : 3 ≤ n) {p q : Fin n} (hpq : p ≠ q) (hqp : q ≠ p) (a : R) :
    Commute (x p q hpq (L.s0 * L.t0)) (x q p hqp (L.s1 * a * L.t1)) := by
  obtain ⟨m, hpm, hqm⟩ := fiveStepCentral_exists_third hn p q
  have hmp : m ≠ p := Ne.symm hpm
  rw [← x_commutator q m p hqm hmp hqp (L.s1 * a) L.t1, commutatorElement_def]
  have hu : Commute (x p q hpq (L.s0 * L.t0)) (x q m hqm (L.s1 * a)) :=
    fiveStepCentralLeavitt_commute_of_mul_eq_zero hpq hqm hpm
      (fiveStepCentralLeavitt_p0_mul_s1 L a)
  have hv : Commute (x p q hpq (L.s0 * L.t0)) (x m p hmp L.t1) :=
    (fiveStepCentralLeavitt_commute_of_mul_eq_zero hmp hpq (Ne.symm hqm)
      (fiveStepCentralLeavitt_t1_mul_p0 L)).symm
  exact ((hu.mul_right hv).mul_right hu.inv_right).mul_right hv.inv_right

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentralLeavitt_commute_lower_opp
