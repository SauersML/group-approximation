import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStFourFPGroup
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Ring
import GroupApproximation.Meta.AxiomGuard

/-!
# Root subgroups `ℤ[1/q] → P` from a Baumslag–Solitar pair (bh-met-91m)

Let `t, y` be elements of a group `P` with `t y t⁻¹ = y ^ Q`, and let `R` be a commutative ring
in which `q = Q`, `ℤ → R` is injective and every `r` has `q ^ k r ∈ ℤ` for some `k`.  Then
`czStFourFP_X t y hsurj r = t⁻ᵏ yⁿ tᵏ` (for any `k, n` with `q ^ k r = n`) is an additive map
`R → P` (`czStFourFP_X_add`), extends `n ↦ yⁿ` (`czStFourFP_X_int`), and satisfies
`t X(r) t⁻¹ = X(q r)` (`czStFourFP_X_conj_t`).  If `g y g⁻¹ = X(ρ)` and conjugation by `g`
commutes with conjugation by `t`, then `g X(r) g⁻¹ = X(ρ r)` (`czStFourFP_X_conj_of`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

section BS

variable {P : Type*} [Group P] {t y : P} {Q : ℤ}

/-- One conjugation by `t`. -/
theorem czStFourFP_bs_conj1 (ht : t * y * t⁻¹ = y ^ Q) (n : ℤ) :
    t * y ^ n * t⁻¹ = y ^ (Q * n) := by
  rw [← conj_zpow, ht, ← zpow_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_bs_conj1

/-- Conjugation by `tʲ`. -/
theorem czStFourFP_bs_conj (ht : t * y * t⁻¹ = y ^ Q) (j : ℕ) (n : ℤ) :
    t ^ j * y ^ n * (t ^ j)⁻¹ = y ^ (Q ^ j * n) := by
  induction j generalizing n with
  | zero => simp only [pow_zero, one_mul, inv_one, mul_one]
  | succ j ih =>
    calc t ^ (j + 1) * y ^ n * (t ^ (j + 1))⁻¹ = t ^ j * (t * y ^ n * t⁻¹) * (t ^ j)⁻¹ := by
          rw [pow_succ, mul_inv_rev]; simp only [mul_assoc]
      _ = y ^ (Q ^ (j + 1) * n) := by
          rw [czStFourFP_bs_conj1 ht, ih]
          congr 1
          ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_bs_conj

/-- Raising the level of a representative. -/
theorem czStFourFP_bs_lift (ht : t * y * t⁻¹ = y ^ Q) (j k : ℕ) (n : ℤ) :
    (t ^ k)⁻¹ * y ^ n * t ^ k = (t ^ (j + k))⁻¹ * y ^ (Q ^ j * n) * t ^ (j + k) := by
  rw [← czStFourFP_bs_conj ht j n, pow_add t j k, mul_inv_rev]
  simp only [mul_assoc, inv_mul_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_bs_lift

end BS

section Level

variable {P : Type*} [Group P] {t y : P} {Q : ℤ} {R : Type*} [CommRing R] {q : R}

/-- Shifting an integrality witness. -/
theorem czStFourFP_bs_shift (hq : q = (Q : R)) {r : R} {k : ℕ} {n : ℤ}
    (h : q ^ k * r = (n : R)) (j : ℕ) : q ^ (k + j) * r = ((Q ^ j * n : ℤ) : R) := by
  rw [Int.cast_mul, Int.cast_pow, ← hq, ← h, pow_add]
  ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_bs_shift

/-- Two representatives of the same element agree. -/
theorem czStFourFP_bs_rep_eq (ht : t * y * t⁻¹ = y ^ Q) (hq : q = (Q : R))
    (hinj : Function.Injective (Int.cast : ℤ → R)) {r : R} {k k' : ℕ} {n n' : ℤ}
    (h : q ^ k * r = (n : R)) (h' : q ^ k' * r = (n' : R)) :
    (t ^ k)⁻¹ * y ^ n * t ^ k = (t ^ k')⁻¹ * y ^ n' * t ^ k' := by
  have hint : Q ^ k' * n = Q ^ k * n' := by
    apply hinj
    rw [Int.cast_mul, Int.cast_mul, Int.cast_pow, Int.cast_pow, ← hq, ← h, ← h']
    exact mul_left_comm _ _ _
  rw [czStFourFP_bs_lift ht k' k n, czStFourFP_bs_lift ht k k' n', hint, add_comm k' k]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_bs_rep_eq

/-- The map `X : R → P`, `X(r) = t⁻ᵏ yⁿ tᵏ` for the chosen `q ^ k r = n`. -/
noncomputable def czStFourFP_X (t y : P)
    (hsurj : ∀ r : R, ∃ k : ℕ, ∃ n : ℤ, q ^ k * r = (n : R)) (r : R) : P :=
  (t ^ (hsurj r).choose)⁻¹ * y ^ (hsurj r).choose_spec.choose * t ^ (hsurj r).choose

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_X

/-- `X` is computed by any representative. -/
theorem czStFourFP_X_rep (ht : t * y * t⁻¹ = y ^ Q) (hq : q = (Q : R))
    (hinj : Function.Injective (Int.cast : ℤ → R))
    (hsurj : ∀ r : R, ∃ k : ℕ, ∃ n : ℤ, q ^ k * r = (n : R)) (r : R) (k : ℕ) (n : ℤ)
    (h : q ^ k * r = (n : R)) : czStFourFP_X t y hsurj r = (t ^ k)⁻¹ * y ^ n * t ^ k :=
  czStFourFP_bs_rep_eq ht hq hinj (hsurj r).choose_spec.choose_spec h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_X_rep

/-- `X` extends `n ↦ yⁿ`. -/
theorem czStFourFP_X_int (ht : t * y * t⁻¹ = y ^ Q) (hq : q = (Q : R))
    (hinj : Function.Injective (Int.cast : ℤ → R))
    (hsurj : ∀ r : R, ∃ k : ℕ, ∃ n : ℤ, q ^ k * r = (n : R)) (n : ℤ) :
    czStFourFP_X t y hsurj (n : R) = y ^ n := by
  rw [czStFourFP_X_rep ht hq hinj hsurj (n : R) 0 n (by rw [pow_zero, one_mul])]
  simp only [pow_zero, inv_one, one_mul, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_X_int

/-- `X` is additive. -/
theorem czStFourFP_X_add (ht : t * y * t⁻¹ = y ^ Q) (hq : q = (Q : R))
    (hinj : Function.Injective (Int.cast : ℤ → R))
    (hsurj : ∀ r : R, ∃ k : ℕ, ∃ n : ℤ, q ^ k * r = (n : R)) (r s : R) :
    czStFourFP_X t y hsurj (r + s) = czStFourFP_X t y hsurj r * czStFourFP_X t y hsurj s := by
  obtain ⟨k₁, n₁, h₁⟩ := hsurj r
  obtain ⟨k₂, n₂, h₂⟩ := hsurj s
  have hr := czStFourFP_bs_shift hq h₁ k₂
  have hs := czStFourFP_bs_shift hq h₂ k₁
  rw [add_comm k₂ k₁] at hs
  have hrs : q ^ (k₁ + k₂) * (r + s) = ((Q ^ k₂ * n₁ + Q ^ k₁ * n₂ : ℤ) : R) := by
    rw [mul_add, hr, hs, Int.cast_add]
  rw [czStFourFP_X_rep ht hq hinj hsurj (r + s) _ _ hrs,
    czStFourFP_X_rep ht hq hinj hsurj r _ _ hr, czStFourFP_X_rep ht hq hinj hsurj s _ _ hs,
    zpow_add]
  simp only [mul_assoc, mul_inv_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_X_add

/-- Integer multiples: `X(s) ^ n = X(n s)`. -/
theorem czStFourFP_X_zpow (ht : t * y * t⁻¹ = y ^ Q) (hq : q = (Q : R))
    (hinj : Function.Injective (Int.cast : ℤ → R))
    (hsurj : ∀ r : R, ∃ k : ℕ, ∃ n : ℤ, q ^ k * r = (n : R)) (s : R) (n : ℤ) :
    czStFourFP_X t y hsurj s ^ n = czStFourFP_X t y hsurj ((n : R) * s) := by
  obtain ⟨k, a, h⟩ := hsurj s
  have h' : q ^ k * ((n : R) * s) = ((a * n : ℤ) : R) := by
    rw [mul_left_comm, h, Int.cast_mul, mul_comm]
  rw [czStFourFP_X_rep ht hq hinj hsurj s k a h,
    czStFourFP_X_rep ht hq hinj hsurj _ k (a * n) h', zpow_mul]
  have e := conj_zpow (i := n) (a := (t ^ k)⁻¹) (b := y ^ a)
  rw [inv_inv] at e
  exact e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_X_zpow

/-- `t X(r) t⁻¹ = X(q r)`. -/
theorem czStFourFP_X_conj_t (ht : t * y * t⁻¹ = y ^ Q) (hq : q = (Q : R))
    (hinj : Function.Injective (Int.cast : ℤ → R))
    (hsurj : ∀ r : R, ∃ k : ℕ, ∃ n : ℤ, q ^ k * r = (n : R)) (r : R) :
    t * czStFourFP_X t y hsurj r * t⁻¹ = czStFourFP_X t y hsurj (q * r) := by
  obtain ⟨k, n, h⟩ := hsurj r
  have h₁ : q ^ (k + 1) * r = ((Q * n : ℤ) : R) := by
    rw [pow_succ', mul_assoc, h, Int.cast_mul, hq]
  have h₂ : q ^ k * (q * r) = ((Q * n : ℤ) : R) := by
    rw [mul_left_comm, h, Int.cast_mul, hq]
  rw [czStFourFP_X_rep ht hq hinj hsurj r (k + 1) (Q * n) h₁,
    czStFourFP_X_rep ht hq hinj hsurj (q * r) k (Q * n) h₂, pow_succ, mul_inv_rev]
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_X_conj_t

/-- `tᵏ X(r) t⁻ᵏ = X(qᵏ r)`. -/
theorem czStFourFP_X_conj_t_pow (ht : t * y * t⁻¹ = y ^ Q) (hq : q = (Q : R))
    (hinj : Function.Injective (Int.cast : ℤ → R))
    (hsurj : ∀ r : R, ∃ k : ℕ, ∃ n : ℤ, q ^ k * r = (n : R)) (k : ℕ) (r : R) :
    t ^ k * czStFourFP_X t y hsurj r * (t ^ k)⁻¹ = czStFourFP_X t y hsurj (q ^ k * r) :=
  czStFourFP_conj_pow_iter (f := czStFourFP_X t y hsurj)
    (czStFourFP_X_conj_t ht hq hinj hsurj) k r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_X_conj_t_pow

end Level

/-- If conjugation by `g` commutes with conjugation by `t`, it commutes with conjugation by
`tᵏ`. -/
theorem czStFourFP_conj_comm_pow {P : Type*} [Group P] {g t : P}
    (hcomm : ∀ h, g * (t * h * t⁻¹) * g⁻¹ = t * (g * h * g⁻¹) * t⁻¹) (k : ℕ) (h : P) :
    g * (t ^ k * h * (t ^ k)⁻¹) * g⁻¹ = t ^ k * (g * h * g⁻¹) * (t ^ k)⁻¹ := by
  induction k generalizing h with
  | zero => simp only [pow_zero, one_mul, inv_one, mul_one]
  | succ k ih =>
    have e : ∀ u : P, t ^ (k + 1) * u * (t ^ (k + 1))⁻¹ = t ^ k * (t * u * t⁻¹) * (t ^ k)⁻¹ := by
      intro u
      rw [pow_succ, mul_inv_rev]
      simp only [mul_assoc]
    rw [e, e, ih, hcomm]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_conj_comm_pow

/-- The same for conjugation by `t⁻ᵏ`. -/
theorem czStFourFP_conj_comm_pow_inv {P : Type*} [Group P] {g t : P}
    (hcomm : ∀ h, g * (t * h * t⁻¹) * g⁻¹ = t * (g * h * g⁻¹) * t⁻¹) (k : ℕ) (h : P) :
    g * ((t ^ k)⁻¹ * h * t ^ k) * g⁻¹ = (t ^ k)⁻¹ * (g * h * g⁻¹) * t ^ k := by
  have e := czStFourFP_conj_comm_pow hcomm k ((t ^ k)⁻¹ * h * t ^ k)
  have hh : t ^ k * ((t ^ k)⁻¹ * h * t ^ k) * (t ^ k)⁻¹ = h := by
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  rw [hh] at e
  rw [e]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_conj_comm_pow_inv

section Scale

variable {P : Type*} [Group P] {t y : P} {Q : ℤ} {R : Type*} [CommRing R] {q : R}

/-- **Scaling.**  If `g y g⁻¹ = X(ρ)` and conjugation by `g` commutes with conjugation by `t`,
then `g X(r) g⁻¹ = X(ρ r)`. -/
theorem czStFourFP_X_conj_of (ht : t * y * t⁻¹ = y ^ Q) (hq : q = (Q : R))
    (hinj : Function.Injective (Int.cast : ℤ → R))
    (hsurj : ∀ r : R, ∃ k : ℕ, ∃ n : ℤ, q ^ k * r = (n : R)) {g : P} {ρ : R}
    (hy : g * y * g⁻¹ = czStFourFP_X t y hsurj ρ)
    (hcomm : ∀ h, g * (t * h * t⁻¹) * g⁻¹ = t * (g * h * g⁻¹) * t⁻¹) (r : R) :
    g * czStFourFP_X t y hsurj r * g⁻¹ = czStFourFP_X t y hsurj (ρ * r) := by
  obtain ⟨k, n, h⟩ := hsurj r
  have e₁ : t ^ k * czStFourFP_X t y hsurj (ρ * r) * (t ^ k)⁻¹ =
      czStFourFP_X t y hsurj ((n : R) * ρ) := by
    rw [czStFourFP_X_conj_t_pow ht hq hinj hsurj k, mul_left_comm, h, mul_comm]
  rw [czStFourFP_X_rep ht hq hinj hsurj r k n h, czStFourFP_conj_comm_pow_inv hcomm k,
    ← conj_zpow, hy, czStFourFP_X_zpow ht hq hinj hsurj, ← e₁]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_X_conj_of

end Scale

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

