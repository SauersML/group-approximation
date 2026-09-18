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

