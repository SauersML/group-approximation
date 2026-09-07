import GroupApproximation.Leavitt.Leavitt

/-!
# One-sided inverses and their complementary idempotent

`non_mf_groups_exist.tex`, Section `sec:one-sided-inverses`.  The proof of
Theorem `thm:full-defect-ring` opens with

> Write `e = 1 - st`.  Then `e² = e`, `es = te = 0`, and there are finitely
> many `a_j, b_j ∈ R` with `∑_j a_j e b_j = 1`.

This module carries the first two sentences over an arbitrary unital ring.  The
data is a bare pair `t s = 1` — the compressor of Theorem
`thm:full-defect-ring` uses nothing else, and in particular no Leavitt family,
no characteristic assumption and no ideal condition on `1 - st`.  The ideal
condition (fullness of `e`) enters only in
`GroupApproximation.Leavitt.FullIdempotentNormalGeneration`.

Besides the four relations `e² = e`, `e s = 0`, `t e = 0`, `e + st = 1`, the
module records the telescoping identities

  `s²t² = 1 - e - set`,  `s³t³ = 1 - e - set - s²et²`,

whose consequence `e + set + s²et² + s³t³ = 1` is the last diagonal entry of the
printed inverse matrix `u⁻¹` of the rank-four compressor.

A binary Leavitt family supplies such a pair through `ofLeavittFamily`, with
`e = p₁ = s₁t₁`; that is the only bridge the Leavitt specialisation needs.
-/

namespace GroupApproximation
namespace OneSidedCompressor

/-- A one-sided inverse pair in a unital ring: `t s = 1`, with `s t` in general
different from `1`.  This is the entire hypothesis the compressor of
Theorem `thm:full-defect-ring` runs on. -/
structure OneSidedInverse (R : Type*) [Ring R] where
  /-- The section `s`. -/
  s : R
  /-- The retraction `t`. -/
  t : R
  /-- The single defining relation `t s = 1`. -/
  t_mul_s : t * s = 1

namespace OneSidedInverse

variable {R : Type*} [Ring R] (P : OneSidedInverse R)

/-- The complementary idempotent `e = 1 - s t` of the printed proof. -/
def e : R := 1 - P.s * P.t

theorem e_eq : P.e = 1 - P.s * P.t := rfl

@[simp] theorem e_add_st : P.e + P.s * P.t = 1 := by
  rw [e_eq]
  abel

theorem s_mul_t : P.s * P.t = 1 - P.e := by
  rw [e_eq]
  abel

@[simp] theorem e_mul_s : P.e * P.s = 0 := by
  rw [e_eq, sub_mul, one_mul, mul_assoc, P.t_mul_s, mul_one, sub_self]

@[simp] theorem t_mul_e : P.t * P.e = 0 := by
  rw [e_eq, mul_sub, mul_one, ← mul_assoc, P.t_mul_s, one_mul, sub_self]

@[simp] theorem e_mul_e : P.e * P.e = P.e := by
  have h : P.e * (1 - P.s * P.t) = P.e := by
    rw [mul_sub, mul_one, ← mul_assoc, P.e_mul_s, zero_mul, sub_zero]
  rw [← e_eq] at h
  exact h

/-- Every positive power of the retraction annihilates the idempotent. -/
theorem t_pow_mul_e (k : ℕ) : P.t ^ (k + 1) * P.e = 0 := by
  rw [pow_succ, mul_assoc, P.t_mul_e, mul_zero]

/-- The idempotent annihilates every positive power of the section. -/
theorem e_mul_s_pow (k : ℕ) : P.e * P.s ^ (k + 1) = 0 := by
  rw [pow_succ', ← mul_assoc, P.e_mul_s, zero_mul]

/-! ### The telescoping identities behind the printed inverse matrix -/

theorem s_sq_mul_t_sq :
    P.s * P.s * P.t * P.t = 1 - P.e - P.s * P.e * P.t := by
  have h := P.s_mul_t
  calc
    P.s * P.s * P.t * P.t = P.s * (P.s * P.t) * P.t := by noncomm_ring
    _ = P.s * (1 - P.e) * P.t := by rw [h]
    _ = P.s * P.t - P.s * P.e * P.t := by noncomm_ring
    _ = 1 - P.e - P.s * P.e * P.t := by rw [h]

theorem s_cube_mul_t_cube :
    P.s * P.s * P.s * P.t * P.t * P.t
      = 1 - P.e - P.s * P.e * P.t - P.s * P.s * P.e * P.t * P.t := by
  have h := P.s_mul_t
  have h2 := P.s_sq_mul_t_sq
  calc
    P.s * P.s * P.s * P.t * P.t * P.t
        = P.s * P.s * (P.s * P.t) * P.t * P.t := by noncomm_ring
    _ = P.s * P.s * (1 - P.e) * P.t * P.t := by rw [h]
    _ = P.s * P.s * P.t * P.t - P.s * P.s * P.e * P.t * P.t := by noncomm_ring
    _ = 1 - P.e - P.s * P.e * P.t - P.s * P.s * P.e * P.t * P.t := by
        rw [h2]

/-- The last diagonal entry of `u⁻¹ u` in the printed rank-four display. -/
theorem sum_four :
    P.e + P.s * P.e * P.t + P.s * P.s * P.e * P.t * P.t
      + P.s * P.s * P.s * P.t * P.t * P.t = 1 := by
  rw [P.s_cube_mul_t_cube]
  abel

end OneSidedInverse

/-! ### The Leavitt specialisation -/

section Leavitt

variable {A : Type*} [Ring A]

/-- A binary Leavitt family is in particular a one-sided inverse pair, through
its zeroth pair `t₀ s₀ = 1`. -/
def ofLeavittFamily (L : LeavittFamily A) : OneSidedInverse A :=
  ⟨L.s0, L.t0, L.t0_s0⟩

@[simp] theorem ofLeavittFamily_s (L : LeavittFamily A) :
    (ofLeavittFamily L).s = L.s0 := rfl

@[simp] theorem ofLeavittFamily_t (L : LeavittFamily A) :
    (ofLeavittFamily L).t = L.t0 := rfl

/-- The complementary idempotent of the zeroth Leavitt pair is the Leavitt
defect coefficient `p₁ = s₁t₁`. -/
theorem e_ofLeavittFamily (L : LeavittFamily A) :
    (ofLeavittFamily L).e = L.p1 := by
  have h1 : L.p0 + L.p1 = 1 := L.p0_add_p1
  have h0 : L.p0 = L.s0 * L.t0 := rfl
  show (1 : A) - L.s0 * L.t0 = L.p1
  rw [← h0, ← h1]
  abel

end Leavitt

end OneSidedCompressor
end GroupApproximation
