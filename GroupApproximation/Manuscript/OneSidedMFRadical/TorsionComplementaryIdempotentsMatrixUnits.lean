import GroupApproximation.Leavitt.OneSidedInverse
import GroupApproximation.Meta.AxiomGuard

/-!
# The matrix units `f_{ij} = s^i e t^j` of `prop:torsion-defect-ring`

`non_mf_groups_exist.tex`, Proposition `prop:torsion-defect-ring` (torsion
complementary idempotents), the opening of its proof:

> Put `f_{ij} = s^i e t^j`.  Since `es = te = 0`, `f_{ij}f_{kl} = δ_{jk}f_{il}`,
> so `f_{ij}^2 = 0` for `i ≠ j`.

Everything here is ring theory over a bare one-sided inverse pair `ts = 1`
(`OneSidedCompressor.OneSidedInverse`).  The complementary idempotent
`e = 1 - st` is not assumed nonzero, not assumed full, and not assumed to have
finite additive order; the torsion hypothesis enters only through
`nsmul_fUnit`, which propagates `m • e = 0` to every `f_{ij}`, and through
`one_add_pow_of_sq_zero`, which is the printed `z^m = D(1 + m f_{12})`.

The family `f_{ij}` is a system of matrix units *without* a unit: the
idempotents `f_{ii}` are orthogonal and each `f_{ij}` transports `f_{jj}` to
`f_{ii}`, but `∑_i f_{ii}` is not `1` and the family is infinite.  That is all
the proof of `prop:torsion-defect-ring` uses, and it is exactly what
`fUnit_mul` says.

The last printed identity of the module, `t f_{12} s^2 = e`, is the printed
reason `z ≠ 1`:

> and `z ≠ 1` because `t f_{12} s^2 = e ≠ 0`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TorsionComplementaryIdempotents

open GroupApproximation.OneSidedCompressor

universe u

variable {R : Type u} [Ring R]

/-! ## Powers of a one-sided inverse pair -/

namespace OneSidedInverse

variable (P : OneSidedInverse R)

/-- `t^k s^k = 1` for every `k`: the single relation `ts = 1`, iterated. -/
theorem t_pow_mul_s_pow (k : ℕ) : P.t ^ k * P.s ^ k = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc P.t P.s, P.t_mul_s, one_mul,
        ih]

end OneSidedInverse

/-! ## The printed family `f_{ij} = s^i e t^j` -/

/-- **Printed:** `f_{ij} = s^i e t^j`. -/
def fUnit (P : OneSidedInverse R) (i j : ℕ) : R := P.s ^ i * P.e * P.t ^ j

theorem fUnit_def (P : OneSidedInverse R) (i j : ℕ) :
    fUnit P i j = P.s ^ i * P.e * P.t ^ j := rfl

@[simp] theorem fUnit_zero_zero (P : OneSidedInverse R) : fUnit P 0 0 = P.e := by
  simp [fUnit]

/-- The core computation behind `f_{ij}f_{kl} = δ_{jk}f_{il}`: the idempotent
`e` absorbs `t^j s^k` exactly when `j = k`, because `t^j s^j = 1` while
`e s = 0` and `t e = 0` kill the two unbalanced cases. -/
theorem e_tpow_mul_spow_e (P : OneSidedInverse R) (j k : ℕ) :
    P.e * P.t ^ j * (P.s ^ k * P.e) = if j = k then P.e else 0 := by
  rcases lt_trichotomy j k with h | h | h
  · obtain ⟨d, hd⟩ : ∃ d, k = j + (d + 1) := ⟨k - j - 1, by omega⟩
    subst hd
    rw [if_neg (by omega)]
    calc P.e * P.t ^ j * (P.s ^ (j + (d + 1)) * P.e)
        = P.e * (P.t ^ j * P.s ^ j) * (P.s ^ (d + 1) * P.e) := by
          rw [pow_add]; noncomm_ring
      _ = P.e * P.s ^ (d + 1) * P.e := by
          rw [OneSidedInverse.t_pow_mul_s_pow P j]; noncomm_ring
      _ = 0 := by rw [P.e_mul_s_pow d, zero_mul]
  · subst h
    rw [if_pos rfl]
    calc P.e * P.t ^ j * (P.s ^ j * P.e)
        = P.e * (P.t ^ j * P.s ^ j) * P.e := by noncomm_ring
      _ = P.e * P.e := by rw [OneSidedInverse.t_pow_mul_s_pow P j, mul_one]
      _ = P.e := P.e_mul_e
  · obtain ⟨d, hd⟩ : ∃ d, j = (d + 1) + k := ⟨j - k - 1, by omega⟩
    subst hd
    rw [if_neg (by omega)]
    calc P.e * P.t ^ ((d + 1) + k) * (P.s ^ k * P.e)
        = P.e * P.t ^ (d + 1) * (P.t ^ k * P.s ^ k) * P.e := by
          rw [pow_add]; noncomm_ring
      _ = P.e * (P.t ^ (d + 1) * P.e) := by
          rw [OneSidedInverse.t_pow_mul_s_pow P k, mul_one]; noncomm_ring
      _ = 0 := by rw [P.t_pow_mul_e d, mul_zero]

/-- **The printed multiplication rule `f_{ij}f_{kl} = δ_{jk}f_{il}`.** -/
theorem fUnit_mul (P : OneSidedInverse R) (i j k l : ℕ) :
    fUnit P i j * fUnit P k l = if j = k then fUnit P i l else 0 := by
  have expand : fUnit P i j * fUnit P k l
      = P.s ^ i * (P.e * P.t ^ j * (P.s ^ k * P.e)) * P.t ^ l := by
    simp only [fUnit]; noncomm_ring
  rw [expand, e_tpow_mul_spow_e P j k]
  by_cases hjk : j = k
  · rw [if_pos hjk, if_pos hjk, fUnit]
  · rw [if_neg hjk, if_neg hjk, mul_zero, zero_mul]

/-- The printed `f_{ij}^2 = 0` for `i ≠ j`. -/
theorem fUnit_mul_self (P : OneSidedInverse R) {i j : ℕ} (hij : i ≠ j) :
    fUnit P i j * fUnit P i j = 0 := by
  rw [fUnit_mul, if_neg (Ne.symm hij)]

/-- `f_{ij}f_{kl} = f_{il}` in the matching case. -/
theorem fUnit_mul_of_eq (P : OneSidedInverse R) (i j l : ℕ) :
    fUnit P i j * fUnit P j l = fUnit P i l := by
  rw [fUnit_mul, if_pos rfl]

/-- `f_{ij}f_{kl} = 0` in the non-matching case. -/
theorem fUnit_mul_of_ne (P : OneSidedInverse R) (i l : ℕ) {j k : ℕ}
    (h : j ≠ k) : fUnit P i j * fUnit P k l = 0 := by
  rw [fUnit_mul, if_neg h]

/-! ## The torsion hypothesis, propagated -/

/-- If `m e = 0` then `m f_{ij} = 0` for every `i, j`: the printed proof needs
this only at `f_{12}`, where it gives `z^m = D(1 + m f_{12}) = 1`. -/
theorem nsmul_fUnit (P : OneSidedInverse R) {m : ℕ} (h : m • P.e = 0)
    (i j : ℕ) : m • fUnit P i j = 0 := by
  rw [fUnit, ← smul_mul_assoc, ← mul_smul_comm, h, mul_zero, zero_mul]

/-- **Printed:** `z^m = D(1 + m f_{12})`, at the level of the ring: a square-zero
element makes `(1 + x)^m = 1 + m x`. -/
theorem one_add_pow_of_sq_zero {x : R} (hx : x * x = 0) (m : ℕ) :
    (1 + x) ^ m = 1 + m • x := by
  induction m with
  | zero => simp
  | succ k ih =>
      have h : (k • x) * x = 0 := by rw [smul_mul_assoc, hx, smul_zero]
      have hstep : (1 + k • x) * (1 + x) = 1 + (k • x + x) := by
        rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, h]
        abel
      rw [pow_succ, ih, hstep, succ_nsmul]

/-! ## The printed reason `z ≠ 1` -/

/-- **Printed:** `t f_{12} s^2 = e`.  So `f_{12} = 0` forces `e = 0`, which is
the printed reason that `z = D(1 + f_{12})` is not the identity. -/
theorem t_mul_fUnit_one_two_mul_s_sq (P : OneSidedInverse R) :
    P.t * fUnit P 1 2 * P.s ^ 2 = P.e := by
  calc P.t * fUnit P 1 2 * P.s ^ 2
      = (P.t * P.s) * P.e * (P.t ^ 2 * P.s ^ 2) := by
        simp only [fUnit, pow_one]; noncomm_ring
    _ = P.e := by
        rw [P.t_mul_s, OneSidedInverse.t_pow_mul_s_pow P 2, one_mul, mul_one]

/-- The printed contrapositive: `f_{12} = 0` only when `e = 0`. -/
theorem fUnit_one_two_ne_zero (P : OneSidedInverse R) (he : P.e ≠ 0) :
    fUnit P 1 2 ≠ 0 := by
  intro h
  apply he
  rw [← t_mul_fUnit_one_two_mul_s_sq P, h, mul_zero, zero_mul]

end TorsionComplementaryIdempotents
end OneSidedMFRadical
end Manuscript
end GroupApproximation
