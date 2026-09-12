import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exponential beats linear, in the form the bootstrap consumes

Bowditch's proof of the guessing-geodesics criterion closes by one instantiation
of a self-applied recursion, and what makes that instantiation legal is a growth
comparison: the dyadic bound of `GGT/GuessingGeodesicsSubdivision.lean` is
logarithmic in the scale, so beyond some radius it is smaller than the scale
itself.  This module is that comparison and nothing else, so it is pure
arithmetic and imports no geometry.

## Two shapes, and why both

`exists_forall_lin_lt_pow` is the clean statement --- `c * u + d < 2 ^ u` for all
large `u` --- and is proved by a doubling induction seeded at `c + d + 2`, the
seed itself needing `N² + 3N < 4 · 2 ^ N`.

`exists_radius_log_lt` is the shape the contradiction step actually uses, where
the scale is `m` rather than the exponent.  The passage between them is
Mathlib's `Nat.log`: `Nat.pow_log_le_self` puts `2 ^ log₂ m` below `m`, and
`Nat.le_log_of_pow_le` turns the radius `2 ^ U` into the hypothesis `U ≤ log₂ m`.

**A logarithm appears here and in no statement of the build.**  The convention
of `GGT/GuessingGeodesicsSubdivision.lean` --- carry the exponent, never
`Nat.log2` --- is about what the subdivision bound says; inside a proof
`Nat.log` is simply the cheapest way to name a near-minimal exponent, and the
alternative, a `Nat.find` on minimality, costs more and reads worse.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

/-! ## Two elementary bounds -/

/-- **`u + 1 ≤ 2 ^ u`.** -/
theorem succ_le_two_pow : ∀ u : ℕ, u + 1 ≤ 2 ^ u := by
  intro u
  induction u with
  | zero => norm_num
  | succ u ih =>
      have h1 : 1 ≤ 2 ^ u := Nat.one_le_pow u 2 (by norm_num)
      have h2 : 2 ^ (u + 1) = 2 ^ u + 2 ^ u := by ring
      omega

/-- **`N² + 3N < 4 · 2 ^ N`**, the seed of the doubling induction below. -/
theorem sq_add_lt_four_mul_two_pow : ∀ N : ℕ, N * N + 3 * N < 4 * 2 ^ N := by
  intro N
  induction N with
  | zero => norm_num
  | succ N ih =>
      have h1 := succ_le_two_pow N
      have h2 : 2 ^ (N + 1) = 2 ^ N + 2 ^ N := by ring
      have h3 : (N + 1) * (N + 1) + 3 * (N + 1) = N * N + 3 * N + (2 * N + 4) := by
        ring
      omega

/-! ## The comparison -/

/-- **Every linear function is eventually below `2 ^ u`.**

Doubling induction from `U = c + d + 2`.  At the seed the linear value is at
most `N² + 3N` with `N = c + d`, and `2 ^ U = 4 · 2 ^ N`; past it each step adds
`c` on the left and doubles on the right, and `c ≤ 2 ^ u` because `c ≤ u`. -/
theorem exists_forall_lin_lt_pow (c d : ℕ) :
    ∃ U : ℕ, ∀ u : ℕ, U ≤ u → c * u + d < 2 ^ u := by
  refine ⟨c + d + 2, ?_⟩
  have key : ∀ j : ℕ, c * (c + d + 2 + j) + d < 2 ^ (c + d + 2 + j) := by
    intro j
    induction j with
    | zero =>
        simp only [Nat.add_zero]
        have hquad := sq_add_lt_four_mul_two_pow (c + d)
        have hle : c * (c + d + 2) + d ≤ (c + d) * (c + d) + 3 * (c + d) :=
          calc c * (c + d + 2) + d
              ≤ (c + d) * (c + d + 2) + (c + d) :=
                Nat.add_le_add
                  (Nat.mul_le_mul (Nat.le_add_right c d) (le_refl (c + d + 2)))
                  (Nat.le_add_left d c)
            _ = (c + d) * (c + d) + 3 * (c + d) := by ring
        have hpow : 2 ^ (c + d + 2) = 4 * 2 ^ (c + d) := by ring
        omega
    | succ j ih =>
        have h1 := succ_le_two_pow (c + d + 2 + j)
        have h2 : 2 ^ (c + d + 2 + (j + 1)) = 2 ^ (c + d + 2 + j) + 2 ^ (c + d + 2 + j) := by
          ring
        have h3 : c * (c + d + 2 + (j + 1)) = c * (c + d + 2 + j) + c := by ring
        omega
  intro u hu
  have hj : c + d + 2 + (u - (c + d + 2)) = u := by omega
  have h := key (u - (c + d + 2))
  rwa [hj] at h

/-- **The comparison at the scale rather than the exponent.**

Beyond the radius `2 ^ U` the logarithmic bound is below the scale.  This is the
hypothesis the one-shot contradiction of the bootstrap is instantiated at. -/
theorem exists_radius_log_lt (c d : ℕ) :
    ∃ r : ℕ, ∀ m : ℕ, r < m → c * (Nat.log 2 m + 1) + d < m := by
  obtain ⟨U, hU⟩ := exists_forall_lin_lt_pow c (c + d)
  refine ⟨2 ^ U, ?_⟩
  intro m hm
  have hpos : 0 < 2 ^ U := Nat.one_le_pow U 2 (by norm_num)
  have hm0 : m ≠ 0 := by omega
  have hlog : U ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by norm_num) (le_of_lt hm)
  have hkey := hU (Nat.log 2 m) hlog
  have hself : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hm0
  have hexp : c * (Nat.log 2 m + 1) + d = c * Nat.log 2 m + (c + d) := by ring
  omega

end OsinEnlargement
end GGT
end GroupApproximation
