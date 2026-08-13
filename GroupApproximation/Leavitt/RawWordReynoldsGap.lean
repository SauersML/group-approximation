import Mathlib.Tactic

/-!
# The dimension-free telescope behind the raw-word Reynolds gap

The compiled raw source word differs from its classically folded word in
exactly twelve `H`-letters.  This file formalizes the analytic mechanism used
to replace them: in any monoid with a bi-invariant distance satisfying the
triangle inequality, the distance between two equal-length products is at
most the sum of the letterwise distances.

The matrix application takes `d` to be normalized Hilbert--Schmidt distance
on unitaries.  Left and right multiplication by unitaries preserve that
distance, so twelve `H`-covariance replacements cost at most `12 * Delta_H`.
-/

namespace GroupApproximation

/-- A noncommutative product telescope for any explicitly bi-invariant
distance.  The distance is supplied as data so this applies directly to the
normalized Hilbert--Schmidt distance, which is not installed as the ambient
metric on matrices. -/
theorem list_prod_distance_le_sum {A : Type*} [Monoid A]
    (d : A → A → ℝ)
    (d_one : d 1 1 = 0)
    (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (mul_left : ∀ a x y, d (a * x) (a * y) = d x y)
    (mul_right : ∀ x y a, d (x * a) (y * a) = d x y) :
    ∀ xs ys : List A, xs.length = ys.length →
      d xs.prod ys.prod ≤ (xs.zipWith d ys).sum := by
  intro xs
  induction xs with
  | nil =>
      intro ys hlength
      cases ys with
      | nil => simpa using le_of_eq d_one
      | cons y ys => simp at hlength
  | cons x xs ih =>
      intro ys hlength
      cases ys with
      | nil => simp at hlength
      | cons y ys =>
          have htail : xs.length = ys.length := by simpa using hlength
          calc
            d ((x :: xs).prod) ((y :: ys).prod) ≤
                d (x * xs.prod) (x * ys.prod) +
                  d (x * ys.prod) (y * ys.prod) := by
                    simpa using triangle (x * xs.prod) (x * ys.prod)
                      (y * ys.prod)
            _ = d xs.prod ys.prod + d x y := by
                  rw [mul_left, mul_right]
            _ ≤ (xs.zipWith d ys).sum + d x y := by
                  linarith [ih ys htail]
            _ = ((x :: xs).zipWith d (y :: ys)).sum := by simp [add_comm]

/-- The exact arithmetic conversion used after the twelve-letter telescope. -/
theorem raw_word_forces_H_gap {epsilon delta : ℝ}
    (h : Real.sqrt 2 ≤ epsilon + 12 * delta) :
    (Real.sqrt 2 - epsilon) / 12 ≤ delta := by
  linarith

/-- At zero residual word error, the raw-word gap and Reynolds identity give
the explicit squared deficit `1/24192`. -/
theorem raw_word_forces_Reynolds_deficit {delta deficit : ℝ}
    (hdelta : Real.sqrt 2 ≤ 12 * delta)
    (hdeficit : delta ^ 2 / 336 ≤ deficit) :
    (1 : ℝ) / 24192 ≤ deficit := by
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hdelta_nonneg : 0 ≤ delta := by
    have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    linarith
  have hsquare : 2 ≤ 144 * delta ^ 2 := by
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg 2)
      (by positivity : 0 ≤ 12 * delta)).2 hdelta
    nlinarith
  calc
    (1 : ℝ) / 24192 = ((1 : ℝ) / 72) / 336 := by norm_num
    _ ≤ delta ^ 2 / 336 := by
      gcongr
      nlinarith
    _ ≤ deficit := hdeficit

end GroupApproximation
