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

open scoped BigOperators

/-- The scalar arithmetic core of coproduct gauge pinning. If `weight` is a
probability vector and `defectSq` is twice one minus its weighted average of
the real coefficients, then one coefficient has squared basis distance at
most `defectSq`. Applied to the Fourier coefficients `c_i` of a unitary in a
finite group algebra, take `weight i = |c_i|^2` and
`realCoeff i = re (c_i)`. This is the finite maximum step in the
dimension-free estimate
`min_g ||C-lambda_g||_2 <= ||Delta C-C tensor C||_2`. -/
theorem exists_scalar_gauge_coefficient_distSq_le_defectSq
    {ι : Type*} [Fintype ι]
    (weight realCoeff : ι → ℝ) (defectSq : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hsum : ∑ i, weight i = 1)
    (hdefect : defectSq = 2 - 2 * ∑ i, weight i * realCoeff i) :
    ∃ i, 2 - 2 * realCoeff i ≤ defectSq := by
  classical
  have hnonempty : (Finset.univ : Finset ι).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.sum_empty] at hsum
    norm_num at hsum
  obtain ⟨i, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) realCoeff
      hnonempty
  have havg : (∑ j, weight j * realCoeff j) ≤ realCoeff i := by
    calc
      (∑ j, weight j * realCoeff j) ≤
          ∑ j, weight j * realCoeff i := by
            exact Finset.sum_le_sum fun j _ ↦
              mul_le_mul_of_nonneg_left
                (hmax j (Finset.mem_univ j)) (hweight j)
      _ = (∑ j, weight j) * realCoeff i := by
            rw [Finset.sum_mul]
      _ = realCoeff i := by rw [hsum, one_mul]
  refine ⟨i, ?_⟩
  rw [hdefect]
  linarith

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

/-- If two fourfold products which differ only by swapping their middle
factors are close to one common comparison point, bi-invariance removes the
outer factors and bounds the middle-factor commutator.  This is the metric
last step in the quantitative multiplicative-unitary classicalization
argument. -/
theorem middle_swap_distance_le_of_common_approximation
    {A : Type*} [Monoid A]
    (d : A → A → ℝ)
    (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (symm : ∀ x y, d x y = d y x)
    (mul_left : ∀ a x y, d (a * x) (a * y) = d x y)
    (mul_right : ∀ x y a, d (x * a) (y * a) = d x y)
    (p x y z t : A) (a b : ℝ)
    (h₁ : d p (x * y * z * t) ≤ a)
    (h₂ : d p (x * z * y * t) ≤ b) :
    d (y * z) (z * y) ≤ a + b := by
  have hprod : d (x * y * z * t) (x * z * y * t) ≤ a + b := by
    calc
      d (x * y * z * t) (x * z * y * t) ≤
          d (x * y * z * t) p + d p (x * z * y * t) :=
        triangle _ p _
      _ = d p (x * y * z * t) + d p (x * z * y * t) := by
        rw [symm]
      _ ≤ a + b := add_le_add h₁ h₂
  have hcancel :
      d (x * y * z * t) (x * z * y * t) = d (y * z) (z * y) := by
    calc
      d (x * y * z * t) (x * z * y * t) =
          d (x * (y * z) * t) (x * (z * y) * t) := by
            simp only [mul_assoc]
      _ = d (x * (y * z)) (x * (z * y)) := mul_right _ _ t
      _ = d (y * z) (z * y) := mul_left x _ _
  rw [hcancel] at hprod
  exact hprod

/-- The `3ε+6ε=9ε` specialization used by the five-leg
multiplicative-unitary comparison. -/
theorem middle_swap_distance_le_nine_mul
    {A : Type*} [Monoid A]
    (d : A → A → ℝ)
    (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (symm : ∀ x y, d x y = d y x)
    (mul_left : ∀ a x y, d (a * x) (a * y) = d x y)
    (mul_right : ∀ x y a, d (x * a) (y * a) = d x y)
    (p x y z t : A) (epsilon : ℝ)
    (h₁ : d p (x * y * z * t) ≤ 3 * epsilon)
    (h₂ : d p (x * z * y * t) ≤ 6 * epsilon) :
    d (y * z) (z * y) ≤ 9 * epsilon := by
  have h := middle_swap_distance_le_of_common_approximation
    d triangle symm mul_left mul_right p x y z t
    (3 * epsilon) (6 * epsilon) h₁ h₂
  linarith

/-- The asymmetric two-defect specialization used for an approximate
bi-corepresentation.  The two expansions cost `right + 2*left` and
`left + 2*right`, so the middle commutator costs
`3*(left+right)`. -/
theorem middle_swap_distance_le_three_mul_add
    {A : Type*} [Monoid A]
    (d : A → A → ℝ)
    (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (symm : ∀ x y, d x y = d y x)
    (mul_left : ∀ a x y, d (a * x) (a * y) = d x y)
    (mul_right : ∀ x y a, d (x * a) (y * a) = d x y)
    (p x y z t : A) (leftDefect rightDefect : ℝ)
    (h₁ : d p (x * y * z * t) ≤ rightDefect + 2 * leftDefect)
    (h₂ : d p (x * z * y * t) ≤ leftDefect + 2 * rightDefect) :
    d (y * z) (z * y) ≤ 3 * (leftDefect + rightDefect) := by
  have h := middle_swap_distance_le_of_common_approximation
    d triangle symm mul_left mul_right p x y z t
    (rightDefect + 2 * leftDefect)
    (leftDefect + 2 * rightDefect) h₁ h₂
  linarith

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

/-- The raw word uses only two distinct `H`-letters, eight copies of the
first and four of the second.  Cauchy--Schwarz converts tracial separation
into the sharper two-generator energy floor `1/40`. -/
theorem raw_word_forces_twoGenerator_energy {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hraw : Real.sqrt 2 ≤ 8 * a + 4 * b) :
    (1 : ℝ) / 40 ≤ a ^ 2 + b ^ 2 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsum : 0 ≤ 8 * a + 4 * b := by positivity
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg 2) hsum).2 hraw
  nlinarith [sq_nonneg (a - 2 * b)]

/-- Including the two named displacements in the full Reynolds energy sum
improves the explicit squared norm deficit to `1/13440`. -/
theorem raw_word_forces_sharp_Reynolds_deficit {a b deficit : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hraw : Real.sqrt 2 ≤ 8 * a + 4 * b)
    (hdeficit : (a ^ 2 + b ^ 2) / 336 ≤ deficit) :
    (1 : ℝ) / 13440 ≤ deficit := by
  have henergy : (1 : ℝ) / 40 ≤ a ^ 2 + b ^ 2 :=
    raw_word_forces_twoGenerator_energy ha hb hraw
  calc
    (1 : ℝ) / 13440 = ((1 : ℝ) / 40) / 336 := by norm_num
    _ ≤ (a ^ 2 + b ^ 2) / 336 := by gcongr
    _ ≤ deficit := hdeficit

/-- Averaging over the six-element subgroup generated by the two raw
`H`-letters yields the stronger localized conditional-expectation deficit
`1/480`. -/
theorem raw_word_forces_S3_Reynolds_deficit {a b deficit : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hraw : Real.sqrt 2 ≤ 8 * a + 4 * b)
    (hdeficit : (a ^ 2 + b ^ 2) / 12 ≤ deficit) :
    (1 : ℝ) / 480 ≤ deficit := by
  have henergy : (1 : ℝ) / 40 ≤ a ^ 2 + b ^ 2 :=
    raw_word_forces_twoGenerator_energy ha hb hraw
  calc
    (1 : ℝ) / 480 = ((1 : ℝ) / 40) / 12 := by norm_num
    _ ≤ (a ^ 2 + b ^ 2) / 12 := by gcongr
    _ ≤ deficit := hdeficit

end GroupApproximation
