import GroupApproximation.XCVWitness.IdealDetection

/-!
# Kishimoto's condition gives ideal detection

`CovariantExpectation C D` packages the data of a reduced crossed product `D = C ⋊ ℤ` that the
simplicity argument uses:
* the coefficient inclusion `ι : C →⋆ₐ[ℂ] D` and the implementing unitary `u`;
* a contractive, faithful linear map `E : D → C` with `E (ι c) = c` and `E (ι c · uⁿ) = 0` for
  `n ≠ 0` (the expectation onto the zeroth Fourier coefficient);
* density of the finite Fourier sums `ι b₀ + ∑ₙ ι bₙ · uⁿ`.

`KishimotoCondition` is the outerness condition in the form the proof consumes. Any finite
Fourier sum can be compressed by a contraction `f ∈ C` so that the zeroth coefficient keeps its
norm and the other coefficients become small.

`detectsIdeals_of_kishimoto` turns the condition into `DetectsIdeals ι`. Then
`isSimpleCStar_of_kishimoto` shows a simple coefficient algebra gives a simple crossed product.
-/

namespace GroupApproximation
namespace XCVWitness

/-- Conditional-expectation data of a reduced crossed product `D = C ⋊ ℤ`. -/
structure CovariantExpectation (C D : Type*) [CStarAlgebra C] [CStarAlgebra D] where
  /-- The coefficient inclusion. -/
  ι : C →⋆ₐ[ℂ] D
  /-- The unitary implementing the automorphism. -/
  u : unitary D
  /-- The expectation onto the zeroth Fourier coefficient. -/
  expect : D →ₗ[ℂ] C
  norm_expect_le : ∀ x, ‖expect x‖ ≤ ‖x‖
  expect_faithful : ∀ a : D, expect (star a * a) = 0 → a = 0
  expect_coeff : ∀ c : C, expect (ι c) = c
  expect_coeff_zpow : ∀ (n : ℤ) (c : C), n ≠ 0 → expect (ι c * ((u ^ n : unitary D) : D)) = 0
  dense : ∀ (x : D) (ε : ℝ), 0 < ε → ∃ (b₀ : C) (s : Finset ℤ) (b : ℤ → C),
    (∀ n ∈ s, n ≠ 0) ∧ ‖x - (ι b₀ + ∑ n ∈ s, ι (b n) * ((u ^ n : unitary D) : D))‖ ≤ ε

variable {C D : Type*} [CStarAlgebra C] [CStarAlgebra D]

/-- Kishimoto's condition: a contraction `f` compresses any finite Fourier sum so that the zeroth
coefficient keeps its norm up to `ε` and every other coefficient drops below `ε`. -/
def KishimotoCondition (P : CovariantExpectation C D) : Prop :=
  ∀ (b₀ : C) (s : Finset ℤ) (b : ℤ → C) (ε : ℝ), 0 < ε → (∀ n ∈ s, n ≠ 0) →
    ∃ f : C, ‖f‖ ≤ 1 ∧ ‖b₀‖ ≤ ‖star f * b₀ * f‖ + ε ∧
      ∀ n ∈ s, ‖P.ι (star f) * (P.ι (b n) * ((P.u ^ n : unitary D) : D)) * P.ι f‖ ≤ ε

/-- Compression by a contraction does not increase the norm. -/
theorem norm_star_mul_mul_le {A : Type*} [CStarAlgebra A] {f : A} (hf : ‖f‖ ≤ 1) (z : A) :
    ‖star f * z * f‖ ≤ ‖z‖ := by
  have h1 : ‖star f‖ ≤ 1 := by rw [norm_star]; exact hf
  calc ‖star f * z * f‖ ≤ ‖star f * z‖ * ‖f‖ := norm_mul_le _ _
    _ ≤ ‖star f * z‖ * 1 := mul_le_mul_of_nonneg_left hf (norm_nonneg _)
    _ = ‖star f * z‖ := mul_one _
    _ ≤ ‖star f‖ * ‖z‖ := norm_mul_le _ _
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖z‖ := one_mul _

namespace CovariantExpectation

variable (P : CovariantExpectation C D)

/-- The expectation of a finite Fourier sum is its zeroth coefficient. -/
theorem expect_fourier (b₀ : C) (s : Finset ℤ) (b : ℤ → C) (hs : ∀ n ∈ s, n ≠ 0) :
    P.expect (P.ι b₀ + ∑ n ∈ s, P.ι (b n) * ((P.u ^ n : unitary D) : D)) = b₀ := by
  have h0 : ∑ n ∈ s, P.expect (P.ι (b n) * ((P.u ^ n : unitary D) : D)) = 0 :=
    Finset.sum_eq_zero fun n hn => P.expect_coeff_zpow n (b n) (hs n hn)
  rw [map_add, map_sum, P.expect_coeff, h0, add_zero]

theorem norm_ι_le (c : C) : ‖P.ι c‖ ≤ ‖c‖ := NonUnitalStarAlgHom.norm_apply_le P.ι c

/-- Model test: `ℂ` carries no such structure over `ℂ`; the unitary is a scalar, so the
expectation of `ι 1 · u` is `u ≠ 0`. -/
theorem not_complex (P : CovariantExpectation ℂ ℂ) : False := by
  have h := P.expect_coeff_zpow 1 1 one_ne_zero
  rw [zpow_one, map_one, one_mul] at h
  have h1 : P.expect 1 = 1 := by simpa using P.expect_coeff 1
  have hu : ((P.u : ℂ)) = (P.u : ℂ) • (1 : ℂ) := by rw [smul_eq_mul, mul_one]
  rw [hu, map_smul, h1, smul_eq_mul, mul_one] at h
  have h2 := Unitary.coe_mul_star_self P.u
  rw [h, zero_mul] at h2
  exact zero_ne_one h2

end CovariantExpectation

/-- **Kishimoto's condition gives ideal detection.** -/
theorem detectsIdeals_of_kishimoto (P : CovariantExpectation C D) (hK : KishimotoCondition P) :
    DetectsIdeals P.ι := by
  intro a ha
  refine ⟨P.expect (star a * a), fun hd => ha (P.expect_faithful a hd), fun ε hε => ?_⟩
  obtain ⟨b₀, s, b, hs, hy⟩ := P.dense (star a * a) (ε / 4) (by linarith)
  obtain ⟨S, hS⟩ : ∃ S : D, S = ∑ n ∈ s, P.ι (b n) * ((P.u ^ n : unitary D) : D) := ⟨_, rfl⟩
  rw [← hS] at hy
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε / 4 / (s.card + 1) := ⟨_, rfl⟩
  have hcard0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have hηpos : 0 < η := by rw [hη]; exact div_pos (by linarith) (by linarith)
  have hηle : η ≤ ε / 4 := by
    rw [hη]; exact div_le_self (by linarith) (by linarith)
  have hcard : (s.card : ℝ) * η ≤ ε / 4 := by
    have hpos : (0 : ℝ) < s.card + 1 := by linarith
    calc (s.card : ℝ) * η = ε / 4 * (s.card / (s.card + 1)) := by rw [hη]; ring
      _ ≤ ε / 4 * 1 :=
        mul_le_mul_of_nonneg_left ((div_le_one₀ hpos).2 (by linarith)) (by linarith)
      _ = ε / 4 := mul_one _
  obtain ⟨f, hf1, hf0, hfn⟩ := hK b₀ s b η hηpos hs
  have hιf : ‖P.ι f‖ ≤ 1 := (P.norm_ι_le f).trans hf1
  have hEy : P.expect (P.ι b₀ + S) = b₀ := by rw [hS]; exact P.expect_fourier b₀ s b hs
  have hbd : ‖b₀ - P.expect (star a * a)‖ ≤ ε / 4 := by
    calc ‖b₀ - P.expect (star a * a)‖ = ‖P.expect (P.ι b₀ + S - star a * a)‖ := by
          rw [map_sub, hEy]
      _ ≤ ‖P.ι b₀ + S - star a * a‖ := P.norm_expect_le _
      _ = ‖star a * a - (P.ι b₀ + S)‖ := norm_sub_rev _ _
      _ ≤ ε / 4 := hy
  have hsum : ‖P.ι (star f) * S * P.ι f‖ ≤ ε / 4 := by
    rw [hS, Finset.mul_sum, Finset.sum_mul]
    refine le_trans (norm_sum_le _ _) (le_trans ?_ hcard)
    have h := Finset.sum_le_card_nsmul s _ η fun n hn => hfn n hn
    rwa [nsmul_eq_mul] at h
  refine ⟨star f, f, ?_, ?_⟩
  · have hsplit : P.ι (star f) * (star a * a) * P.ι f - P.ι (star f * P.expect (star a * a) * f) =
        P.ι (star f) * (star a * a - (P.ι b₀ + S)) * P.ι f
          + P.ι (star f * (b₀ - P.expect (star a * a)) * f) + P.ι (star f) * S * P.ι f := by
      simp only [map_mul, map_sub, mul_sub, sub_mul, mul_add, add_mul]
      abel
    have h1 : ‖P.ι (star f) * (star a * a - (P.ι b₀ + S)) * P.ι f‖ ≤ ε / 4 := by
      rw [map_star]
      exact (norm_star_mul_mul_le hιf _).trans hy
    have h2 : ‖P.ι (star f * (b₀ - P.expect (star a * a)) * f)‖ ≤ ε / 4 :=
      ((P.norm_ι_le _).trans (norm_star_mul_mul_le hf1 _)).trans hbd
    rw [hsplit]
    refine norm_add₃_le.trans ?_
    linarith
  · have hsplit₀ : star f * b₀ * f =
        star f * P.expect (star a * a) * f + star f * (b₀ - P.expect (star a * a)) * f := by
      simp only [mul_sub, sub_mul]
      abel
    have h4 : ‖star f * b₀ * f‖ ≤ ‖star f * P.expect (star a * a) * f‖ + ε / 4 := by
      rw [hsplit₀]
      linarith [norm_add_le (star f * P.expect (star a * a) * f)
        (star f * (b₀ - P.expect (star a * a)) * f),
        norm_star_mul_mul_le hf1 (b₀ - P.expect (star a * a))]
    have h5 := norm_sub_norm_le (P.expect (star a * a)) b₀
    rw [norm_sub_rev] at h5
    linarith

/-- **Kishimoto's condition and a simple coefficient algebra give a simple crossed product.** -/
theorem isSimpleCStar_of_kishimoto [Nontrivial D] (hC : IsSimpleCStar C)
    (P : CovariantExpectation C D) (hK : KishimotoCondition P) : IsSimpleCStar D :=
  isSimpleCStar_of_detectsIdeals hC P.ι (detectsIdeals_of_kishimoto P hK)

end XCVWitness
end GroupApproximation
