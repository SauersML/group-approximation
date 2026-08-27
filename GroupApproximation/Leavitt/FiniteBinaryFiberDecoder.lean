import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
# Majority decoding on binary extension fibers

For one coarse source atom, let `m₀,m₁` be the masses of the two raw branch
labels among its extension atoms.  The optimal deterministic decoder makes
error `min m₀ m₁`.  Two conditionally independent samples from the same
fiber disagree with mass

`2 m₀ m₁ / (m₀ + m₁)`.

These quantities differ by at most a factor of two.  Thus vanishing
conditional branch variance is exactly the finite scalar estimate needed to
make the raw branch label a deterministic function of the coarse source
character, without selecting a fixed-rank fiber.
-/

namespace GroupApproximation
namespace FiniteBinaryFiberDecoder

noncomputable section

/-- Error mass of the fiberwise majority decoder. -/
def majorityError (m₀ m₁ : ℝ) : ℝ :=
  if m₁ ≤ m₀ then m₁ else m₀

/-- Mass of disagreement between two conditionally independent branch
samples from one fiber.  A zero-mass fiber contributes zero. -/
def pairDisagreementMass (m₀ m₁ : ℝ) : ℝ :=
  if m₀ + m₁ = 0 then 0 else 2 * m₀ * m₁ / (m₀ + m₁)

/-- Conditional variance of the branch-one indicator on one fiber. -/
def conditionalVariance (m₀ m₁ : ℝ) : ℝ :=
  if m₀ + m₁ = 0 then 0 else m₀ * m₁ / (m₀ + m₁)

theorem majorityError_eq_min (m₀ m₁ : ℝ) :
    majorityError m₀ m₁ = min m₀ m₁ := by
  by_cases h : m₁ ≤ m₀
  · simp [majorityError, h]
  · have h' : m₀ ≤ m₁ := le_of_not_ge h
    simp [majorityError, h, min_eq_left h']

theorem pairDisagreementMass_eq_two_mul_conditionalVariance
    (m₀ m₁ : ℝ) :
    pairDisagreementMass m₀ m₁ = 2 * conditionalVariance m₀ m₁ := by
  by_cases h : m₀ + m₁ = 0
  · simp [pairDisagreementMass, conditionalVariance, h]
  · simp only [pairDisagreementMass, conditionalVariance, if_neg h]
    ring

/-- The majority error is no larger than the conditional two-copy
disagreement mass. -/
theorem majorityError_le_pairDisagreementMass
    (m₀ m₁ : ℝ) (h₀ : 0 ≤ m₀) (h₁ : 0 ≤ m₁) :
    majorityError m₀ m₁ ≤ pairDisagreementMass m₀ m₁ := by
  rw [majorityError_eq_min]
  by_cases hsum : m₀ + m₁ = 0
  · have hm₀ : m₀ = 0 := by nlinarith
    have hm₁ : m₁ = 0 := by nlinarith
    simp [pairDisagreementMass, hm₀, hm₁]
  · have hpos : 0 < m₀ + m₁ :=
      lt_of_le_of_ne (add_nonneg h₀ h₁) (Ne.symm hsum)
    rw [pairDisagreementMass, if_neg hsum, le_div_iff₀ hpos]
    rcases le_total m₀ m₁ with hle | hle
    · rw [min_eq_left hle]
      have haux : 0 ≤ m₀ * (m₁ - m₀) :=
        mul_nonneg h₀ (sub_nonneg.mpr hle)
      nlinarith
    · rw [min_eq_right hle]
      have haux : 0 ≤ m₁ * (m₀ - m₁) :=
        mul_nonneg h₁ (sub_nonneg.mpr hle)
      nlinarith

/-- Conditional two-copy disagreement is at most twice the majority error. -/
theorem pairDisagreementMass_le_two_mul_majorityError
    (m₀ m₁ : ℝ) (h₀ : 0 ≤ m₀) (h₁ : 0 ≤ m₁) :
    pairDisagreementMass m₀ m₁ ≤ 2 * majorityError m₀ m₁ := by
  rw [majorityError_eq_min]
  by_cases hsum : m₀ + m₁ = 0
  · have hm₀ : m₀ = 0 := by nlinarith
    have hm₁ : m₁ = 0 := by nlinarith
    simp [pairDisagreementMass, hm₀, hm₁]
  · have hpos : 0 < m₀ + m₁ :=
      lt_of_le_of_ne (add_nonneg h₀ h₁) (Ne.symm hsum)
    rw [pairDisagreementMass, if_neg hsum, div_le_iff₀ hpos]
    rcases le_total m₀ m₁ with hle | hle
    · rw [min_eq_left hle]
      have hsq : 0 ≤ m₀ * m₀ := mul_self_nonneg m₀
      nlinarith
    · rw [min_eq_right hle]
      have hsq : 0 ≤ m₁ * m₁ := mul_self_nonneg m₁
      nlinarith

/-- The local majority error and two-copy disagreement are quantitatively
equivalent. -/
theorem majority_pairDisagreement_sandwich
    (m₀ m₁ : ℝ) (h₀ : 0 ≤ m₀) (h₁ : 0 ≤ m₁) :
    majorityError m₀ m₁ ≤ pairDisagreementMass m₀ m₁ ∧
      pairDisagreementMass m₀ m₁ ≤ 2 * majorityError m₀ m₁ :=
  ⟨majorityError_le_pairDisagreementMass m₀ m₁ h₀ h₁,
    pairDisagreementMass_le_two_mul_majorityError m₀ m₁ h₀ h₁⟩

/-- Direct conditional-variance form of the decoder bound. -/
theorem majorityError_le_two_mul_conditionalVariance
    (m₀ m₁ : ℝ) (h₀ : 0 ≤ m₀) (h₁ : 0 ≤ m₁) :
    majorityError m₀ m₁ ≤ 2 * conditionalVariance m₀ m₁ := by
  rw [← pairDisagreementMass_eq_two_mul_conditionalVariance]
  exact majorityError_le_pairDisagreementMass m₀ m₁ h₀ h₁

section FiberFamily

variable {Y : Type*} [Fintype Y]

/-- The same comparison survives summation over arbitrarily different
source fibers. -/
theorem sum_majorityError_le_sum_pairDisagreementMass
    (m₀ m₁ : Y → ℝ) (h₀ : ∀ y, 0 ≤ m₀ y) (h₁ : ∀ y, 0 ≤ m₁ y) :
    ∑ y, majorityError (m₀ y) (m₁ y) ≤
      ∑ y, pairDisagreementMass (m₀ y) (m₁ y) := by
  exact Finset.sum_le_sum fun y _ ↦
    majorityError_le_pairDisagreementMass (m₀ y) (m₁ y) (h₀ y) (h₁ y)

theorem sum_pairDisagreementMass_le_two_mul_sum_majorityError
    (m₀ m₁ : Y → ℝ) (h₀ : ∀ y, 0 ≤ m₀ y) (h₁ : ∀ y, 0 ≤ m₁ y) :
    ∑ y, pairDisagreementMass (m₀ y) (m₁ y) ≤
      2 * ∑ y, majorityError (m₀ y) (m₁ y) := by
  calc
    ∑ y, pairDisagreementMass (m₀ y) (m₁ y) ≤
        ∑ y, 2 * majorityError (m₀ y) (m₁ y) :=
      Finset.sum_le_sum fun y _ ↦
        pairDisagreementMass_le_two_mul_majorityError
          (m₀ y) (m₁ y) (h₀ y) (h₁ y)
    _ = 2 * ∑ y, majorityError (m₀ y) (m₁ y) := by
      rw [Finset.mul_sum]

/-- Summed conditional variance directly controls the total majority-decoder
error, with no lower bound on individual fiber masses. -/
theorem sum_majorityError_le_two_mul_sum_conditionalVariance
    (m₀ m₁ : Y → ℝ) (h₀ : ∀ y, 0 ≤ m₀ y) (h₁ : ∀ y, 0 ≤ m₁ y) :
    ∑ y, majorityError (m₀ y) (m₁ y) ≤
      2 * ∑ y, conditionalVariance (m₀ y) (m₁ y) := by
  calc
    ∑ y, majorityError (m₀ y) (m₁ y) ≤
        ∑ y, 2 * conditionalVariance (m₀ y) (m₁ y) :=
      Finset.sum_le_sum fun y _ ↦
        majorityError_le_two_mul_conditionalVariance
          (m₀ y) (m₁ y) (h₀ y) (h₁ y)
    _ = 2 * ∑ y, conditionalVariance (m₀ y) (m₁ y) := by
      rw [Finset.mul_sum]

end FiberFamily

end
end FiniteBinaryFiberDecoder
end GroupApproximation
