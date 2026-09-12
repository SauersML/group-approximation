import GroupApproximation.Monsters.P13Weyl13Calculus

/-!
# All three Weyl fourth powers die in P13

The presentation displays only `w₁₂⁴ = 1`.  The other two fourth powers
follow: the third table sends the letters of `w = w₁₂` to the letters
of the second braid word, so `w₂₃ = w₁₃ w₁₂ w₁₃⁻¹` — the transposition
identity `(23) = (13)(12)(13)` realized with signs — and conjugation
transports the relator.  Hence each of the three signed swaps has order
dividing four, and each block pair satisfies both defining relations of
the rank-two braid presentation.
-/

namespace GroupApproximation
namespace P13WeylFourthPowers

open LiteralP13Presentation P13SteinbergCalculus
open P13WeylCalculus P13Weyl23Calculus P13Weyl13Calculus

noncomputable section

/-- The transposition identity `(23) = (13)(12)(13)` with signs. -/
theorem w13_conj_w : w13 * w * w13⁻¹ = w23 := by
  have hw : ∀ g h : P13, w13 * (g * h) * w13⁻¹ =
      (w13 * g * w13⁻¹) * (w13 * h * w13⁻¹) := by
    intro g h; group
  have h21 : w13 * x 2 (-1) * w13⁻¹ = x 3 1 := by
    have h := w13_conj_21 (-1)
    rw [neg_neg] at h
    exact h
  show w13 * (x 0 1 * x 2 (-1) * x 0 1) * w13⁻¹ = w23
  rw [hw, hw, w13_conj_12, h21]
  show x 5 (-1) * x 3 1 * x 5 (-1) = w23
  rw [← braid23]
  rfl

/-- The second Weyl fourth power dies. -/
theorem w23_pow_four : w23 * w23 * w23 * w23 = 1 := by
  rw [← w13_conj_w]
  calc (w13 * w * w13⁻¹) * (w13 * w * w13⁻¹) * (w13 * w * w13⁻¹) *
      (w13 * w * w13⁻¹)
      = w13 * (w * w * w * w) * w13⁻¹ := by group
    _ = w13 * 1 * w13⁻¹ := by rw [w_pow_four]
    _ = 1 := by group

/-- The third Weyl fourth power dies. -/
theorem w13_pow_four : w13 * w13 * w13 * w13 = 1 := by
  rw [w13_eq_conj]
  calc (w * w23 * w⁻¹) * (w * w23 * w⁻¹) * (w * w23 * w⁻¹) *
      (w * w23 * w⁻¹)
      = w * (w23 * w23 * w23 * w23) * w⁻¹ := by group
    _ = w * 1 * w⁻¹ := by rw [w23_pow_four]
    _ = 1 := by group

end

end P13WeylFourthPowers
end GroupApproximation
