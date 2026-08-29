import GroupApproximation.Monsters.P13Weyl23Calculus

/-!
# The third Weyl element of the P13 presentation

The signed swap `w₁₃ = x₁₃(1) x₃₁(-1) x₁₃(1)` is the conjugate of
`w₂₃` by the first Weyl element, so its conjugation table follows by
composing the two established tables:

  `w₁₃ x₁₂(a) w₁₃⁻¹ = x₃₂(-a)`,  `w₁₃ x₃₂(a) w₁₃⁻¹ = x₁₂(a)`,
  `w₁₃ x₂₁(a) w₁₃⁻¹ = x₂₃(-a)`,  `w₁₃ x₂₃(a) w₁₃⁻¹ = x₂₁(a)`,
  `w₁₃ x₁₃(a) w₁₃⁻¹ = x₃₁(-a)`,  `w₁₃ x₃₁(a) w₁₃⁻¹ = x₁₃(-a)`.

With all three signed swaps and their tables the full monomial
calculus of the rank-two root system is available.
-/

namespace GroupApproximation
namespace P13Weyl13Calculus

open LiteralP13Presentation P13SteinbergCalculus
open P13WeylCalculus P13Weyl23Calculus

noncomputable section

/-- The Weyl element `x₁₃(1) x₃₁(-1) x₁₃(1)`. -/
def w13 : P13 := x 1 1 * x 4 (-1) * x 1 1

/-- The third swap is the conjugate of the second by the first. -/
theorem w13_eq_conj : w13 = w * w23 * w⁻¹ :=
  w_conj_w23.symm

private theorem inv_conj_of_conj {G : Type*} [Group G] {u g h : G}
    (H : u * g * u⁻¹ = h) : u⁻¹ * h * u = g := by
  rw [← H]; group

/-- Composite three-step conjugation by `w₁₃ = w w₂₃ w⁻¹`. -/
private theorem w13_conj_via {g h k l : P13}
    (h1 : w⁻¹ * g * w = h)
    (h2 : w23 * h * w23⁻¹ = k)
    (h3 : w * k * w⁻¹ = l) :
    w13 * g * w13⁻¹ = l := by
  rw [w13_eq_conj]
  calc (w * w23 * w⁻¹) * g * (w * w23 * w⁻¹)⁻¹
      = w * (w23 * (w⁻¹ * g * w) * w23⁻¹) * w⁻¹ := by group
    _ = w * (w23 * h * w23⁻¹) * w⁻¹ := by rw [h1]
    _ = w * k * w⁻¹ := by rw [h2]
    _ = l := h3

theorem w13_conj_12 (a : ℤ) : w13 * x 0 a * w13⁻¹ = x 5 (-a) := by
  refine w13_conj_via (h := x 2 (-a)) (k := x 4 a) ?_ ?_ (w_conj_31 a)
  · have h := inv_conj_of_conj (w_conj_21 (-a))
    rw [neg_neg] at h
    exact h
  · have h := w23_conj_21 (-a)
    rw [neg_neg] at h
    exact h

theorem w13_conj_21 (a : ℤ) : w13 * x 2 a * w13⁻¹ = x 3 (-a) := by
  refine w13_conj_via (h := x 0 (-a)) (k := x 1 a) ?_ ?_ (w_conj_13 a)
  · have h := inv_conj_of_conj (w_conj_12 (-a))
    rw [neg_neg] at h
    exact h
  · have h := w23_conj_12 (-a)
    rw [neg_neg] at h
    exact h

theorem w13_conj_23 (a : ℤ) : w13 * x 3 a * w13⁻¹ = x 2 a := by
  refine w13_conj_via (h := x 1 (-a)) (k := x 0 (-a)) ?_
    (w23_conj_13 (-a)) ?_
  · have h := inv_conj_of_conj (w_conj_13 (-a))
    rw [neg_neg] at h
    exact h
  · have h := w_conj_12 (-a)
    rw [neg_neg] at h
    exact h

theorem w13_conj_32 (a : ℤ) : w13 * x 5 a * w13⁻¹ = x 0 a := by
  refine w13_conj_via (h := x 4 (-a)) (k := x 2 (-a)) ?_
    (w23_conj_31 (-a)) ?_
  · have h := inv_conj_of_conj (w_conj_31 (-a))
    rw [neg_neg] at h
    exact h
  · have h := w_conj_21 (-a)
    rw [neg_neg] at h
    exact h

theorem w13_conj_13 (a : ℤ) : w13 * x 1 a * w13⁻¹ = x 4 (-a) := by
  refine w13_conj_via (h := x 3 a) (k := x 5 (-a))
    (inv_conj_of_conj (w_conj_23 a)) (w23_conj_23 a) (w_conj_32 (-a))

theorem w13_conj_31 (a : ℤ) : w13 * x 4 a * w13⁻¹ = x 1 (-a) := by
  refine w13_conj_via (h := x 5 a) (k := x 3 (-a))
    (inv_conj_of_conj (w_conj_32 a)) (w23_conj_32 a) (w_conj_23 (-a))

/-- The braid relation for `x₁₃(1)` and `x₃₁(-1)`. -/
theorem braid13 :
    x 1 1 * x 4 (-1) * x 1 1 = x 4 (-1) * x 1 1 * x 4 (-1) := by
  have h2 : w13 * x 1 1 = x 4 (-1) * w13 := by
    calc w13 * x 1 1 = (w13 * x 1 1 * w13⁻¹) * w13 := by group
      _ = x 4 (-1) * w13 := by rw [w13_conj_13]
  have h3 : (x 1 1 * x 4 (-1) * x 1 1) * x 1 1 =
      x 4 (-1) * (x 1 1 * x 4 (-1) * x 1 1) := h2
  calc x 1 1 * x 4 (-1) * x 1 1
      = (x 1 1 * x 4 (-1) * x 1 1) * x 1 1 * (x 1 1)⁻¹ := by group
    _ = x 4 (-1) * (x 1 1 * x 4 (-1) * x 1 1) * (x 1 1)⁻¹ := by
        rw [h3]
    _ = x 4 (-1) * x 1 1 * x 4 (-1) := by group

end

end P13Weyl13Calculus
end GroupApproximation
