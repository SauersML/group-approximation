import GroupApproximation.Monsters.P13UnipotentInjectivity

/-!
# The Weyl element of the P13 presentation

The signed-swap Weyl element `w = x₁₂(1) x₂₁(-1) x₁₂(1)` acts on the six
root families by the transposition of the first two indices, with
explicit signs:

  `w x₁₃(a) w⁻¹ = x₂₃(-a)`,  `w x₂₃(a) w⁻¹ = x₁₃(a)`,
  `w x₃₁(a) w⁻¹ = x₃₂(-a)`,  `w x₃₂(a) w⁻¹ = x₃₁(a)`,
  `w x₁₂(a) w⁻¹ = x₂₁(-a)`,  `w x₂₁(a) w⁻¹ = x₁₂(-a)`.

The four off-corner conjugations are direct three-step computations from
the Steinberg calculus, using two reverse-conjugation helpers; the two
corner conjugations follow by writing the corner root as a Steinberg
commutator of off-corner roots and conjugating the commutator.  The
corner case at `a = 1` is the braid relation for `x₁₂(1)` and
`x₂₁(-1)`, and the displayed relator makes `w⁴ = 1` in `P13`.  These are
the monomial ingredients of the kernel computation.
-/

namespace GroupApproximation
namespace P13WeylCalculus

open LiteralP13Presentation P13SteinbergCalculus P13UnipotentInjectivity
open LiteralP13MatrixModel

noncomputable section

/-- The Weyl element `x₁₂(1) x₂₁(-1) x₁₂(1)`. -/
def w : P13 := x 0 1 * x 2 (-1) * x 0 1

/-- Three-step conjugation by `w`. -/
theorem w_conj_via {g h k l : P13}
    (h1 : x 0 1 * g * (x 0 1)⁻¹ = h)
    (h2 : x 2 (-1) * h * (x 2 (-1))⁻¹ = k)
    (h3 : x 0 1 * k * (x 0 1)⁻¹ = l) :
    w * g * w⁻¹ = l := by
  unfold w
  calc x 0 1 * x 2 (-1) * x 0 1 * g * (x 0 1 * x 2 (-1) * x 0 1)⁻¹
      = x 0 1 * (x 2 (-1) * (x 0 1 * g * (x 0 1)⁻¹) * (x 2 (-1))⁻¹) *
        (x 0 1)⁻¹ := by group
    _ = x 0 1 * (x 2 (-1) * h * (x 2 (-1))⁻¹) * (x 0 1)⁻¹ := by rw [h1]
    _ = x 0 1 * k * (x 0 1)⁻¹ := by rw [h2]
    _ = l := h3

private theorem conj_of_commute {G : Type*} [Group G] {u g : G}
    (h : Commute u g) : u * g * u⁻¹ = g := by
  rw [h.eq]; group

/-! ## Reverse conjugations -/

/-- `x₁₂(b) x₃₁(a) x₁₂(b)⁻¹ = x₃₂(-(a b)) x₃₁(a)`. -/
theorem x_conj_rev_12_31 (b a : ℤ) :
    x 0 b * x 4 a * (x 0 b)⁻¹ = x 5 (-(a * b)) * x 4 a := by
  -- `x₃₁(a) x₁₂(b) x₃₁(a)⁻¹ = x₃₂(a b) x₁₂(b)`
  have h1 : x 4 a * x 0 b = x 5 (a * b) * x 0 b * x 4 a := by
    simpa [mul_assoc] using congrArg (· * x 4 a) (x_conj_31_12 a b)
  have h2 : x 0 b * x 4 a = x 5 (-(a * b)) * x 4 a * x 0 b := by
    calc x 0 b * x 4 a
        = x 5 (-(a * b)) * (x 4 a * x 0 b) * (x 0 b)⁻¹ * x 0 b := by
          rw [h1, x_neg]
          group
      _ = x 5 (-(a * b)) * x 4 a * x 0 b := by group
  calc x 0 b * x 4 a * (x 0 b)⁻¹
      = (x 5 (-(a * b)) * x 4 a * x 0 b) * (x 0 b)⁻¹ := by rw [← h2]
    _ = x 5 (-(a * b)) * x 4 a := by group

/-- `x₂₁(b) x₃₂(a) x₂₁(b)⁻¹ = x₃₁(-(a b)) x₃₂(a)`. -/
theorem x_conj_rev_21_32 (b a : ℤ) :
    x 2 b * x 5 a * (x 2 b)⁻¹ = x 4 (-(a * b)) * x 5 a := by
  have h1 : x 5 a * x 2 b = x 4 (a * b) * x 2 b * x 5 a := by
    simpa [mul_assoc] using congrArg (· * x 5 a) (x_conj_32_21 a b)
  have h2 : x 2 b * x 5 a = x 4 (-(a * b)) * x 5 a * x 2 b := by
    calc x 2 b * x 5 a
        = x 4 (-(a * b)) * (x 5 a * x 2 b) * (x 2 b)⁻¹ * x 2 b := by
          rw [h1, x_neg]
          group
      _ = x 4 (-(a * b)) * x 5 a * x 2 b := by group
  calc x 2 b * x 5 a * (x 2 b)⁻¹
      = (x 4 (-(a * b)) * x 5 a * x 2 b) * (x 2 b)⁻¹ := by rw [← h2]
    _ = x 4 (-(a * b)) * x 5 a := by group

/-! ## The four off-corner conjugations -/

theorem w_conj_13 (a : ℤ) : w * x 1 a * w⁻¹ = x 3 (-a) := by
  refine w_conj_via (k := x 3 (-1 * a) * x 1 a)
    (conj_of_commute (x_commute_12_13 1 a)) (x_conj_21_13 (-1) a) ?_
  calc x 0 1 * (x 3 (-1 * a) * x 1 a) * (x 0 1)⁻¹
      = (x 0 1 * x 3 (-1 * a) * (x 0 1)⁻¹) *
        (x 0 1 * x 1 a * (x 0 1)⁻¹) := by group
    _ = (x 1 (1 * (-1 * a)) * x 3 (-1 * a)) * x 1 a := by
        rw [x_conj_12_23 1 (-1 * a),
          conj_of_commute (x_commute_12_13 1 a)]
    _ = x 1 (-a) * x 3 (-a) * x 1 a := by norm_num
    _ = x 3 (-a) * (x 1 (-a) * x 1 a) := by
        rw [((x_commute_13_23 (-a) (-a)).eq)]
        group
    _ = x 3 (-a) * x 1 (-a + a) := by rw [x_add]
    _ = x 3 (-a) := by norm_num

theorem w_conj_23 (a : ℤ) : w * x 3 a * w⁻¹ = x 1 a := by
  refine w_conj_via (k := x 1 a) (x_conj_12_23 1 a) ?_
    (conj_of_commute (x_commute_12_13 1 a))
  calc x 2 (-1) * (x 1 (1 * a) * x 3 a) * (x 2 (-1))⁻¹
      = (x 2 (-1) * x 1 (1 * a) * (x 2 (-1))⁻¹) *
        (x 2 (-1) * x 3 a * (x 2 (-1))⁻¹) := by group
    _ = (x 3 (-1 * (1 * a)) * x 1 (1 * a)) * x 3 a := by
        rw [x_conj_21_13 (-1) (1 * a),
          conj_of_commute (x_commute_21_23 (-1) a)]
    _ = x 3 (-a) * x 1 a * x 3 a := by norm_num
    _ = x 1 a * (x 3 (-a) * x 3 a) := by
        rw [((x_commute_13_23 a (-a)).eq).symm]
        group
    _ = x 1 a * x 3 (-a + a) := by rw [x_add]
    _ = x 1 a := by norm_num

theorem w_conj_31 (a : ℤ) : w * x 4 a * w⁻¹ = x 5 (-a) := by
  refine w_conj_via (k := x 5 (-a)) (x_conj_rev_12_31 1 a) ?_
    (conj_of_commute (x_commute_12_32 1 (-a)))
  calc x 2 (-1) * (x 5 (-(a * 1)) * x 4 a) * (x 2 (-1))⁻¹
      = (x 2 (-1) * x 5 (-(a * 1)) * (x 2 (-1))⁻¹) *
        (x 2 (-1) * x 4 a * (x 2 (-1))⁻¹) := by group
    _ = (x 4 (-(-(a * 1) * -1)) * x 5 (-(a * 1))) * x 4 a := by
        rw [x_conj_rev_21_32 (-1) (-(a * 1)),
          conj_of_commute (x_commute_21_31 (-1) a)]
    _ = x 4 (-a) * x 5 (-a) * x 4 a := by norm_num
    _ = x 5 (-a) * (x 4 (-a) * x 4 a) := by
        rw [((x_commute_31_32 (-a) (-a)).eq)]
        group
    _ = x 5 (-a) * x 4 (-a + a) := by rw [x_add]
    _ = x 5 (-a) := by norm_num

theorem w_conj_32 (a : ℤ) : w * x 5 a * w⁻¹ = x 4 a := by
  refine w_conj_via (k := x 4 (-(a * -1)) * x 5 a)
    (conj_of_commute (x_commute_12_32 1 a))
    (x_conj_rev_21_32 (-1) a) ?_
  calc x 0 1 * (x 4 (-(a * -1)) * x 5 a) * (x 0 1)⁻¹
      = (x 0 1 * x 4 (-(a * -1)) * (x 0 1)⁻¹) *
        (x 0 1 * x 5 a * (x 0 1)⁻¹) := by group
    _ = (x 5 (-(-(a * -1) * 1)) * x 4 (-(a * -1))) * x 5 a := by
        rw [x_conj_rev_12_31 1 (-(a * -1)),
          conj_of_commute (x_commute_12_32 1 a)]
    _ = x 5 (-a) * x 4 a * x 5 a := by norm_num
    _ = x 4 a * (x 5 (-a) * x 5 a) := by
        rw [((x_commute_31_32 a (-a)).eq).symm]
        group
    _ = x 4 a * x 5 (-a + a) := by rw [x_add]
    _ = x 4 a := by norm_num

/-! ## The two corner conjugations -/

theorem w_conj_12 (a : ℤ) : w * x 0 a * w⁻¹ = x 2 (-a) := by
  -- `x₁₂(a) = [x₁₃(a), x₃₂(1)]`, and `w` transports the commutator.
  have hcomm : x 0 a = x 1 a * x 5 1 * (x 1 a)⁻¹ * (x 5 1)⁻¹ := by
    simpa [mul_assoc, mul_one] using
      (congrArg (· * (x 5 1)⁻¹) (x_conj_13_32 a 1)).symm
  rw [hcomm]
  have hw : ∀ g h : P13, w * (g * h) * w⁻¹ =
      (w * g * w⁻¹) * (w * h * w⁻¹) := by
    intro g h; group
  have hwinv : ∀ g : P13, w * g⁻¹ * w⁻¹ = (w * g * w⁻¹)⁻¹ := by
    intro g; group
  rw [hw, hw, hw, hwinv, hwinv, w_conj_13, w_conj_32]
  calc x 3 (-a) * x 4 1 * (x 3 (-a))⁻¹ * (x 4 1)⁻¹
      = x 2 (-a * 1) := by
        simpa [mul_assoc, mul_one] using
          congrArg (· * (x 4 1)⁻¹) (x_conj_23_31 (-a) 1)
    _ = x 2 (-a) := by norm_num

theorem w_conj_21 (a : ℤ) : w * x 2 a * w⁻¹ = x 0 (-a) := by
  have hcomm : x 2 a = x 3 a * x 4 1 * (x 3 a)⁻¹ * (x 4 1)⁻¹ := by
    simpa [mul_assoc, mul_one] using
      (congrArg (· * (x 4 1)⁻¹) (x_conj_23_31 a 1)).symm
  rw [hcomm]
  have hw : ∀ g h : P13, w * (g * h) * w⁻¹ =
      (w * g * w⁻¹) * (w * h * w⁻¹) := by
    intro g h; group
  have hwinv : ∀ g : P13, w * g⁻¹ * w⁻¹ = (w * g * w⁻¹)⁻¹ := by
    intro g; group
  rw [hw, hw, hw, hwinv, hwinv, w_conj_23, w_conj_31]
  calc x 1 a * x 5 (-1) * (x 1 a)⁻¹ * (x 5 (-1))⁻¹
      = x 0 (a * -1) := by
        simpa [mul_assoc, mul_one] using
          congrArg (· * (x 5 (-1))⁻¹) (x_conj_13_32 a (-1))
    _ = x 0 (-a) := by norm_num

/-! ## The braid relation and the fourth power -/

/-- The braid relation for `x₁₂(1)` and `x₂₁(-1)`. -/
theorem braid :
    x 0 1 * x 2 (-1) * x 0 1 = x 2 (-1) * x 0 1 * x 2 (-1) := by
  -- `w x₁₂(1) w⁻¹ = x₂₁(-1)` unfolds to the braid relation.
  have h2 : w * x 0 1 = x 2 (-1) * w := by
    calc w * x 0 1 = (w * x 0 1 * w⁻¹) * w := by group
      _ = x 2 (-1) * w := by rw [w_conj_12 1]
  calc x 0 1 * x 2 (-1) * x 0 1
      = (x 0 1 * x 2 (-1) * x 0 1) * x 0 1 * (x 0 1)⁻¹ := by group
    _ = x 2 (-1) * (x 0 1 * x 2 (-1) * x 0 1) * (x 0 1)⁻¹ := by
        change (w * x 0 1) * (x 0 1)⁻¹ = (x 2 (-1) * w) * (x 0 1)⁻¹
        rw [h2]
    _ = x 2 (-1) * x 0 1 * x 2 (-1) := by group

/-- The Weyl element has order dividing four: the displayed relator. -/
theorem w_pow_four : w * w * w * w = 1 := by
  simpa [w, x_one, x_neg] using weyl_fourth_power

end

end P13WeylCalculus
end GroupApproximation
