import GroupApproximation.Monsters.P13WeylCalculus

/-!
# The second Weyl element of the P13 presentation

The signed-swap Weyl element `w₂₃ = x₂₃(1) x₃₂(-1) x₂₃(1)` acts on the
six root families by the transposition of the last two indices, with
explicit signs:

  `w₂₃ x₁₂(a) w₂₃⁻¹ = x₁₃(-a)`,  `w₂₃ x₁₃(a) w₂₃⁻¹ = x₁₂(a)`,
  `w₂₃ x₂₁(a) w₂₃⁻¹ = x₃₁(-a)`,  `w₂₃ x₃₁(a) w₂₃⁻¹ = x₂₁(a)`,
  `w₂₃ x₂₃(a) w₂₃⁻¹ = x₃₂(-a)`,  `w₂₃ x₃₂(a) w₂₃⁻¹ = x₂₃(-a)`.

The four off-corner conjugations are three-step computations from the
Steinberg calculus through two further reverse-conjugation helpers; the
two corner conjugations transport the corner root written as a
commutator of off-corner roots.  The corner case at `a = 1` yields the
braid relation for `x₂₃(1)` and `x₃₂(-1)`.  Conjugating by the first
Weyl element sends `w₂₃` to the third signed swap `w₁₃`, so this table
generates the full monomial calculus.
-/

namespace GroupApproximation
namespace P13Weyl23Calculus

open LiteralP13Presentation P13SteinbergCalculus P13UnipotentInjectivity
open LiteralP13MatrixModel P13WeylCalculus

noncomputable section

/-- The Weyl element `x₂₃(1) x₃₂(-1) x₂₃(1)`. -/
def w23 : P13 := x 3 1 * x 5 (-1) * x 3 1

/-- Three-step conjugation by `w₂₃`. -/
theorem w23_conj_via {g h k l : P13}
    (h1 : x 3 1 * g * (x 3 1)⁻¹ = h)
    (h2 : x 5 (-1) * h * (x 5 (-1))⁻¹ = k)
    (h3 : x 3 1 * k * (x 3 1)⁻¹ = l) :
    w23 * g * w23⁻¹ = l := by
  unfold w23
  calc x 3 1 * x 5 (-1) * x 3 1 * g * (x 3 1 * x 5 (-1) * x 3 1)⁻¹
      = x 3 1 * (x 5 (-1) * (x 3 1 * g * (x 3 1)⁻¹) * (x 5 (-1))⁻¹) *
        (x 3 1)⁻¹ := by group
    _ = x 3 1 * (x 5 (-1) * h * (x 5 (-1))⁻¹) * (x 3 1)⁻¹ := by rw [h1]
    _ = x 3 1 * k * (x 3 1)⁻¹ := by rw [h2]
    _ = l := h3

private theorem conj_of_commute {G : Type*} [Group G] {u g : G}
    (h : Commute u g) : u * g * u⁻¹ = g := by
  rw [h.eq]; group

private theorem conj_mul {G : Type*} [Group G] (u g h : G) :
    u * (g * h) * u⁻¹ = (u * g * u⁻¹) * (u * h * u⁻¹) := by
  group

private theorem conj_inv {G : Type*} [Group G] (u g : G) :
    u * g⁻¹ * u⁻¹ = (u * g * u⁻¹)⁻¹ := by
  group

/-! ## Reverse conjugations -/

/-- `x₂₃(b) x₁₂(a) x₂₃(b)⁻¹ = x₁₃(-(a b)) x₁₂(a)`. -/
theorem x_conj_rev_23_12 (b a : ℤ) :
    x 3 b * x 0 a * (x 3 b)⁻¹ = x 1 (-(a * b)) * x 0 a := by
  have hF := x_conj_12_23 a b
  have h1 : x 0 a * x 3 b = x 1 (a * b) * x 3 b * x 0 a := by
    have := congrArg (· * x 0 a) hF
    simpa [mul_assoc] using this
  have h2 : x 3 b * x 0 a = x 1 (-(a * b)) * x 0 a * x 3 b := by
    have h3 : x 1 (-(a * b)) * (x 0 a * x 3 b) =
        x 3 b * x 0 a := by
      rw [h1, x_neg]
      group
    calc x 3 b * x 0 a
        = x 1 (-(a * b)) * (x 0 a * x 3 b) * (x 3 b)⁻¹ * x 3 b := by
          rw [h3]; group
      _ = x 1 (-(a * b)) * x 0 a * x 3 b := by group
  calc x 3 b * x 0 a * (x 3 b)⁻¹
      = (x 1 (-(a * b)) * x 0 a * x 3 b) * (x 3 b)⁻¹ := by rw [← h2]
    _ = x 1 (-(a * b)) * x 0 a := by group

/-- `x₃₂(b) x₁₃(a) x₃₂(b)⁻¹ = x₁₂(-(a b)) x₁₃(a)`. -/
theorem x_conj_rev_32_13 (b a : ℤ) :
    x 5 b * x 1 a * (x 5 b)⁻¹ = x 0 (-(a * b)) * x 1 a := by
  have hF := x_conj_13_32 a b
  have h1 : x 1 a * x 5 b = x 0 (a * b) * x 5 b * x 1 a := by
    have := congrArg (· * x 1 a) hF
    simpa [mul_assoc] using this
  have h2 : x 5 b * x 1 a = x 0 (-(a * b)) * x 1 a * x 5 b := by
    have h3 : x 0 (-(a * b)) * (x 1 a * x 5 b) =
        x 5 b * x 1 a := by
      rw [h1, x_neg]
      group
    calc x 5 b * x 1 a
        = x 0 (-(a * b)) * (x 1 a * x 5 b) * (x 5 b)⁻¹ * x 5 b := by
          rw [h3]; group
      _ = x 0 (-(a * b)) * x 1 a * x 5 b := by group
  calc x 5 b * x 1 a * (x 5 b)⁻¹
      = (x 0 (-(a * b)) * x 1 a * x 5 b) * (x 5 b)⁻¹ := by rw [← h2]
    _ = x 0 (-(a * b)) * x 1 a := by group

/-! ## The four off-corner conjugations -/

theorem w23_conj_12 (a : ℤ) : w23 * x 0 a * w23⁻¹ = x 1 (-a) := by
  refine w23_conj_via (k := x 1 (-a))
    (x_conj_rev_23_12 1 a) ?_
    (conj_of_commute (x_commute_13_23 (-a) 1).symm)
  calc x 5 (-1) * (x 1 (-(a * 1)) * x 0 a) * (x 5 (-1))⁻¹
      = (x 5 (-1) * x 1 (-(a * 1)) * (x 5 (-1))⁻¹) *
        (x 5 (-1) * x 0 a * (x 5 (-1))⁻¹) := by group
    _ = (x 0 (-(-(a * 1) * -1)) * x 1 (-(a * 1))) * x 0 a := by
        rw [x_conj_rev_32_13, conj_of_commute (x_commute_12_32 a (-1)).symm]
    _ = x 0 (-a) * x 1 (-a) * x 0 a := by norm_num
    _ = x 1 (-a) * (x 0 (-a) * x 0 a) := by
        rw [((x_commute_12_13 (-a) (-a)).eq)]
        group
    _ = x 1 (-a) * x 0 (-a + a) := by rw [x_add]
    _ = x 1 (-a) := by norm_num

theorem w23_conj_21 (a : ℤ) : w23 * x 2 a * w23⁻¹ = x 4 (-a) := by
  refine w23_conj_via (k := x 4 (-1 * a) * x 2 a)
    (conj_of_commute (x_commute_21_23 a 1).symm)
    (x_conj_32_21 (-1) a) ?_
  calc x 3 1 * (x 4 (-1 * a) * x 2 a) * (x 3 1)⁻¹
      = (x 3 1 * x 4 (-1 * a) * (x 3 1)⁻¹) *
        (x 3 1 * x 2 a * (x 3 1)⁻¹) := by group
    _ = (x 2 (1 * (-1 * a)) * x 4 (-1 * a)) * x 2 a := by
        rw [x_conj_23_31, conj_of_commute (x_commute_21_23 a 1).symm]
    _ = x 2 (-a) * x 4 (-a) * x 2 a := by norm_num
    _ = x 4 (-a) * (x 2 (-a) * x 2 a) := by
        rw [((x_commute_21_31 (-a) (-a)).eq)]
        group
    _ = x 4 (-a) * x 2 (-a + a) := by rw [x_add]
    _ = x 4 (-a) := by norm_num

theorem w23_conj_31 (a : ℤ) : w23 * x 4 a * w23⁻¹ = x 2 a := by
  refine w23_conj_via (k := x 2 a) (x_conj_23_31 1 a) ?_
    (conj_of_commute (x_commute_21_23 a 1).symm)
  calc x 5 (-1) * (x 2 (1 * a) * x 4 a) * (x 5 (-1))⁻¹
      = (x 5 (-1) * x 2 (1 * a) * (x 5 (-1))⁻¹) *
        (x 5 (-1) * x 4 a * (x 5 (-1))⁻¹) := by group
    _ = (x 4 (-1 * (1 * a)) * x 2 (1 * a)) * x 4 a := by
        rw [x_conj_32_21, conj_of_commute (x_commute_31_32 a (-1)).symm]
    _ = x 4 (-a) * x 2 a * x 4 a := by norm_num
    _ = x 2 a * (x 4 (-a) * x 4 a) := by
        rw [((x_commute_21_31 a (-a)).eq).symm]
        group
    _ = x 2 a * x 4 (-a + a) := by rw [x_add]
    _ = x 2 a := by norm_num

theorem w23_conj_13 (a : ℤ) : w23 * x 1 a * w23⁻¹ = x 0 a := by
  refine w23_conj_via (k := x 0 a * x 1 a)
    (conj_of_commute (x_commute_13_23 a 1).symm) ?_ ?_
  · calc x 5 (-1) * x 1 a * (x 5 (-1))⁻¹
        = x 0 (-(a * -1)) * x 1 a := x_conj_rev_32_13 (-1) a
      _ = x 0 a * x 1 a := by norm_num
  · have h13 : x 3 1 * x 1 a * (x 3 1)⁻¹ = x 1 a :=
      conj_of_commute (x_commute_13_23 a 1).symm
    calc x 3 1 * (x 0 a * x 1 a) * (x 3 1)⁻¹
        = (x 3 1 * x 0 a * (x 3 1)⁻¹) *
          (x 3 1 * x 1 a * (x 3 1)⁻¹) := by group
      _ = (x 1 (-(a * 1)) * x 0 a) * x 1 a := by
          rw [x_conj_rev_23_12 1 a, h13]
      _ = x 1 (-a) * x 0 a * x 1 a := by norm_num
      _ = x 0 a * (x 1 (-a) * x 1 a) := by
          rw [((x_commute_12_13 a (-a)).eq).symm]
          group
      _ = x 0 a * x 1 (-a + a) := by rw [x_add]
      _ = x 0 a := by norm_num

/-! ## The two corner conjugations -/

theorem w23_conj_23 (a : ℤ) : w23 * x 3 a * w23⁻¹ = x 5 (-a) := by
  -- `x₂₃(a) = [x₂₁(a), x₁₃(1)]`, and `w₂₃` transports the commutator.
  have hcomm : x 3 a = x 2 a * x 1 1 * (x 2 a)⁻¹ * (x 1 1)⁻¹ := by
    have h := x_conj_21_13 a 1
    have := congrArg (· * (x 1 1)⁻¹) h
    simpa [mul_assoc, mul_one] using this.symm
  rw [hcomm]
  rw [conj_mul, conj_mul, conj_mul, conj_inv, conj_inv, w23_conj_21, w23_conj_13]
  have h := x_conj_31_12 (-a) 1
  have := congrArg (· * (x 0 1)⁻¹) h
  calc x 4 (-a) * x 0 1 * (x 4 (-a))⁻¹ * (x 0 1)⁻¹
      = x 5 (-a * 1) := by simpa [mul_assoc, mul_one] using this
    _ = x 5 (-a) := by norm_num

theorem w23_conj_32 (a : ℤ) : w23 * x 5 a * w23⁻¹ = x 3 (-a) := by
  have hcomm : x 5 a = x 4 a * x 0 1 * (x 4 a)⁻¹ * (x 0 1)⁻¹ := by
    have h := x_conj_31_12 a 1
    have := congrArg (· * (x 0 1)⁻¹) h
    simpa [mul_assoc, mul_one] using this.symm
  rw [hcomm]
  rw [conj_mul, conj_mul, conj_mul, conj_inv, conj_inv, w23_conj_31, w23_conj_12]
  have h := x_conj_21_13 a (-1)
  have := congrArg (· * (x 1 (-1))⁻¹) h
  calc x 2 a * x 1 (-1) * (x 2 a)⁻¹ * (x 1 (-1))⁻¹
      = x 3 (a * -1) := by simpa [mul_assoc, mul_one] using this
    _ = x 3 (-a) := by norm_num

/-! ## The braid relation and the third swap -/

/-- The braid relation for `x₂₃(1)` and `x₃₂(-1)`. -/
theorem braid23 :
    x 3 1 * x 5 (-1) * x 3 1 = x 5 (-1) * x 3 1 * x 5 (-1) := by
  have h : w23 * x 3 1 * w23⁻¹ = x 5 (-1) := w23_conj_23 1
  have h2 : w23 * x 3 1 = x 5 (-1) * w23 := by
    calc w23 * x 3 1 = (w23 * x 3 1 * w23⁻¹) * w23 := by group
      _ = x 5 (-1) * w23 := by rw [h]
  have h3 : (x 3 1 * x 5 (-1) * x 3 1) * x 3 1 =
      x 5 (-1) * (x 3 1 * x 5 (-1) * x 3 1) := h2
  calc x 3 1 * x 5 (-1) * x 3 1
      = (x 3 1 * x 5 (-1) * x 3 1) * x 3 1 * (x 3 1)⁻¹ := by group
    _ = x 5 (-1) * (x 3 1 * x 5 (-1) * x 3 1) * (x 3 1)⁻¹ := by
        rw [h3]
    _ = x 5 (-1) * x 3 1 * x 5 (-1) := by group

/-- Conjugating the second Weyl element by the first produces the third
signed swap `w₁₃ = x₁₃(1) x₃₁(-1) x₁₃(1)`. -/
theorem w_conj_w23 :
    w * w23 * w⁻¹ = x 1 1 * x 4 (-1) * x 1 1 := by
  unfold w23
  rw [conj_mul, conj_mul, w_conj_23, w_conj_32]

end

end P13Weyl23Calculus
end GroupApproximation
