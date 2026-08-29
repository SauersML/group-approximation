import GroupApproximation.Monsters.P13WordDescent

/-!
# The rewrite case table of the word descent

At the topmost worst violation the descent replaces the two offending
letters by a short block, chosen from a finite catalog validated by
the numerical model (`scripts/descent_model.py`).  This file provides,
class by class, the two halves each rewrite needs:

* the *identity lemmas*: the replacement block evaluates to the same
  element of `P13` (up to the emitted signed-swap word in the braid
  and emission cases), all derived from the Steinberg calculus by
  cancellation and single commutations;
* the *existence lemmas*: under the violation hypothesis
  `vnorm (act p (act q u)) < vnorm (act q u)` and the height-side
  hypothesis `vnorm u ≤ vnorm (act q u)`, at least one catalog block
  has all its internal trajectory norms strictly below the violated
  height.  These are sign-case splits followed by `omega`.

The classes, by the write/read coordinates of the six root letters
(`x0 = e₁₂ : v₀ += c·v₁`, `x1 = e₁₃ : v₀ += c·v₂`,
`x2 = e₂₁ : v₁ += c·v₀`, `x3 = e₂₃ : v₁ += c·v₂`,
`x4 = e₃₁ : v₂ += c·v₀`, `x5 = e₃₂ : v₂ += c·v₁`):

* same family — only the anti-aligned pair occurs (cancellation); the
  aligned pair is impossible at a violation;
* same read (`{0,5}, {1,3}, {2,4}`) — the plain swap cuts the peak;
* same write (`{0,1}, {2,3}, {4,5}`) — the swap or one of two
  conjugation sandwiches cuts the peak;
* Steinberg (`(0,3),(1,5),(2,1),(3,4),(4,0),(5,2)` and reversals) —
  one of the three split orders or the block-Weyl emission cuts the
  peak;
* braid (`{0,2}, {1,4}, {3,5}`) — only the anti-aligned pair occurs,
  and its one-letter emission block has no internals at all.
-/

namespace GroupApproximation
namespace P13DescentCases

open LiteralP13Presentation P13SteinbergCalculus LiteralP13MatrixModel
open P13WeylCalculus P13Weyl13Calculus P13Weyl23Calculus
open P13ColumnLift P13ParabolicKernel P13MonomialMachine P13DescentCore
open P13WordDescent

noncomputable section

/-! ## Same family: cancellation, and impossibility of alignment -/

/-- Anti-aligned same-family letters cancel. -/
theorem cancel_pair (i : Fin 6) (c : ℤ) : x i c * x i (-c) = 1 := by
  rw [x_add, show c + -c = 0 from by ring, x_zero]

/-- An aligned same-family pair cannot sit at a violation: `e₁₂`. -/
theorem same_aligned_0 (c : ℤ) (hc : c = 1 ∨ c = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 0 c)) (act (toSL3 (x 0 c)) u)) <
      vnorm (act (toSL3 (x 0 c)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 0 c)) u)) : False := by
  rcases hc with rfl | rfl <;>
    simp only [act_x0] at hviol hside <;>
    simp [vnorm] at hviol hside <;>
    omega

/-- An aligned same-family pair cannot sit at a violation: `e₁₃`. -/
theorem same_aligned_1 (c : ℤ) (hc : c = 1 ∨ c = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 1 c)) (act (toSL3 (x 1 c)) u)) <
      vnorm (act (toSL3 (x 1 c)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 1 c)) u)) : False := by
  rcases hc with rfl | rfl <;>
    simp only [act_x1] at hviol hside <;>
    simp [vnorm] at hviol hside <;>
    omega

/-- An aligned same-family pair cannot sit at a violation: `e₂₁`. -/
theorem same_aligned_2 (c : ℤ) (hc : c = 1 ∨ c = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 2 c)) (act (toSL3 (x 2 c)) u)) <
      vnorm (act (toSL3 (x 2 c)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 2 c)) u)) : False := by
  rcases hc with rfl | rfl <;>
    simp only [act_x2] at hviol hside <;>
    simp [vnorm] at hviol hside <;>
    omega

/-- An aligned same-family pair cannot sit at a violation: `e₂₃`. -/
theorem same_aligned_3 (c : ℤ) (hc : c = 1 ∨ c = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 3 c)) (act (toSL3 (x 3 c)) u)) <
      vnorm (act (toSL3 (x 3 c)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 3 c)) u)) : False := by
  rcases hc with rfl | rfl <;>
    simp only [act_x3] at hviol hside <;>
    simp [vnorm] at hviol hside <;>
    omega

/-- An aligned same-family pair cannot sit at a violation: `e₃₁`. -/
theorem same_aligned_4 (c : ℤ) (hc : c = 1 ∨ c = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 4 c)) (act (toSL3 (x 4 c)) u)) <
      vnorm (act (toSL3 (x 4 c)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 4 c)) u)) : False := by
  rcases hc with rfl | rfl <;>
    simp only [act_x4] at hviol hside <;>
    simp [vnorm] at hviol hside <;>
    omega

/-- An aligned same-family pair cannot sit at a violation: `e₃₂`. -/
theorem same_aligned_5 (c : ℤ) (hc : c = 1 ∨ c = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 5 c)) (act (toSL3 (x 5 c)) u)) <
      vnorm (act (toSL3 (x 5 c)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 5 c)) u)) : False := by
  rcases hc with rfl | rfl <;>
    simp only [act_x5] at hviol hside <;>
    simp [vnorm] at hviol hside <;>
    omega

/-! ## Same read: the swap cuts the peak -/

/-- `(e₁₂, e₃₂)`: shared read coordinate `v₁`. -/
theorem exist_sr_05 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 0 c)) (act (toSL3 (x 5 cp)) u)) <
      vnorm (act (toSL3 (x 5 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 5 cp)) u)) :
    vnorm (act (toSL3 (x 0 c)) u) < vnorm (act (toSL3 (x 5 cp)) u) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;>
    simp only [act_x0, act_x5] at hviol hside ⊢ <;>
    simp [vnorm] at hviol hside ⊢ <;>
    omega

/-- `(e₃₂, e₁₂)`. -/
theorem exist_sr_50 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 5 c)) (act (toSL3 (x 0 cp)) u)) <
      vnorm (act (toSL3 (x 0 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 0 cp)) u)) :
    vnorm (act (toSL3 (x 5 c)) u) < vnorm (act (toSL3 (x 0 cp)) u) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;>
    simp only [act_x0, act_x5] at hviol hside ⊢ <;>
    simp [vnorm] at hviol hside ⊢ <;>
    omega

/-- `(e₁₃, e₂₃)`: shared read coordinate `v₂`. -/
theorem exist_sr_13 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 1 c)) (act (toSL3 (x 3 cp)) u)) <
      vnorm (act (toSL3 (x 3 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 3 cp)) u)) :
    vnorm (act (toSL3 (x 1 c)) u) < vnorm (act (toSL3 (x 3 cp)) u) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;>
    simp only [act_x1, act_x3] at hviol hside ⊢ <;>
    simp [vnorm] at hviol hside ⊢ <;>
    omega

/-- `(e₂₃, e₁₃)`. -/
theorem exist_sr_31 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 3 c)) (act (toSL3 (x 1 cp)) u)) <
      vnorm (act (toSL3 (x 1 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 1 cp)) u)) :
    vnorm (act (toSL3 (x 3 c)) u) < vnorm (act (toSL3 (x 1 cp)) u) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;>
    simp only [act_x1, act_x3] at hviol hside ⊢ <;>
    simp [vnorm] at hviol hside ⊢ <;>
    omega

/-- `(e₂₁, e₃₁)`: shared read coordinate `v₀`. -/
theorem exist_sr_24 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 2 c)) (act (toSL3 (x 4 cp)) u)) <
      vnorm (act (toSL3 (x 4 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 4 cp)) u)) :
    vnorm (act (toSL3 (x 2 c)) u) < vnorm (act (toSL3 (x 4 cp)) u) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;>
    simp only [act_x2, act_x4] at hviol hside ⊢ <;>
    simp [vnorm] at hviol hside ⊢ <;>
    omega

/-- `(e₃₁, e₂₁)`. -/
theorem exist_sr_42 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 4 c)) (act (toSL3 (x 2 cp)) u)) <
      vnorm (act (toSL3 (x 2 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 2 cp)) u)) :
    vnorm (act (toSL3 (x 4 c)) u) < vnorm (act (toSL3 (x 2 cp)) u) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;>
    simp only [act_x2, act_x4] at hviol hside ⊢ <;>
    simp [vnorm] at hviol hside ⊢ <;>
    omega

/-! ## The conjugation sandwiches

For each root letter, sandwiching by a suitable third letter re-emits
the composite root on the outside; each identity is one Steinberg
conjugation plus one commutation plus a cancellation. -/

/-- `x₃(e) · x₀(c) · x₃(−e) = x₁(−ec) · x₀(c)`. -/
theorem sand3_conj (e c : ℤ) :
    x 3 e * x 0 c * x 3 (-e) = x 1 (-(e * c)) * x 0 c := by
  have h2 : x 0 c * x 3 (-e) = x 1 (c * -e) * x 3 (-e) * x 0 c := by
    calc x 0 c * x 3 (-e)
        = (x 0 c * x 3 (-e) * (x 0 c)⁻¹) * x 0 c := by group
      _ = x 1 (c * -e) * x 3 (-e) * x 0 c := by rw [x_conj_12_23]
  calc x 3 e * x 0 c * x 3 (-e)
      = x 3 e * (x 0 c * x 3 (-e)) := by group
    _ = x 3 e * (x 1 (c * -e) * x 3 (-e) * x 0 c) := by rw [h2]
    _ = (x 3 e * x 1 (c * -e)) * x 3 (-e) * x 0 c := by group
    _ = (x 1 (c * -e) * x 3 e) * x 3 (-e) * x 0 c := by
        rw [((x_commute_13_23 (c * -e) e).symm).eq]
    _ = x 1 (c * -e) * (x 3 e * x 3 (-e)) * x 0 c := by group
    _ = x 1 (c * -e) * x 0 c := by
        rw [x_add, show e + -e = 0 from by ring, x_zero, mul_one]
    _ = x 1 (-(e * c)) * x 0 c := by
        rw [show c * -e = -(e * c) from by ring]

/-- `x₅(e) · x₁(c) · x₅(−e) = x₀(−ec) · x₁(c)`. -/
theorem sand5_conj (e c : ℤ) :
    x 5 e * x 1 c * x 5 (-e) = x 0 (-(e * c)) * x 1 c := by
  have h2 : x 1 c * x 5 (-e) = x 0 (c * -e) * x 5 (-e) * x 1 c := by
    calc x 1 c * x 5 (-e)
        = (x 1 c * x 5 (-e) * (x 1 c)⁻¹) * x 1 c := by group
      _ = x 0 (c * -e) * x 5 (-e) * x 1 c := by rw [x_conj_13_32]
  calc x 5 e * x 1 c * x 5 (-e)
      = x 5 e * (x 1 c * x 5 (-e)) := by group
    _ = x 5 e * (x 0 (c * -e) * x 5 (-e) * x 1 c) := by rw [h2]
    _ = (x 5 e * x 0 (c * -e)) * x 5 (-e) * x 1 c := by group
    _ = (x 0 (c * -e) * x 5 e) * x 5 (-e) * x 1 c := by
        rw [((x_commute_12_32 (c * -e) e).symm).eq]
    _ = x 0 (c * -e) * (x 5 e * x 5 (-e)) * x 1 c := by group
    _ = x 0 (c * -e) * x 1 c := by
        rw [x_add, show e + -e = 0 from by ring, x_zero, mul_one]
    _ = x 0 (-(e * c)) * x 1 c := by
        rw [show c * -e = -(e * c) from by ring]

/-- `x₁(e) · x₂(c) · x₁(−e) = x₃(−ec) · x₂(c)`. -/
theorem sand1_conj (e c : ℤ) :
    x 1 e * x 2 c * x 1 (-e) = x 3 (-(e * c)) * x 2 c := by
  have h2 : x 2 c * x 1 (-e) = x 3 (c * -e) * x 1 (-e) * x 2 c := by
    calc x 2 c * x 1 (-e)
        = (x 2 c * x 1 (-e) * (x 2 c)⁻¹) * x 2 c := by group
      _ = x 3 (c * -e) * x 1 (-e) * x 2 c := by rw [x_conj_21_13]
  calc x 1 e * x 2 c * x 1 (-e)
      = x 1 e * (x 2 c * x 1 (-e)) := by group
    _ = x 1 e * (x 3 (c * -e) * x 1 (-e) * x 2 c) := by rw [h2]
    _ = (x 1 e * x 3 (c * -e)) * x 1 (-e) * x 2 c := by group
    _ = (x 3 (c * -e) * x 1 e) * x 1 (-e) * x 2 c := by
        rw [(x_commute_13_23 e (c * -e)).eq]
    _ = x 3 (c * -e) * (x 1 e * x 1 (-e)) * x 2 c := by group
    _ = x 3 (c * -e) * x 2 c := by
        rw [x_add, show e + -e = 0 from by ring, x_zero, mul_one]
    _ = x 3 (-(e * c)) * x 2 c := by
        rw [show c * -e = -(e * c) from by ring]

/-- `x₄(e) · x₃(c) · x₄(−e) = x₂(−ec) · x₃(c)`. -/
theorem sand4_conj (e c : ℤ) :
    x 4 e * x 3 c * x 4 (-e) = x 2 (-(e * c)) * x 3 c := by
  have h2 : x 3 c * x 4 (-e) = x 2 (c * -e) * x 4 (-e) * x 3 c := by
    calc x 3 c * x 4 (-e)
        = (x 3 c * x 4 (-e) * (x 3 c)⁻¹) * x 3 c := by group
      _ = x 2 (c * -e) * x 4 (-e) * x 3 c := by rw [x_conj_23_31]
  calc x 4 e * x 3 c * x 4 (-e)
      = x 4 e * (x 3 c * x 4 (-e)) := by group
    _ = x 4 e * (x 2 (c * -e) * x 4 (-e) * x 3 c) := by rw [h2]
    _ = (x 4 e * x 2 (c * -e)) * x 4 (-e) * x 3 c := by group
    _ = (x 2 (c * -e) * x 4 e) * x 4 (-e) * x 3 c := by
        rw [((x_commute_21_31 (c * -e) e).symm).eq]
    _ = x 2 (c * -e) * (x 4 e * x 4 (-e)) * x 3 c := by group
    _ = x 2 (c * -e) * x 3 c := by
        rw [x_add, show e + -e = 0 from by ring, x_zero, mul_one]
    _ = x 2 (-(e * c)) * x 3 c := by
        rw [show c * -e = -(e * c) from by ring]

/-- `x₀(e) · x₄(c) · x₀(−e) = x₅(−ec) · x₄(c)`. -/
theorem sand0_conj (e c : ℤ) :
    x 0 e * x 4 c * x 0 (-e) = x 5 (-(e * c)) * x 4 c := by
  have h2 : x 4 c * x 0 (-e) = x 5 (c * -e) * x 0 (-e) * x 4 c := by
    calc x 4 c * x 0 (-e)
        = (x 4 c * x 0 (-e) * (x 4 c)⁻¹) * x 4 c := by group
      _ = x 5 (c * -e) * x 0 (-e) * x 4 c := by rw [x_conj_31_12]
  calc x 0 e * x 4 c * x 0 (-e)
      = x 0 e * (x 4 c * x 0 (-e)) := by group
    _ = x 0 e * (x 5 (c * -e) * x 0 (-e) * x 4 c) := by rw [h2]
    _ = (x 0 e * x 5 (c * -e)) * x 0 (-e) * x 4 c := by group
    _ = (x 5 (c * -e) * x 0 e) * x 0 (-e) * x 4 c := by
        rw [(x_commute_12_32 e (c * -e)).eq]
    _ = x 5 (c * -e) * (x 0 e * x 0 (-e)) * x 4 c := by group
    _ = x 5 (c * -e) * x 4 c := by
        rw [x_add, show e + -e = 0 from by ring, x_zero, mul_one]
    _ = x 5 (-(e * c)) * x 4 c := by
        rw [show c * -e = -(e * c) from by ring]

/-- `x₂(e) · x₅(c) · x₂(−e) = x₄(−ec) · x₅(c)`. -/
theorem sand2_conj (e c : ℤ) :
    x 2 e * x 5 c * x 2 (-e) = x 4 (-(e * c)) * x 5 c := by
  have h2 : x 5 c * x 2 (-e) = x 4 (c * -e) * x 2 (-e) * x 5 c := by
    calc x 5 c * x 2 (-e)
        = (x 5 c * x 2 (-e) * (x 5 c)⁻¹) * x 5 c := by group
      _ = x 4 (c * -e) * x 2 (-e) * x 5 c := by rw [x_conj_32_21]
  calc x 2 e * x 5 c * x 2 (-e)
      = x 2 e * (x 5 c * x 2 (-e)) := by group
    _ = x 2 e * (x 4 (c * -e) * x 2 (-e) * x 5 c) := by rw [h2]
    _ = (x 2 e * x 4 (c * -e)) * x 2 (-e) * x 5 c := by group
    _ = (x 4 (c * -e) * x 2 e) * x 2 (-e) * x 5 c := by
        rw [(x_commute_21_31 e (c * -e)).eq]
    _ = x 4 (c * -e) * (x 2 e * x 2 (-e)) * x 5 c := by group
    _ = x 4 (c * -e) * x 5 c := by
        rw [x_add, show e + -e = 0 from by ring, x_zero, mul_one]
    _ = x 4 (-(e * c)) * x 5 c := by
        rw [show c * -e = -(e * c) from by ring]

/-! ## Same write: swap or one of two sandwiches cuts the peak -/

/-- `(e₁₂, e₁₃)`: both write `v₀`. -/
theorem exist_sw_01 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 0 c)) (act (toSL3 (x 1 cp)) u)) <
      vnorm (act (toSL3 (x 1 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 1 cp)) u)) :
    vnorm (act (toSL3 (x 0 c)) u) < vnorm (act (toSL3 (x 1 cp)) u) ∨
    (vnorm (act (toSL3 (x 3 (c * cp))) u) <
        vnorm (act (toSL3 (x 1 cp)) u) ∧
      vnorm (act (toSL3 (x 0 c)) (act (toSL3 (x 3 (c * cp))) u)) <
        vnorm (act (toSL3 (x 1 cp)) u)) ∨
    (vnorm (act (toSL3 (x 5 (c * cp))) u) <
        vnorm (act (toSL3 (x 1 cp)) u) ∧
      vnorm (act (toSL3 (x 1 cp)) (act (toSL3 (x 5 (c * cp))) u)) <
        vnorm (act (toSL3 (x 1 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;>
    simp only [act_x0, act_x1, act_x3, act_x5] at hviol hside ⊢ <;>
    simp [vnorm] at hviol hside ⊢ <;>
    omega

/-- `(e₁₃, e₁₂)`. -/
theorem exist_sw_10 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 1 c)) (act (toSL3 (x 0 cp)) u)) <
      vnorm (act (toSL3 (x 0 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 0 cp)) u)) :
    vnorm (act (toSL3 (x 1 c)) u) < vnorm (act (toSL3 (x 0 cp)) u) ∨
    (vnorm (act (toSL3 (x 5 (c * cp))) u) <
        vnorm (act (toSL3 (x 0 cp)) u) ∧
      vnorm (act (toSL3 (x 1 c)) (act (toSL3 (x 5 (c * cp))) u)) <
        vnorm (act (toSL3 (x 0 cp)) u)) ∨
    (vnorm (act (toSL3 (x 3 (c * cp))) u) <
        vnorm (act (toSL3 (x 0 cp)) u) ∧
      vnorm (act (toSL3 (x 0 cp)) (act (toSL3 (x 3 (c * cp))) u)) <
        vnorm (act (toSL3 (x 0 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;>
    simp only [act_x0, act_x1, act_x3, act_x5] at hviol hside ⊢ <;>
    simp [vnorm] at hviol hside ⊢ <;>
    omega

/-- `(e₂₁, e₂₃)`: both write `v₁`. -/
theorem exist_sw_23 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 2 c)) (act (toSL3 (x 3 cp)) u)) <
      vnorm (act (toSL3 (x 3 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 3 cp)) u)) :
    vnorm (act (toSL3 (x 2 c)) u) < vnorm (act (toSL3 (x 3 cp)) u) ∨
    (vnorm (act (toSL3 (x 1 (c * cp))) u) <
        vnorm (act (toSL3 (x 3 cp)) u) ∧
      vnorm (act (toSL3 (x 2 c)) (act (toSL3 (x 1 (c * cp))) u)) <
        vnorm (act (toSL3 (x 3 cp)) u)) ∨
    (vnorm (act (toSL3 (x 4 (c * cp))) u) <
        vnorm (act (toSL3 (x 3 cp)) u) ∧
      vnorm (act (toSL3 (x 3 cp)) (act (toSL3 (x 4 (c * cp))) u)) <
        vnorm (act (toSL3 (x 3 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;>
    simp only [act_x1, act_x2, act_x3, act_x4] at hviol hside ⊢ <;>
    simp [vnorm] at hviol hside ⊢ <;>
    omega

/-- `(e₂₃, e₂₁)`. -/
theorem exist_sw_32 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 3 c)) (act (toSL3 (x 2 cp)) u)) <
      vnorm (act (toSL3 (x 2 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 2 cp)) u)) :
    vnorm (act (toSL3 (x 3 c)) u) < vnorm (act (toSL3 (x 2 cp)) u) ∨
    (vnorm (act (toSL3 (x 4 (c * cp))) u) <
        vnorm (act (toSL3 (x 2 cp)) u) ∧
      vnorm (act (toSL3 (x 3 c)) (act (toSL3 (x 4 (c * cp))) u)) <
        vnorm (act (toSL3 (x 2 cp)) u)) ∨
    (vnorm (act (toSL3 (x 1 (c * cp))) u) <
        vnorm (act (toSL3 (x 2 cp)) u) ∧
      vnorm (act (toSL3 (x 2 cp)) (act (toSL3 (x 1 (c * cp))) u)) <
        vnorm (act (toSL3 (x 2 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;>
    simp only [act_x1, act_x2, act_x3, act_x4] at hviol hside ⊢ <;>
    simp [vnorm] at hviol hside ⊢ <;>
    omega

/-- `(e₃₁, e₃₂)`: both write `v₂`. -/
theorem exist_sw_45 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 4 c)) (act (toSL3 (x 5 cp)) u)) <
      vnorm (act (toSL3 (x 5 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 5 cp)) u)) :
    vnorm (act (toSL3 (x 4 c)) u) < vnorm (act (toSL3 (x 5 cp)) u) ∨
    (vnorm (act (toSL3 (x 0 (c * cp))) u) <
        vnorm (act (toSL3 (x 5 cp)) u) ∧
      vnorm (act (toSL3 (x 4 c)) (act (toSL3 (x 0 (c * cp))) u)) <
        vnorm (act (toSL3 (x 5 cp)) u)) ∨
    (vnorm (act (toSL3 (x 2 (c * cp))) u) <
        vnorm (act (toSL3 (x 5 cp)) u) ∧
      vnorm (act (toSL3 (x 5 cp)) (act (toSL3 (x 2 (c * cp))) u)) <
        vnorm (act (toSL3 (x 5 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;>
    simp only [act_x0, act_x2, act_x4, act_x5] at hviol hside ⊢ <;>
    simp [vnorm] at hviol hside ⊢ <;>
    omega

/-- `(e₃₂, e₃₁)`. -/
theorem exist_sw_54 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 5 c)) (act (toSL3 (x 4 cp)) u)) <
      vnorm (act (toSL3 (x 4 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 4 cp)) u)) :
    vnorm (act (toSL3 (x 5 c)) u) < vnorm (act (toSL3 (x 4 cp)) u) ∨
    (vnorm (act (toSL3 (x 2 (c * cp))) u) <
        vnorm (act (toSL3 (x 4 cp)) u) ∧
      vnorm (act (toSL3 (x 5 c)) (act (toSL3 (x 2 (c * cp))) u)) <
        vnorm (act (toSL3 (x 4 cp)) u)) ∨
    (vnorm (act (toSL3 (x 0 (c * cp))) u) <
        vnorm (act (toSL3 (x 4 cp)) u) ∧
      vnorm (act (toSL3 (x 4 cp)) (act (toSL3 (x 0 (c * cp))) u)) <
        vnorm (act (toSL3 (x 4 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;>
    simp only [act_x0, act_x2, act_x4, act_x5] at hviol hside ⊢ <;>
    simp [vnorm] at hviol hside ⊢ <;>
    omega

/-! ## Steinberg splits: the three orders of the composite letter -/

private theorem shuffle_mid {K Q P X : P13} (h : X = K * Q * P)
    (hKQ : K * Q = Q * K) : X = Q * K * P := by
  rw [h, hKQ]

private theorem shuffle_last {K Q P X : P13} (h : X = K * Q * P)
    (hKQ : K * Q = Q * K) (hKP : K * P = P * K) : X = Q * P * K := by
  rw [h]
  calc K * Q * P = (Q * K) * P := by rw [hKQ]
    _ = Q * (K * P) := by group
    _ = Q * (P * K) := by rw [hKP]
    _ = Q * P * K := by group

/-- `x₀(c) · x₃(cp) = x₁(c·cp) · x₃(cp) · x₀(c)`. -/
theorem st_03 (c cp : ℤ) :
    x 0 c * x 3 cp = x 1 (c * cp) * x 3 cp * x 0 c := by
  calc x 0 c * x 3 cp = (x 0 c * x 3 cp * (x 0 c)⁻¹) * x 0 c := by group
    _ = x 1 (c * cp) * x 3 cp * x 0 c := by rw [x_conj_12_23]

theorem st_03_mid (c cp : ℤ) :
    x 0 c * x 3 cp = x 3 cp * x 1 (c * cp) * x 0 c :=
  shuffle_mid (st_03 c cp) (x_commute_13_23 (c * cp) cp).eq

theorem st_03_last (c cp : ℤ) :
    x 0 c * x 3 cp = x 3 cp * x 0 c * x 1 (c * cp) :=
  shuffle_last (st_03 c cp) (x_commute_13_23 (c * cp) cp).eq
    ((x_commute_12_13 c (c * cp)).symm).eq

/-- `x₁(c) · x₅(cp) = x₀(c·cp) · x₅(cp) · x₁(c)`. -/
theorem st_15 (c cp : ℤ) :
    x 1 c * x 5 cp = x 0 (c * cp) * x 5 cp * x 1 c := by
  calc x 1 c * x 5 cp = (x 1 c * x 5 cp * (x 1 c)⁻¹) * x 1 c := by group
    _ = x 0 (c * cp) * x 5 cp * x 1 c := by rw [x_conj_13_32]

theorem st_15_mid (c cp : ℤ) :
    x 1 c * x 5 cp = x 5 cp * x 0 (c * cp) * x 1 c :=
  shuffle_mid (st_15 c cp) (x_commute_12_32 (c * cp) cp).eq

theorem st_15_last (c cp : ℤ) :
    x 1 c * x 5 cp = x 5 cp * x 1 c * x 0 (c * cp) :=
  shuffle_last (st_15 c cp) (x_commute_12_32 (c * cp) cp).eq
    (x_commute_12_13 (c * cp) c).eq

/-- `x₂(c) · x₁(cp) = x₃(c·cp) · x₁(cp) · x₂(c)`. -/
theorem st_21 (c cp : ℤ) :
    x 2 c * x 1 cp = x 3 (c * cp) * x 1 cp * x 2 c := by
  calc x 2 c * x 1 cp = (x 2 c * x 1 cp * (x 2 c)⁻¹) * x 2 c := by group
    _ = x 3 (c * cp) * x 1 cp * x 2 c := by rw [x_conj_21_13]

theorem st_21_mid (c cp : ℤ) :
    x 2 c * x 1 cp = x 1 cp * x 3 (c * cp) * x 2 c :=
  shuffle_mid (st_21 c cp) ((x_commute_13_23 cp (c * cp)).symm).eq

theorem st_21_last (c cp : ℤ) :
    x 2 c * x 1 cp = x 1 cp * x 2 c * x 3 (c * cp) :=
  shuffle_last (st_21 c cp) ((x_commute_13_23 cp (c * cp)).symm).eq
    ((x_commute_21_23 c (c * cp)).symm).eq

/-- `x₃(c) · x₄(cp) = x₂(c·cp) · x₄(cp) · x₃(c)`. -/
theorem st_34 (c cp : ℤ) :
    x 3 c * x 4 cp = x 2 (c * cp) * x 4 cp * x 3 c := by
  calc x 3 c * x 4 cp = (x 3 c * x 4 cp * (x 3 c)⁻¹) * x 3 c := by group
    _ = x 2 (c * cp) * x 4 cp * x 3 c := by rw [x_conj_23_31]

theorem st_34_mid (c cp : ℤ) :
    x 3 c * x 4 cp = x 4 cp * x 2 (c * cp) * x 3 c :=
  shuffle_mid (st_34 c cp) (x_commute_21_31 (c * cp) cp).eq

theorem st_34_last (c cp : ℤ) :
    x 3 c * x 4 cp = x 4 cp * x 3 c * x 2 (c * cp) :=
  shuffle_last (st_34 c cp) (x_commute_21_31 (c * cp) cp).eq
    (x_commute_21_23 (c * cp) c).eq

/-- `x₄(c) · x₀(cp) = x₅(c·cp) · x₀(cp) · x₄(c)`. -/
theorem st_40 (c cp : ℤ) :
    x 4 c * x 0 cp = x 5 (c * cp) * x 0 cp * x 4 c := by
  calc x 4 c * x 0 cp = (x 4 c * x 0 cp * (x 4 c)⁻¹) * x 4 c := by group
    _ = x 5 (c * cp) * x 0 cp * x 4 c := by rw [x_conj_31_12]

theorem st_40_mid (c cp : ℤ) :
    x 4 c * x 0 cp = x 0 cp * x 5 (c * cp) * x 4 c :=
  shuffle_mid (st_40 c cp) ((x_commute_12_32 cp (c * cp)).symm).eq

theorem st_40_last (c cp : ℤ) :
    x 4 c * x 0 cp = x 0 cp * x 4 c * x 5 (c * cp) :=
  shuffle_last (st_40 c cp) ((x_commute_12_32 cp (c * cp)).symm).eq
    ((x_commute_31_32 c (c * cp)).symm).eq

/-- `x₅(c) · x₂(cp) = x₄(c·cp) · x₂(cp) · x₅(c)`. -/
theorem st_52 (c cp : ℤ) :
    x 5 c * x 2 cp = x 4 (c * cp) * x 2 cp * x 5 c := by
  calc x 5 c * x 2 cp = (x 5 c * x 2 cp * (x 5 c)⁻¹) * x 5 c := by group
    _ = x 4 (c * cp) * x 2 cp * x 5 c := by rw [x_conj_32_21]

theorem st_52_mid (c cp : ℤ) :
    x 5 c * x 2 cp = x 2 cp * x 4 (c * cp) * x 5 c :=
  shuffle_mid (st_52 c cp) ((x_commute_21_31 cp (c * cp)).symm).eq

theorem st_52_last (c cp : ℤ) :
    x 5 c * x 2 cp = x 2 cp * x 5 c * x 4 (c * cp) :=
  shuffle_last (st_52 c cp) ((x_commute_21_31 cp (c * cp)).symm).eq
    (x_commute_31_32 (c * cp) c).eq

/-! ## Steinberg splits, reversed orientation -/

private theorem stB_of_stA {K Q P : P13}
    (h : Q * P = K * P * Q) : P * Q = K⁻¹ * Q * P := by
  calc P * Q = K⁻¹ * (K * P * Q) * Q⁻¹ * Q := by group
    _ = K⁻¹ * (Q * P) * Q⁻¹ * Q := by rw [← h]
    _ = K⁻¹ * Q * P := by group

/-- `x₃(c) · x₀(cp) = x₁(−(cp·c)) · x₀(cp) · x₃(c)`. -/
theorem stB_30 (c cp : ℤ) :
    x 3 c * x 0 cp = x 1 (-(cp * c)) * x 0 cp * x 3 c := by
  have h := stB_of_stA (st_03 cp c)
  rwa [← x_neg] at h

/-- `x₅(c) · x₁(cp) = x₀(−(cp·c)) · x₁(cp) · x₅(c)`. -/
theorem stB_51 (c cp : ℤ) :
    x 5 c * x 1 cp = x 0 (-(cp * c)) * x 1 cp * x 5 c := by
  have h := stB_of_stA (st_15 cp c)
  rwa [← x_neg] at h

/-- `x₁(c) · x₂(cp) = x₃(−(cp·c)) · x₂(cp) · x₁(c)`. -/
theorem stB_12 (c cp : ℤ) :
    x 1 c * x 2 cp = x 3 (-(cp * c)) * x 2 cp * x 1 c := by
  have h := stB_of_stA (st_21 cp c)
  rwa [← x_neg] at h

/-- `x₄(c) · x₃(cp) = x₂(−(cp·c)) · x₃(cp) · x₄(c)`. -/
theorem stB_43 (c cp : ℤ) :
    x 4 c * x 3 cp = x 2 (-(cp * c)) * x 3 cp * x 4 c := by
  have h := stB_of_stA (st_34 cp c)
  rwa [← x_neg] at h

/-- `x₀(c) · x₄(cp) = x₅(−(cp·c)) · x₄(cp) · x₀(c)`. -/
theorem stB_04 (c cp : ℤ) :
    x 0 c * x 4 cp = x 5 (-(cp * c)) * x 4 cp * x 0 c := by
  have h := stB_of_stA (st_40 cp c)
  rwa [← x_neg] at h

/-- `x₂(c) · x₅(cp) = x₄(−(cp·c)) · x₅(cp) · x₂(c)`. -/
theorem stB_25 (c cp : ℤ) :
    x 2 c * x 5 cp = x 4 (-(cp * c)) * x 5 cp * x 2 c := by
  have h := stB_of_stA (st_52 cp c)
  rwa [← x_neg] at h

/-! ## The emission spellings

Each Steinberg pair equals a three-letter block times the block Weyl
word of the deeper letter's family: the partner letter conjugates
past the shallow letter by a commutation, and the braid word cancels
by additivity.  The single generic shape covers all twelve pairs. -/

private theorem em_generic {Pp Qf Pt : Fin 6} (c cp : ℤ)
    (hcomm : x Pt cp * x Pp c = x Pp c * x Pt cp) :
    x Pt cp * x Pp c * x Qf (-cp) *
        (x Qf cp * x Pt (-cp) * x Qf cp) =
      x Pp c * x Qf cp := by
  have h1 : x Qf (-cp) * (x Qf cp * x Pt (-cp) * x Qf cp) =
      x Pt (-cp) * x Qf cp := by
    calc x Qf (-cp) * (x Qf cp * x Pt (-cp) * x Qf cp)
        = (x Qf (-cp) * x Qf cp) * (x Pt (-cp) * x Qf cp) := by group
      _ = x Pt (-cp) * x Qf cp := by
          rw [x_add, show -cp + cp = 0 from by ring, x_zero, one_mul]
  calc x Pt cp * x Pp c * x Qf (-cp) *
        (x Qf cp * x Pt (-cp) * x Qf cp)
      = x Pt cp * x Pp c *
          (x Qf (-cp) * (x Qf cp * x Pt (-cp) * x Qf cp)) := by group
    _ = x Pt cp * x Pp c * (x Pt (-cp) * x Qf cp) := by rw [h1]
    _ = (x Pt cp * x Pp c) * x Pt (-cp) * x Qf cp := by group
    _ = (x Pp c * x Pt cp) * x Pt (-cp) * x Qf cp := by rw [hcomm]
    _ = x Pp c * (x Pt cp * x Pt (-cp)) * x Qf cp := by group
    _ = x Pp c * x Qf cp := by
        rw [x_add, show cp + -cp = 0 from by ring, x_zero, mul_one]

theorem em_03 (c cp : ℤ) :
    x 5 cp * x 0 c * x 3 (-cp) * (x 3 cp * x 5 (-cp) * x 3 cp) =
      x 0 c * x 3 cp :=
  em_generic c cp ((x_commute_12_32 c cp).symm).eq

theorem em_15 (c cp : ℤ) :
    x 3 cp * x 1 c * x 5 (-cp) * (x 5 cp * x 3 (-cp) * x 5 cp) =
      x 1 c * x 5 cp :=
  em_generic c cp ((x_commute_13_23 c cp).symm).eq

theorem em_21 (c cp : ℤ) :
    x 4 cp * x 2 c * x 1 (-cp) * (x 1 cp * x 4 (-cp) * x 1 cp) =
      x 2 c * x 1 cp :=
  em_generic c cp ((x_commute_21_31 c cp).symm).eq

theorem em_34 (c cp : ℤ) :
    x 1 cp * x 3 c * x 4 (-cp) * (x 4 cp * x 1 (-cp) * x 4 cp) =
      x 3 c * x 4 cp :=
  em_generic c cp (x_commute_13_23 cp c).eq

theorem em_40 (c cp : ℤ) :
    x 2 cp * x 4 c * x 0 (-cp) * (x 0 cp * x 2 (-cp) * x 0 cp) =
      x 4 c * x 0 cp :=
  em_generic c cp (x_commute_21_31 cp c).eq

theorem em_52 (c cp : ℤ) :
    x 0 cp * x 5 c * x 2 (-cp) * (x 2 cp * x 0 (-cp) * x 2 cp) =
      x 5 c * x 2 cp :=
  em_generic c cp (x_commute_12_32 cp c).eq

/-! ## Steinberg existence: a split order or the emission cuts the peak

For the forward pairs all three split orders and the emission compete;
for the reversed pairs the first split order and the emission suffice.
The emission internals run over the base transported by the block
Weyl word of the deeper letter's family. -/

private theorem exist_st_03_pp (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 0 1)) (act (toSL3 (x 3 1)) u)) <
      vnorm (act (toSL3 (x 3 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 3 1)) u)) :
    (vnorm (act (toSL3 (x 0 1)) u) < vnorm (act (toSL3 (x 3 1)) u) ∧
      vnorm (act (toSL3 (x 3 1)) (act (toSL3 (x 0 1)) u)) <
        vnorm (act (toSL3 (x 3 1)) u)) ∨
    (vnorm (act (toSL3 (x 0 1)) u) < vnorm (act (toSL3 (x 3 1)) u) ∧
      vnorm (act (toSL3 (x 1 (1 * 1))) (act (toSL3 (x 0 1)) u)) <
        vnorm (act (toSL3 (x 3 1)) u)) ∨
    (vnorm (act (toSL3 (x 1 (1 * 1))) u) <
        vnorm (act (toSL3 (x 3 1)) u) ∧
      vnorm (act (toSL3 (x 0 1)) (act (toSL3 (x 1 (1 * 1))) u)) <
        vnorm (act (toSL3 (x 3 1)) u)) ∨
    (vnorm (act (toSL3 (x 3 (-1))) ![u 0, 1 * u 2, -(1 * u 1)]) <
        vnorm (act (toSL3 (x 3 1)) u) ∧
      vnorm (act (toSL3 (x 0 1)) (act (toSL3 (x 3 (-1)))
          ![u 0, 1 * u 2, -(1 * u 1)])) <
        vnorm (act (toSL3 (x 3 1)) u)) := by
  simp only [act_x0, act_x1, act_x3, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_03_pm (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 0 1)) (act (toSL3 (x 3 (-1))) u)) <
      vnorm (act (toSL3 (x 3 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 3 (-1))) u)) :
    (vnorm (act (toSL3 (x 0 1)) u) < vnorm (act (toSL3 (x 3 (-1))) u) ∧
      vnorm (act (toSL3 (x 3 (-1))) (act (toSL3 (x 0 1)) u)) <
        vnorm (act (toSL3 (x 3 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 0 1)) u) < vnorm (act (toSL3 (x 3 (-1))) u) ∧
      vnorm (act (toSL3 (x 1 (1 * (-1)))) (act (toSL3 (x 0 1)) u)) <
        vnorm (act (toSL3 (x 3 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 1 (1 * (-1)))) u) <
        vnorm (act (toSL3 (x 3 (-1))) u) ∧
      vnorm (act (toSL3 (x 0 1)) (act (toSL3 (x 1 (1 * (-1)))) u)) <
        vnorm (act (toSL3 (x 3 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 3 (-(-1)))) ![u 0, (-1) * u 2, -((-1) * u 1)]) <
        vnorm (act (toSL3 (x 3 (-1))) u) ∧
      vnorm (act (toSL3 (x 0 1)) (act (toSL3 (x 3 (-(-1))))
          ![u 0, (-1) * u 2, -((-1) * u 1)])) <
        vnorm (act (toSL3 (x 3 (-1))) u)) := by
  simp only [act_x0, act_x1, act_x3, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_03_mp (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 0 (-1))) (act (toSL3 (x 3 1)) u)) <
      vnorm (act (toSL3 (x 3 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 3 1)) u)) :
    (vnorm (act (toSL3 (x 0 (-1))) u) < vnorm (act (toSL3 (x 3 1)) u) ∧
      vnorm (act (toSL3 (x 3 1)) (act (toSL3 (x 0 (-1))) u)) <
        vnorm (act (toSL3 (x 3 1)) u)) ∨
    (vnorm (act (toSL3 (x 0 (-1))) u) < vnorm (act (toSL3 (x 3 1)) u) ∧
      vnorm (act (toSL3 (x 1 ((-1) * 1))) (act (toSL3 (x 0 (-1))) u)) <
        vnorm (act (toSL3 (x 3 1)) u)) ∨
    (vnorm (act (toSL3 (x 1 ((-1) * 1))) u) <
        vnorm (act (toSL3 (x 3 1)) u) ∧
      vnorm (act (toSL3 (x 0 (-1))) (act (toSL3 (x 1 ((-1) * 1))) u)) <
        vnorm (act (toSL3 (x 3 1)) u)) ∨
    (vnorm (act (toSL3 (x 3 (-1))) ![u 0, 1 * u 2, -(1 * u 1)]) <
        vnorm (act (toSL3 (x 3 1)) u) ∧
      vnorm (act (toSL3 (x 0 (-1))) (act (toSL3 (x 3 (-1)))
          ![u 0, 1 * u 2, -(1 * u 1)])) <
        vnorm (act (toSL3 (x 3 1)) u)) := by
  simp only [act_x0, act_x1, act_x3, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_03_mm (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 0 (-1))) (act (toSL3 (x 3 (-1))) u)) <
      vnorm (act (toSL3 (x 3 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 3 (-1))) u)) :
    (vnorm (act (toSL3 (x 0 (-1))) u) < vnorm (act (toSL3 (x 3 (-1))) u) ∧
      vnorm (act (toSL3 (x 3 (-1))) (act (toSL3 (x 0 (-1))) u)) <
        vnorm (act (toSL3 (x 3 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 0 (-1))) u) < vnorm (act (toSL3 (x 3 (-1))) u) ∧
      vnorm (act (toSL3 (x 1 ((-1) * (-1)))) (act (toSL3 (x 0 (-1))) u)) <
        vnorm (act (toSL3 (x 3 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 1 ((-1) * (-1)))) u) <
        vnorm (act (toSL3 (x 3 (-1))) u) ∧
      vnorm (act (toSL3 (x 0 (-1))) (act (toSL3 (x 1 ((-1) * (-1)))) u)) <
        vnorm (act (toSL3 (x 3 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 3 (-(-1)))) ![u 0, (-1) * u 2, -((-1) * u 1)]) <
        vnorm (act (toSL3 (x 3 (-1))) u) ∧
      vnorm (act (toSL3 (x 0 (-1))) (act (toSL3 (x 3 (-(-1))))
          ![u 0, (-1) * u 2, -((-1) * u 1)])) <
        vnorm (act (toSL3 (x 3 (-1))) u)) := by
  simp only [act_x0, act_x1, act_x3, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

theorem exist_st_03 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 0 c)) (act (toSL3 (x 3 cp)) u)) <
      vnorm (act (toSL3 (x 3 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 3 cp)) u)) :
    (vnorm (act (toSL3 (x 0 c)) u) < vnorm (act (toSL3 (x 3 cp)) u) ∧
      vnorm (act (toSL3 (x 3 cp)) (act (toSL3 (x 0 c)) u)) <
        vnorm (act (toSL3 (x 3 cp)) u)) ∨
    (vnorm (act (toSL3 (x 0 c)) u) < vnorm (act (toSL3 (x 3 cp)) u) ∧
      vnorm (act (toSL3 (x 1 (c * cp))) (act (toSL3 (x 0 c)) u)) <
        vnorm (act (toSL3 (x 3 cp)) u)) ∨
    (vnorm (act (toSL3 (x 1 (c * cp))) u) <
        vnorm (act (toSL3 (x 3 cp)) u) ∧
      vnorm (act (toSL3 (x 0 c)) (act (toSL3 (x 1 (c * cp))) u)) <
        vnorm (act (toSL3 (x 3 cp)) u)) ∨
    (vnorm (act (toSL3 (x 3 (-cp))) ![u 0, cp * u 2, -(cp * u 1)]) <
        vnorm (act (toSL3 (x 3 cp)) u) ∧
      vnorm (act (toSL3 (x 0 c)) (act (toSL3 (x 3 (-cp)))
          ![u 0, cp * u 2, -(cp * u 1)])) <
        vnorm (act (toSL3 (x 3 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
  exacts [exist_st_03_pp u hviol hside, exist_st_03_pm u hviol hside,
    exist_st_03_mp u hviol hside, exist_st_03_mm u hviol hside]

private theorem exist_st_21_pp (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 2 1)) (act (toSL3 (x 1 1)) u)) <
      vnorm (act (toSL3 (x 1 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 1 1)) u)) :
    (vnorm (act (toSL3 (x 2 1)) u) < vnorm (act (toSL3 (x 1 1)) u) ∧
      vnorm (act (toSL3 (x 1 1)) (act (toSL3 (x 2 1)) u)) <
        vnorm (act (toSL3 (x 1 1)) u)) ∨
    (vnorm (act (toSL3 (x 2 1)) u) < vnorm (act (toSL3 (x 1 1)) u) ∧
      vnorm (act (toSL3 (x 3 (1 * 1))) (act (toSL3 (x 2 1)) u)) <
        vnorm (act (toSL3 (x 1 1)) u)) ∨
    (vnorm (act (toSL3 (x 3 (1 * 1))) u) <
        vnorm (act (toSL3 (x 1 1)) u) ∧
      vnorm (act (toSL3 (x 2 1)) (act (toSL3 (x 3 (1 * 1))) u)) <
        vnorm (act (toSL3 (x 1 1)) u)) ∨
    (vnorm (act (toSL3 (x 1 (-1))) ![1 * u 2, u 1, -(1 * u 0)]) <
        vnorm (act (toSL3 (x 1 1)) u) ∧
      vnorm (act (toSL3 (x 2 1)) (act (toSL3 (x 1 (-1)))
          ![1 * u 2, u 1, -(1 * u 0)])) <
        vnorm (act (toSL3 (x 1 1)) u)) := by
  simp only [act_x1, act_x2, act_x3, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_21_pm (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 2 1)) (act (toSL3 (x 1 (-1))) u)) <
      vnorm (act (toSL3 (x 1 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 1 (-1))) u)) :
    (vnorm (act (toSL3 (x 2 1)) u) < vnorm (act (toSL3 (x 1 (-1))) u) ∧
      vnorm (act (toSL3 (x 1 (-1))) (act (toSL3 (x 2 1)) u)) <
        vnorm (act (toSL3 (x 1 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 2 1)) u) < vnorm (act (toSL3 (x 1 (-1))) u) ∧
      vnorm (act (toSL3 (x 3 (1 * (-1)))) (act (toSL3 (x 2 1)) u)) <
        vnorm (act (toSL3 (x 1 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 3 (1 * (-1)))) u) <
        vnorm (act (toSL3 (x 1 (-1))) u) ∧
      vnorm (act (toSL3 (x 2 1)) (act (toSL3 (x 3 (1 * (-1)))) u)) <
        vnorm (act (toSL3 (x 1 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 1 (-(-1)))) ![(-1) * u 2, u 1, -((-1) * u 0)]) <
        vnorm (act (toSL3 (x 1 (-1))) u) ∧
      vnorm (act (toSL3 (x 2 1)) (act (toSL3 (x 1 (-(-1))))
          ![(-1) * u 2, u 1, -((-1) * u 0)])) <
        vnorm (act (toSL3 (x 1 (-1))) u)) := by
  simp only [act_x1, act_x2, act_x3, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_21_mp (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 2 (-1))) (act (toSL3 (x 1 1)) u)) <
      vnorm (act (toSL3 (x 1 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 1 1)) u)) :
    (vnorm (act (toSL3 (x 2 (-1))) u) < vnorm (act (toSL3 (x 1 1)) u) ∧
      vnorm (act (toSL3 (x 1 1)) (act (toSL3 (x 2 (-1))) u)) <
        vnorm (act (toSL3 (x 1 1)) u)) ∨
    (vnorm (act (toSL3 (x 2 (-1))) u) < vnorm (act (toSL3 (x 1 1)) u) ∧
      vnorm (act (toSL3 (x 3 ((-1) * 1))) (act (toSL3 (x 2 (-1))) u)) <
        vnorm (act (toSL3 (x 1 1)) u)) ∨
    (vnorm (act (toSL3 (x 3 ((-1) * 1))) u) <
        vnorm (act (toSL3 (x 1 1)) u) ∧
      vnorm (act (toSL3 (x 2 (-1))) (act (toSL3 (x 3 ((-1) * 1))) u)) <
        vnorm (act (toSL3 (x 1 1)) u)) ∨
    (vnorm (act (toSL3 (x 1 (-1))) ![1 * u 2, u 1, -(1 * u 0)]) <
        vnorm (act (toSL3 (x 1 1)) u) ∧
      vnorm (act (toSL3 (x 2 (-1))) (act (toSL3 (x 1 (-1)))
          ![1 * u 2, u 1, -(1 * u 0)])) <
        vnorm (act (toSL3 (x 1 1)) u)) := by
  simp only [act_x1, act_x2, act_x3, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_21_mm (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 2 (-1))) (act (toSL3 (x 1 (-1))) u)) <
      vnorm (act (toSL3 (x 1 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 1 (-1))) u)) :
    (vnorm (act (toSL3 (x 2 (-1))) u) < vnorm (act (toSL3 (x 1 (-1))) u) ∧
      vnorm (act (toSL3 (x 1 (-1))) (act (toSL3 (x 2 (-1))) u)) <
        vnorm (act (toSL3 (x 1 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 2 (-1))) u) < vnorm (act (toSL3 (x 1 (-1))) u) ∧
      vnorm (act (toSL3 (x 3 ((-1) * (-1)))) (act (toSL3 (x 2 (-1))) u)) <
        vnorm (act (toSL3 (x 1 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 3 ((-1) * (-1)))) u) <
        vnorm (act (toSL3 (x 1 (-1))) u) ∧
      vnorm (act (toSL3 (x 2 (-1))) (act (toSL3 (x 3 ((-1) * (-1)))) u)) <
        vnorm (act (toSL3 (x 1 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 1 (-(-1)))) ![(-1) * u 2, u 1, -((-1) * u 0)]) <
        vnorm (act (toSL3 (x 1 (-1))) u) ∧
      vnorm (act (toSL3 (x 2 (-1))) (act (toSL3 (x 1 (-(-1))))
          ![(-1) * u 2, u 1, -((-1) * u 0)])) <
        vnorm (act (toSL3 (x 1 (-1))) u)) := by
  simp only [act_x1, act_x2, act_x3, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

theorem exist_st_21 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 2 c)) (act (toSL3 (x 1 cp)) u)) <
      vnorm (act (toSL3 (x 1 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 1 cp)) u)) :
    (vnorm (act (toSL3 (x 2 c)) u) < vnorm (act (toSL3 (x 1 cp)) u) ∧
      vnorm (act (toSL3 (x 1 cp)) (act (toSL3 (x 2 c)) u)) <
        vnorm (act (toSL3 (x 1 cp)) u)) ∨
    (vnorm (act (toSL3 (x 2 c)) u) < vnorm (act (toSL3 (x 1 cp)) u) ∧
      vnorm (act (toSL3 (x 3 (c * cp))) (act (toSL3 (x 2 c)) u)) <
        vnorm (act (toSL3 (x 1 cp)) u)) ∨
    (vnorm (act (toSL3 (x 3 (c * cp))) u) <
        vnorm (act (toSL3 (x 1 cp)) u) ∧
      vnorm (act (toSL3 (x 2 c)) (act (toSL3 (x 3 (c * cp))) u)) <
        vnorm (act (toSL3 (x 1 cp)) u)) ∨
    (vnorm (act (toSL3 (x 1 (-cp))) ![cp * u 2, u 1, -(cp * u 0)]) <
        vnorm (act (toSL3 (x 1 cp)) u) ∧
      vnorm (act (toSL3 (x 2 c)) (act (toSL3 (x 1 (-cp)))
          ![cp * u 2, u 1, -(cp * u 0)])) <
        vnorm (act (toSL3 (x 1 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
  exacts [exist_st_21_pp u hviol hside, exist_st_21_pm u hviol hside,
    exist_st_21_mp u hviol hside, exist_st_21_mm u hviol hside]

private theorem exist_st_40_pp (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 4 1)) (act (toSL3 (x 0 1)) u)) <
      vnorm (act (toSL3 (x 0 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 0 1)) u)) :
    (vnorm (act (toSL3 (x 4 1)) u) < vnorm (act (toSL3 (x 0 1)) u) ∧
      vnorm (act (toSL3 (x 0 1)) (act (toSL3 (x 4 1)) u)) <
        vnorm (act (toSL3 (x 0 1)) u)) ∨
    (vnorm (act (toSL3 (x 4 1)) u) < vnorm (act (toSL3 (x 0 1)) u) ∧
      vnorm (act (toSL3 (x 5 (1 * 1))) (act (toSL3 (x 4 1)) u)) <
        vnorm (act (toSL3 (x 0 1)) u)) ∨
    (vnorm (act (toSL3 (x 5 (1 * 1))) u) <
        vnorm (act (toSL3 (x 0 1)) u) ∧
      vnorm (act (toSL3 (x 4 1)) (act (toSL3 (x 5 (1 * 1))) u)) <
        vnorm (act (toSL3 (x 0 1)) u)) ∨
    (vnorm (act (toSL3 (x 0 (-1))) ![1 * u 1, -(1 * u 0), u 2]) <
        vnorm (act (toSL3 (x 0 1)) u) ∧
      vnorm (act (toSL3 (x 4 1)) (act (toSL3 (x 0 (-1)))
          ![1 * u 1, -(1 * u 0), u 2])) <
        vnorm (act (toSL3 (x 0 1)) u)) := by
  simp only [act_x0, act_x4, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_40_pm (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 4 1)) (act (toSL3 (x 0 (-1))) u)) <
      vnorm (act (toSL3 (x 0 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 0 (-1))) u)) :
    (vnorm (act (toSL3 (x 4 1)) u) < vnorm (act (toSL3 (x 0 (-1))) u) ∧
      vnorm (act (toSL3 (x 0 (-1))) (act (toSL3 (x 4 1)) u)) <
        vnorm (act (toSL3 (x 0 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 4 1)) u) < vnorm (act (toSL3 (x 0 (-1))) u) ∧
      vnorm (act (toSL3 (x 5 (1 * (-1)))) (act (toSL3 (x 4 1)) u)) <
        vnorm (act (toSL3 (x 0 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 5 (1 * (-1)))) u) <
        vnorm (act (toSL3 (x 0 (-1))) u) ∧
      vnorm (act (toSL3 (x 4 1)) (act (toSL3 (x 5 (1 * (-1)))) u)) <
        vnorm (act (toSL3 (x 0 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 0 (-(-1)))) ![(-1) * u 1, -((-1) * u 0), u 2]) <
        vnorm (act (toSL3 (x 0 (-1))) u) ∧
      vnorm (act (toSL3 (x 4 1)) (act (toSL3 (x 0 (-(-1))))
          ![(-1) * u 1, -((-1) * u 0), u 2])) <
        vnorm (act (toSL3 (x 0 (-1))) u)) := by
  simp only [act_x0, act_x4, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_40_mp (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 4 (-1))) (act (toSL3 (x 0 1)) u)) <
      vnorm (act (toSL3 (x 0 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 0 1)) u)) :
    (vnorm (act (toSL3 (x 4 (-1))) u) < vnorm (act (toSL3 (x 0 1)) u) ∧
      vnorm (act (toSL3 (x 0 1)) (act (toSL3 (x 4 (-1))) u)) <
        vnorm (act (toSL3 (x 0 1)) u)) ∨
    (vnorm (act (toSL3 (x 4 (-1))) u) < vnorm (act (toSL3 (x 0 1)) u) ∧
      vnorm (act (toSL3 (x 5 ((-1) * 1))) (act (toSL3 (x 4 (-1))) u)) <
        vnorm (act (toSL3 (x 0 1)) u)) ∨
    (vnorm (act (toSL3 (x 5 ((-1) * 1))) u) <
        vnorm (act (toSL3 (x 0 1)) u) ∧
      vnorm (act (toSL3 (x 4 (-1))) (act (toSL3 (x 5 ((-1) * 1))) u)) <
        vnorm (act (toSL3 (x 0 1)) u)) ∨
    (vnorm (act (toSL3 (x 0 (-1))) ![1 * u 1, -(1 * u 0), u 2]) <
        vnorm (act (toSL3 (x 0 1)) u) ∧
      vnorm (act (toSL3 (x 4 (-1))) (act (toSL3 (x 0 (-1)))
          ![1 * u 1, -(1 * u 0), u 2])) <
        vnorm (act (toSL3 (x 0 1)) u)) := by
  simp only [act_x0, act_x4, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_40_mm (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 4 (-1))) (act (toSL3 (x 0 (-1))) u)) <
      vnorm (act (toSL3 (x 0 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 0 (-1))) u)) :
    (vnorm (act (toSL3 (x 4 (-1))) u) < vnorm (act (toSL3 (x 0 (-1))) u) ∧
      vnorm (act (toSL3 (x 0 (-1))) (act (toSL3 (x 4 (-1))) u)) <
        vnorm (act (toSL3 (x 0 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 4 (-1))) u) < vnorm (act (toSL3 (x 0 (-1))) u) ∧
      vnorm (act (toSL3 (x 5 ((-1) * (-1)))) (act (toSL3 (x 4 (-1))) u)) <
        vnorm (act (toSL3 (x 0 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 5 ((-1) * (-1)))) u) <
        vnorm (act (toSL3 (x 0 (-1))) u) ∧
      vnorm (act (toSL3 (x 4 (-1))) (act (toSL3 (x 5 ((-1) * (-1)))) u)) <
        vnorm (act (toSL3 (x 0 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 0 (-(-1)))) ![(-1) * u 1, -((-1) * u 0), u 2]) <
        vnorm (act (toSL3 (x 0 (-1))) u) ∧
      vnorm (act (toSL3 (x 4 (-1))) (act (toSL3 (x 0 (-(-1))))
          ![(-1) * u 1, -((-1) * u 0), u 2])) <
        vnorm (act (toSL3 (x 0 (-1))) u)) := by
  simp only [act_x0, act_x4, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

theorem exist_st_40 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 4 c)) (act (toSL3 (x 0 cp)) u)) <
      vnorm (act (toSL3 (x 0 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 0 cp)) u)) :
    (vnorm (act (toSL3 (x 4 c)) u) < vnorm (act (toSL3 (x 0 cp)) u) ∧
      vnorm (act (toSL3 (x 0 cp)) (act (toSL3 (x 4 c)) u)) <
        vnorm (act (toSL3 (x 0 cp)) u)) ∨
    (vnorm (act (toSL3 (x 4 c)) u) < vnorm (act (toSL3 (x 0 cp)) u) ∧
      vnorm (act (toSL3 (x 5 (c * cp))) (act (toSL3 (x 4 c)) u)) <
        vnorm (act (toSL3 (x 0 cp)) u)) ∨
    (vnorm (act (toSL3 (x 5 (c * cp))) u) <
        vnorm (act (toSL3 (x 0 cp)) u) ∧
      vnorm (act (toSL3 (x 4 c)) (act (toSL3 (x 5 (c * cp))) u)) <
        vnorm (act (toSL3 (x 0 cp)) u)) ∨
    (vnorm (act (toSL3 (x 0 (-cp))) ![cp * u 1, -(cp * u 0), u 2]) <
        vnorm (act (toSL3 (x 0 cp)) u) ∧
      vnorm (act (toSL3 (x 4 c)) (act (toSL3 (x 0 (-cp)))
          ![cp * u 1, -(cp * u 0), u 2])) <
        vnorm (act (toSL3 (x 0 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
  exacts [exist_st_40_pp u hviol hside, exist_st_40_pm u hviol hside,
    exist_st_40_mp u hviol hside, exist_st_40_mm u hviol hside]

private theorem exist_st_30_pp (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 3 1)) (act (toSL3 (x 0 1)) u)) <
      vnorm (act (toSL3 (x 0 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 0 1)) u)) :
    (vnorm (act (toSL3 (x 3 1)) u) < vnorm (act (toSL3 (x 0 1)) u) ∧
      vnorm (act (toSL3 (x 0 1)) (act (toSL3 (x 3 1)) u)) <
        vnorm (act (toSL3 (x 0 1)) u)) ∨
    (vnorm (act (toSL3 (x 3 (-1))) ![u 0, 1 * u 2, -(1 * u 1)]) <
        vnorm (act (toSL3 (x 0 1)) u) ∧
      vnorm (act (toSL3 (x 1 (-(1 * 1)))) (act (toSL3 (x 3 (-1)))
          ![u 0, 1 * u 2, -(1 * u 1)])) <
        vnorm (act (toSL3 (x 0 1)) u)) := by
  simp only [act_x0, act_x1, act_x3, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_30_pm (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 3 1)) (act (toSL3 (x 0 (-1))) u)) <
      vnorm (act (toSL3 (x 0 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 0 (-1))) u)) :
    (vnorm (act (toSL3 (x 3 1)) u) < vnorm (act (toSL3 (x 0 (-1))) u) ∧
      vnorm (act (toSL3 (x 0 (-1))) (act (toSL3 (x 3 1)) u)) <
        vnorm (act (toSL3 (x 0 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 3 (-1))) ![u 0, 1 * u 2, -(1 * u 1)]) <
        vnorm (act (toSL3 (x 0 (-1))) u) ∧
      vnorm (act (toSL3 (x 1 (-(1 * (-1))))) (act (toSL3 (x 3 (-1)))
          ![u 0, 1 * u 2, -(1 * u 1)])) <
        vnorm (act (toSL3 (x 0 (-1))) u)) := by
  simp only [act_x0, act_x1, act_x3, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_30_mp (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 3 (-1))) (act (toSL3 (x 0 1)) u)) <
      vnorm (act (toSL3 (x 0 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 0 1)) u)) :
    (vnorm (act (toSL3 (x 3 (-1))) u) < vnorm (act (toSL3 (x 0 1)) u) ∧
      vnorm (act (toSL3 (x 0 1)) (act (toSL3 (x 3 (-1))) u)) <
        vnorm (act (toSL3 (x 0 1)) u)) ∨
    (vnorm (act (toSL3 (x 3 (-(-1)))) ![u 0, (-1) * u 2, -((-1) * u 1)]) <
        vnorm (act (toSL3 (x 0 1)) u) ∧
      vnorm (act (toSL3 (x 1 (-((-1) * 1)))) (act (toSL3 (x 3 (-(-1))))
          ![u 0, (-1) * u 2, -((-1) * u 1)])) <
        vnorm (act (toSL3 (x 0 1)) u)) := by
  simp only [act_x0, act_x1, act_x3, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_30_mm (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 3 (-1))) (act (toSL3 (x 0 (-1))) u)) <
      vnorm (act (toSL3 (x 0 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 0 (-1))) u)) :
    (vnorm (act (toSL3 (x 3 (-1))) u) < vnorm (act (toSL3 (x 0 (-1))) u) ∧
      vnorm (act (toSL3 (x 0 (-1))) (act (toSL3 (x 3 (-1))) u)) <
        vnorm (act (toSL3 (x 0 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 3 (-(-1)))) ![u 0, (-1) * u 2, -((-1) * u 1)]) <
        vnorm (act (toSL3 (x 0 (-1))) u) ∧
      vnorm (act (toSL3 (x 1 (-((-1) * (-1))))) (act (toSL3 (x 3 (-(-1))))
          ![u 0, (-1) * u 2, -((-1) * u 1)])) <
        vnorm (act (toSL3 (x 0 (-1))) u)) := by
  simp only [act_x0, act_x1, act_x3, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

theorem exist_st_30 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 3 c)) (act (toSL3 (x 0 cp)) u)) <
      vnorm (act (toSL3 (x 0 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 0 cp)) u)) :
    (vnorm (act (toSL3 (x 3 c)) u) < vnorm (act (toSL3 (x 0 cp)) u) ∧
      vnorm (act (toSL3 (x 0 cp)) (act (toSL3 (x 3 c)) u)) <
        vnorm (act (toSL3 (x 0 cp)) u)) ∨
    (vnorm (act (toSL3 (x 3 (-c))) ![u 0, c * u 2, -(c * u 1)]) <
        vnorm (act (toSL3 (x 0 cp)) u) ∧
      vnorm (act (toSL3 (x 1 (-(c * cp)))) (act (toSL3 (x 3 (-c)))
          ![u 0, c * u 2, -(c * u 1)])) <
        vnorm (act (toSL3 (x 0 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
  exacts [exist_st_30_pp u hviol hside, exist_st_30_pm u hviol hside,
    exist_st_30_mp u hviol hside, exist_st_30_mm u hviol hside]

private theorem exist_st_51_pp (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 5 1)) (act (toSL3 (x 1 1)) u)) <
      vnorm (act (toSL3 (x 1 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 1 1)) u)) :
    (vnorm (act (toSL3 (x 5 1)) u) < vnorm (act (toSL3 (x 1 1)) u) ∧
      vnorm (act (toSL3 (x 1 1)) (act (toSL3 (x 5 1)) u)) <
        vnorm (act (toSL3 (x 1 1)) u)) ∨
    (vnorm (act (toSL3 (x 5 (-1))) ![u 0, -(1 * u 2), 1 * u 1]) <
        vnorm (act (toSL3 (x 1 1)) u) ∧
      vnorm (act (toSL3 (x 0 (-(1 * 1)))) (act (toSL3 (x 5 (-1)))
          ![u 0, -(1 * u 2), 1 * u 1])) <
        vnorm (act (toSL3 (x 1 1)) u)) := by
  simp only [act_x0, act_x1, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_51_pm (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 5 1)) (act (toSL3 (x 1 (-1))) u)) <
      vnorm (act (toSL3 (x 1 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 1 (-1))) u)) :
    (vnorm (act (toSL3 (x 5 1)) u) < vnorm (act (toSL3 (x 1 (-1))) u) ∧
      vnorm (act (toSL3 (x 1 (-1))) (act (toSL3 (x 5 1)) u)) <
        vnorm (act (toSL3 (x 1 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 5 (-1))) ![u 0, -(1 * u 2), 1 * u 1]) <
        vnorm (act (toSL3 (x 1 (-1))) u) ∧
      vnorm (act (toSL3 (x 0 (-(1 * (-1))))) (act (toSL3 (x 5 (-1)))
          ![u 0, -(1 * u 2), 1 * u 1])) <
        vnorm (act (toSL3 (x 1 (-1))) u)) := by
  simp only [act_x0, act_x1, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_51_mp (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 5 (-1))) (act (toSL3 (x 1 1)) u)) <
      vnorm (act (toSL3 (x 1 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 1 1)) u)) :
    (vnorm (act (toSL3 (x 5 (-1))) u) < vnorm (act (toSL3 (x 1 1)) u) ∧
      vnorm (act (toSL3 (x 1 1)) (act (toSL3 (x 5 (-1))) u)) <
        vnorm (act (toSL3 (x 1 1)) u)) ∨
    (vnorm (act (toSL3 (x 5 (-(-1)))) ![u 0, -((-1) * u 2), (-1) * u 1]) <
        vnorm (act (toSL3 (x 1 1)) u) ∧
      vnorm (act (toSL3 (x 0 (-((-1) * 1)))) (act (toSL3 (x 5 (-(-1))))
          ![u 0, -((-1) * u 2), (-1) * u 1])) <
        vnorm (act (toSL3 (x 1 1)) u)) := by
  simp only [act_x0, act_x1, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_51_mm (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 5 (-1))) (act (toSL3 (x 1 (-1))) u)) <
      vnorm (act (toSL3 (x 1 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 1 (-1))) u)) :
    (vnorm (act (toSL3 (x 5 (-1))) u) < vnorm (act (toSL3 (x 1 (-1))) u) ∧
      vnorm (act (toSL3 (x 1 (-1))) (act (toSL3 (x 5 (-1))) u)) <
        vnorm (act (toSL3 (x 1 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 5 (-(-1)))) ![u 0, -((-1) * u 2), (-1) * u 1]) <
        vnorm (act (toSL3 (x 1 (-1))) u) ∧
      vnorm (act (toSL3 (x 0 (-((-1) * (-1))))) (act (toSL3 (x 5 (-(-1))))
          ![u 0, -((-1) * u 2), (-1) * u 1])) <
        vnorm (act (toSL3 (x 1 (-1))) u)) := by
  simp only [act_x0, act_x1, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

theorem exist_st_51 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 5 c)) (act (toSL3 (x 1 cp)) u)) <
      vnorm (act (toSL3 (x 1 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 1 cp)) u)) :
    (vnorm (act (toSL3 (x 5 c)) u) < vnorm (act (toSL3 (x 1 cp)) u) ∧
      vnorm (act (toSL3 (x 1 cp)) (act (toSL3 (x 5 c)) u)) <
        vnorm (act (toSL3 (x 1 cp)) u)) ∨
    (vnorm (act (toSL3 (x 5 (-c))) ![u 0, -(c * u 2), c * u 1]) <
        vnorm (act (toSL3 (x 1 cp)) u) ∧
      vnorm (act (toSL3 (x 0 (-(c * cp)))) (act (toSL3 (x 5 (-c)))
          ![u 0, -(c * u 2), c * u 1])) <
        vnorm (act (toSL3 (x 1 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
  exacts [exist_st_51_pp u hviol hside, exist_st_51_pm u hviol hside,
    exist_st_51_mp u hviol hside, exist_st_51_mm u hviol hside]

private theorem exist_st_12_pp (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 1 1)) (act (toSL3 (x 2 1)) u)) <
      vnorm (act (toSL3 (x 2 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 2 1)) u)) :
    (vnorm (act (toSL3 (x 1 1)) u) < vnorm (act (toSL3 (x 2 1)) u) ∧
      vnorm (act (toSL3 (x 2 1)) (act (toSL3 (x 1 1)) u)) <
        vnorm (act (toSL3 (x 2 1)) u)) ∨
    (vnorm (act (toSL3 (x 1 (-1))) ![1 * u 2, u 1, -(1 * u 0)]) <
        vnorm (act (toSL3 (x 2 1)) u) ∧
      vnorm (act (toSL3 (x 3 (-(1 * 1)))) (act (toSL3 (x 1 (-1)))
          ![1 * u 2, u 1, -(1 * u 0)])) <
        vnorm (act (toSL3 (x 2 1)) u)) := by
  simp only [act_x1, act_x2, act_x3, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_12_pm (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 1 1)) (act (toSL3 (x 2 (-1))) u)) <
      vnorm (act (toSL3 (x 2 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 2 (-1))) u)) :
    (vnorm (act (toSL3 (x 1 1)) u) < vnorm (act (toSL3 (x 2 (-1))) u) ∧
      vnorm (act (toSL3 (x 2 (-1))) (act (toSL3 (x 1 1)) u)) <
        vnorm (act (toSL3 (x 2 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 1 (-1))) ![1 * u 2, u 1, -(1 * u 0)]) <
        vnorm (act (toSL3 (x 2 (-1))) u) ∧
      vnorm (act (toSL3 (x 3 (-(1 * (-1))))) (act (toSL3 (x 1 (-1)))
          ![1 * u 2, u 1, -(1 * u 0)])) <
        vnorm (act (toSL3 (x 2 (-1))) u)) := by
  simp only [act_x1, act_x2, act_x3, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_12_mp (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 1 (-1))) (act (toSL3 (x 2 1)) u)) <
      vnorm (act (toSL3 (x 2 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 2 1)) u)) :
    (vnorm (act (toSL3 (x 1 (-1))) u) < vnorm (act (toSL3 (x 2 1)) u) ∧
      vnorm (act (toSL3 (x 2 1)) (act (toSL3 (x 1 (-1))) u)) <
        vnorm (act (toSL3 (x 2 1)) u)) ∨
    (vnorm (act (toSL3 (x 1 (-(-1)))) ![(-1) * u 2, u 1, -((-1) * u 0)]) <
        vnorm (act (toSL3 (x 2 1)) u) ∧
      vnorm (act (toSL3 (x 3 (-((-1) * 1)))) (act (toSL3 (x 1 (-(-1))))
          ![(-1) * u 2, u 1, -((-1) * u 0)])) <
        vnorm (act (toSL3 (x 2 1)) u)) := by
  simp only [act_x1, act_x2, act_x3, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_12_mm (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 1 (-1))) (act (toSL3 (x 2 (-1))) u)) <
      vnorm (act (toSL3 (x 2 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 2 (-1))) u)) :
    (vnorm (act (toSL3 (x 1 (-1))) u) < vnorm (act (toSL3 (x 2 (-1))) u) ∧
      vnorm (act (toSL3 (x 2 (-1))) (act (toSL3 (x 1 (-1))) u)) <
        vnorm (act (toSL3 (x 2 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 1 (-(-1)))) ![(-1) * u 2, u 1, -((-1) * u 0)]) <
        vnorm (act (toSL3 (x 2 (-1))) u) ∧
      vnorm (act (toSL3 (x 3 (-((-1) * (-1))))) (act (toSL3 (x 1 (-(-1))))
          ![(-1) * u 2, u 1, -((-1) * u 0)])) <
        vnorm (act (toSL3 (x 2 (-1))) u)) := by
  simp only [act_x1, act_x2, act_x3, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

theorem exist_st_12 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 1 c)) (act (toSL3 (x 2 cp)) u)) <
      vnorm (act (toSL3 (x 2 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 2 cp)) u)) :
    (vnorm (act (toSL3 (x 1 c)) u) < vnorm (act (toSL3 (x 2 cp)) u) ∧
      vnorm (act (toSL3 (x 2 cp)) (act (toSL3 (x 1 c)) u)) <
        vnorm (act (toSL3 (x 2 cp)) u)) ∨
    (vnorm (act (toSL3 (x 1 (-c))) ![c * u 2, u 1, -(c * u 0)]) <
        vnorm (act (toSL3 (x 2 cp)) u) ∧
      vnorm (act (toSL3 (x 3 (-(c * cp)))) (act (toSL3 (x 1 (-c)))
          ![c * u 2, u 1, -(c * u 0)])) <
        vnorm (act (toSL3 (x 2 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
  exacts [exist_st_12_pp u hviol hside, exist_st_12_pm u hviol hside,
    exist_st_12_mp u hviol hside, exist_st_12_mm u hviol hside]

private theorem exist_st_43_pp (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 4 1)) (act (toSL3 (x 3 1)) u)) <
      vnorm (act (toSL3 (x 3 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 3 1)) u)) :
    (vnorm (act (toSL3 (x 4 1)) u) < vnorm (act (toSL3 (x 3 1)) u) ∧
      vnorm (act (toSL3 (x 3 1)) (act (toSL3 (x 4 1)) u)) <
        vnorm (act (toSL3 (x 3 1)) u)) ∨
    (vnorm (act (toSL3 (x 4 (-1))) ![-(1 * u 2), u 1, 1 * u 0]) <
        vnorm (act (toSL3 (x 3 1)) u) ∧
      vnorm (act (toSL3 (x 2 (-(1 * 1)))) (act (toSL3 (x 4 (-1)))
          ![-(1 * u 2), u 1, 1 * u 0])) <
        vnorm (act (toSL3 (x 3 1)) u)) := by
  simp only [act_x2, act_x3, act_x4, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_43_pm (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 4 1)) (act (toSL3 (x 3 (-1))) u)) <
      vnorm (act (toSL3 (x 3 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 3 (-1))) u)) :
    (vnorm (act (toSL3 (x 4 1)) u) < vnorm (act (toSL3 (x 3 (-1))) u) ∧
      vnorm (act (toSL3 (x 3 (-1))) (act (toSL3 (x 4 1)) u)) <
        vnorm (act (toSL3 (x 3 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 4 (-1))) ![-(1 * u 2), u 1, 1 * u 0]) <
        vnorm (act (toSL3 (x 3 (-1))) u) ∧
      vnorm (act (toSL3 (x 2 (-(1 * (-1))))) (act (toSL3 (x 4 (-1)))
          ![-(1 * u 2), u 1, 1 * u 0])) <
        vnorm (act (toSL3 (x 3 (-1))) u)) := by
  simp only [act_x2, act_x3, act_x4, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_43_mp (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 4 (-1))) (act (toSL3 (x 3 1)) u)) <
      vnorm (act (toSL3 (x 3 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 3 1)) u)) :
    (vnorm (act (toSL3 (x 4 (-1))) u) < vnorm (act (toSL3 (x 3 1)) u) ∧
      vnorm (act (toSL3 (x 3 1)) (act (toSL3 (x 4 (-1))) u)) <
        vnorm (act (toSL3 (x 3 1)) u)) ∨
    (vnorm (act (toSL3 (x 4 (-(-1)))) ![-((-1) * u 2), u 1, (-1) * u 0]) <
        vnorm (act (toSL3 (x 3 1)) u) ∧
      vnorm (act (toSL3 (x 2 (-((-1) * 1)))) (act (toSL3 (x 4 (-(-1))))
          ![-((-1) * u 2), u 1, (-1) * u 0])) <
        vnorm (act (toSL3 (x 3 1)) u)) := by
  simp only [act_x2, act_x3, act_x4, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_43_mm (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 4 (-1))) (act (toSL3 (x 3 (-1))) u)) <
      vnorm (act (toSL3 (x 3 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 3 (-1))) u)) :
    (vnorm (act (toSL3 (x 4 (-1))) u) < vnorm (act (toSL3 (x 3 (-1))) u) ∧
      vnorm (act (toSL3 (x 3 (-1))) (act (toSL3 (x 4 (-1))) u)) <
        vnorm (act (toSL3 (x 3 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 4 (-(-1)))) ![-((-1) * u 2), u 1, (-1) * u 0]) <
        vnorm (act (toSL3 (x 3 (-1))) u) ∧
      vnorm (act (toSL3 (x 2 (-((-1) * (-1))))) (act (toSL3 (x 4 (-(-1))))
          ![-((-1) * u 2), u 1, (-1) * u 0])) <
        vnorm (act (toSL3 (x 3 (-1))) u)) := by
  simp only [act_x2, act_x3, act_x4, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

theorem exist_st_43 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 4 c)) (act (toSL3 (x 3 cp)) u)) <
      vnorm (act (toSL3 (x 3 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 3 cp)) u)) :
    (vnorm (act (toSL3 (x 4 c)) u) < vnorm (act (toSL3 (x 3 cp)) u) ∧
      vnorm (act (toSL3 (x 3 cp)) (act (toSL3 (x 4 c)) u)) <
        vnorm (act (toSL3 (x 3 cp)) u)) ∨
    (vnorm (act (toSL3 (x 4 (-c))) ![-(c * u 2), u 1, c * u 0]) <
        vnorm (act (toSL3 (x 3 cp)) u) ∧
      vnorm (act (toSL3 (x 2 (-(c * cp)))) (act (toSL3 (x 4 (-c)))
          ![-(c * u 2), u 1, c * u 0])) <
        vnorm (act (toSL3 (x 3 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
  exacts [exist_st_43_pp u hviol hside, exist_st_43_pm u hviol hside,
    exist_st_43_mp u hviol hside, exist_st_43_mm u hviol hside]

private theorem exist_st_04_pp (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 0 1)) (act (toSL3 (x 4 1)) u)) <
      vnorm (act (toSL3 (x 4 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 4 1)) u)) :
    (vnorm (act (toSL3 (x 0 1)) u) < vnorm (act (toSL3 (x 4 1)) u) ∧
      vnorm (act (toSL3 (x 4 1)) (act (toSL3 (x 0 1)) u)) <
        vnorm (act (toSL3 (x 4 1)) u)) ∨
    (vnorm (act (toSL3 (x 0 (-1))) ![1 * u 1, -(1 * u 0), u 2]) <
        vnorm (act (toSL3 (x 4 1)) u) ∧
      vnorm (act (toSL3 (x 5 (-(1 * 1)))) (act (toSL3 (x 0 (-1)))
          ![1 * u 1, -(1 * u 0), u 2])) <
        vnorm (act (toSL3 (x 4 1)) u)) := by
  simp only [act_x0, act_x4, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_04_pm (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 0 1)) (act (toSL3 (x 4 (-1))) u)) <
      vnorm (act (toSL3 (x 4 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 4 (-1))) u)) :
    (vnorm (act (toSL3 (x 0 1)) u) < vnorm (act (toSL3 (x 4 (-1))) u) ∧
      vnorm (act (toSL3 (x 4 (-1))) (act (toSL3 (x 0 1)) u)) <
        vnorm (act (toSL3 (x 4 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 0 (-1))) ![1 * u 1, -(1 * u 0), u 2]) <
        vnorm (act (toSL3 (x 4 (-1))) u) ∧
      vnorm (act (toSL3 (x 5 (-(1 * (-1))))) (act (toSL3 (x 0 (-1)))
          ![1 * u 1, -(1 * u 0), u 2])) <
        vnorm (act (toSL3 (x 4 (-1))) u)) := by
  simp only [act_x0, act_x4, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_04_mp (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 0 (-1))) (act (toSL3 (x 4 1)) u)) <
      vnorm (act (toSL3 (x 4 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 4 1)) u)) :
    (vnorm (act (toSL3 (x 0 (-1))) u) < vnorm (act (toSL3 (x 4 1)) u) ∧
      vnorm (act (toSL3 (x 4 1)) (act (toSL3 (x 0 (-1))) u)) <
        vnorm (act (toSL3 (x 4 1)) u)) ∨
    (vnorm (act (toSL3 (x 0 (-(-1)))) ![(-1) * u 1, -((-1) * u 0), u 2]) <
        vnorm (act (toSL3 (x 4 1)) u) ∧
      vnorm (act (toSL3 (x 5 (-((-1) * 1)))) (act (toSL3 (x 0 (-(-1))))
          ![(-1) * u 1, -((-1) * u 0), u 2])) <
        vnorm (act (toSL3 (x 4 1)) u)) := by
  simp only [act_x0, act_x4, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_04_mm (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 0 (-1))) (act (toSL3 (x 4 (-1))) u)) <
      vnorm (act (toSL3 (x 4 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 4 (-1))) u)) :
    (vnorm (act (toSL3 (x 0 (-1))) u) < vnorm (act (toSL3 (x 4 (-1))) u) ∧
      vnorm (act (toSL3 (x 4 (-1))) (act (toSL3 (x 0 (-1))) u)) <
        vnorm (act (toSL3 (x 4 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 0 (-(-1)))) ![(-1) * u 1, -((-1) * u 0), u 2]) <
        vnorm (act (toSL3 (x 4 (-1))) u) ∧
      vnorm (act (toSL3 (x 5 (-((-1) * (-1))))) (act (toSL3 (x 0 (-(-1))))
          ![(-1) * u 1, -((-1) * u 0), u 2])) <
        vnorm (act (toSL3 (x 4 (-1))) u)) := by
  simp only [act_x0, act_x4, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

theorem exist_st_04 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 0 c)) (act (toSL3 (x 4 cp)) u)) <
      vnorm (act (toSL3 (x 4 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 4 cp)) u)) :
    (vnorm (act (toSL3 (x 0 c)) u) < vnorm (act (toSL3 (x 4 cp)) u) ∧
      vnorm (act (toSL3 (x 4 cp)) (act (toSL3 (x 0 c)) u)) <
        vnorm (act (toSL3 (x 4 cp)) u)) ∨
    (vnorm (act (toSL3 (x 0 (-c))) ![c * u 1, -(c * u 0), u 2]) <
        vnorm (act (toSL3 (x 4 cp)) u) ∧
      vnorm (act (toSL3 (x 5 (-(c * cp)))) (act (toSL3 (x 0 (-c)))
          ![c * u 1, -(c * u 0), u 2])) <
        vnorm (act (toSL3 (x 4 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
  exacts [exist_st_04_pp u hviol hside, exist_st_04_pm u hviol hside,
    exist_st_04_mp u hviol hside, exist_st_04_mm u hviol hside]

private theorem exist_st_25_pp (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 2 1)) (act (toSL3 (x 5 1)) u)) <
      vnorm (act (toSL3 (x 5 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 5 1)) u)) :
    (vnorm (act (toSL3 (x 2 1)) u) < vnorm (act (toSL3 (x 5 1)) u) ∧
      vnorm (act (toSL3 (x 5 1)) (act (toSL3 (x 2 1)) u)) <
        vnorm (act (toSL3 (x 5 1)) u)) ∨
    (vnorm (act (toSL3 (x 2 (-1))) ![-(1 * u 1), 1 * u 0, u 2]) <
        vnorm (act (toSL3 (x 5 1)) u) ∧
      vnorm (act (toSL3 (x 4 (-(1 * 1)))) (act (toSL3 (x 2 (-1)))
          ![-(1 * u 1), 1 * u 0, u 2])) <
        vnorm (act (toSL3 (x 5 1)) u)) := by
  simp only [act_x2, act_x4, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_25_pm (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 2 1)) (act (toSL3 (x 5 (-1))) u)) <
      vnorm (act (toSL3 (x 5 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 5 (-1))) u)) :
    (vnorm (act (toSL3 (x 2 1)) u) < vnorm (act (toSL3 (x 5 (-1))) u) ∧
      vnorm (act (toSL3 (x 5 (-1))) (act (toSL3 (x 2 1)) u)) <
        vnorm (act (toSL3 (x 5 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 2 (-1))) ![-(1 * u 1), 1 * u 0, u 2]) <
        vnorm (act (toSL3 (x 5 (-1))) u) ∧
      vnorm (act (toSL3 (x 4 (-(1 * (-1))))) (act (toSL3 (x 2 (-1)))
          ![-(1 * u 1), 1 * u 0, u 2])) <
        vnorm (act (toSL3 (x 5 (-1))) u)) := by
  simp only [act_x2, act_x4, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_25_mp (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 2 (-1))) (act (toSL3 (x 5 1)) u)) <
      vnorm (act (toSL3 (x 5 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 5 1)) u)) :
    (vnorm (act (toSL3 (x 2 (-1))) u) < vnorm (act (toSL3 (x 5 1)) u) ∧
      vnorm (act (toSL3 (x 5 1)) (act (toSL3 (x 2 (-1))) u)) <
        vnorm (act (toSL3 (x 5 1)) u)) ∨
    (vnorm (act (toSL3 (x 2 (-(-1)))) ![-((-1) * u 1), (-1) * u 0, u 2]) <
        vnorm (act (toSL3 (x 5 1)) u) ∧
      vnorm (act (toSL3 (x 4 (-((-1) * 1)))) (act (toSL3 (x 2 (-(-1))))
          ![-((-1) * u 1), (-1) * u 0, u 2])) <
        vnorm (act (toSL3 (x 5 1)) u)) := by
  simp only [act_x2, act_x4, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

private theorem exist_st_25_mm (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 2 (-1))) (act (toSL3 (x 5 (-1))) u)) <
      vnorm (act (toSL3 (x 5 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 5 (-1))) u)) :
    (vnorm (act (toSL3 (x 2 (-1))) u) < vnorm (act (toSL3 (x 5 (-1))) u) ∧
      vnorm (act (toSL3 (x 5 (-1))) (act (toSL3 (x 2 (-1))) u)) <
        vnorm (act (toSL3 (x 5 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 2 (-(-1)))) ![-((-1) * u 1), (-1) * u 0, u 2]) <
        vnorm (act (toSL3 (x 5 (-1))) u) ∧
      vnorm (act (toSL3 (x 4 (-((-1) * (-1))))) (act (toSL3 (x 2 (-(-1))))
          ![-((-1) * u 1), (-1) * u 0, u 2])) <
        vnorm (act (toSL3 (x 5 (-1))) u)) := by
  simp only [act_x2, act_x4, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  omega

theorem exist_st_25 (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 2 c)) (act (toSL3 (x 5 cp)) u)) <
      vnorm (act (toSL3 (x 5 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 5 cp)) u)) :
    (vnorm (act (toSL3 (x 2 c)) u) < vnorm (act (toSL3 (x 5 cp)) u) ∧
      vnorm (act (toSL3 (x 5 cp)) (act (toSL3 (x 2 c)) u)) <
        vnorm (act (toSL3 (x 5 cp)) u)) ∨
    (vnorm (act (toSL3 (x 2 (-c))) ![-(c * u 1), c * u 0, u 2]) <
        vnorm (act (toSL3 (x 5 cp)) u) ∧
      vnorm (act (toSL3 (x 4 (-(c * cp)))) (act (toSL3 (x 2 (-c)))
          ![-(c * u 1), c * u 0, u 2])) <
        vnorm (act (toSL3 (x 5 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
  exacts [exist_st_25_pp u hviol hside, exist_st_25_pm u hviol hside,
    exist_st_25_mp u hviol hside, exist_st_25_mm u hviol hside]

/-! ## Braid pairs: alignment is impossible at a violation -/

theorem braid_aligned_02 (c : ℤ) (hc : c = 1 ∨ c = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 0 c)) (act (toSL3 (x 2 c)) u)) <
      vnorm (act (toSL3 (x 2 c)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 2 c)) u)) : False := by
  rcases hc with rfl | rfl <;>
    simp only [act_x0, act_x2] at hviol hside <;>
    simp [vnorm] at hviol hside <;>
    omega

theorem braid_aligned_20 (c : ℤ) (hc : c = 1 ∨ c = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 2 c)) (act (toSL3 (x 0 c)) u)) <
      vnorm (act (toSL3 (x 0 c)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 0 c)) u)) : False := by
  rcases hc with rfl | rfl <;>
    simp only [act_x0, act_x2] at hviol hside <;>
    simp [vnorm] at hviol hside <;>
    omega

theorem braid_aligned_14 (c : ℤ) (hc : c = 1 ∨ c = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 1 c)) (act (toSL3 (x 4 c)) u)) <
      vnorm (act (toSL3 (x 4 c)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 4 c)) u)) : False := by
  rcases hc with rfl | rfl <;>
    simp only [act_x1, act_x4] at hviol hside <;>
    simp [vnorm] at hviol hside <;>
    omega

theorem braid_aligned_41 (c : ℤ) (hc : c = 1 ∨ c = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 4 c)) (act (toSL3 (x 1 c)) u)) <
      vnorm (act (toSL3 (x 1 c)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 1 c)) u)) : False := by
  rcases hc with rfl | rfl <;>
    simp only [act_x1, act_x4] at hviol hside <;>
    simp [vnorm] at hviol hside <;>
    omega

theorem braid_aligned_35 (c : ℤ) (hc : c = 1 ∨ c = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 3 c)) (act (toSL3 (x 5 c)) u)) <
      vnorm (act (toSL3 (x 5 c)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 5 c)) u)) : False := by
  rcases hc with rfl | rfl <;>
    simp only [act_x3, act_x5] at hviol hside <;>
    simp [vnorm] at hviol hside <;>
    omega

theorem braid_aligned_53 (c : ℤ) (hc : c = 1 ∨ c = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 5 c)) (act (toSL3 (x 3 c)) u)) <
      vnorm (act (toSL3 (x 3 c)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 3 c)) u)) : False := by
  rcases hc with rfl | rfl <;>
    simp only [act_x3, act_x5] at hviol hside <;>
    simp [vnorm] at hviol hside <;>
    omega

end

end P13DescentCases
end GroupApproximation
