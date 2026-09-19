import GroupApproximation.CharClass.LerayHirschRankTwo

/-!
# The triangular change of basis

A projective-factor Künneth produces the two-term decomposition with the class the
connecting map supplies, while Leray–Hirsch consumes it with the tautological
class.  The two differ by a class pulled back from the base, and this file moves
the decomposition across that difference.

The change of basis is `(a, b) ↦ (a + b ⌣ u, b)`: only the first coordinate
moves, and it moves by something determined by the second, so it is triangular
and, in characteristic two, its own inverse.  Both halves of the interface
transfer, and no degree transport appears anywhere, because `b ⌣ u` already sits
in degree `n + 2`.

## Main declarations

* `add_cancel_pair` — the cancellation the change of basis needs.
* `cup_pull_shift` — cupping with the shifted class.
* `hsurj_of_shift`, `huniq_of_shift` — **the two halves, transferred**.
* `bijective_lhSum_two_of_shift` — rank-two Leray–Hirsch for the shifted class.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable {X P : TopCat.{0}}

theorem add_cancel_pair (A : TopCat.{0}) (n : ℕ) (w x y : Hmod2 A n) :
    w + x + (y + x) = w + y := by
  have h : w + x + (y + x) = w + y + (x + x) := by abel
  rw [h, add_self, add_zero]

/-- Cupping with a class shifted by a pullback. -/
theorem cup_pull_shift (π : P ⟶ X) (κ : Hmod2 P 2) (u : Hmod2 X 2) (n : ℕ)
    (b : Hmod2 X n) :
    cup (pull π n b) (κ + pull π 2 u)
      = cup (pull π n b) κ + pull π (n + 2) (cup b u) := by
  rw [cup_add_right, ← pull_cup]

/-- **Spanning transfers.** -/
theorem hsurj_of_shift (π : P ⟶ X) (κ : Hmod2 P 2) (u : Hmod2 X 2)
    (h : ∀ (n : ℕ) (z : Hmod2 P (n + 2)), ∃ (a : Hmod2 X (n + 2)) (b : Hmod2 X n),
      z = pull π (n + 2) a + cup (pull π n b) κ)
    (n : ℕ) (z : Hmod2 P (n + 2)) :
    ∃ (a : Hmod2 X (n + 2)) (b : Hmod2 X n),
      z = pull π (n + 2) a + cup (pull π n b) (κ + pull π 2 u) := by
  obtain ⟨a, b, hz⟩ := h n z
  refine ⟨a + cup b u, b, ?_⟩
  rw [cup_pull_shift, pull_add, hz]
  exact (add_cancel_pair P (n + 2) (pull π (n + 2) a) (pull π (n + 2) (cup b u))
    (cup (pull π n b) κ)).symm

/-- **Freeness transfers.** -/
theorem huniq_of_shift (π : P ⟶ X) (κ : Hmod2 P 2) (u : Hmod2 X 2)
    (h : ∀ (n : ℕ) (a : Hmod2 X (n + 2)) (b : Hmod2 X n),
      pull π (n + 2) a + cup (pull π n b) κ = 0 → a = 0 ∧ b = 0)
    (n : ℕ) (a : Hmod2 X (n + 2)) (b : Hmod2 X n)
    (hab : pull π (n + 2) a + cup (pull π n b) (κ + pull π 2 u) = 0) : a = 0 ∧ b = 0 := by
  rw [cup_pull_shift] at hab
  have hab' : pull π (n + 2) (cup b u + a) + cup (pull π n b) κ = 0 := by
    rw [pull_add,
      show pull π (n + 2) (cup b u) + pull π (n + 2) a + cup (pull π n b) κ
        = pull π (n + 2) a + (cup (pull π n b) κ + pull π (n + 2) (cup b u)) from by abel]
    exact hab
  obtain ⟨h1, h2⟩ := h n (cup b u + a) b hab'
  refine ⟨?_, h2⟩
  rw [h2, zero_cup, zero_add] at h1
  exact h1

/-- **Rank-two Leray–Hirsch for a class shifted by a pullback.** -/
theorem bijective_lhSum_two_of_shift (π : P ⟶ X) (κ : Hmod2 P 2) (u : Hmod2 X 2)
    (hlow : ∀ n : ℕ, n < 2 → Function.Bijective (pull π n))
    (hsurj : ∀ (n : ℕ) (z : Hmod2 P (n + 2)), ∃ (a : Hmod2 X (n + 2)) (b : Hmod2 X n),
      z = pull π (n + 2) a + cup (pull π n b) κ)
    (huniq : ∀ (n : ℕ) (a : Hmod2 X (n + 2)) (b : Hmod2 X n),
      pull π (n + 2) a + cup (pull π n b) κ = 0 → a = 0 ∧ b = 0)
    (n : ℕ) : Function.Bijective (lhSum π (κ + pull π 2 u) 2 n) :=
  bijective_lhSum_two π (κ + pull π 2 u) hlow
    (hsurj_of_shift π κ u hsurj) (huniq_of_shift π κ u huniq) n

end

end LH
end CharClass
end GroupApproximation
