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

* `hsurj_of_shift`, `huniq_of_shift` — the change of basis, in both directions.
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

variable {K : Type} [CommRing K] {X P : TopCat.{0}}


/-- Cupping with a class shifted by a pullback. -/
theorem cup_pull_shift (π : P ⟶ X) (κ : Hmod K P 2) (u : Hmod K X 2) (n : ℕ)
    (b : Hmod K X n) :
    cup (pull π n b) (κ + pull π 2 u)
      = cup (pull π n b) κ + pull π (n + 2) (cup b u) := by
  rw [cup_add_right, ← pull_cup]

/-- **Spanning transfers.** -/
theorem hsurj_of_shift (π : P ⟶ X) (κ : Hmod K P 2) (u : Hmod K X 2)
    (h : ∀ (n : ℕ) (z : Hmod K P (n + 2)), ∃ (a : Hmod K X (n + 2)) (b : Hmod K X n),
      z = pull π (n + 2) a + cup (pull π n b) κ)
    (n : ℕ) (z : Hmod K P (n + 2)) :
    ∃ (a : Hmod K X (n + 2)) (b : Hmod K X n),
      z = pull π (n + 2) a + cup (pull π n b) (κ + pull π 2 u) := by
  obtain ⟨a, b, hz⟩ := h n z
  -- the shift by `pull π 2 u` adds `pull π (n+2) (cup b u)` to the second term, so the
  -- first term has to lose it.  Mod 2 the tree added it instead, which is the same
  -- element there and the wrong one over `K`.
  refine ⟨a - cup b u, b, ?_⟩
  rw [cup_pull_shift, pull_sub, hz]
  abel

/-- **Freeness transfers.** -/
theorem huniq_of_shift (π : P ⟶ X) (κ : Hmod K P 2) (u : Hmod K X 2)
    (h : ∀ (n : ℕ) (a : Hmod K X (n + 2)) (b : Hmod K X n),
      pull π (n + 2) a + cup (pull π n b) κ = 0 → a = 0 ∧ b = 0)
    (n : ℕ) (a : Hmod K X (n + 2)) (b : Hmod K X n)
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
theorem bijective_lhSum_two_of_shift (π : P ⟶ X) (κ : Hmod K P 2) (u : Hmod K X 2)
    (hlow : ∀ n : ℕ, n < 2 → Function.Bijective (pull (K := K) π n))
    (hsurj : ∀ (n : ℕ) (z : Hmod K P (n + 2)), ∃ (a : Hmod K X (n + 2)) (b : Hmod K X n),
      z = pull π (n + 2) a + cup (pull π n b) κ)
    (huniq : ∀ (n : ℕ) (a : Hmod K X (n + 2)) (b : Hmod K X n),
      pull π (n + 2) a + cup (pull π n b) κ = 0 → a = 0 ∧ b = 0)
    (n : ℕ) : Function.Bijective (lhSum π (κ + pull π 2 u) 2 n) :=
  bijective_lhSum_two π (κ + pull π 2 u) hlow
    (hsurj_of_shift π κ u hsurj) (huniq_of_shift π κ u huniq) n

end

end LH
end CharClass
end GroupApproximation
