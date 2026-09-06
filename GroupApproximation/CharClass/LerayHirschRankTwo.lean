import GroupApproximation.CharClass.GysinFromGraded
import GroupApproximation.CharClass.LerayHirschCover

/-!
# Rank two: the interface a Künneth statement has to supply

At rank two the Leray–Hirsch map has exactly two summands, so bijectivity in every
degree is equivalent to three elementary statements about the base: pullback is
bijective in the two degrees below two, and in every higher degree a class is
*uniquely* a pullback plus a pullback cupped with the class.

`bijective_lhSum_two` is that equivalence in the direction a consumer needs, and
it is the interface any projective-factor Künneth has to land on.  Nothing in it
mentions a cover, a bundle, or a projective space: it is pure repackaging of the
rank-two combination, which `lhSum_two_apply` already writes out with no
transport.

## Main declarations

* `lhTerm_zero_index`, `lhSum_two_low` — the combination below degree two, where
  only the zeroth summand survives.
* `colLow` — the column element in those degrees.
* `bijective_lhSum_two` — **the interface**.
* `LHOver_two_of_decomposition` — the same, phrased over a trivialising open.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace

noncomputable section

variable {X P : TopCat.{0}}

/-! ## 1. Below degree two -/

theorem lhTerm_zero_index (π : P ⟶ X) (ξ : Hmod2 P 2) (n : ℕ)
    (a : Hmod2 X (n - 2 * 0)) : lhTerm π ξ n 0 a = pull π n a := by
  rw [lhTerm_of_le π ξ (by omega : 2 * 0 ≤ n), cupPowE_zero, cup_one]
  exact cohCast_self _ _

/-- The column element in a degree below two: only the zeroth summand is present. -/
def colLow (X : TopCat.{0}) (n : ℕ) (hn : n < 2) (x : Hmod2 X n) : lhDomain X 2 n :=
  ⟨Fin.cases (motive := fun j : Fin 2 => Hmod2 X (n - 2 * (j : ℕ))) x (fun _ => 0), by
    intro j hj
    revert hj
    induction j using Fin.cases with
    | zero => exact fun hj => absurd hj (by omega)
    | succ i => exact fun _ => rfl⟩

@[simp] theorem colLow_zero (n : ℕ) (hn : n < 2) (x : Hmod2 X n) :
    ((colLow X n hn x : lhDomain X 2 n) :
      (j : Fin 2) → Hmod2 X (n - 2 * (j : ℕ))) 0 = x := rfl

theorem lhSum_two_low (π : P ⟶ X) (ξ : Hmod2 P 2) (n : ℕ) (hn : n < 2)
    (c : lhDomain X 2 n) :
    lhSum π ξ 2 n c = pull π n ((c : (j : Fin 2) → Hmod2 X (n - 2 * (j : ℕ))) 0) := by
  have h1 : (c : (j : Fin 2) → Hmod2 X (n - 2 * (j : ℕ))) 1 = 0 :=
    lhDomain_vanish c 1 (by change n < 2; omega)
  rw [lhSum_apply, Fin.sum_univ_two]
  show lhTerm π ξ n 0 ((c : (j : Fin 2) → Hmod2 X (n - 2 * (j : ℕ))) 0)
    + lhTerm π ξ n 1 ((c : (j : Fin 2) → Hmod2 X (n - 2 * (j : ℕ))) 1) = _
  rw [h1, lhTerm_zero, add_zero, lhTerm_zero_index]

/-! ## 2. The interface -/

/-- **Rank-two Leray–Hirsch from a two-term decomposition.**  Bijectivity in every
degree follows from pullback being bijective below degree two together with
existence and uniqueness of the two-term form above it.  This is what a
projective-factor Künneth has to supply, and nothing else. -/
theorem bijective_lhSum_two (π : P ⟶ X) (ξ : Hmod2 P 2)
    (hlow : ∀ n : ℕ, n < 2 → Function.Bijective (pull π n))
    (hsurj : ∀ (n : ℕ) (z : Hmod2 P (n + 2)),
      ∃ (a : Hmod2 X (n + 2)) (b : Hmod2 X n),
        z = pull π (n + 2) a + cup (pull π n b) ξ)
    (huniq : ∀ (n : ℕ) (a : Hmod2 X (n + 2)) (b : Hmod2 X n),
      pull π (n + 2) a + cup (pull π n b) ξ = 0 → a = 0 ∧ b = 0)
    (n : ℕ) : Function.Bijective (lhSum π ξ 2 n) := by
  match n with
  | 0 | 1 =>
    constructor
    · intro c c' h
      rw [lhSum_two_low π ξ _ (by omega), lhSum_two_low π ξ _ (by omega)] at h
      refine lhDomain_ext ?_
      rw [Fin.forall_fin_two]
      exact ⟨(hlow _ (by omega)).1 h,
        (lhDomain_vanish c 1 (by change _ < 2; omega)).trans
          (lhDomain_vanish c' 1 (by change _ < 2; omega)).symm⟩
    · intro y
      obtain ⟨x, hx⟩ := (hlow _ (by omega)).2 y
      exact ⟨colLow X _ (by omega) x, by rw [lhSum_two_low π ξ _ (by omega), colLow_zero, hx]⟩
  | (m + 2) =>
    constructor
    · intro c c' h
      have hz : lhSum π ξ 2 (m + 2) (c - c') = 0 := by rw [map_sub, h, sub_self]
      rw [lhSum_two_apply] at hz
      obtain ⟨h0, h1⟩ := huniq m _ _ hz
      refine sub_eq_zero.mp (lhDomain_ext ?_)
      rw [Fin.forall_fin_two]
      exact ⟨by rw [lhDomain_zero_apply]; exact h0, by rw [lhDomain_zero_apply]; exact h1⟩
    · intro z
      obtain ⟨a, b, hab⟩ := hsurj m z
      exact ⟨colTwo X m a b, by rw [lhSum_two_apply, colTwo_zero, colTwo_one, ← hab]⟩

/-- **The interface, over a trivialising open set.** -/
theorem LHOver_two_of_decomposition (f : P ⟶ X) (ξ : Hmod2 P 2) (U : Opens X)
    (hlow : ∀ n : ℕ, n < 2 → Function.Bijective (pull (opensRestrict f U) n))
    (hsurj : ∀ (n : ℕ) (z : Hmod2 (opSpace (opensComap f U)) (n + 2)),
      ∃ (a : Hmod2 (opSpace U) (n + 2)) (b : Hmod2 (opSpace U) n),
        z = pull (opensRestrict f U) (n + 2) a
          + cup (pull (opensRestrict f U) n b) (lhClass f ξ U))
    (huniq : ∀ (n : ℕ) (a : Hmod2 (opSpace U) (n + 2)) (b : Hmod2 (opSpace U) n),
      pull (opensRestrict f U) (n + 2) a
          + cup (pull (opensRestrict f U) n b) (lhClass f ξ U) = 0 → a = 0 ∧ b = 0) :
    LHOver f ξ 2 U :=
  bijective_lhSum_two (opensRestrict f U) (lhClass f ξ U) hlow hsurj huniq

end

end LH
end CharClass
end GroupApproximation
