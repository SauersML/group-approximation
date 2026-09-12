import GroupApproximation.CharClass.CohomologyChartTowerFree

/-!
# A tower with no coefficients above `j₀` is a shorter tower times a power

The rank induction for freeness needs one structural fact.  Restricting a tower to
the punctured piece leaves the coefficients and the base degree alone, so the
inductive hypothesis at the smaller rank reaches every coefficient whose power
survives there.  Exactly one index escapes it, the one whose power is the top
power at the larger rank, and to reach that index the tower has to be recognised
as a shorter tower multiplied by a power of the generator.

`peelTower_eq_cup_pow` is that recognition, and it is the only place a cast
appears, because `m + 2 * j₀ + 2 * p` and `m + 2 * (j₀ + p)` are equal only
propositionally.  That is the single point where the cast-free indexing of the
tower does not extend, and it is unavoidable: the two degrees differ by an
associativity step over a variable index.

## Main declarations

* `KnCP.PeelFreeAt` — freeness stated index by index rather than under a global
  length bound, so that the restriction to the smaller rank is the same tower at
  the same base degree, with no shift.
* `KnCP.peelTower_eq_cup_pow` — **the collapse**.
* `KnCP.peelFree_of_peelFreeAt` — the bounded form follows from the index-wise
  one, so nothing already built against `PeelFree` has to move.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-! ## 1. Freeness, index by index -/

/-- **Freeness stated index by index.**  A coefficient of a vanishing tower
vanishes as soon as *its own* power survives the rank, that is as soon as
`k - j ≤ d + 1`.  Strictly stronger than `PeelFree`, and stated so that the
restriction to the smaller rank is the same tower at the same base degree: no
index shift, hence no cast, at the step where the induction changes rank. -/
def PeelFreeAt (d : ℕ) : Prop :=
  ∀ (U : Type) [TopologicalSpace U] (hd : 1 ≤ d + 1) (m k : ℕ)
    (a : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j)),
    peelTower U d hd m a k = 0 → ∀ j, j ≤ k → k - j ≤ d + 1 → a j = 0

/-- The bounded form is the index-wise form specialised, so consumers already
building against `PeelFree` are unaffected. -/
theorem peelFree_of_peelFreeAt (d : ℕ) (h : PeelFreeAt d) : PeelFree d := by
  intro U _ hd m k hk a hzero j hj
  exact h U hd m k a hzero j hj (by omega)

/-! ## 2. The collapse -/

set_option maxHeartbeats 1000000 in
/-- **A tower whose coefficients above `j₀` all vanish is the tower truncated at
`j₀`, cupped with a power of the generator.**  Proved by induction on the number
of vanishing coefficients, so the generator accumulates one power at a time and
`cup_assoc'` is applied once per step. -/
theorem peelTower_eq_cup_pow (hd : 1 ≤ d + 1) (m j₀ : ℕ)
    (a : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j)) :
    ∀ p : ℕ, (∀ j, j₀ < j → j ≤ j₀ + p → a j = 0) →
      peelTower U d hd m a (j₀ + p)
        = cohCast (show m + 2 * j₀ + 2 * p = m + 2 * (j₀ + p) by omega)
            (cup (peelTower U d hd m a j₀)
              (cupPowE (pull (cpPrCP U d) 2 (cpGen (d + 1) hd)) p)) := by
  intro p
  induction p with
  | zero =>
    intro _
    rw [cupPowE_zero, cup_one]
    exact rfl
  | succ q ih =>
    intro hz
    have ha : a (j₀ + q + 1) = 0 := hz (j₀ + q + 1) (by omega) (by omega)
    have hstep : peelTower U d hd m a (j₀ + (q + 1))
        = cup (peelTower U d hd m a (j₀ + q))
            (pull (cpPrCP U d) 2 (cpGen (d + 1) hd)) := by
      show peelTower U d hd m a (j₀ + q + 1) = _
      simp only [peelTower]
      rw [ha, pull_zero, zero_add]
    rw [hstep, ih (fun j hj1 hj2 => hz j hj1 (by omega)), cup_cohCast_left,
      cup_assoc', cohCast_cohCast, ← cupPowE_succ]

end KnCP

end

end GroupApproximation.CharClass
