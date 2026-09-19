import GroupApproximation.CharClass.CohomologyChartTowerCollapse

/-!
# The one index a rank restriction cannot see

Restricting a vanishing tower to the punctured piece leaves its coefficients and
its base degree alone, so the freeness statement at the smaller rank reaches every
coefficient whose power survives there.  Exactly one index escapes: the one whose
power is the **top** power at the larger rank, which is precisely the power the
smaller rank kills.

This file reaches that index.  The tower collapses onto it by
`peelTower_eq_cup_pow`, everything below it is annihilated because its powers have
run past the fibre dimension, and what is left is the top class cupped with a
pullback, where `cpTop_cup_injective_closed` finishes.

## Main declarations

* `KnCP.cupPowE_pull_eq_zero` — powers of the generator past the fibre dimension
  vanish on the product.
* `KnCP.peelTower_top_coeff_eq_zero` — the last coefficient of a vanishing tower
  vanishes, at any rank and with no hypothesis.
* `KnCP.peelTower_top_index_eq_zero` — **the escaping index**, for a tower whose
  coefficients above it are already known to vanish.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-! ## 1. Powers past the fibre dimension -/

/-- **Powers of the generator past the fibre dimension vanish on the product**,
because they already vanish on the fibre. -/
theorem cupPowE_pull_eq_zero (hd : 1 ≤ d + 1) (p : ℕ) (hp : d + 1 < p) :
    cupPowE (pull (cpPrCP U d) 2 (cpGen (d + 1) hd)) p = 0 := by
  rw [← pull_cupPowE,
    cupPowE_eq_zero_of_gt (cpGen (d + 1) hd) (d + 1) (hasCPCohomology_CP (d + 1)) hp,
    pull_zero]

/-- One more generator past the top power is zero, with the generator on the left,
which is the side `cup_assoc'` produces. -/
theorem cup_gen_cupPowE_top_eq_zero (hd : 1 ≤ d + 1) :
    cup (pull (cpPrCP U d) 2 (cpGen (d + 1) hd))
        (cupPowE (pull (cpPrCP U d) 2 (cpGen (d + 1) hd)) (d + 1)) = 0 := by
  rw [cup_comm, ← cupPowE_succ, cupPowE_pull_eq_zero U d hd (d + 1 + 1) (by omega),
    cohCast_zero]

/-! ## 2. The last coefficient -/

/-- **The last coefficient of a vanishing tower vanishes**, at any rank and with no
hypothesis: it is the slice argument, not a Künneth statement. -/
theorem peelTower_top_coeff_eq_zero (hd : 1 ≤ d + 1) (m k : ℕ)
    (a : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j))
    (h : peelTower U d hd m a k = 0) : a k = 0 := by
  match k with
  | 0 => exact peelTower_zero_eq_zero U d hd m a h
  | (k' + 1) => exact (peelTower_succ_top_eq_zero U d hd m k' a h).1

/-! ## 3. The escaping index -/

set_option maxHeartbeats 1000000 in
/-- Below the escaping index every power has run past the fibre dimension, so the
whole tail annihilates the top power and only the escaping coefficient survives. -/
theorem cup_peelTower_cupPowE_top (hd : 1 ≤ d + 1) (m j₀ : ℕ)
    (a : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j)) :
    cup (peelTower U d hd m a j₀)
        (cupPowE (pull (cpPrCP U d) 2 (cpGen (d + 1) hd)) (d + 1))
      = cup (pull (cpPrU U d) (m + 2 * j₀) (a j₀))
          (cupPowE (pull (cpPrCP U d) 2 (cpGen (d + 1) hd)) (d + 1)) := by
  match j₀ with
  | 0 => simp only [peelTower]
  | (j' + 1) =>
    simp only [peelTower]
    rw [cup_add_left, cup_assoc', cup_gen_cupPowE_top_eq_zero U d hd, cup_zero,
      cohCast_zero, add_zero]

set_option maxHeartbeats 1000000 in
/-- **The escaping index.**  If a tower vanishes and every coefficient above `j₀`
is already known to vanish, and `j₀`'s own power is the top power, then `a j₀`
vanishes too.  This is the only step of the rank induction that the restriction to
the smaller rank cannot supply, and the only one that uses the ring. -/
theorem peelTower_top_index_eq_zero (hd : 1 ≤ d + 1) (hd1 : 1 ≤ d) (m j₀ : ℕ)
    (a : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j))
    (hhi : ∀ j, j₀ < j → j ≤ j₀ + (d + 1) → a j = 0)
    (hzero : peelTower U d hd m a (j₀ + (d + 1)) = 0) : a j₀ = 0 := by
  have hcol := peelTower_eq_cup_pow U d hd m j₀ a (d + 1) hhi
  have hz : cup (peelTower U d hd m a j₀)
      (cupPowE (pull (cpPrCP U d) 2 (cpGen (d + 1) hd)) (d + 1)) = 0 :=
    (cohCast_eq_zero_iff _ _).mp (hcol.symm.trans hzero)
  rw [cup_peelTower_cupPowE_top U d hd m j₀ a] at hz
  have htop : cup (pull (cpPrU U d) (m + 2 * j₀) (a j₀)) (cpTop U d) = 0 := by
    rw [cpTop_eq_pull_cupPowE U d hd, pull_cupPowE]
    exact hz
  refine cpTop_cup_injective_closed U d hd1 (m + 2 * j₀) (a j₀) ?_
  rw [cup_comm (cpTop U d) (pull (cpPrU U d) (m + 2 * j₀) (a j₀)), htop, cohCast_zero]

end KnCP

end

end GroupApproximation.CharClass
