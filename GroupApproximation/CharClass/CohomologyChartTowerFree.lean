import GroupApproximation.CharClass.CohomologyChartTower

/-!
# Freeness of the peel tower: the target, and its ingredients

`exists_peelTower` says every class is a tower.  Freeness is the other half: a
vanishing tower has vanishing coefficients.  That half is **not** available from
the tower recursion, which runs on the degree and so cannot see the rank, and it
is false without a bound relating the two.

## Why the length bound is not optional

A tower of length `k` puts the coefficient `a i` against the `(k - i)`-th power of
the generator.  On a fibre `ℂP^{d+1}` every power above `d + 1` vanishes, so if
`k > d + 1` the coefficients `a i` with `k - i > d + 1` multiply zero and are free
parameters that the tower cannot see.  `PeelFree` therefore carries `k ≤ d + 1`.
This is the same failure that made one-step uniqueness false, seen from the other
end: there the coefficient lived on the wrong space, here the index set outruns
what the rank can support.

## Main declarations

* `KnCP.PeelFree` — **the target**, with the length bound `cc-projective`'s
  reindex needs.
* `KnCP.peel_base_eq_zero_right` — the slice argument, generator on the right.
* `KnCP.peelTower_zero_eq_zero`, `KnCP.peelTower_succ_top_eq_zero` — the two ends
  of the induction; the top coefficient always dies, unconditionally.
* `KnCP.cpTopPt_ne_zero`, `KnCP.cpTopPt_eq_cupPowE`, `KnCP.cpTop_eq_pull_cupPowE`
  — the connecting class **is** the top power of the generator, at every rank.
  This is what closes the last step of the rank induction, where the whole tower
  has collapsed onto its top power.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-! ## 1. The target -/

/-- **Freeness of the tower**, as a named statement so consumers can build over it
before it is discharged.  The bound `k ≤ d + 1` is required, not cosmetic: beyond
it the coefficients multiply vanishing powers and are not determined. -/
def PeelFree (d : ℕ) : Prop :=
  ∀ (U : Type) [TopologicalSpace U] (hd : 1 ≤ d + 1) (m k : ℕ), k ≤ d + 1 →
    ∀ a : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j),
      peelTower U d hd m a k = 0 → ∀ j, j ≤ k → a j = 0

/-! ## 2. The top coefficient always dies -/

set_option maxHeartbeats 1000000 in
/-- `peel_base_eq_zero` with the generator on the right, which is the side the
tower is built on. -/
theorem peel_base_eq_zero_right (hd : 1 ≤ d + 1) (n : ℕ)
    (a : Hmod2 (TopCat.of U) (n + 2)) (y : Hmod2 (cpProdTop U d) n)
    (h : pull (cpPrU U d) (n + 2) a
      + cup y (pull (cpPrCP U d) 2 (cpGen (d + 1) hd)) = 0) : a = 0 := by
  obtain ⟨p⟩ := nonempty_CPtop (d + 1)
  have hconst : pull (cpSliceGen U (d + 1) p ≫ cpPrCP U d) 2 (cpGen (d + 1) hd) = 0 := by
    rw [cpSliceGen_comp_cpPrCP]
    exact pull_const_eq_zero U p 2 (by omega) (cpGen (d + 1) hd)
  have hs := congrArg (pull (cpSliceGen U (d + 1) p) (n + 2)) h
  rw [pull_add, pull_zero, ← pull_comp, cpSliceGen_comp_cpFst, pull_id, pull_cup,
    ← pull_comp, hconst, cup_zero, add_zero] at hs
  exact hs

/-- A tower of length zero is a pullback, so it determines its one coefficient. -/
theorem peelTower_zero_eq_zero (hd : 1 ≤ d + 1) (m : ℕ)
    (a : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j))
    (h : peelTower U d hd m a 0 = 0) : a 0 = 0 := by
  simp only [peelTower] at h
  refine pull_cpFst_injective U (d + 1) (m + 2 * 0) ?_
  rw [pull_zero]
  exact h

set_option maxHeartbeats 1000000 in
/-- **The top coefficient of a vanishing tower vanishes, with no bound at all**,
and what is left is the shorter tower cupped with the generator.  Only the second
half needs the rank; this half is the slice. -/
theorem peelTower_succ_top_eq_zero (hd : 1 ≤ d + 1) (m k : ℕ)
    (a : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j))
    (h : peelTower U d hd m a (k + 1) = 0) :
    a (k + 1) = 0 ∧
      cup (peelTower U d hd m a k) (pull (cpPrCP U d) 2 (cpGen (d + 1) hd)) = 0 := by
  simp only [peelTower] at h
  have htop : a (k + 1) = 0 :=
    peel_base_eq_zero_right U d hd (m + 2 * k) (a (k + 1)) (peelTower U d hd m a k) h
  refine ⟨htop, ?_⟩
  rw [htop, pull_zero, zero_add] at h
  exact h

/-! ## 3. The connecting class is the top power -/

set_option maxHeartbeats 1000000 in
/-- **The connecting class of the chart cover is nonzero at every rank.**  At rank
two this was `cpTopPt_zero_ne_zero`; above it the same argument runs on
`cpTop_cup_injective_closed`, which is now unconditional. -/
theorem cpTopPt_ne_zero (d : ℕ) : cpTopPt d ≠ 0 := by
  match d with
  | 0 => exact cpTopPt_zero_ne_zero
  | (e + 1) =>
    intro h0
    haveI : Nonempty ↥(TopCat.of Unit) := ⟨()⟩
    have hz : cup (cpTop Unit (e + 1))
        (pull (cpPrU Unit (e + 1)) 0 (one (TopCat.of Unit))) = 0 := by
      rw [cpTop_eq_pull_cpTopPt, h0, pull_zero, zero_cup]
    exact one_ne_zero_cohZero (TopCat.of Unit)
      (cpTop_cup_injective_closed Unit (e + 1) (by omega) 0 (one (TopCat.of Unit)) hz)

/-- **The connecting class IS the top power of the generator.**  `H^{2d+2}` of the
fibre is a line, the class is nonzero, and the top power is the other nonzero
element, so they coincide. -/
theorem cpTopPt_eq_cupPowE (d : ℕ) (hd : 1 ≤ d + 1) :
    cpTopPt d = cupPowE (cpGen (d + 1) hd) (d + 1) := by
  rcases eq_zero_or_eq_cupPowE_cpGen (d + 1) hd (le_refl (d + 1)) (cpTopPt d) with h | h
  · exact absurd h (cpTopPt_ne_zero d)
  · exact h

/-- **The top class on the product is the top power, pulled back.**  This is what
finishes the rank induction: once a tower has collapsed onto its top power, the
coefficient there is determined by `cpTop_cup_injective_closed`. -/
theorem cpTop_eq_pull_cupPowE (hd : 1 ≤ d + 1) :
    cpTop U d
      = pull (cpPrCP U d) (2 * (d + 1)) (cupPowE (cpGen (d + 1) hd) (d + 1)) := by
  rw [cpTop_eq_pull_cpTopPt, cpTopPt_eq_cupPowE d hd]
  exact rfl

end KnCP

end

end GroupApproximation.CharClass
