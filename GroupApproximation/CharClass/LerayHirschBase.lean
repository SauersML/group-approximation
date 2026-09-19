import GroupApproximation.CharClass.LerayHirschPoint

/-!
# The base case in the shapes a consumer has it

`bijective_lhSum_point` takes the cohomology of the base and of the fibre apart
into their pieces.  A consumer holds them bundled, as `HasPointCohomology` and
`HasCPCohomology`, so this file restates the base case that way and records the
one case that needs no ring structure at all.

For a `ℂP^1` fibre the powers of `ξ` that have to be nonzero are only `1` and `ξ`
itself.  The first is the unit and the second is the hypothesis, so the base case
for a rank-two bundle is available with nothing beyond the additive cohomology of
`ℂP^1`.  That is what keeps the Gysin bootstrap free of circularity: it produces
the ring structure of `H^*(ℂP^n)` without ever assuming any of it.

## Main declarations

* `bijective_lhSum_point_of_shapes` — the base case, over bundled hypotheses.
* `cupPowE_ne_zero_of_le_one` — for a `ℂP^1` fibre there are only two powers.
* `bijective_lhSum_point_cpOne` — **the base case for a rank-two bundle**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable {Z Y : TopCat.{0}}

/-- **The base case, over bundled hypotheses.** -/
theorem bijective_lhSum_point_of_shapes (π : Y ⟶ Z)
    (hZ : HasPointCohomology Z) (hone : one Z ≠ (0 : Hmod2 Z 0))
    (ξ : Hmod2 Y 2) (d : ℕ) (hY : HasCPCohomology Y d)
    (hpow : ∀ m : ℕ, m ≤ d → cupPowE ξ m ≠ 0) (n : ℕ) :
    Function.Bijective (lhSum π ξ (d + 1) n) :=
  bijective_lhSum_point π hZ.1.some hone hZ.2 ξ d hY.1 hY.2 hpow n

/-- For a `ℂP^1` fibre there are only two powers to check, and neither needs a ring
structure: the zeroth is the unit and the first is the class itself. -/
theorem cupPowE_ne_zero_of_le_one {X : TopCat.{0}} (e : Hmod2 X 2)
    (hone : one X ≠ (0 : Hmod2 X 0)) (he : e ≠ 0) :
    ∀ m : ℕ, m ≤ 1 → cupPowE e m ≠ 0 := by
  intro m hm
  interval_cases m
  · exact hone
  · show cup (cupPowE e 0) e ≠ 0
    rw [cupPowE_zero, one_cup']
    exact fun h => he ((cohCast_eq_zero_iff _ _).mp h)

/-- **The base case for a rank-two bundle**, with a `ℂP^1` fibre.  No ring structure
is used, which is what makes the Gysin bootstrap non-circular. -/
theorem bijective_lhSum_point_cpOne (π : Y ⟶ Z)
    (hZ : HasPointCohomology Z) (honeZ : one Z ≠ (0 : Hmod2 Z 0))
    (ξ : Hmod2 Y 2) (hY : HasCPCohomology Y 1)
    (honeY : one Y ≠ (0 : Hmod2 Y 0)) (hξ : ξ ≠ 0) (n : ℕ) :
    Function.Bijective (lhSum π ξ 2 n) :=
  bijective_lhSum_point_of_shapes π hZ honeZ ξ 1 hY
    (cupPowE_ne_zero_of_le_one ξ honeY hξ) n

end

end LH
end CharClass
end GroupApproximation
