import GroupApproximation.CharClass.LerayHirschBase
import GroupApproximation.CharClass.LerayHirschCover
import GroupApproximation.CharClass.ProjectiveSpaceCharts
import GroupApproximation.CharClass.ProjectiveSpaceComputation
import GroupApproximation.CharClass.CohomologyKunnethParity

/-!
# Odd-degree vanishing for `ℂP^d`, and the base case over a trivialising open

Two small things owed to other lanes, and the three-line bridge that turns a
chart of a bundle into `LHOver`.

`isZero_odd_CP` is `hasCPCohomology_CP` read in odd degrees, and
`isZero_cohomology_CP_three` is its instance at `3`, which is what makes `Sq¹` of
a Chern root vanish.  `noOddCohomology_CP` puts the same fact in the predicate
`cc-cohom-api`'s parity corollaries consume.

`LHOver_of_chart` is the shape a trivialising open set arrives in: the base has
the cohomology of a point, the part of the total space over it has the cohomology
of `ℂP^1`, and the class is nonzero.  Nothing about the bundle appears, so the
geometry can be supplied separately from the cohomology.

## Main declarations

* `isZero_of_forall_eq_zero` — the vanishing of every element, as `IsZero`.
* `isZero_odd_CP`, `isZero_cohomology_CP_three`, `noOddCohomology_CP`.
* `LHOver_of_chart` — **the base case over a trivialising open, for a rank-two bundle**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59

noncomputable section

/-- A cohomology group all of whose elements vanish is a zero object. -/
theorem isZero_of_forall_eq_zero {X : TopCat.{0}} {k : ℕ}
    (h : ∀ a : Hmod2 X k, a = 0) : Limits.IsZero (Hmod2 X k) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  exact ⟨fun a b => (h a).trans (h b).symm⟩

namespace CPn

/-- **`ℂP^d` has no odd cohomology.** -/
theorem isZero_odd_CP (d k : ℕ) (hk : Odd k) : Limits.IsZero (Hmod2 (CPtop d) k) := by
  obtain ⟨j, rfl⟩ := hk
  refine isZero_of_forall_eq_zero fun a => (hasCPCohomology_CP d).2 _ ?_ a
  intro n _
  omega

/-- `H^3(ℂP^d; F₂) = 0`, which is what makes `Sq¹` of a Chern root vanish. -/
theorem isZero_cohomology_CP_three (d : ℕ) : Limits.IsZero (Hmod2 (CPtop d) 3) :=
  isZero_odd_CP d 3 (by decide)

/-- The same, in the predicate the parity corollaries consume. -/
theorem noOddCohomology_CP (d : ℕ) : KnHemi.NoOddCohomology (CP d) :=
  fun j hj => isZero_odd_CP d j hj

end CPn

/-! ## The base case over a trivialising open -/

namespace LH

variable {X P : TopCat.{0}}

/-- **Leray–Hirsch over a trivialising open set, for a rank-two bundle.**  The base
has the cohomology of a point, the part of the total space over it has the
cohomology of `ℂP^1`, and the class is nonzero.  No ring structure is used, so
this is available before any of `H^*(ℂP^n)` is known. -/
theorem LHOver_of_chart (f : P ⟶ X) (ξ : Hmod2 P 2) (U : Opens X)
    (hU : HasPointCohomology (opSpace U))
    (honeU : one (opSpace U) ≠ (0 : Hmod2 (opSpace U) 0))
    (hY : HasCPCohomology (opSpace (opensComap f U)) 1)
    (honeY : one (opSpace (opensComap f U))
      ≠ (0 : Hmod2 (opSpace (opensComap f U)) 0))
    (hξ : lhClass f ξ U ≠ 0) : LHOver f ξ 2 U :=
  fun n => bijective_lhSum_point_cpOne (opensRestrict f U) hU honeU
    (lhClass f ξ U) hY honeY hξ n

end LH

end

end CharClass
end GroupApproximation
