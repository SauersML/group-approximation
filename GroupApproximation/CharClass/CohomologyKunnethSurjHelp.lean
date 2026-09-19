import GroupApproximation.CharClass.CohomologyKunnethStep
import GroupApproximation.CharClass.MayerVietorisZero
import GroupApproximation.CharClass.CohomologySphereZero

/-!
# Ingredients for Künneth surjectivity

The decomposition of `H^*(Y × S^{n+1})` runs the same Mayer–Vietoris argument as
the injectivity, in the opposite direction: restrict a class to the two
hemispherical pieces, observe that the two restrictions come from the *same*
class on `Y`, subtract it, and land in the image of the connecting map.

This file collects the four facts that step needs and that the injectivity did
not: the restriction of a pullback from `Y` is the projection of the piece, the
two restrictions to the band agree, the projection of the band is injective on
cohomology, and the connecting map kills anything pulled back from `Y`.

## Main declarations

* `spherePoint` — a point of every sphere, so `pull (knPrY …)` is always injective.
* `KnHemi.mvResU_pull_knPrY`, `KnHemi.mvResV_pull_knPrY`.
* `KnHemi.mvResWU_mvResU`, `KnHemi.mvResWV_mvResV`.
* `KnHemi.pull_prSub_band_injective`.
* `KnHemi.mvDelta_pull_prSub_band` — the connecting map kills a pullback from `Y`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- A point of every sphere: the two-point sphere has its positive point, and every
higher sphere has its north pole. -/
def spherePoint : (n : ℕ) → Sphere n
  | 0 => ((Classical.choice nonempty_sphereZeroPos) : ↥(sphereZeroPos : Set (Sphere 0))).1
  | (k + 1) => northPole k

namespace KnHemi

variable (Y : Type) [TopologicalSpace Y] (n : ℕ)

/-! ## 1. Restriction of a pullback from `Y` -/

theorem mvResU_pull_knPrY (k : ℕ) (a : Hmod2 (TopCat.of Y) k) :
    (mvResU (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom
        (pull (knPrY Y (n + 1)) k a)
      = pull (prSub Y n (hemiUSet Y n)) k a := by
  rw [mvResU_eq_pull, cohPullback_apply_eq, ← pull_comp, sInclusion_comp_prSub]

theorem mvResV_pull_knPrY (k : ℕ) (a : Hmod2 (TopCat.of Y) k) :
    (mvResV (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom
        (pull (knPrY Y (n + 1)) k a)
      = pull (prSub Y n (hemiVSet Y n)) k a := by
  rw [mvResV_eq_pull, cohPullback_apply_eq, ← pull_comp, sInclusion_comp_prSub]

/-! ## 2. The two restrictions to the band agree -/

theorem mvResWU_mvResU (k : ℕ) (z : Hmod2 (prodTop Y n) k) :
    (mvResWU (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom
        ((mvResU (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom z)
      = pull (sInclusion (bandSet Y n)) k z := by
  rw [mvResWU_eq_pull, mvResU_eq_pull, cohPullback_apply_eq, cohPullback_apply_eq,
    ← pull_comp, subInclusion_comp_sInclusion]

theorem mvResWV_mvResV (k : ℕ) (z : Hmod2 (prodTop Y n) k) :
    (mvResWV (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom
        ((mvResV (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom z)
      = pull (sInclusion (bandSet Y n)) k z := by
  rw [mvResWV_eq_pull, mvResV_eq_pull, cohPullback_apply_eq, cohPullback_apply_eq,
    ← pull_comp, subInclusion_comp_sInclusion]

/-! ## 3. The projection of the band is injective on cohomology -/

theorem pull_prSub_band_injective (k : ℕ) :
    Function.Injective (pull (prSub Y n (bandSet Y n)) k) := by
  intro c₁ c₂ hc
  refine pull_knPrY_injective Y n (spherePoint n) k ?_
  refine pull_bandHE_injective Y n k ?_
  rw [pull_bandHE_knPrY, pull_bandHE_knPrY]
  exact hc

/-! ## 4. The connecting map kills a pullback from `Y` -/

theorem mvDelta_pull_prSub_band (k : ℕ) (c : Hmod2 (TopCat.of Y) k) :
    (mvDelta (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom
      (pull (prSub Y n (bandSet Y n)) k c) = 0 := by
  refine (mvExactW (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k _).2 ?_
  refine ⟨pull (prSub Y n (hemiUSet Y n)) k c, 0, ?_⟩
  rw [mvResWU_pull_prSub, map_zero, add_zero]

end KnHemi

end

end GroupApproximation.CharClass
