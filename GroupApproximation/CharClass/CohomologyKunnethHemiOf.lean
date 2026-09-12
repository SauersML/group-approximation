import GroupApproximation.CharClass.CohomologyKunnethBand
import GroupApproximation.CharClass.CohomologyKunnethSphereOf
import GroupApproximation.CharClass.MayerVietorisPullOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The hemispherical cover of a product with a sphere, over any ring

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5).

Additive twin of `CohomologyKunnethHemi` and `CohomologyKunnethBand` with coefficients in `K`.
The cover `KnHemi.hemiU`, `KnHemi.hemiV`, the projections `KnHemi.prSub`, the homotopy
equivalences of the pieces with `Y` and of the band with `Y × S^n`, and the commuting squares
between them carry no coefficients and are the `F₂` files' own.  What is new over `K`:

* every class on a piece is pulled back from `Y`, by homotopy invariance over `K`;
* the restrictions to the band are the honest pullbacks, `mvResWUOf_eq_pull` and
  `mvResWVOf_eq_pull` (lane `lix-lh`, `MayerVietorisPullOf`), so a **sum** of restrictions from
  the two pieces is pulled back from `Y`.

**The sign.**  Over `K` the middle map of Mayer–Vietoris is the difference of the two
restrictions, and exactness at the intersection (`mvExactWOf`) reads "killed by `δ` iff a sum
`a| + b|` of honest restrictions", because `b ↦ −b` is a bijection.  So
`exists_pull_prSub_of_resOf` keeps the `F₂` statement's `+` and needs no sign.

## Main declarations

* `KnHemi.exists_pull_prSub_hemiUOf`, `KnHemi.exists_pull_prSub_hemiVOf`.
* `KnHemi.exists_pull_prSub_of_resOf` — a sum of restrictions is pulled back from `Y`.
* `KnHemi.bandPullEquivOf`, `KnHemi.pull_bandHE_injectiveOf`, `KnHemi.pull_bandHE_knPrYOf`,
  `KnHemi.pull_bandHE_knPrSOf` — the band of the product is `Y × S^n`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- The pullback morphism over `K`, applied to an element, is `pull`. -/
theorem cohPullbackK_apply_eq {K : Type} [CommRing K] {A B : TopCat.{0}} (f : A ⟶ B) (n : ℕ)
    (x : Hmod K B n) : (cohPullbackK K f n).hom x = pull f n x := rfl

namespace KnHemi

/-! ## 1. Each piece is `Y`, over `K` -/

/-- Every class on the upper piece is pulled back from `Y`, over any ring. -/
theorem exists_pull_prSub_hemiUOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y]
    (n m : ℕ) (a : Hmod K (TopCat.of ↥(hemiUSet Y n)) m) :
    ∃ c : Hmod K (TopCat.of Y) m, pull (prSub Y n (hemiUSet Y n)) m c = a := by
  refine ⟨(pullEquivOfHomotopyEquivOf K (hemiUHomotopyEquiv Y n) m).symm a, ?_⟩
  rw [prSub_hemiU_eq]
  exact (pullEquivOfHomotopyEquivOf K (hemiUHomotopyEquiv Y n) m).apply_symm_apply a

/-- Every class on the lower piece is pulled back from `Y`, over any ring. -/
theorem exists_pull_prSub_hemiVOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y]
    (n m : ℕ) (a : Hmod K (TopCat.of ↥(hemiVSet Y n)) m) :
    ∃ c : Hmod K (TopCat.of Y) m, pull (prSub Y n (hemiVSet Y n)) m c = a := by
  refine ⟨(pullEquivOfHomotopyEquivOf K (hemiVHomotopyEquiv Y n) m).symm a, ?_⟩
  rw [prSub_hemiV_eq]
  exact (pullEquivOfHomotopyEquivOf K (hemiVHomotopyEquiv Y n) m).apply_symm_apply a

/-! ## 2. The restrictions to the band -/

set_option maxHeartbeats 1000000 in
/-- The restriction of the upper piece to the band is the projection to `Y`, after a class on
the upper piece is written as a pullback. -/
theorem mvResWUOf_pull_prSub (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y] (n m : ℕ)
    (ca : Hmod K (TopCat.of Y) m) :
    (mvResWUOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) m).hom
        (pull (prSub Y n (hemiUSet Y n)) m ca)
      = pull (prSub Y n (bandSet Y n)) m ca := by
  rw [mvResWUOf_eq_pull, cohPullbackK_apply_eq, ← pull_comp, subInclusion_comp_prSub]

set_option maxHeartbeats 1000000 in
/-- The restriction of the lower piece to the band is the projection to `Y`, after a class on
the lower piece is written as a pullback. -/
theorem mvResWVOf_pull_prSub (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y] (n m : ℕ)
    (cb : Hmod K (TopCat.of Y) m) :
    (mvResWVOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) m).hom
        (pull (prSub Y n (hemiVSet Y n)) m cb)
      = pull (prSub Y n (bandSet Y n)) m cb := by
  rw [mvResWVOf_eq_pull, cohPullbackK_apply_eq, ← pull_comp, subInclusion_comp_prSub]

set_option maxHeartbeats 1000000 in
/-- **A sum of restrictions from the two hemispheres is pulled back from `Y`**, over any ring. -/
theorem exists_pull_prSub_of_resOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y]
    (n m : ℕ) (w : Hmod K (TopCat.of ↥(bandSet Y n)) m)
    (a : Hmod K (TopCat.of ↥(hemiUSet Y n)) m) (b : Hmod K (TopCat.of ↥(hemiVSet Y n)) m)
    (hw : (mvResWUOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) m).hom a
      + (mvResWVOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) m).hom b = w) :
    ∃ c : Hmod K (TopCat.of Y) m, pull (prSub Y n (bandSet Y n)) m c = w := by
  obtain ⟨ca, hca⟩ := exists_pull_prSub_hemiUOf K Y n m a
  obtain ⟨cb, hcb⟩ := exists_pull_prSub_hemiVOf K Y n m b
  refine ⟨ca + cb, ?_⟩
  rw [pull_add, ← hw, ← hca, ← hcb, mvResWUOf_pull_prSub, mvResWVOf_pull_prSub]

/-! ## 3. The band of the product is `Y × S^n`, over `K` -/

/-- Pulling back along the band equivalence is a linear isomorphism over `K`. -/
def bandPullEquivOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y] (n k : ℕ) :
    Hmod K (TopCat.of (Y × Sphere n)) k ≃ₗ[K] Hmod K (TopCat.of ↥(bandSet Y n)) k :=
  pullEquivOfHomotopyEquivOf K (bandHomotopyEquiv Y n) k

/-- The band equivalence is injective on cohomology over `K`. -/
theorem pull_bandHE_injectiveOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y]
    (n k : ℕ) {x y : Hmod K (TopCat.of (Y × Sphere n)) k}
    (h : pull (cmap (bandHomotopyEquiv Y n).toFun) k x
      = pull (cmap (bandHomotopyEquiv Y n).toFun) k y) : x = y :=
  (bandPullEquivOf K Y n k).injective h

theorem pull_bandHE_knPrYOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y] (n k : ℕ)
    (c : Hmod K (TopCat.of Y) k) :
    pull (cmap (bandHomotopyEquiv Y n).toFun) k (pull (knPrY Y n) k c)
      = pull (prSub Y n (bandSet Y n)) k c := by
  rw [← pull_comp, bandHE_comp_knPrY]

theorem pull_bandHE_knPrSOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y] (n k : ℕ)
    (t : Hmod K (TopCat.of (Sphere n)) k) :
    pull (cmap (bandHomotopyEquiv Y n).toFun) k (pull (knPrS Y n) k t)
      = pull (bandRestrict Y n) k (pull (cmap (bandToSphere n)) k t) := by
  rw [← pull_comp, ← pull_comp, bandHE_comp_knPrS]

end KnHemi

end

/-! Audited on every build. -/

#audit_axioms KnHemi.exists_pull_prSub_of_resOf
#audit_axioms KnHemi.pull_bandHE_injectiveOf

end GroupApproximation.CharClass
