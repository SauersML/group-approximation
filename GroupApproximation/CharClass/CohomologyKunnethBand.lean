import GroupApproximation.CharClass.CohomologyKunnethHemi

/-!
# The equatorial band of a product with a sphere

The intersection of the two hemispherical pieces of `Y × S^{n+1}` is
`Y × (equatorial band)`, homotopy equivalent to `Y × S^n`.  Both the projection
to `Y` and the projection to the sphere factor are compatible with that
equivalence, which is what lets the Künneth induction step move an identity
between `H^*(Y × S^n)` and the intersection.

The other observation here is that the preimage of the hemispherical cover of
`S^{n+1}` under the projection `Y × S^{n+1} → S^{n+1}` **is** the product cover,
on the nose: `Opens` carries a `Prop` field and the two carriers are the same
preimage, so the two opens are definitionally equal.  That is what makes
`mvDelta_naturality` applicable with no transport.

## Main declarations

* `KnHemi.bandRestrict` — the sphere projection restricted to the band.
* `KnHemi.bandHomotopyEquiv` — the band of the product is `Y × S^n`.
* `KnHemi.bandHE_comp_knPrY`, `KnHemi.bandHE_comp_knPrS` — compatibility with
  both projections.
* `KnHemi.opensComap_knPrS_upper`, `KnHemi.opensComap_knPrS_lower`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnHemi

variable (Y : Type) [TopologicalSpace Y] (n : ℕ)

/-! ## 1. The product cover is the preimage cover -/

theorem opensComap_knPrS_upper :
    opensComap (knPrS Y (n + 1)) (upperOpens n) = hemiU Y n := rfl

theorem opensComap_knPrS_lower :
    opensComap (knPrS Y (n + 1)) (lowerOpens n) = hemiV Y n := rfl

/-- The sphere projection restricted to the band. -/
def bandRestrict : TopCat.of ↥(bandSet Y n) ⟶ TopCat.of ↥(sphereBand n) :=
  interRestrict (knPrS Y (n + 1)) (upperOpens n) (lowerOpens n)

/-! ## 2. The band of the product is `Y × S^n` -/

/-- The intersection of the two hemispherical pieces is `Y × S^n`. -/
def bandHomotopyEquiv : ContinuousMap.HomotopyEquiv ↥(bandSet Y n) (Y × Sphere n) :=
  (prodSubtypeHomeo Y (sphereBand n)).toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.refl Y).prodCongr (sphereBandHomotopyEquiv n))

/-- The band equivalence commutes with the projection to `Y`. -/
theorem bandHE_comp_knPrY :
    cmap (bandHomotopyEquiv Y n).toFun ≫ knPrY Y n = prSub Y n (bandSet Y n) := by
  apply TopCat.Hom.ext
  ext p
  rfl

/-- The band equivalence commutes with the projection to the sphere. -/
theorem bandHE_comp_knPrS :
    cmap (bandHomotopyEquiv Y n).toFun ≫ knPrS Y n
      = bandRestrict Y n ≫ cmap (bandToSphere n) := by
  apply TopCat.Hom.ext
  ext p
  rfl

/-- Pulling back along the band equivalence is a linear isomorphism. -/
def bandPullEquiv (k : ℕ) :
    Hmod2 (TopCat.of (Y × Sphere n)) k ≃ₗ[ZMod 2] Hmod2 (TopCat.of ↥(bandSet Y n)) k :=
  pullEquivOfHomotopyEquiv (bandHomotopyEquiv Y n) k

theorem bandPullEquiv_apply (k : ℕ) (x : Hmod2 (TopCat.of (Y × Sphere n)) k) :
    bandPullEquiv Y n k x = pull (cmap (bandHomotopyEquiv Y n).toFun) k x := rfl

/-- The band equivalence is injective on cohomology, which is how an identity on the
intersection is moved to `Y × S^n`. -/
theorem pull_bandHE_injective (k : ℕ) {x y : Hmod2 (TopCat.of (Y × Sphere n)) k}
    (h : pull (cmap (bandHomotopyEquiv Y n).toFun) k x
      = pull (cmap (bandHomotopyEquiv Y n).toFun) k y) : x = y :=
  (bandPullEquiv Y n k).injective h

/-! ## 3. The two projections through the band equivalence -/

theorem pull_bandHE_knPrY (k : ℕ) (c : Hmod2 (TopCat.of Y) k) :
    pull (cmap (bandHomotopyEquiv Y n).toFun) k (pull (knPrY Y n) k c)
      = pull (prSub Y n (bandSet Y n)) k c := by
  rw [← pull_comp, bandHE_comp_knPrY]

theorem pull_bandHE_knPrS (k : ℕ) (t : Hmod2 (TopCat.of (Sphere n)) k) :
    pull (cmap (bandHomotopyEquiv Y n).toFun) k (pull (knPrS Y n) k t)
      = pull (bandRestrict Y n) k (pull (cmap (bandToSphere n)) k t) := by
  rw [← pull_comp, ← pull_comp, bandHE_comp_knPrS]

end KnHemi

end

end GroupApproximation.CharClass
