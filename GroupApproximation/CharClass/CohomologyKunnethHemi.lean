import GroupApproximation.CharClass.CohomologyKunnethSphere
import GroupApproximation.CharClass.CohomologyKunnethSplit
import GroupApproximation.CharClass.MayerVietorisNaturality

/-!
# The hemispherical cover of a product with a sphere

For the Künneth injectivity statement the product `Y × S^{n+1}` is covered by
`Y × (upper punctured sphere)` and `Y × (lower punctured sphere)`.  Both pieces
are homotopy equivalent to `Y` **through the projection**, so every class on a
piece is pulled back from `Y`.

The one consequence needed downstream is `KnHemi.exists_pull_prSub_of_res`: a
class on the intersection that is a sum of restrictions from the two pieces is
pulled back from `Y`.  Combined with the slice retraction, which kills the sphere
class, this is what makes the kernel of the connecting map harmless in the
Künneth induction.

## Main declarations

* `KnHemi.hemiU`, `KnHemi.hemiV`, `KnHemi.hemi_sup` — the cover.
* `KnHemi.prSub` — the projection of a subspace of the product to `Y`.
* `KnHemi.hemiUHomotopyEquiv`, `KnHemi.hemiVHomotopyEquiv` — the pieces are `Y`,
  and `KnHemi.prSub_hemiU_eq` says the equivalence *is* the projection.
* `KnHemi.exists_pull_prSub_of_res`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- The pullback morphism, applied to an element, is `pull`. -/
theorem cohPullback_apply_eq {A B : TopCat.{0}} (f : A ⟶ B) (n : ℕ) (x : Hmod2 B n) :
    (cohPullback f n).hom x = pull f n x := rfl

namespace KnHemi

variable (Y : Type) [TopologicalSpace Y] (n : ℕ)

/-- The product `Y × S^{n+1}` as an object of `TopCat`.  Every set and open below is
typed over this object, because the ambient `TopCat` of `subInclusion`, `mvResWU`
and friends is *not* inferable from a `Set (Y × Sphere (n + 1))`. -/
abbrev prodTop : TopCat.{0} := TopCat.of (Y × Sphere (n + 1))

/-- The upper hemispherical open of `Y × S^{n+1}`. -/
abbrev hemiU : Opens ↥(prodTop Y n) := prodOpen Y (upperOpens n)

/-- The lower hemispherical open of `Y × S^{n+1}`. -/
abbrev hemiV : Opens ↥(prodTop Y n) := prodOpen Y (lowerOpens n)

/-- The upper piece as a set. -/
abbrev hemiUSet : Set ↥(prodTop Y n) := (hemiU Y n : Set ↥(prodTop Y n))

/-- The lower piece as a set. -/
abbrev hemiVSet : Set ↥(prodTop Y n) := (hemiV Y n : Set ↥(prodTop Y n))

/-- The intersection of the two pieces, `Y × (equatorial band)`. -/
abbrev bandSet : Set ↥(prodTop Y n) := hemiUSet Y n ∩ hemiVSet Y n

theorem hemi_sup : hemiU Y n ⊔ hemiV Y n = ⊤ :=
  prodOpen_sup Y (upperOpens_sup_lowerOpens n)

/-! ## 1. The projection of a subspace to `Y` -/

/-- The projection to `Y` of a subspace of `Y × S^{n+1}`. -/
def prSub (S : Set ↥(prodTop Y n)) : TopCat.of ↥S ⟶ TopCat.of Y :=
  cmap ⟨fun p => (p : Y × Sphere (n + 1)).1,
    continuous_fst.comp continuous_subtype_val⟩

/-- The inclusion of a subspace into the ambient product, as a `TopCat` morphism. -/
theorem sInclusion_comp_prSub (S : Set ↥(prodTop Y n)) :
    sInclusion S ≫ knPrY Y (n + 1) = prSub Y n S := rfl

theorem subInclusion_comp_prSub {S T : Set ↥(prodTop Y n)} (h : S ⊆ T) :
    subInclusion h ≫ prSub Y n T = prSub Y n S := rfl

/-! ## 2. Each piece is `Y` -/

/-- The upper piece `Y × (upper punctured sphere)` is homotopy equivalent to `Y`. -/
def hemiUHomotopyEquiv : ContinuousMap.HomotopyEquiv ↥(hemiUSet Y n) Y :=
  (prodSubtypeHomeo Y
      ((upperOpens n : Opens (Sphere (n + 1))) : Set (Sphere (n + 1)))).toHomotopyEquiv.trans
    (prodContractibleEquiv Y
      ↥((upperOpens n : Opens (Sphere (n + 1))) : Set (Sphere (n + 1))))

/-- The lower piece is homotopy equivalent to `Y`. -/
def hemiVHomotopyEquiv : ContinuousMap.HomotopyEquiv ↥(hemiVSet Y n) Y :=
  (prodSubtypeHomeo Y
      ((lowerOpens n : Opens (Sphere (n + 1))) : Set (Sphere (n + 1)))).toHomotopyEquiv.trans
    (prodContractibleEquiv Y
      ↥((lowerOpens n : Opens (Sphere (n + 1))) : Set (Sphere (n + 1))))

theorem hemiUHomotopyEquiv_toFun :
    (hemiUHomotopyEquiv Y n).toFun = (prSub Y n (hemiUSet Y n)).hom := by
  ext p
  rfl

theorem hemiVHomotopyEquiv_toFun :
    (hemiVHomotopyEquiv Y n).toFun = (prSub Y n (hemiVSet Y n)).hom := by
  ext p
  rfl

/-- The projection of the upper piece **is** the homotopy equivalence with `Y`. -/
theorem prSub_hemiU_eq :
    prSub Y n (hemiUSet Y n) = cmap (hemiUHomotopyEquiv Y n).toFun :=
  (TopCat.Hom.ext (hemiUHomotopyEquiv_toFun Y n)).symm

/-- The projection of the lower piece **is** the homotopy equivalence with `Y`. -/
theorem prSub_hemiV_eq :
    prSub Y n (hemiVSet Y n) = cmap (hemiVHomotopyEquiv Y n).toFun :=
  (TopCat.Hom.ext (hemiVHomotopyEquiv_toFun Y n)).symm

/-- Every class on the upper piece is pulled back from `Y`. -/
theorem exists_pull_prSub_hemiU (m : ℕ)
    (a : Hmod2 (TopCat.of ↥(hemiUSet Y n)) m) :
    ∃ c : Hmod2 (TopCat.of Y) m, pull (prSub Y n (hemiUSet Y n)) m c = a := by
  refine ⟨(pullEquivOfHomotopyEquiv (hemiUHomotopyEquiv Y n) m).symm a, ?_⟩
  rw [prSub_hemiU_eq]
  exact (pullEquivOfHomotopyEquiv (hemiUHomotopyEquiv Y n) m).apply_symm_apply a

/-- Every class on the lower piece is pulled back from `Y`. -/
theorem exists_pull_prSub_hemiV (m : ℕ)
    (a : Hmod2 (TopCat.of ↥(hemiVSet Y n)) m) :
    ∃ c : Hmod2 (TopCat.of Y) m, pull (prSub Y n (hemiVSet Y n)) m c = a := by
  refine ⟨(pullEquivOfHomotopyEquiv (hemiVHomotopyEquiv Y n) m).symm a, ?_⟩
  rw [prSub_hemiV_eq]
  exact (pullEquivOfHomotopyEquiv (hemiVHomotopyEquiv Y n) m).apply_symm_apply a

/-! ## 3. The kernel of the connecting map is pulled back from `Y` -/

set_option maxHeartbeats 1000000 in
/-- The restriction of the upper piece to the band is the projection to `Y`, after a
class on the upper piece is written as a pullback. -/
theorem mvResWU_pull_prSub (m : ℕ) (ca : Hmod2 (TopCat.of Y) m) :
    (mvResWU (hemiU Y n) (hemiV Y n) (hemi_sup Y n) m).hom
        (pull (prSub Y n (hemiUSet Y n)) m ca)
      = pull (prSub Y n (bandSet Y n)) m ca := by
  rw [mvResWU_eq_pull, cohPullback_apply_eq, ← pull_comp, subInclusion_comp_prSub]

set_option maxHeartbeats 1000000 in
theorem mvResWV_pull_prSub (m : ℕ) (cb : Hmod2 (TopCat.of Y) m) :
    (mvResWV (hemiU Y n) (hemiV Y n) (hemi_sup Y n) m).hom
        (pull (prSub Y n (hemiVSet Y n)) m cb)
      = pull (prSub Y n (bandSet Y n)) m cb := by
  rw [mvResWV_eq_pull, cohPullback_apply_eq, ← pull_comp, subInclusion_comp_prSub]

set_option maxHeartbeats 1000000 in
/-- **A sum of restrictions from the two hemispheres is pulled back from `Y`.** -/
theorem exists_pull_prSub_of_res (m : ℕ)
    (w : Hmod2 (TopCat.of ↥(bandSet Y n)) m)
    (a : Hmod2 (TopCat.of ↥(hemiUSet Y n)) m)
    (b : Hmod2 (TopCat.of ↥(hemiVSet Y n)) m)
    (hw : (mvResWU (hemiU Y n) (hemiV Y n) (hemi_sup Y n) m).hom a
      + (mvResWV (hemiU Y n) (hemiV Y n) (hemi_sup Y n) m).hom b = w) :
    ∃ c : Hmod2 (TopCat.of Y) m, pull (prSub Y n (bandSet Y n)) m c = w := by
  obtain ⟨ca, hca⟩ := exists_pull_prSub_hemiU Y n m a
  obtain ⟨cb, hcb⟩ := exists_pull_prSub_hemiV Y n m b
  refine ⟨ca + cb, ?_⟩
  rw [pull_add, ← hw, ← hca, ← hcb, mvResWU_pull_prSub, mvResWV_pull_prSub]

end KnHemi

end

end GroupApproximation.CharClass
