import GroupApproximation.CharClass.CohomologyProductCover
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereHomologyMVStep

/-!
# Künneth with a sphere factor, in vanishing form

`S^{n+1}` is covered by its two punctured hemispheres, both contractible, with
intersection the equatorial band, which is homotopy equivalent to `S^n`
(`upperOpens`, `lowerOpens`, `sphereBandHomotopyEquiv`, all vendored).  Crossing
that cover with a space `A` gives a cover of `A × S^{n+1}` by two opens with the
cohomology of `A` and intersection `A × S^n`, so Mayer–Vietoris in the vanishing
form `isZero_mvAmbient` propagates a vanishing range one sphere dimension at a
time:

```text
H^m(A × S^n) = 0  and  H^{m+1}(A) = 0   ⇒   H^{m+1}(A × S^{n+1}) = 0.
```

This is the inductive step of the Künneth vanishing statement `A2` that the
punctured-product recursion of lane `cc-thom` consumes.  The same argument with
`A` a point gives the cohomology suspension isomorphism of spheres, recorded here
because it is the cheapest end-to-end check that the Mayer–Vietoris construction
is the right one.

## Main declarations

* `isZero_prod_sphere_succ` — the inductive step.
* `sphereCohSuspension` — `H^j(S^n; F₂) ≅ H^{j+1}(S^{n+1}; F₂)` for `j ≥ 1`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- The intersection of the two hemispherical opens of `S^{n+1}` is the equatorial
band. -/
theorem upperOpens_inter_lowerOpens (n : ℕ) :
    ((upperOpens n : Opens (sphereSpace n)) : Set (Sphere (n + 1)))
        ∩ ((lowerOpens n : Opens (sphereSpace n)) : Set (Sphere (n + 1)))
      = sphereBand n := rfl

/-- The intersection of the two hemispherical opens of `A × S^{n+1}` is
`A × (equatorial band)`. -/
theorem prodOpen_hemispheres_inter (A : Type) [TopologicalSpace A] (n : ℕ) :
    ((prodOpen A (upperOpens n) : Opens (A × Sphere (n + 1))) : Set (A × Sphere (n + 1)))
        ∩ ((prodOpen A (lowerOpens n) : Opens (A × Sphere (n + 1))) : Set (A × Sphere (n + 1)))
      = Prod.snd ⁻¹' (sphereBand n) := by
  rw [prodOpen_coe_inter, upperOpens_inter_lowerOpens]

/-- `H^m(A × band) = 0` as soon as `H^m(A × S^n) = 0`. -/
theorem isZero_prod_band (A : Type) [TopologicalSpace A] (n m : ℕ)
    (hband : IsZero (Hmod2 (TopCat.of (A × Sphere n)) m)) :
    IsZero (Hmod2 (TopCat.of ↥(Prod.snd ⁻¹' (sphereBand n) : Set (A × Sphere (n + 1)))) m) :=
  isZero_of_linearEquiv (pullEquivOfHomeomorph (prodSubtypeHomeo A (sphereBand n)) m)
    (isZero_of_linearEquiv
      (pullEquivOfHomotopyEquiv
        ((ContinuousMap.HomotopyEquiv.refl A).prodCongr (sphereBandHomotopyEquiv n)) m)
      hband)

set_option maxHeartbeats 1000000 in
/-- **The Künneth vanishing step.**  If the cohomology of `A × S^n` vanishes in
degree `m` and that of `A` vanishes in degree `m+1`, then the cohomology of
`A × S^{n+1}` vanishes in degree `m+1`. -/
theorem isZero_prod_sphere_succ (A : Type) [TopologicalSpace A] (n m : ℕ)
    (hband : IsZero (Hmod2 (TopCat.of (A × Sphere n)) m))
    (hA : IsZero (Hmod2 (TopCat.of A) (m + 1))) :
    IsZero (Hmod2 (TopCat.of (A × Sphere (n + 1))) (m + 1)) := by
  refine isZero_mvAmbient (prodOpen A (upperOpens n)) (prodOpen A (lowerOpens n))
    (prodOpen_sup A (upperOpens_sup_lowerOpens n)) m ?_
    (isZero_prodOpen_of_contractible A (upperOpens n) (m + 1) hA)
    (isZero_prodOpen_of_contractible A (lowerOpens n) (m + 1) hA)
  rw [prodOpen_coe_inter, upperOpens_inter_lowerOpens]
  exact isZero_prod_band A n m hband

/-! ## The cohomology suspension isomorphism -/

/-- **`H^j(S^n; F₂) ≅ H^{j+1}(S^{n+1}; F₂)` for `j ≥ 1`.**  The two hemispheres are
contractible, so the Mayer–Vietoris connecting map from the band is an
isomorphism; the band is homotopy equivalent to `S^n`. -/
def sphereCohSuspension (n j : ℕ) (hj : 1 ≤ j) :
    Hmod2 (TopCat.of (Sphere n)) j ≃ₗ[ZMod 2] Hmod2 (TopCat.of (Sphere (n + 1))) (j + 1) :=
  (pullEquivOfHomotopyEquiv (sphereBandHomotopyEquiv n) j).trans
    (mvConnectingIso (upperOpens n) (lowerOpens n) (upperOpens_sup_lowerOpens n) j
      (cohomology_isZero_of_contractible _ j hj)
      (cohomology_isZero_of_contractible _ j hj)
      (cohomology_isZero_of_contractible _ (j + 1) (by omega))
      (cohomology_isZero_of_contractible _ (j + 1) (by omega))).toLinearEquiv

end

end GroupApproximation.CharClass
