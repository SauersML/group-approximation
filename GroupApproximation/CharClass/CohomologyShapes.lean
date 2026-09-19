import GroupApproximation.CharClass.CohomologySphere
import GroupApproximation.CharClass.CohomologyContractible
import GroupApproximation.CharClass.ProjectiveSpaceCohomology

/-!
# The cohomology of a point and of a sphere, in the shapes `cc-projective` uses

Lane `cc-projective` phrases "this space has the cohomology of a point / of
`S^m`" as the predicates `HasPointCohomology` and `HasSphereCohomology` of
`CharClass/ProjectiveSpaceCohomology.lean`.  This file discharges both for the
spaces that actually have those cohomologies: any contractible space, and the
vendored sphere model `Sphere n`.

## Main declarations

* `hasPointCohomology_of_contractible`
* `hasSphereCohomology_sphere`
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- **A contractible space has the mod-2 cohomology of a point.** -/
theorem hasPointCohomology_of_contractible (Y : Type) [TopologicalSpace Y]
    [ContractibleSpace Y] : HasPointCohomology (TopCat.of Y) :=
  ⟨⟨cohZeroEquivOfContractible Y⟩, fun k hk a =>
    cohomology_eq_zero_of_contractible Y k (Nat.one_le_iff_ne_zero.mpr hk) a⟩

/-- **`S^n` has the mod-2 cohomology of `S^n`**: `F₂` in degrees `0` and `n`, zero
elsewhere. -/
theorem hasSphereCohomology_sphere (n : ℕ) (hn : 1 ≤ n) :
    HasSphereCohomology (TopCat.of (Sphere n)) n :=
  ⟨⟨sphereCohZeroEquiv n hn⟩, ⟨sphereTopEquiv n hn⟩, fun k hk hm a =>
    sphere_coh_eq_zero_of_ne n k hk hm a⟩

end

end GroupApproximation.CharClass
