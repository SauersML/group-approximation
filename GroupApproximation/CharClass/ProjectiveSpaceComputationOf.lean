import GroupApproximation.CharClass.ProjectiveSpaceComputation
import GroupApproximation.CharClass.MayerVietorisSequenceOf
import GroupApproximation.CharClass.ChernEulerBundleOf
import GroupApproximation.CharClass.GysinSphereOf

/-!
# `H^*(ℂP^d; K)` over any field, assembled

The coefficient-generic form of `ProjectiveSpaceComputation.hasCPCohomology_CP`: the cohomology
of complex projective space with coefficients in a field `K` is a line in each even degree up to
`2d` and zero elsewhere.

The induction is the `F₂` one, on the cover of `ℂP^{d+1}` by the affine chart and the complement
of the base point, and every input now exists over `K`:

* the step `ProjectiveSpaceCohomology.hasCPCohomologyOf_succ`, which was coefficient-generic
  already;
* the Mayer–Vietoris sequence over a field, `MayerVietorisSequenceOf.mvSequenceOf`;
* the chart is contractible, `ChernEulerBundleOf.hasPointCohomology_of_contractibleOf`;
* the complement retracts onto `ℂP^d`, by homotopy invariance over `K`
  (`KroneckerContractible.pullEquivOfHomotopyEquivOf`);
* the intersection is `S^{2d+1}`, by the sphere over `K` (`GysinSphereOf.hasSphereCohomologyOf_sphere`);
* the degree-zero hypothesis from the line structure alone,
  `ProjectiveSpaceComputation.exists_sum_eq_of_lines`, which was generic over a field already.

No generator is chosen: over `K` a line has no canonical nonzero element.

## Main declarations

* `hasPointCohomologyOf_chartSpace`, `hasSphereCohomologyOf_interSpace`,
  `hasCPCohomologyOf_punctSpace`, `HasCPCohomologyOf.of_point`, `hasCPCohomologyOf_zero`,
  `punctCohZeroEquivOf`.
* `hasCPCohomologyOf_CP` — **`H^*(ℂP^d; K)`, unconditionally.**
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree (Sphere)

noncomputable section

/-- The affine chart has the `K`-cohomology of a point. -/
theorem hasPointCohomologyOf_chartSpace (K : Type) [Field K] (d : ℕ) :
    HasPointCohomologyOf K (chartSpace d) :=
  haveI : ContractibleSpace ↥(chartOpen d) := contractibleSpace_chartOpen d
  hasPointCohomology_of_contractibleOf K ↥(chartOpen d)

/-- The intersection has the `K`-cohomology of `S^{2d+1}`. -/
theorem hasSphereCohomologyOf_interSpace (K : Type) [Field K] (d : ℕ) :
    HasSphereCohomologyOf K (interSpace d) (2 * d + 1) := by
  refine HasSphereCohomologyOf.of_linearEquiv
    (fun k => (pullEquivOfHomotopyEquivOf K (interSphereHomotopyEquiv d) k).symm) ?_
  exact hasSphereCohomologyOf_sphere K (2 * d + 1) (by omega)

/-- The punctured projective space has the `K`-cohomology of `ℂP^d` once `ℂP^d` does. -/
theorem hasCPCohomologyOf_punctSpace (K : Type) [Field K] (d : ℕ)
    (h : HasCPCohomologyOf K (CPtop d) d) : HasCPCohomologyOf K (punctSpace d) d :=
  HasCPCohomologyOf.of_linearEquiv
    (fun k => (pullEquivOfHomotopyEquivOf K (punctOpenHomotopyEquiv d) k).symm) h

/-- A space with the `K`-cohomology of a point has the `K`-cohomology of `ℂP^0`. -/
theorem HasCPCohomologyOf.of_point {K : Type} [CommRing K] {X : TopCat.{0}}
    (h : HasPointCohomologyOf K X) : HasCPCohomologyOf K X 0 := by
  refine ⟨fun n hn => ?_, fun k hk a => ?_⟩
  · have hn0 : n = 0 := Nat.le_zero.mp hn
    subst hn0
    simpa using h.1
  · exact h.2 k (fun hk0 => hk 0 (le_refl 0) (by omega)) a

/-- **`ℂP^0` is a point**, over `K`. -/
theorem hasCPCohomologyOf_zero (K : Type) [Field K] : HasCPCohomologyOf K (CPtop 0) 0 :=
  HasCPCohomologyOf.of_point (hasPointCohomology_of_contractibleOf K ↥(CPtop 0))

/-- `H^0` of the punctured space is a line over `K`. -/
def punctCohZeroEquivOf (K : Type) [Field K] (d : ℕ) : Hmod K (punctSpace d) 0 ≃ₗ[K] K :=
  (pullEquivOfHomotopyEquivOf K (punctOpenHomotopyEquiv d) 0).symm.trans
    (cohZeroEquivOf K (CPtop d))

/-- **`H^*(ℂP^d; K)`, unconditionally**, over any field: a line in `H^{2n}` for every `n ≤ d`,
and nothing in any other degree. -/
theorem hasCPCohomologyOf_CP (K : Type) [Field K] (d : ℕ) : HasCPCohomologyOf K (CPtop d) d := by
  induction d with
  | zero => exact hasCPCohomologyOf_zero K
  | succ d ih =>
    exact hasCPCohomologyOf_succ
      (mvSequenceOf K (chartOpen d) (punctOpen d) (chartOpen_sup_punctOpen d)) d
      (hasPointCohomologyOf_chartSpace K d)
      (hasCPCohomologyOf_punctSpace K d ih)
      (hasSphereCohomologyOf_interSpace K d)
      (fun w => exists_sum_eq_of_lines _ (cohZeroEquivOf K (CPtop (d + 1)))
        (hasPointCohomologyOf_chartSpace K d).1.some (punctCohZeroEquivOf K d)
        (hasSphereCohomologyOf_interSpace K d).1.some w)
      ⟨cohZeroEquivOf K (CPtop (d + 1))⟩

end

end CharClass
end GroupApproximation
