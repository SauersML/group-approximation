import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereHomologyS1BaseMV
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.SphereTopHomologyReduction

/-!
# Branch 1 assembly: the unconditional `SphereSuspensionTower`

This file assembles the two Mayer–Vietoris ingredients proved in the previous
prompts into a single concrete, unconditional term of type
`SphereSuspensionTower`:

* the base case `sphereTopHomologyIso_one : SphereTopHomologyIso 1`
  (i.e. `H₁(S¹; ℤ) ≅ ℤ`), from `SphereHomologyS1BaseMV.lean`, and
* the recursive step
  `sphereTopHomology_step_MV : Hₙ₊₁(Sⁿ⁺¹; ℤ) ≅ Hₙ(Sⁿ; ℤ)` (`n ≥ 1`),
  from `SphereHomologyMVStep.lean`.

No Branch 1 theorem is assumed and no placeholder is introduced; the tower is a
genuine term built only from the exported results above.
-/

open CategoryTheory

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **The unconditional sphere suspension tower**, assembled from the
Mayer–Vietoris base case `sphereTopHomologyIso_one` and the Mayer–Vietoris
recursive step `sphereTopHomology_step_MV`. -/
def sphereSuspensionTower_from_MV : SphereSuspensionTower where
  base := sphereTopHomologyIso_one
  step := fun n hn => sphereTopHomology_step_MV n hn

/-- From the unconditional suspension tower, the genuine positive-dimensional
sphere orientation `SphereOrientationPos`. -/
def sphereOrientationPos_from_MV : SphereOrientationPos :=
  sphereSuspensionTower_from_MV.orientation

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
