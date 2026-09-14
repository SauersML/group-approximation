/-
Local adaptation of the HamSandwich development at
https://github.com/akopjan/HamSandwich/tree/76202dbbb6610ffcebbccfbf7a56f833a4c2a376
Changed for this repository: namespace isolation, Lean 4.32 porting,
and local proof integration. The original license is retained in this tree.
-/
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereSuspensionTowerFromMV
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereOrientationPosFromMV
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularHomologyHomotopyInvariance





















noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Root assumption `SphereSuspensionTower` — discharged unconditionally.**
Alias of the Mayer–Vietoris assembly `sphereSuspensionTower_from_MV`. -/
def final_sphereSuspensionTower : SphereSuspensionTower :=
  sphereSuspensionTower_from_MV

/-- **Root assumption `SphereOrientationPos` — discharged unconditionally.**
Alias of `sphereOrientationPos_unconditional` (built from the Mayer–Vietoris
suspension tower). -/
def final_sphereOrientationPos : SphereOrientationPos :=
  sphereOrientationPos_unconditional

/-- **Root assumption `SphereTopHomologyIso n` — discharged unconditionally for
`n ≥ 1`.**  Alias of `sphereTopHomologyIso_unconditional`.  (There is no `n = 0`
term: `SphereTopHomologyIso 0` is genuinely empty.) -/
def final_sphereTopHomologyIso (n : ℕ) (hn : 1 ≤ n) : SphereTopHomologyIso n :=
  sphereTopHomologyIso_unconditional n hn

/-- **The singular prism operator — discharged unconditionally.**  Alias of
`singularPrismOperator`; this is the homotopy-invariance input that combines with
`final_sphereOrientationPos` to give the full integral degree theory. -/
theorem final_singularPrismOperator : SingularPrismOperator :=
  singularPrismOperator

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

