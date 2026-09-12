import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereSuspensionTowerFromMV
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereOrientationPosFromMV
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularHomologyHomotopyInvariance

/-!
# Final assumption aliases (Prompt 61)

This file collects, under stable `final_`-prefixed names, the root assumptions of
the project that already have a genuine **unconditional** constructor after
Branches 1–4.  Every declaration below is a one-line application of an existing,
already-proved term; **no new mathematics, hypotheses, `axiom`, `sorry`,
`opaque`, `unsafe`, or `admit` is introduced.**

Only the assumptions that are unconditionally constructed in the current project
are aliased here.  The assumptions that remain genuinely conditional
(`ModTwoTopClassComparison`, `RPnGeneratorIdentification`,
`RPnTopPowerIdentification`, `RPnCellularCochainStructure`, `RPnTopClassTransfer`,
`RPToSphereTransferTopNonzero`, `TopHomologyTransferNonzeroWitness`) are **not**
given unconditional aliases here, because their underlying constructors still take
free hypotheses; doing so would falsely claim them discharged.  See
`FINAL_ASSUMPTION_INVENTORY.md` for the exact status of each assumption and the
conditional constructors that do exist.
-/

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

