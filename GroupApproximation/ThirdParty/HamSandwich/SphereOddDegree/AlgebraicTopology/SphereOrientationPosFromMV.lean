import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereSuspensionTowerFromMV

/-!
# Branch 1 finalization: the unconditional `SphereOrientationPos`

Prompt 25 assembled the unconditional Mayer–Vietoris sphere suspension tower
`sphereSuspensionTower_from_MV : SphereSuspensionTower` and already derived the
positive-dimensional sphere orientation `sphereOrientationPos_from_MV` from it via
`SphereSuspensionTower.orientation`.

This file exposes the **stable final names** that downstream code (Prompt 27) can
depend on:

* `sphereOrientationPos_unconditional : SphereOrientationPos` — the canonical
  unconditional positive-dimensional sphere orientation, built solely from the
  Mayer–Vietoris suspension tower (no Branch 1 theorem is assumed).
* `sphereTopHomologyIso_unconditional (n : ℕ) (hn : 1 ≤ n) : SphereTopHomologyIso n`
  — the projection giving the integral top-homology identification
  `Hₙ(Sⁿ; ℤ) ≅ ℤ` in each dimension `n ≥ 1`.

No `n = 0` case is restored: `SphereTopHomologyIso 0` is genuinely empty
(`sphereTopHomologyIso_zero_isEmpty`), so the only correct object is the
positive-dimensional `SphereOrientationPos`.

No placeholders or forbidden tokens are introduced; everything is a genuine term
built from the previously proved Mayer–Vietoris results.
-/

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **The canonical unconditional positive-dimensional sphere orientation.**

This is the stable export of the Branch 1 construction: a genuine, non-vacuous
`SphereOrientationPos` built entirely from the unconditional Mayer–Vietoris
suspension tower `sphereSuspensionTower_from_MV` (no Branch 1 hypothesis is
assumed). -/
def sphereOrientationPos_unconditional : SphereOrientationPos :=
  sphereOrientationPos_from_MV

/-- **Stable projection.** The integral top-homology identification
`Hₙ(Sⁿ; ℤ) ≅ ℤ` for every dimension `n ≥ 1`, read off the unconditional
positive-dimensional orientation. -/
def sphereTopHomologyIso_unconditional (n : ℕ) (hn : 1 ≤ n) :
    SphereTopHomologyIso n :=
  sphereOrientationPos_unconditional.iso n hn

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
