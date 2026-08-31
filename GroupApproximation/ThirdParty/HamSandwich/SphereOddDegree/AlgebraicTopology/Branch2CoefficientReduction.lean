import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoefficientReduction
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.Branch2RankOne
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.Branch2IntegralDegreeAction

/-!
# Branch 2 Prompt 05 — Coefficient reduction to `ModTwoTopHomologyScalar`

This file fixes the canonical Branch 2 name for the coefficient-reduction-to-
homology-scalar step, connecting the integral degree action on top homology to
the mod-two scalar action on top `F₂` homology.

All genuine mathematical content already lives in the project:

* `CoefficientReduction.lean` constructs the natural coefficient reduction
  `red_{X,n} : Hₙ(X; ℤ) ⟶ Hₙ(X; F₂)` and proves the reduced-generator action
  (`degree_modTwo_action_on_reduced_generator`), as well as the project-facing
  rank-one packaging `modTwoTopHomologyScalar_of_data`.
* `Branch2RankOne.lean` exposes the sphere wrapper
  `branch2_modTwoTopHomologyScalar_of_data`.

Here we only repackage these under the canonical Branch 2 names consumed by
Prompts 06 and 07. The remaining topological facts (`g_ne`, `spans`, `action`)
remain explicit named fields of `SphereModTwoTopData e`; nothing is hidden.
-/

open CategoryTheory

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Canonical Branch 2 name** for the coefficient-reduction-to-homology-scalar
step: from the bundled top `F₂`-homology datum `SphereModTwoTopData e` (nonzero
spanning generator with the mod-two degree action), every class of
`Hₙ(Sⁿ; F₂)` has the degree-mod-two scalar action, i.e. `ModTwoTopHomologyScalar e`.

This is a thin wrapper around the project's proved
`modTwoTopHomologyScalar_of_data` (equivalently the Branch 2 wrapper
`branch2_modTwoTopHomologyScalar_of_data`). -/
theorem modTwoTopHomologyScalar_of_coefficientReduction {n : ℕ}
    (e : SphereTopHomologyIso n) (d : SphereModTwoTopData e) :
    ModTwoTopHomologyScalar e :=
  branch2_modTwoTopHomologyScalar_of_data e d

/-- **Branch 2 comparison from coefficient reduction data.** Combining the
canonical scalar-action theorem with the project's proved reduction
`modTwoTopClassComparison_of_topHomologyScalar`, the mod-two top-class comparison
`ModTwoTopClassComparison e` follows from the single bundled datum
`SphereModTwoTopData e`. -/
theorem modTwoTopClassComparison_of_coefficientReduction {n : ℕ}
    (e : SphereTopHomologyIso n) (d : SphereModTwoTopData e) :
    ModTwoTopClassComparison e :=
  modTwoTopClassComparison_of_topHomologyScalar e
    (modTwoTopHomologyScalar_of_coefficientReduction e d)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

