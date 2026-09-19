import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoefficientReduction

/-!
# Branch 2 Prompt 04 — Integral degree action on the chosen top generator

This file exposes, as clean Branch 2 wrappers, the integral homology action
formula that defines the degree:

```text
f_* g_Z = degreeOfIso e f • g_Z,
```

where `g_Z = e⁻¹(1)` is the integral top generator
(`integralTopGenerator e`) determined by an identification
`e : Hₙ(Sⁿ; ℤ) ≅ ℤ` and `f : C(Sphere n, Sphere n)` is any continuous self-map.

The underlying mathematical fact is already proved in
`CoefficientReduction.lean` as
`inducedOnTopHomology_apply_integralTopGenerator`; here we only repackage it with
the exact target types used downstream (coefficient reduction / Prompt 05).
-/

open CategoryTheory

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- Branch 2 wrapper: the integral pushforward acts on the chosen integral top
generator by the integer degree.  Stated over the categorical sphere model
`TopCat.sphere n`. -/
theorem branch2_integralTopGenerator_action {n : ℕ}
    (e : (singularHomologyℤ n).obj (TopCat.sphere.{0} n) ≅ ModuleCat.of ℤ ℤ)
    (f : C(Sphere n, Sphere n)) :
    (inducedOnTopHomology f).hom (integralTopGenerator e)
      = degreeOfIso e f • integralTopGenerator e :=
  inducedOnTopHomology_apply_integralTopGenerator e f

/-- Branch 2 wrapper, stated for the project type `SphereTopHomologyIso n`.

Since `SphereTopHomologyIso n` unfolds (through the abbreviations
`sphereTopHomologyℤ`/`sphereHomologyℤ`) to
`(singularHomologyℤ n).obj (TopCat.sphere.{0} n) ≅ ModuleCat.of ℤ ℤ`, this is the
same statement and is discharged by the same underlying lemma — no model
transport between `TopCat.sphere n` and `TopCat.of (Sphere n)` is involved. -/
theorem branch2_integralTopGenerator_action_sphereIso {n : ℕ}
    (e : SphereTopHomologyIso n) (f : C(Sphere n, Sphere n)) :
    (inducedOnTopHomology f).hom (integralTopGenerator e)
      = degreeOfIso e f • integralTopGenerator e :=
  inducedOnTopHomology_apply_integralTopGenerator e f

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

