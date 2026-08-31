import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Final.OddDegreeTheoremBranch2Discharged
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Final.OddMapFixesTopClassUnconditional
import Mathlib

/-!
# Prompt 07 — Final odd-degree assembly and honest audit

## What this file assembles

The Branch-2 side of the odd-degree argument is discharged **unconditionally** in
`OddDegreeTheoremBranch2Discharged.lean`:

```text
odd_degree_of_odd_sphere_self_map_branch2_discharged
    {n} (hn : 1 ≤ n) (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f)
```

so the *only* remaining input to the public odd-degree theorem is
`OddMapFixesTopClass n`.

Prompt 06 (`OddMapFixesTopClassUnconditional.lean`) reduced `OddMapFixesTopClass n`
— removing the `RPnCellularCochainStructure n` datum and the homology-transfer
witness — to **one single mod-2 cohomological vanishing fact**:

```text
IsZero (rpCohomology n (n+1))     -- i.e. Hⁿ⁺¹(RPⁿ; F₂) = 0
```

via `oddMapFixesTopClass_of_topVanish`.

This file records the fully-assembled odd-degree theorem **conditional on that one
fact**, in both the transfer-orientation and canonical-orientation forms, with no
`sorry` and only the standard project axioms.

## Honest status of the `*_unconditional` theorem (Prompt 07 audit)

The prompt asked for a *fully unconditional* theorem

```text
odd_degree_of_odd_sphere_self_map_unconditional
```

built by feeding an unconditional

```text
oddMapFixesTopClass_unconditional (n) (hn : 1 ≤ n) : OddMapFixesTopClass n
```

into the Branch-2-discharged theorem. **That unconditional constructor was not
found/proved in the project.** Its only missing ingredient is

```text
rpCohomology_topPlusOne_isZero (n) (hn : 1 ≤ n) : IsZero (rpCohomology n (n+1))
```

which is the classical **singular excision / good-pair computation** for the pair
`(RPⁿ⁺¹, RPⁿ)` (equivalently `H^{n+1}(RPⁿ⁺¹, RPⁿ; F₂) ≅ H̃^{n+1}(Sⁿ⁺¹; F₂)`).
This is the single theorem the project header
(`RPnAdditiveCohomologyStructureUnconditional.lean`) identifies as absent from
pinned Mathlib and from the current project machinery. It is **Branch-3
mathematics**, which this final-assembly prompt is explicitly instructed not to
prove.

In keeping with the prompt's stated failure mode, no fake `*_unconditional`
theorem is created here: the honest theorems below carry the explicit hypothesis
`hvanish : IsZero (rpCohomology n (n+1))`, and the axiom-free chain that discharges
`OddMapFixesTopClass n` from it (`oddMapFixesTopClass_of_topVanish`) is reused
directly. See `FINAL_UNCONDITIONAL_BUILD_REPORT.md`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Odd-degree theorem, reduced to the single RPⁿ top-dimension vanishing fact.**

An odd self-map of `Sⁿ` (`n ≥ 1`) has odd topological degree, provided the one
genuinely-missing mod-2 cohomological fact `Hⁿ⁺¹(RPⁿ; F₂) = 0`
(`hvanish : IsZero (rpCohomology n (n+1))`). Branch 2 is discharged
unconditionally, and `OddMapFixesTopClass n` is obtained from `hvanish` through
`oddMapFixesTopClass_of_topVanish` with **no** `RPnCellularCochainStructure n`,
`RPnGeneratorIdentification n`, or homology-transfer witness. -/
theorem odd_degree_of_odd_sphere_self_map_of_rpTopVanish
    {n : ℕ} (hn : 1 ≤ n)
    (hvanish : IsZero (rpCohomology n (n + 1)))
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f) :=
  odd_degree_of_odd_sphere_self_map_branch2_discharged hn
    (oddMapFixesTopClass_of_topVanish n hn hvanish) f hf

/-- **Canonical-degree form**, reduced to the single RPⁿ top-dimension vanishing
fact `Hⁿ⁺¹(RPⁿ; F₂) = 0`. -/
theorem odd_canonical_degree_of_odd_sphere_self_map_of_rpTopVanish
    {n : ℕ} (hn : 1 ≤ n)
    (hvanish : IsZero (rpCohomology n (n + 1)))
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (final_sphereOrientationPos.degree hn f) :=
  odd_canonical_degree_of_odd_sphere_self_map_branch2_discharged hn
    (oddMapFixesTopClass_of_topVanish n hn hvanish) f hf

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

