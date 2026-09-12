import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.FinalOddMapComparisonUnconditionalSphere
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoefficientReduction

/-!
# Final assembly: odd self-maps of the sphere have odd degree (Prompt 62)

This file assembles the final odd-degree theorem from the branch constructors
produced by Branches 1–4.  It proves no new topology; every step is a *dependency
application* of already-proved terms.

## Goal and honest status

The intended fully unconditional statement is

```text
n ≥ 1, f : C(Sⁿ, Sⁿ) odd  ⇒  Odd (degree f).
```

Its proof factors through the project's existing final conditional theorem
`SphereOddDegree.oddMap_degree_odd_final`, which combines the branches:

```text
e    : SphereTopHomologyIso n        (Branch 1: integral top homology / orientation)
hcmp : ModTwoTopClassComparison e    (Branch 2: F₂ degree comparison)
htop : OddMapFixesTopClass n         (Branches 3+4: RPⁿ descent + double-cover transfer)
⊢ Odd (degreeOfIso e f).
```

**Status of the branches (verified against the current source; see
`FINAL_ASSUMPTION_INVENTORY.md`):**

* **Branch 1 is discharged unconditionally.** For every `n ≥ 1` the integral
  identification `Hₙ(Sⁿ; ℤ) ≅ ℤ` is supplied by
  `sphereTopHomologyIso_unconditional n hn`, built from the Mayer–Vietoris
  sphere-homology computation.  No Branch 1 hypothesis appears below.
* **Branch 2 is now discharged unconditionally.** The `F₂` sphere top-homology
  datum `SphereModTwoTopData e` has an unconditional constructor
  `construct_SphereModTwoTopData`, and `final_modTwoTopClassComparison hn` supplies
  `ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn)` with no
  hypotheses (see `AlgebraicTopology/ModTwoTopClassComparisonUnconditional.lean`).
  Consequently `Final/OddDegreeTheoremBranch2Discharged.lean` removes `hcmp`
  entirely.
* **Branches 3+4 remain open.** They are packaged as `OddMapFixesTopClass n`;
  its constructors reduce (through `RPnGeneratorIdentification n` /
  `RPnTopClassTransfer n`, or `B4TopData n`) to the single primitive
  `RPnCellularCochainStructure n` — the RPⁿ cellular-approximation isomorphism,
  which is absent from pinned Mathlib and has **no constructor** anywhere in the
  tree.  (`RPnCupProductStructure c` is *no longer* a free primitive: Prompt 44's
  `construct_RPnCupProductStructure` derives it from any
  `c : RPnCellularCochainStructure n`.)

**Superseded.**  The paragraph that stood here said a fully unconditional
theorem removing both `hcmp` and `htop` could not be produced honestly, the
obstruction being `RPnCellularCochainStructure n`.  That is no longer true and
the build refutes it.  `htop` is supplied by
`Final/OddMapFixesTopClassUnconditional.oddMapFixesTopClass_unconditional`,
which bypasses the cellular primitive entirely — it derives
`OddMapFixesTopClass n` from `IsZero (rpCohomology n (n+1))` alone, and
`RPnCohomologyDimensionVanishing.rpCohomology_topPlusOne_isZero_direct` proves
that by Kronecker duality.  `hcmp` was already supplied by
`final_modTwoTopClassComparison`.  The fully unconditional endpoint is
`odd_degree_of_odd_sphere_self_map_unconditional`
(`Final/OddDegreeTheoremUnconditional.lean`), and `BorsukUlam.borsuk_ulam_closed`
gates it with `#audit_closed_axioms`, so a returning hypothesis binder would be
a build error rather than a docstring correction.  This file therefore exports the strongest
honest theorems, with the remaining assumption(s) stated **explicitly** (never
hidden inside a new structure or instance argument).  Branch 2 being discharged,
the preferred endpoint is `odd_degree_of_odd_sphere_self_map_branch2_discharged`
(`Final/OddDegreeTheoremBranch2Discharged.lean`), whose only open hypothesis is
`htop : OddMapFixesTopClass n`.

## Why the finer Branch 3/4 split is not exposed in this same file

The literal four-branch theorem `SphereOddDegree.finalComparison_topPowerInput`
takes the *separate* Branch 3 and Branch 4 predicates
`RPnGeneratorIdentification n` and `RPnTopClassTransfer n`.  Discharging Branch 1
requires the Mayer–Vietoris machinery (`…SmallSimplices`), whose schematic
singular-simplex accessor is `SphereOddDegree.mvSimplexMap`; the cochain accessor
of `RPnW1Cochain.lean` used by the RPⁿ generator/transfer constructors is
`SphereOddDegree.rpCochainSimplexMap`.  These helpers now have distinct qualified
names, so the Branch-1 discharge and the RPⁿ generator/transfer machinery can be
imported into a single environment without a name clash (see
`NamespaceCollisionSmokeTest.lean`).  This file nonetheless keeps the packaging
choice below for stability:

* this file discharges Branch 1 and states Branches 3+4 as the merged predicate
  `OddMapFixesTopClass n` (available on the Branch-1 side);
* the finer split into `RPnGeneratorIdentification n` + `RPnTopClassTransfer n`
  (Branch 1 kept as an explicit `e`) is exactly the pre-existing theorem
  `SphereOddDegree.finalComparison_topPowerInput`.

No `axiom`, `sorry`, `admit`, `opaque`, `constant`, or `unsafe` is used.
-/

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Strongest honest odd-degree theorem — Branch 1 discharged.**

`n ≥ 1`, `f : C(Sⁿ, Sⁿ)` odd, together with the two still-open branch predicates
imply `f` has odd integer degree:

* `hcmp : ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn)` —
  Branch 2 (the `F₂` degree comparison);
* `htop : OddMapFixesTopClass n` — Branches 3+4 (odd self-maps fix a nonzero top
  `F₂`-class, via RPⁿ descent and the double-cover transfer).

The Branch 1 identification `Hₙ(Sⁿ; ℤ) ≅ ℤ` is supplied unconditionally by
`sphereTopHomologyIso_unconditional n hn`; the two remaining hypotheses are the
genuinely open branches, stated as explicit arguments (not hidden in a structure or
instance).  Supplying genuine terms for `hcmp` and `htop` specializes this to the
fully unconditional theorem with no change of proof. -/
theorem odd_degree_of_odd_sphere_self_map_of_comparison {n : ℕ} (hn : 1 ≤ n)
    (hcmp : ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn))
    (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f) :=
  oddMap_degree_odd_final_unconditionalSphere hn hcmp htop f hf

/-- **Same result, Branch 2 drilled to its raw datum.**

Identical to `odd_degree_of_odd_sphere_self_map_of_comparison`, but the Branch 2 predicate is
*constructed inline* from the never-constructed primitive
`d2 : SphereModTwoTopData (sphereTopHomologyIso_unconditional n hn)` via the Branch 2
constructor `modTwoTopClassComparison_of_data`.  The remaining data is therefore
exactly:

* Branch 2: `d2 : SphereModTwoTopData (sphereTopHomologyIso_unconditional n hn)`;
* Branches 3+4: `htop : OddMapFixesTopClass n`.

Once a future prompt exhibits an unconditional term for `SphereModTwoTopData` (and
for the primitives behind `OddMapFixesTopClass`), this specializes to the fully
unconditional statement with no change of proof. -/
theorem odd_degree_of_odd_sphere_self_map_from_branch_data {n : ℕ} (hn : 1 ≤ n)
    (d2 : SphereModTwoTopData (sphereTopHomologyIso_unconditional n hn))
    (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f) := by
  -- Branch 2: mod-two top-class comparison from the F₂ sphere top-homology datum.
  have hcmp : ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn) :=
    modTwoTopClassComparison_of_data (sphereTopHomologyIso_unconditional n hn) d2
  exact odd_degree_of_odd_sphere_self_map_of_comparison hn hcmp htop f hf

/-- **Compatibility alias** for `odd_degree_of_odd_sphere_self_map_of_comparison` under the
descriptive name matching the intended mathematical statement. -/
theorem odd_degree_of_antipodal_odd_map {n : ℕ} (hn : 1 ≤ n)
    (hcmp : ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn))
    (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f) :=
  odd_degree_of_odd_sphere_self_map_of_comparison hn hcmp htop f hf

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

