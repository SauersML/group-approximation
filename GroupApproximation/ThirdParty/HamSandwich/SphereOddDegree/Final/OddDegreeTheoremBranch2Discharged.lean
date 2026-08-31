import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Final.OddDegreeTheoremCanonical
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.ModTwoTopClassComparisonUnconditional
import Mathlib

/-!
# Prompt 10 — Discharge the remaining Branch-2 assumption of the final theorem

This file drives towards the *fully unconditional* odd-degree theorem by removing as
many of the two remaining branch hypotheses of `odd_degree_of_odd_sphere_self_map_of_comparison` as
are genuinely dischargeable with the pinned Mathlib API.

The final public theorem `SphereOddDegree.odd_degree_of_odd_sphere_self_map_of_comparison`
(in `Final/OddDegreeTheorem.lean`) has, after Branch 1 is discharged unconditionally,
exactly two remaining explicit hypotheses:

```text
hcmp : ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn)  -- Branch 2
htop : OddMapFixesTopClass n                                              -- Branches 3+4
```

## What Prompt 06 delivers (Branch 2) — discharged here

Prompt 06 (`AlgebraicTopology/ModTwoTopClassComparisonUnconditional.lean`) supplies a
genuine **unconditional** constructor

```text
final_modTwoTopClassComparison (hn : 1 ≤ n) :
    ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn)
```

(built from `construct_SphereModTwoTopData` via `modTwoTopClassComparison_of_data`),
which depends only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`.
We use it below to remove `hcmp` entirely, leaving `htop` as the **only** remaining
open hypothesis.

## Honest status of Prompt 09 (Branches 3+4) — NOT dischargeable

Prompt 09 (`Branch34OddMapFixesTopClassAssembly.lean`) does **not** provide a
parameterless `final_oddMapFixesTopClass (hn : 1 ≤ n) : OddMapFixesTopClass n`, and no
such term exists anywhere in the project. As documented in `FINAL_ASSUMPTION_INVENTORY.md`
and in the header of the Prompt 09 file, `OddMapFixesTopClass n` is only ever derived
from honest, Mathlib-absent topological primitives — `RPnCellularCochainStructure n`
(Branch 3, which has *no constructor at all*, its literal strict cochain-complex
isomorphism not being provable as stated) and `B4TopData n` together with the sphere
rank-one input (Branch 4). These are never inhabited unconditionally.

Consequently a *fully* unconditional theorem removing **both** `hcmp` and `htop` is
**not attainable**, and is not claimed here. Fabricating `htop` would require an
`axiom`/`sorry`, which this file deliberately avoids. Instead we produce the strongest
honest statement: Branch 2 discharged, `htop` retained as an explicit hypothesis.

If a future prompt exhibits an unconditional `OddMapFixesTopClass n`, plugging it into
the theorems below yields the fully unconditional result with no change of proof.

No `axiom`, `sorry`, `opaque`, `admit`, `constant`, or `unsafe` is used.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Final odd-degree theorem with Branch 2 discharged unconditionally.**

For `n ≥ 1` and an odd map `f : C(Sⁿ, Sⁿ)`, the iso-relative integer degree of `f` is
odd. Compared with `odd_degree_of_odd_sphere_self_map_of_comparison`, the Branch-2 hypothesis `hcmp`
is discharged unconditionally via `final_modTwoTopClassComparison` (Prompt 06), so the
**only** remaining open hypothesis is `htop : OddMapFixesTopClass n` (Branches 3+4).

A fully assumption-free version is not attainable: `OddMapFixesTopClass n` has no
unconditional constructor (see the file header and `FINAL_ASSUMPTION_INVENTORY.md`). -/
theorem odd_degree_of_odd_sphere_self_map_branch2_discharged
    {n : ℕ} (hn : 1 ≤ n)
    (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f) :=
  odd_degree_of_odd_sphere_self_map_of_comparison hn (final_modTwoTopClassComparison hn) htop f hf

/-- **Canonical-degree form, Branch 2 discharged unconditionally.**

Restates `odd_degree_of_odd_sphere_self_map_branch2_discharged` using the project's
canonical unconditional degree `SphereOrientationPos.degree` at the
unconditionally-constructed orientation `final_sphereOrientationPos`. The two
conclusions are definitionally equal. The only remaining open hypothesis is
`htop : OddMapFixesTopClass n`. -/
theorem odd_canonical_degree_of_odd_sphere_self_map_branch2_discharged
    {n : ℕ} (hn : 1 ≤ n)
    (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (final_sphereOrientationPos.degree hn f) :=
  odd_canonical_degree_of_odd_sphere_self_map_of_comparison hn (final_modTwoTopClassComparison hn) htop f hf

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

