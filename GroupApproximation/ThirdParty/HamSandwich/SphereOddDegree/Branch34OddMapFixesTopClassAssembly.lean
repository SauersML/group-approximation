import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnActualAlphaPowerNonvanishing
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Branch3RPnGeneratorIdentificationFromCellular
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.Branch4TransferNonvanishing
import Mathlib

/-!
# Prompt 09 — Assemble `OddMapFixesTopClass n` from Branch 3 and Branch 4

This file eliminates the previously monolithic public assumption

```text
htop : OddMapFixesTopClass n
```

by *deriving* it from the available Branch-3 and Branch-4 constructors, rather than
assuming it as a black box.

The relevant existing assembly theorem is

```text
oddMapFixesTopClass_of_generatorIdentification
    (I : RPnGeneratorIdentification n) (htr : RPnTopClassTransfer n) :
    OddMapFixesTopClass n
```

(in `RPnActualAlphaPowerNonvanishing.lean`). This file plugs into it the two branch
data:

* **Branch 3.** `rpNGeneratorIdentification_from_cellular n hn c` builds
  `I : RPnGeneratorIdentification n` from the honest cellular-cochain datum
  `c : RPnCellularCochainStructure n` (the cup-product structure is supplied
  internally by the completed constructor `construct_RPnCupProductStructure`).

* **Branch 4.** `construct_RPnTopClassTransfer_from_B4TopData n d hsphere` builds
  `htr : RPnTopClassTransfer n` from the concrete top-degree datum `d : B4TopData n`
  and the rank-one input `hsphere : Module.finrank (ZMod 2) (b4_sphereCohomology n n) = 1`.

Since `B4TopData n` already bundles a cellular datum in its field `d.cc`, the whole
assembly can be driven by the single Branch-4 datum `d` plus `hsphere`.

## Honest status

A *fully parameterless* `oddMapFixesTopClass_unconditional (n : ℕ) (hn : 1 ≤ n) :
OddMapFixesTopClass n` — with **no** further hypotheses — is **not** attainable with
the pinned Mathlib API, and is *not* claimed here. As documented in
`FINAL_ASSUMPTION_INVENTORY.md`, the genuine, Mathlib-absent topological primitives

* `RPnCellularCochainStructure n` (Branch 3), and
* `B4TopData n` together with `hsphere` (Branch 4)

are never inhabited unconditionally anywhere in the project. Fabricating them would
require either a false strict cochain-complex isomorphism or an unproven transfer
identity; we therefore keep them as explicit, honest inputs.

What this file does deliver — and what "eliminating `htop`" concretely means — is
that `OddMapFixesTopClass n` is no longer needed as a *free* assumption: it is a
*theorem* consequence of the honest Branch-3 and Branch-4 data. No `axiom`, `sorry`,
`opaque`, `admit`, `constant`, or `unsafe` is used.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Generic Branch-3 + Branch-4 assembly.** `OddMapFixesTopClass n` from the
Branch-3 generator identification `I` and the Branch-4 top-class transfer `htr`.
This is a thin re-export of `oddMapFixesTopClass_of_generatorIdentification` under a
descriptive name mentioning both branches. -/
theorem oddMapFixesTopClass_of_generatorIdentification_and_transfer {n : ℕ}
    (I : RPnGeneratorIdentification n) (htr : RPnTopClassTransfer n) :
    OddMapFixesTopClass n :=
  oddMapFixesTopClass_of_generatorIdentification I htr

/-- **`OddMapFixesTopClass n` from an honest cellular datum and top-class transfer.**
Given the Branch-3 cellular-cochain datum `c : RPnCellularCochainStructure n` and the
Branch-4 double-cover transfer `htr : RPnTopClassTransfer n`, every odd self-map of
`Sⁿ` fixes a nonzero top `F₂`-class. The generator identification is built from `c`
via `rpNGeneratorIdentification_from_cellular`. -/
theorem oddMapFixesTopClass_of_cellular_and_transfer
    (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (htr : RPnTopClassTransfer n) :
    OddMapFixesTopClass n :=
  oddMapFixesTopClass_of_generatorIdentification
    (rpNGeneratorIdentification_from_cellular n hn c) htr

/-- **`OddMapFixesTopClass n` from the single Branch-4 top datum.** The concrete
top-degree datum `d : B4TopData n` supplies both branch inputs: its cellular field
`d.cc : RPnCellularCochainStructure n` drives the Branch-3 generator identification,
and, together with the sphere rank-one input `hsphere`, it drives the Branch-4
top-class transfer via `construct_RPnTopClassTransfer_from_B4TopData`. The monolithic
`OddMapFixesTopClass n` assumption is thereby *derived*, not assumed. -/
theorem oddMapFixesTopClass_of_branch4TopData
    (n : ℕ) (hn : 1 ≤ n)
    (d : B4TopData n)
    (hsphere : Module.finrank (ZMod 2) (b4_sphereCohomology n n) = 1) :
    OddMapFixesTopClass n :=
  oddMapFixesTopClass_of_cellular_and_transfer n hn d.cc
    (construct_RPnTopClassTransfer_from_B4TopData n d hsphere)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

