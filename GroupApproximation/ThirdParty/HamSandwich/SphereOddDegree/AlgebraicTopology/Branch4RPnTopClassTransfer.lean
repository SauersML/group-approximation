import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.Branch4TransferWitness
import Mathlib

/-!
# Branch 4 — Package `RPnTopClassTransfer` (Prompt 56)

This file is pure packaging.  It exposes the double-cover top-class transfer
predicate `RPnTopClassTransfer n` under stable Branch-4 names, built entirely
from infrastructure already present in the project:

* the conditional assembly theorem `rpnTopClassTransfer_of_cellular_witness`
  (in `RPnTopClassTransferAssembly.lean`), and
* the Prompt-55 witness constructions `b4_topHomologyTransferNonzeroWitness` /
  `b4_RPnTopClassTransfer_of_cellular` (in `Branch4TransferWitness.lean`).

No new algebraic topology is introduced here, and no `axiom`, `sorry`, `opaque`,
`admit`, `constant`, or `unsafe` is used.

## Honest status: conditional (Outcome B)

An *unconditional* `RPnTopClassTransfer n` cannot be produced honestly at this
point, because the required inputs are not constructed unconditionally anywhere
in the project:

* **Missing Branch-3 term.** `RPnCellularCochainStructure n` (defined in
  `RPnAdditiveCohomology.lean`) is never inhabited unconditionally — every
  consumer takes it as a hypothesis.  It bundles the (Mathlib-absent)
  cellular-approximation isomorphism
  `singularCochainComplexZMod2.obj (op (TopCat.of (RP n))) ≅ rpCellularCochainComplex n`.
  There is **no** Branch-3 theorem of the form
  `theorem rpnCellularCochainStructure_constructed (n : ℕ) : RPnCellularCochainStructure n`;
  producing one is the outstanding Branch-3 task.

* **Missing Branch-4 top data.** `B4TopData n` (in `Branch4TransferTopClass.lean`)
  additionally bundles a `MonodromyFunctional n`, chosen top homology/cohomology
  generators, dual-generator pairings, and the geometric homology-transfer
  identity `tr_*(r_n) = s_n` (the honest missing topological input).  It, too,
  is never inhabited unconditionally.

Accordingly we deliver the *explicit-input* theorems below.  Once the two terms
named above are supplied upstream, the wrappers here become unconditional by
feeding those terms in — see `b4_rpnTopClassTransfer_of_constructions`, which is
already unconditional *relative to* those two constructions.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
namespace Branch4

/-- **Explicit-input Branch-4 top-class transfer (from cellular datum + witness).**
Direct wrapper around the existing conditional assembly theorem
`rpnTopClassTransfer_of_cellular_witness`: given the honest cellular-cochain
datum `cc : RPnCellularCochainStructure n` (Branch 3) and the homology-side
transfer witness `hw : TopHomologyTransferNonzeroWitness n` (Prompt 55), the
double-cover top-class transfer predicate `RPnTopClassTransfer n` holds. -/
theorem b4_rpnTopClassTransfer_of_witness
    (n : ℕ)
    (cc : RPnCellularCochainStructure n)
    (hw : TopHomologyTransferNonzeroWitness n) :
    RPnTopClassTransfer n :=
  rpnTopClassTransfer_of_cellular_witness n cc hw

/-- Alias kept for the Prompt-56 naming convention. -/
theorem rpnTopClassTransfer_of_cellular_witness_wrapper
    (n : ℕ)
    (cc : RPnCellularCochainStructure n)
    (hw : TopHomologyTransferNonzeroWitness n) :
    RPnTopClassTransfer n :=
  b4_rpnTopClassTransfer_of_witness n cc hw

/-- **Explicit-input Branch-4 top-class transfer (from bundled top data).**
Given the Prompt-53/54 bundled top data `d : B4TopData n` and one-dimensionality
of `Hⁿ(Sⁿ; F₂)` (`hsphere`), the double-cover top-class transfer predicate
`RPnTopClassTransfer n` holds.  This packages the Prompt-55 result
`b4_RPnTopClassTransfer_of_cellular`, whose cellular input is the bundled
`d.cc` and whose transfer input is the constructed witness
`b4_topHomologyTransferNonzeroWitness`. -/
theorem b4_rpnTopClassTransfer_of_topData
    (n : ℕ) (d : B4TopData n)
    (hsphere : Module.finrank (ZMod 2) (b4_sphereCohomology n n) = 1) :
    RPnTopClassTransfer n :=
  b4_RPnTopClassTransfer_of_cellular n d hsphere

/-- **Unconditional relative to the two outstanding constructions.**  As soon as
Branch 3 supplies `cc : RPnCellularCochainStructure n` and Prompt 55's witness
`hw : TopHomologyTransferNonzeroWitness n` is available, `RPnTopClassTransfer n`
follows with no further hypotheses.  This is the exported form the successor
prompt can specialize to a genuinely-unconditional theorem once
`rpnCellularCochainStructure_constructed` (missing Branch-3 theorem) exists. -/
theorem b4_rpnTopClassTransfer_of_constructions
    (n : ℕ)
    (cc : RPnCellularCochainStructure n)
    (hw : TopHomologyTransferNonzeroWitness n) :
    RPnTopClassTransfer n :=
  b4_rpnTopClassTransfer_of_witness n cc hw

end Branch4
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

