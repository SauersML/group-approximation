import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.Branch4TransferWitness
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.Branch4RPnTopClassTransfer
import Mathlib

/-!
# Prompt 08 Lean patch: prove nonvanishing of the RP^n top-class transfer to the sphere

This file accompanies Prompt 08 from the current remaining-project prompt list:

  Prove Nonvanishing of the RP^n Top-Class Transfer to the Sphere

Prompt 07 constructs the concrete top-degree Branch-4 datum

  d : B4TopData n

containing the chosen sphere/RP^n top homology classes, the sphere top
cohomology class, the Kronecker normalizations, and the geometric top homology
transfer identity.  This prompt proves that this datum implies the exact
nonvanishing predicates consumed by the final Branch-4 assembly.

The hard topological statement is not hidden here: it is the `transfer_top` field
inside `B4TopData n`.  Once that field is available, the nonvanishing proof is
Kronecker pairing plus rank-one linear algebra over `ZMod 2`.

The project already contains the lower-level proofs:

* `b4_cohTransfer_sphereTopClass_ne_zero`
* `b4_RPToSphereTransferTopNonzero`
* `b4_topHomologyTransferNonzeroWitness`
* `b4_RPnTopClassTransfer_of_cellular`
* `Branch4.b4_rpnTopClassTransfer_of_topData`

This file gives stable Prompt-08 names and bundles the results into a compact
package.  It contains no `sorry`, `axiom`, `constant`, `opaque`, `unsafe`, or
`admit`.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- Prompt-08 package: the three nonvanishing/transfer outputs needed by Branch 4.

* `topNonzero` is the cohomology-transfer nonvanishing predicate.
* `witness` is the homology-side Kronecker witness consumed by older assembly
  theorems.
* `topClassTransfer` is the project-level `RPnTopClassTransfer n` predicate.
-/
structure Branch4TransferNonvanishingPackage (n : Nat) where
  topNonzero : RPToSphereTransferTopNonzero n
  witness : TopHomologyTransferNonzeroWitness n
  topClassTransfer : RPnTopClassTransfer n

/-- The specific chosen sphere top class has nonzero cohomology transfer to
`RP^n`.  This is the direct Kronecker-pairing consequence of `B4TopData`. -/
theorem prompt08_cohTransfer_sphereTopClass_ne_zero
    (n : Nat) (d : B4TopData n) :
    (b4_cohTransferSphereToRP n n).hom d.sphereTopClass ≠ 0 :=
  b4_cohTransfer_sphereTopClass_ne_zero n d

/-- The cohomology transfer is nonzero on every nonzero top sphere class, once
`H^n(S^n; F_2)` is rank one. -/
theorem construct_RPToSphereTransferTopNonzero_from_B4TopData
    (n : Nat) (d : B4TopData n)
    (hsphere : Module.finrank (ZMod 2) (b4_sphereCohomology n n) = 1) :
    RPToSphereTransferTopNonzero n :=
  b4_RPToSphereTransferTopNonzero n d hsphere

/-- Convert the cohomology-transfer nonvanishing statement into the homology-side
Kronecker witness used by the older Branch-4 transfer assembly. -/
theorem construct_TopHomologyTransferNonzeroWitness_from_B4TopData
    (n : Nat) (d : B4TopData n)
    (hsphere : Module.finrank (ZMod 2) (b4_sphereCohomology n n) = 1) :
    TopHomologyTransferNonzeroWitness n :=
  b4_topHomologyTransferNonzeroWitness n d hsphere

/-- Main Prompt-08 project-level output: from `B4TopData n` and the rank-one
sphere top cohomology input, construct `RPnTopClassTransfer n`. -/
theorem construct_RPnTopClassTransfer_from_B4TopData
    (n : Nat) (d : B4TopData n)
    (hsphere : Module.finrank (ZMod 2) (b4_sphereCohomology n n) = 1) :
    RPnTopClassTransfer n :=
  b4_RPnTopClassTransfer_of_cellular n d hsphere

/-- Same output under the stable `Branch4` namespace used by the final assembly
files. -/
theorem construct_RPnTopClassTransfer_from_B4TopData_branch4
    (n : Nat) (d : B4TopData n)
    (hsphere : Module.finrank (ZMod 2) (b4_sphereCohomology n n) = 1) :
    RPnTopClassTransfer n :=
  Branch4.b4_rpnTopClassTransfer_of_topData n d hsphere

/-- Bundle all Prompt-08 outputs into one structure. -/
def construct_Branch4TransferNonvanishingPackage
    (n : Nat) (d : B4TopData n)
    (hsphere : Module.finrank (ZMod 2) (b4_sphereCohomology n n) = 1) :
    Branch4TransferNonvanishingPackage n where
  topNonzero := construct_RPToSphereTransferTopNonzero_from_B4TopData n d hsphere
  witness := construct_TopHomologyTransferNonzeroWitness_from_B4TopData n d hsphere
  topClassTransfer := construct_RPnTopClassTransfer_from_B4TopData n d hsphere

namespace Branch4TransferNonvanishingPackage

/-- Recover the cohomology-transfer nonvanishing predicate from the Prompt-08
package. -/
theorem RPToSphereTransferTopNonzero {n : Nat}
    (P : Branch4TransferNonvanishingPackage n) :
    RPToSphereTransferTopNonzero n :=
  P.topNonzero

/-- Recover the homology-side witness from the Prompt-08 package. -/
theorem TopHomologyTransferNonzeroWitness {n : Nat}
    (P : Branch4TransferNonvanishingPackage n) :
    TopHomologyTransferNonzeroWitness n :=
  P.witness

/-- Recover the project-level Branch-4 transfer predicate from the Prompt-08
package. -/
theorem RPnTopClassTransfer {n : Nat}
    (P : Branch4TransferNonvanishingPackage n) :
    RPnTopClassTransfer n :=
  P.topClassTransfer

end Branch4TransferNonvanishingPackage

/-- If Prompt 07 supplies an unconditional `d : B4TopData n` and Prompts 04/05
supply the rank-one top cohomology statement for `S^n`, Prompt 08 is finished by
this one-line specialization.  This theorem is intentionally parameterized by
those two upstream outputs rather than re-proving them. -/
theorem prompt08_finished_from_prompt07_and_sphere_rank
    (n : Nat) (d : B4TopData n)
    (hsphere : Module.finrank (ZMod 2) (b4_sphereCohomology n n) = 1) :
    RPnTopClassTransfer n :=
  construct_RPnTopClassTransfer_from_B4TopData n d hsphere

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
