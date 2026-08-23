import GroupApproximation.Sofic.LiteralBaseP13RotationQuotient
import GroupApproximation.Sofic.LiteralBasePropertyTBridge
import GroupApproximation.Monsters.P13InvariantProjection

/-!
# Property (T) transfer from P13 to the literal affine base

The checked P13 substitution maps onto the abstract rotation presentation.
Property `(T)` therefore descends from P13 to the rotation group, and the
intrinsic affine bridge then promotes it to the literal twenty-relator base.

This is the module the manuscript badges at Proposition `prop:literal-base-T`,
so its three inputs are the three printed steps, each taken from the module
that states it in the manuscript's own terms:

* **Step 1** — property `(T)` of the thirteen-relator presentation — comes from
  `Monsters/P13InvariantProjection.t1_07_p13_hasKazhdanPropertyT`, which reaches
  the Kazhdan pair through the printed spectral localization, the printed
  identification `ker Δ = invariants`, and the printed projection estimate
  "an almost-fixed unit vector is close to an invariant vector".
* **Step 2** — the explicit surjection onto the linear presentation — is the
  quotient permanence `HasKazhdanPropertyT.of_surjective`, applied to the
  checked substitution `p13ToRotation`.
* **Step 3** — the fixed-point bridge to the base — is
  `LiteralBasePropertyTBridge.base_hasKazhdanPropertyT_of_rotation`, which in
  turn routes through `Monsters/P13CircumcenterRouteStep3.lean`.
-/

namespace GroupApproximation
namespace LiteralBaseP13PropertyTBridge

universe w

open LiteralP13Presentation LiteralBaseP13RotationQuotient
open LiteralBaseRotationRetract LiteralBasePropertyTBridge
open LiteralNonMFPresentation

/-- Property `(T)` of the exact P13 presentation implies property `(T)` of
the literal twenty-relator affine base. -/
theorem base_hasKazhdanPropertyT_of_p13
    (hP13 : HasKazhdanPropertyT.{0, 0} P13) :
    HasKazhdanPropertyT.{0, 0} Base := by
  apply base_hasKazhdanPropertyT_of_rotation
  exact HasKazhdanPropertyT.of_surjective p13ToRotation
    p13ToRotation_surjective hP13

/-- The literal twenty-relator affine base has property `(T)`, with the exact
P13 certificate and every transfer premise discharged inside the kernel.

Step 1 enters through `P13InvariantProjection.t1_07_p13_hasKazhdanPropertyT`,
which derives the Kazhdan pair from the printed spectral gap `1/500` by way of
the printed projection estimate.  `LiteralP13HodgeCertificate.p13_hasKazhdanPropertyT`
proves the same conclusion by the damped Richardson iteration and remains
available as the alternate route; both rest on the same exact certificate. -/
theorem base_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} Base :=
  base_hasKazhdanPropertyT_of_p13
    P13InvariantProjection.t1_07_p13_hasKazhdanPropertyT

/-- The premise-free property-`(T)` conclusion for the literal base, exposed
both in the small real formulation used internally and in the
universe-polymorphic textbook complex formulation printed in the manuscript. -/
theorem manuscriptBaseHasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} Base ∧
      HasKazhdanPropertyTComplex.{0, w} Base :=
  ⟨base_hasKazhdanPropertyT,
    hasKazhdanPropertyT_iff_textbook.mp base_hasKazhdanPropertyT⟩

end LiteralBaseP13PropertyTBridge
end GroupApproximation
