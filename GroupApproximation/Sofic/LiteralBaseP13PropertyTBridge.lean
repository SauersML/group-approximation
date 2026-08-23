import GroupApproximation.Sofic.LiteralBaseP13RotationQuotient
import GroupApproximation.Sofic.LiteralBasePropertyTBridge
import GroupApproximation.Sofic.LiteralP13HodgeCertificate

/-!
# Property (T) transfer from P13 to the literal affine base

The checked P13 substitution maps onto the abstract rotation presentation.
Property `(T)` therefore descends from P13 to the rotation group, and the
intrinsic affine bridge then promotes it to the literal twenty-relator base.

The exact Hodge certificate proves property `(T)` for the thirteen-relator
presentation.  Property `(T)` then descends through the checked substitution
onto the rotation group and passes to the literal base through the affine
fixed-point argument.
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

/-- The literal twenty-relator affine base has property `(T)`. -/
theorem base_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} Base :=
  base_hasKazhdanPropertyT_of_p13
    LiteralP13HodgeCertificate.p13_hasKazhdanPropertyT

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
