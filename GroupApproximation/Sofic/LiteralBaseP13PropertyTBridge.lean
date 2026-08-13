import GroupApproximation.Sofic.LiteralBaseP13RotationQuotient
import GroupApproximation.Sofic.LiteralBasePropertyTBridge

/-!
# Property (T) transfer from P13 to the literal affine base

The checked P13 substitution maps onto the abstract rotation presentation.
Property `(T)` therefore descends from P13 to the rotation group, and the
intrinsic affine bridge then promotes it to the literal twenty-relator base.
-/

namespace GroupApproximation
namespace LiteralBaseP13PropertyTBridge

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

end LiteralBaseP13PropertyTBridge
end GroupApproximation
