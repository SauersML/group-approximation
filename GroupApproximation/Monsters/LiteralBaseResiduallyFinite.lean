import GroupApproximation.Monsters.LiteralBaseCompleteness
import GroupApproximation.Monsters.ExplicitIntegralLinearModel
import GroupApproximation.Sofic.LEFSofic

/-!
# Residual finiteness and soficity of the literal base

Input I1 of the E-soficity tower
(`notes/SOFICITY_TOWER_MJ_DESIGN_2026-08-15.md`): the twenty-relator
presented base is residually finite and sofic.

The completeness engine identifies the presented base with the concrete
affine matrix group (`LiteralBaseCompleteness.baseAffineEquiv`), whose
residual finiteness and soficity are unconditional
(`ExplicitIntegralLinearModel`); both properties transfer along the
isomorphism.  With this input the telescope levels of the tower are
residually finite, and the kernel trick of the tower design needs only
the finite-range site action.
-/

namespace GroupApproximation
namespace LiteralBaseResiduallyFinite

open LiteralBaseCompleteness ExplicitIntegralLinearModel

noncomputable section

/-- **Tower input I1**: the presented literal base is residually
finite. -/
theorem base_residuallyFinite :
    Group.ResiduallyFinite LiteralNonMFPresentation.Base := by
  haveI := gammaBar_residuallyFinite
  exact residuallyFinite_of_mulEquiv baseAffineEquiv

/-- The presented literal base is sofic. -/
theorem base_isSofic : IsSofic LiteralNonMFPresentation.Base := by
  letI : Group.ResiduallyFinite LiteralNonMFPresentation.Base :=
    base_residuallyFinite
  exact isSofic_of_isLEF isLEF_of_residuallyFinite

/-- The presented literal base is operator MF. -/
theorem base_isOperatorMF :
    IsOperatorMF LiteralNonMFPresentation.Base := by
  letI : Group.ResiduallyFinite LiteralNonMFPresentation.Base :=
    base_residuallyFinite
  exact isOperatorMF_of_residuallyFinite

end

end LiteralBaseResiduallyFinite
end GroupApproximation
