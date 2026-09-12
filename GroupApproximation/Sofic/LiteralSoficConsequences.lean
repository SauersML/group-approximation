import GroupApproximation.Sofic.LiteralSoficAssembly
import GroupApproximation.Sofic.LiteralSoficEndpoint

namespace GroupApproximation
namespace LiteralSoficAssembly

open LiteralNonMFPresentation

/-- The literal group is hyperlinear. -/
theorem markedGroup_isHyperlinear : IsHyperlinear MarkedGroup :=
  isHyperlinear_of_isSofic markedGroup_isSofic

/-- The literal group is finitely presented, sofic, and not MF. -/
theorem markedGroup_finitelyPresented_sofic_nonMF :
    Group.IsFinitelyPresented MarkedGroup ∧ IsSofic MarkedGroup ∧
      ¬ IsCDEOperatorMF MarkedGroup :=
  LiteralSoficEndpoint.markedGroup_finitelyPresented_sofic_not_isCDEOperatorMF
    markedGroup_isSofic

/-- The hyperlinear form of the same separation. -/
theorem markedGroup_finitelyPresented_hyperlinear_nonMF :
    Group.IsFinitelyPresented MarkedGroup ∧ IsHyperlinear MarkedGroup ∧
      ¬ IsCDEOperatorMF MarkedGroup :=
  LiteralSoficEndpoint.markedGroup_finitelyPresented_hyperlinear_not_isCDEOperatorMF
    markedGroup_isSofic

/-- The literal group is sofic, not LEF, and not residually finite. -/
theorem markedGroup_sofic_not_isLEF_unconditional :
    IsSofic MarkedGroup ∧ ¬ IsLEF MarkedGroup ∧
      ¬ Group.ResiduallyFinite MarkedGroup :=
  LiteralSoficEndpoint.markedGroup_sofic_not_isLEF markedGroup_isSofic

end LiteralSoficAssembly
end GroupApproximation
