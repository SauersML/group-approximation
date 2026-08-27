import GroupApproximation.Sofic.LiteralAffineCongruenceBase
import GroupApproximation.Sofic.LiteralBaseP13PropertyTBridge
import GroupApproximation.Kazhdan.KazhdanFiniteIndex

/-!
# Finite-presentation and Kazhdan properties of the affine congruence base

This module is deliberately separate from the torsion-free core so importing
the elementary torsion argument does not load the analytic property-`(T)`
development.
-/

namespace GroupApproximation
namespace LiteralAffineCongruenceBase

open LiteralNonMFPresentation

noncomputable section

/-- Finite presentation passes from the literal affine base to its
finite-index level-three subgroup. -/
theorem p_isFinitelyPresented : Group.IsFinitelyPresented P :=
  FiniteIndex.isFinitelyPresented_subgroup_of_finiteIndex' levelThree
    (inferInstance : Group.IsFinitelyPresented Base)

/-- Property `(T)` passes from the literal affine base to its finite-index
level-three subgroup. -/
theorem p_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} P :=
  FiniteIndex.hasKazhdanPropertyT_of_finiteIndex levelThree
    LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT

end

end LiteralAffineCongruenceBase
end GroupApproximation
