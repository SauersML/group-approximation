import GroupApproximation.Sofic.MFDefinitions
import GroupApproximation.Sofic.ChosenNonMFTheorem

/-!
# The non-MF witness under every analytic meaning

The group-corona, CDE-corona, ultraproduct, finite-set, and bare
MF-embeddable-ambient formulations are equivalent for the chosen countable
group.  The trace-preserving,
trace-regular, and reduced-C-star meanings are stronger, so the same
counterexample rules them out by contraposition.  Full group C-star
consequences are pointwise in a supplied formal realization and therefore do
not appear in this closed aggregate.

The unrelated modular-by-finite predicate is intentionally absent: the
letters “MF” have a different meaning there, and no implication between that
subgroup-lattice property and matrix-factorization MF is asserted.
-/

namespace GroupApproximation
namespace ChosenNonMFTheorem

open ChosenMarkedPresentation

/-- The chosen finitely presented counterexample fails every closed matrix
and reduced-C-star MF predicate formalized in `MFDefinitions`. -/
theorem chosenFinitelyPresented_not_all_analyticMFDefinitions :
    Group.IsFinitelyPresented MarkedGroup ∧
      ¬ IsGroupTheoreticMF MarkedGroup ∧
      ¬ IsCDEOperatorMF MarkedGroup ∧
      ¬ IsUltraproductMF MarkedGroup ∧
      ¬ IsFiniteSetMF MarkedGroup ∧
      ¬ HasMFAlgebraUnitaryEmbedding MarkedGroup ∧
      ¬ IsStrongMF MarkedGroup ∧
      ¬ IsTracePreservingMF MarkedGroup ∧
      ¬ IsTraceRegularMF MarkedGroup ∧
      ¬ IsReducedGroupCStarMF MarkedGroup := by
  have h : ¬ IsGroupTheoreticMF MarkedGroup :=
    chosenFinitelyPresented_not_isOperatorMF.2
  exact ⟨chosenFinitelyPresented_not_isOperatorMF.1, h,
    not_isCDEOperatorMF_of_not_isGroupTheoreticMF h,
    not_isUltraproductMF_of_not_isGroupTheoreticMF h,
    not_isFiniteSetMF_of_not_isGroupTheoreticMF h,
    not_hasMFAlgebraUnitaryEmbedding_of_not_isGroupTheoreticMF h,
    not_isStrongMF_of_not_isGroupTheoreticMF h,
    not_isTracePreservingMF_of_not_isGroupTheoreticMF h,
    not_isTraceRegularMF_of_not_isGroupTheoreticMF h,
    not_isReducedGroupCStarMF_of_not_isGroupTheoreticMF h⟩

end ChosenNonMFTheorem
end GroupApproximation
