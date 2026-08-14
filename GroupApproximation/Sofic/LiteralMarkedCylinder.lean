import GroupApproximation.Sofic.LiteralMarkedCylinderTopology
import GroupApproximation.Sofic.LiteralUniversalHorn

/-!
# The literal clopen cylinder consists entirely of non-MF groups

The forty-one printed relators and the nontriviality of the marked word form
one finite, clopen condition in the space of eight-marked groups.  The literal
universal Horn theorem excludes every operator-MF group from this cylinder.
Consequently the obstruction is finite, local, logical, and stable under
perturbation in marked-group space.
-/

namespace GroupApproximation
namespace LiteralMarkedCylinder

open LiteralNonMFPresentation LiteralUniversalHorn MarkedGroupSpace

noncomputable section

/-- Every point of the exact literal cylinder is non-MF. -/
theorem literalCylinder_subset_nonMF :
    literalCylinder ⊆
      {N : MarkedGroupSpace 8 | ¬ IsOperatorMF N.Quotient} := by
  intro N hN hMF
  have hkill :=
    isOperatorMF_satisfies_literalQuasiIdentity N.Quotient hMF
  exact cylinder_markedWord_ne_one
    LiteralNonMFLinearWitness.literal_mark_ne_one hN
    (hkill (quotientGenerator N) (fun _ hr ↦
      cylinder_relator_eq_one hN hr))

/-- **Exact literal marked-cylinder package.**  The displayed rank-eight
cylinder is nonempty and clopen, and every one of its points is non-MF. -/
theorem literal_nonempty_clopen_nonMF_cylinder :
    literalCylinder.Nonempty ∧
      IsClopen literalCylinder ∧
      literalCylinder ⊆
        {N : MarkedGroupSpace 8 | ¬ IsOperatorMF N.Quotient} :=
  ⟨literalCylinder_nonempty, literalCylinder_isClopen,
    literalCylinder_subset_nonMF⟩

end
end LiteralMarkedCylinder
end GroupApproximation
