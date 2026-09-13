import GroupApproximation.Sofic.StrongConvergenceMF
import GroupApproximation.Meta.AxiomGuard

/-!
# The strong-convergence convention is inhabited

`non_mf_groups_exist.tex`, Introduction, tex lines 102-105:

> The strong convergence convention of~\cite{GaoEtAl,Schafhauser} also requires
> the models to reproduce the operator norms of the left regular representation,
> so a group that is not MF as defined here is not MF in that convention either.

`Sofic/StrongConvergenceMF` carries the sentence: `IsStronglyOperatorMF` is the
convention, `IsStronglyOperatorMF.isOperatorMF` is "also requires", and
`not_isStronglyOperatorMF_of_not_isOperatorMF` is the printed contrapositive.
This module shows that the convention is not vacuous: a trivial group is strongly
MF, with the one-point model and constant identity matrices, because in both
algebras `∑ c_g · 1 = (∑ c_g) · 1` has norm `|∑ c_g|`.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u

namespace StrongConvergencePoint

/-- The one-point finite model. -/
def pointModel : FiniteModel where
  carrier := Unit
  fintype := inferInstance
  decidableEq := inferInstance

instance pointModel_nonempty : Nonempty pointModel := ⟨()⟩

end StrongConvergencePoint

open StrongConvergencePoint

/-- **A trivial group is strongly MF.**  The models are the one-point model with
every group element sent to the identity matrix; the corona homomorphism is
trivial, which is injective on a subsingleton, and both sides of the norm
condition equal `|∑ c_g|`. -/
theorem isStronglyOperatorMF_of_subsingleton (G : Type u) [Group G] [Subsingleton G] :
    IsStronglyOperatorMF G := by
  refine ⟨fun _ ↦ pointModel, fun _ ↦ Fintype.card_pos_iff.mpr ⟨()⟩, fun _ _ ↦ 1,
    ⟨1, fun a b _ ↦ Subsingleton.elim a b, fun _ ↦ rfl⟩, fun c ↦ ?_⟩
  have hreg : ∀ g ∈ c.support, c g • reducedLeftRegular G g = c g • 1 := fun g _ ↦ by
    rw [Subsingleton.elim g 1, reducedLeftRegular_one]
  refine tendsto_const_nhds.congr fun n ↦ ?_
  show leftRegularNorm c = ‖∑ g ∈ c.support,
    c g • ((1 : Matrix.unitaryGroup pointModel ℂ) : Matrix pointModel pointModel ℂ)‖
  rw [leftRegularNorm, Finset.sum_congr rfl hreg, Matrix.unitaryGroup.one_val,
    ← Finset.sum_smul, ← Finset.sum_smul, norm_smul, norm_smul, CStarRing.norm_one,
    CStarRing.norm_one]

/-- **The trivial group is strongly MF.** -/
theorem isStronglyOperatorMF_unit : IsStronglyOperatorMF Unit :=
  isStronglyOperatorMF_of_subsingleton Unit

end GroupApproximation

open GroupApproximation

#audit_axioms isStronglyOperatorMF_of_subsingleton
#audit_closed_axioms isStronglyOperatorMF_unit
