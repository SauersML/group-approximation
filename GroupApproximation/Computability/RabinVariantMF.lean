import GroupApproximation.Algebra.RabinVariantPresentation
import GroupApproximation.Sofic.OperatorMFPositiveControls
import GroupApproximation.Sofic.FreeGroupResiduallyFinite

/-!
# The MF side of the variant construction

`Algebra.RabinVariantPresentation` proves both halves of the biconditional in
group-theoretic form: the source group embeds in `P(w)` when the witness has
infinite order, and the `tᵢ` and `k` freely generate `P(w)` when the word is
trivial in the source.

This file reads the second of those in the language the reduction needs.  A
free group is residually finite, hence operator-MF
(`Sofic.FreeGroupResiduallyFinite.freeGroup_residuallyFinite` together with
`isOperatorMF_of_residuallyFinite`), and MF pulls back along an injective
homomorphism (`IsOperatorMF.comap`), so `P(w)` is MF whenever the collapse
fires.

This is the step that made the whole variant possible: the collapse only has to
reach a *free* group, never the trivial one, and it is what allowed every
associated subgroup in the tower to be cyclic or exhibited by a retraction.
-/

namespace GroupApproximation
namespace RabinVariantMF

open RabinVariantPresentation

/-- A free group on a countable alphabet is countable: it is a quotient of the
lists of signed letters. -/
instance freeGroupCountable (α : Type) [Countable α] : Countable (FreeGroup α) := by
  refine Function.Surjective.countable
    (f := fun l : List (α × Bool) => FreeGroup.mk l) ?_
  intro x
  obtain ⟨l, rfl⟩ := Quot.exists_rep x
  exact ⟨l, rfl⟩

variable {m : ℕ} (R : Set (FreeGroup (Fin m))) (w : FreeGroup (Fin m))

/-- The isomorphism the collapse produces. -/
noncomputable def collapseEquiv (hw : PresentedGroup.mk R w = 1) :
    FreeGroup (FreeGen m) ≃* Pres R w :=
  MulEquiv.ofBijective _ (pres_free R w hw)

/-- **The collapse side, in MF form.**  If the word is trivial in the source
group then the group the construction presents is operator-MF. -/
theorem pres_isOperatorMF (hw : PresentedGroup.mk R w = 1) :
    IsOperatorMF (Pres R w) :=
  (isOperatorMF_of_residuallyFinite (K := FreeGroup (FreeGen m))).comap
    (collapseEquiv R w hw).symm.toMonoidHom
    (collapseEquiv R w hw).symm.injective

end RabinVariantMF
end GroupApproximation
