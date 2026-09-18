import GroupApproximation.Analysis.PropertyAExtension
import GroupApproximation.Analysis.PropertyATelescope
import GroupApproximation.Analysis.ExactnessGroupSideEndpoint
import GroupApproximation.Sofic.LiteralVerticalBridge
import GroupApproximation.Manuscript.NonMFNotes.Full.Exactness.BlockCliffordPropertyA
import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessGHW.AmenablePropertyA

/-!
# From the base `Σ` to the literal marked group

`non_mf_group_notes.tex`, paragraph `\paragraph{Exactness.}` after
`prop:blocknormalform`: exactness of the literal group `E` is reduced to
exactness of the linear base `Σ = gammaBar ≤ GL₄(ℚ)` (Guentner--Higson--Weinberger)
through permanence steps.  This file performs every permanence step, in the
combinatorial form of exactness used by the repository
(`ExactnessPermanence.HasPropertyA`):

* the vertical group `Vertical α hα = Telescope α hα ⋊ ℤ` has property A as
  soon as its base does (increasing union `PropertyATelescope.hasPropertyA_telescope`,
  extension by the amenable group `ℤ`);
* `LiteralBlockNormalForm.Vertical ≃* LiteralLampKernelSplit.V`
  (`LiteralVerticalBridge.verticalEquiv`);
* `E ≃* C(𝒢) ⋊ Vertical` (`LiteralBlockNormalForm.markedGroupEquivModel`) with
  property A of the Clifford factor `Full.NN09.hasPropertyA_lampFactor`.

The only input left is property A of `gammaBar` itself, which is supplied by
the coarse embedding of `ExactnessGHW` into the solvable group of
upper-triangular matrices.
-/

namespace GroupApproximation.Full.NN09b

open GroupApproximation.ExactnessPermanence

/-- **Exact group**, in Yu's combinatorial form: property A.  For countable
discrete groups this is equivalent to exactness of the reduced group
`C*`-algebra (Ozawa; the crossover is lane NN09c). -/
abbrev IsExactGroup (G : Type*) [Group G] : Prop :=
  HasPropertyA G

/-- **The ascending HNN extension of a group with property A has property A.**
`Vertical α hα = Telescope α hα ⋊ ℤ`: the telescope is an increasing union of
copies of `Γ`, and `ℤ` is amenable. -/
theorem hasPropertyA_vertical_of_base {Γ : Type} [Group Γ] (α : Γ →* Γ)
    (hα : Function.Injective α) (hΓ : HasPropertyA Γ) :
    HasPropertyA (MarkedCompression.Vertical α hα) :=
  hasPropertyA_semidirectProduct (PropertyATelescope.hasPropertyA_telescope α hα hΓ)
    hasPropertyA_multiplicativeInt

/-- The ascending HNN extension `V` of `Σ = gammaBar` along doubling. -/
theorem hasPropertyA_literalV_of_gammaBar
    (hΓ : HasPropertyA ExplicitLinearModel.gammaBar) :
    HasPropertyA LiteralLampKernelSplit.V :=
  hasPropertyA_vertical_of_base LiteralNonMFLinearWitness.alpha
    ExplicitLinearModel.conjD_injective hΓ

/-- The seven-letter vertical quotient `E/⟨⟨c⟩⟩`. -/
theorem hasPropertyA_blockVertical_of_gammaBar
    (hΓ : HasPropertyA ExplicitLinearModel.gammaBar) :
    HasPropertyA LiteralBlockNormalForm.Vertical :=
  HasPropertyA.of_mulEquiv LiteralVerticalBridge.verticalEquiv.symm
    (hasPropertyA_literalV_of_gammaBar hΓ)

/-- The block normal-form model `C(𝒢) ⋊ Vertical`. -/
theorem hasPropertyA_model_of_gammaBar
    (hΓ : HasPropertyA ExplicitLinearModel.gammaBar) :
    HasPropertyA LiteralBlockNormalForm.Model :=
  hasPropertyA_semidirectProduct Full.NN09.hasPropertyA_lampFactor
    (hasPropertyA_blockVertical_of_gammaBar hΓ)

/-- **The literal marked group has property A once `Σ` does.**
`non_mf_group_notes.tex`, `\paragraph{Exactness.}`. -/
theorem hasPropertyA_markedGroup_of_gammaBar
    (hΓ : HasPropertyA ExplicitLinearModel.gammaBar) :
    HasPropertyA LiteralNonMFPresentation.MarkedGroup :=
  HasPropertyA.of_mulEquiv LiteralBlockNormalForm.markedGroupEquivModel.symm
    (hasPropertyA_model_of_gammaBar hΓ)

/-- The literal marked group is exact once `Σ` is. -/
theorem markedGroup_isExactGroup_of_gammaBar
    (hΓ : IsExactGroup ExplicitLinearModel.gammaBar) :
    IsExactGroup LiteralNonMFPresentation.MarkedGroup :=
  hasPropertyA_markedGroup_of_gammaBar hΓ

/-- The marked-compression witness group `ClLamp(Cosets) ⋊ V` has property A
once `Σ` does. -/
theorem hasPropertyA_witnessGroup_of_gammaBar
    (hΓ : HasPropertyA ExplicitLinearModel.gammaBar) :
    HasPropertyA LiteralNonMFLinearWitness.WitnessGroup :=
  ExactnessGroupSideEndpoint.witnessGroup_hasPropertyA_of_vertical
    (hasPropertyA_literalV_of_gammaBar hΓ)

end GroupApproximation.Full.NN09b
