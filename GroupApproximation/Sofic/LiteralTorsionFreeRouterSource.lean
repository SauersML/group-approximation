import GroupApproximation.Sofic.BareDefectSource
import GroupApproximation.Sofic.LiteralBaseP13PropertyTBridge
import GroupApproximation.Monsters.ExplicitLinearModel
import GroupApproximation.Monsters.LiteralBaseCompleteness
import GroupApproximation.Algebra.ProductFinitePresentation
import GroupApproximation.Algebra.HNNFinitePresentation

/-!
# A premise-free torsion-free-router source from the literal Kazhdan base

The literal base is finitely presented and Kazhdan.  Via its proved
equivalence with the explicit affine matrix group, conjugation by `D` gives an
injective proper self-map.  Feeding that map to the affine HNN skeleton gives
the router source with an infinite cyclic protected direction.  This avoids
both the finite-order Clifford lamp and every universal-group/literature input.
-/

namespace GroupApproximation
namespace LiteralTorsionFreeRouterSource

open LiteralNonMFPresentation

noncomputable section

/-- The literal-base compression transported from the affine matrix model. -/
noncomputable def compression : Base →* Base :=
  LiteralBaseCompleteness.baseAffineEquiv.symm.toMonoidHom.comp
    (ExplicitLinearModel.conjD.comp
      LiteralBaseCompleteness.baseAffineEquiv.toMonoidHom)

/-- Transport preserves injectivity of the explicit matrix compression. -/
theorem compression_injective : Function.Injective compression := by
  intro x y hxy
  change
    LiteralBaseCompleteness.baseAffineEquiv.symm
        (ExplicitLinearModel.conjD (LiteralBaseCompleteness.baseAffineEquiv x)) =
      LiteralBaseCompleteness.baseAffineEquiv.symm
        (ExplicitLinearModel.conjD (LiteralBaseCompleteness.baseAffineEquiv y))
    at hxy
  have hconj :
      ExplicitLinearModel.conjD (LiteralBaseCompleteness.baseAffineEquiv x) =
        ExplicitLinearModel.conjD (LiteralBaseCompleteness.baseAffineEquiv y) :=
    LiteralBaseCompleteness.baseAffineEquiv.symm.injective hxy
  exact LiteralBaseCompleteness.baseAffineEquiv.injective
    (ExplicitLinearModel.conjD_injective hconj)

/-- The transported first affine generator is omitted by the compression. -/
noncomputable def omitted : Base :=
  LiteralBaseCompleteness.baseAffineEquiv.symm ExplicitLinearModel.v1G

theorem omitted_not_mem_range : omitted ∉ Set.range compression := by
  rintro ⟨x, hx⟩
  change
    LiteralBaseCompleteness.baseAffineEquiv.symm
        (ExplicitLinearModel.conjD (LiteralBaseCompleteness.baseAffineEquiv x)) =
      LiteralBaseCompleteness.baseAffineEquiv.symm ExplicitLinearModel.v1G
    at hx
  apply ExplicitLinearModel.v1G_not_mem_range
  exact ⟨LiteralBaseCompleteness.baseAffineEquiv x,
    LiteralBaseCompleteness.baseAffineEquiv.symm.injective hx⟩

/-- The affine HNN envelope carrying the infinite protected direction. -/
noncomputable abbrev Envelope : Type :=
  ConcreteCompressionSource.SourceGroup compression compression_injective

/-- The premise-free compression datum before adjoining property `(T)`. -/
noncomputable def compressionSourceData :
    ConcreteCompressionSource.CompressionSourceData Base Envelope :=
  ConcreteCompressionSource.sourceData compression compression_injective
    omitted_not_mem_range

/-- The closed slim source consumed by the torsion-free router. -/
noncomputable def literalBareDefectSourceData :
    BareDefectSourceData Base Envelope :=
  compressionSourceData.toBareDefectSourceData
    LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT

/-- The affine HNN envelope remains finitely presented. -/
theorem envelope_isFinitelyPresented : Group.IsFinitelyPresented Envelope := by
  letI : Group.FG Base := ProductFinitePresentation.fg_of_isFinitelyPresented Base
  exact HNNFinitePresentation.isFinitelyPresented_hnnExtension
    (ConcreteCompressionSource.sourceEquiv compression compression_injective)

end

end LiteralTorsionFreeRouterSource
end GroupApproximation
