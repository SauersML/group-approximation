import GroupApproximation.Sofic.LiteralAffineCongruenceSource
import GroupApproximation.Higman.CoprodTorsion
import GroupApproximation.Algebra.BassSerreFreeProductAction
import Mathlib.GroupTheory.FinitelyPresentedGroup

/-!
# Unconditional free-product amplification of the affine defect source

The concrete affine congruence HNN envelope already carries a closed bare
defect datum and is torsion-free and finitely presented.  Embed it as the left
factor of its free product with `Multiplicative ℤ`.  Injectivity transports the
entire defect datum, while standard free-product permanence proves the two
ambient finiteness properties.  Both factors are proved nontrivial here.
-/

namespace GroupApproximation.LiteralAffineFreeProductSource

open scoped Monoid.Coprod
open LiteralAffineCongruenceSource

noncomputable section

abbrev Ambient : Type := Monoid.Coprod Envelope (Multiplicative ℤ)

def envelopeEmbedding : Envelope →* Ambient := Monoid.Coprod.inl

theorem envelopeEmbedding_injective : Function.Injective envelopeEmbedding :=
  Monoid.Coprod.inl_injective

/-- The affine bare source transported into the free-product ambient. -/
def amplifiedDefectData : BareDefectSourceData P Ambient :=
  literalBareDefectSourceData.mapAmbient envelopeEmbedding
    envelopeEmbedding_injective

theorem envelope_nontrivial : Nontrivial Envelope := by
  let D := literalBareDefectSourceData
  exact ⟨⟨D.s, 1, D.s_ne_one⟩⟩

theorem cyclic_nontrivial : Nontrivial (Multiplicative ℤ) := inferInstance

theorem ambient_isPowerTorsionFree : IsPowerTorsionFree Ambient :=
  Higman.isPowerTorsionFree_coprod envelope_isPowerTorsionFree
    IsPowerTorsionFree.of_isMulTorsionFree

theorem ambient_isFinitelyPresented : Group.IsFinitelyPresented Ambient := by
  letI : Group.IsFinitelyPresented Envelope := envelope_isFinitelyPresented
  exact inferInstance

/-- The right free factor also embeds nontrivially; this is the second factor
needed by the Bass--Serre free-product geometry. -/
theorem inr_one_ne_one :
    (Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ)) : Ambient) ≠ 1 := by
  intro h
  have h' :
      Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ)) =
        Monoid.Coprod.inr (1 : Multiplicative ℤ) := by
    simpa using h
  have := Monoid.Coprod.inr_injective h'
  norm_num at this

/-! ## Adapter to the generic Bass--Serre geometry -/

abbrev BassSerreVertex := BassSerreFreeProduct.Vertex Envelope

def bassSerreBaseEdge : BassSerreVertex × BassSerreVertex :=
  BassSerreFreeProduct.baseEdge Envelope

/-- The generic free-product action applies definitionally to the amplified
ambient.  Its base edge has trivial pointwise stabilizer. -/
theorem bassSerreBaseEdge_pointwiseStabilizer_eq_bot :
    MulAction.stabilizer Ambient bassSerreBaseEdge = ⊥ :=
  BassSerreFreeProduct.baseEdge_pointwiseStabilizer_eq_bot Envelope

/-- The unconditional amplified source-stage deliverable. -/
theorem amplifiedDefectData_package :
    IsPowerTorsionFree Ambient ∧
      Group.IsFinitelyPresented Ambient ∧
      Nonempty (BareDefectSourceData P Ambient) :=
  ⟨ambient_isPowerTorsionFree, ambient_isFinitelyPresented,
    ⟨amplifiedDefectData⟩⟩

end

end GroupApproximation.LiteralAffineFreeProductSource
