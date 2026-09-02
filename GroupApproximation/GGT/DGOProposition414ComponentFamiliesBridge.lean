import GroupApproximation.GGT.DGOProposition414Uniform
import GroupApproximation.GGT.DGOProposition414UniformBridge

/-!
# Component families in the DGO radius interface

The balanced gap reduction gives a linear `SumBound` for a fixed integer
additive parameter.  The radius bridge converts that statement to the
`DGOUniformSumBound` interface used by Lemma 4.21.  This file composes the two
bridges for the smaller component-family and target-separation producer.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- The component-family producer yields the fixed-parameter DGO radius bound
used by the `(1,b)` specialization of Lemma 4.21. -/
theorem exists_dgoUniformSumBound_of_componentFamilies
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (produce : ∀ {n k R : ℕ} (P : SumBoundInput D (b : ℝ) n)
      (B : DGOProposition414.BalancedSplitData D hsymm b hδ P k R),
      Nonempty (DGOProposition414.BalancedSplitData.FirstGapComponentFamily B) ∧
      Nonempty (DGOProposition414.BalancedSplitData.SecondGapComponentFamily B) ∧
      DGOProposition414.BalancedSplitData.FirstGapTargetSeparation B ∧
      DGOProposition414.BalancedSplitData.SecondGapTargetSeparation B) :
    ∃ C : ℕ, 0 < C ∧ DGOUniformSumBound D 1 (b : ℝ) C := by
  apply OsinComponents.exists_dgoUniformSumBound_of_linearSumBound D b
  exact uniformSumBound_of_componentFamilies D hsymm b hδ produce

end DGOProposition414
end GGT
end GroupApproximation
