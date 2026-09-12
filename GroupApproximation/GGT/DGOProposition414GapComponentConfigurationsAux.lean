import GroupApproximation.GGT.DGOProposition414GapComponentAssembly

/-!
# Target-isolation bridge for Proposition 4.14 gap children

This module packages the four full-cycle component and isolation families
needed by the balanced-split gap interval producer.  It records the explicit
geometric frontier after the factor-placement package has landed, using the
component-file constructors from the proof of DGO Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- Four target-component/isolation families assemble into the complete pair
of gap component configurations. -/
theorem exists_gapComponentConfigurations_of_targetIsolated
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (firstTarget : ∀ j, ∀ s ∈ B.firstGapTarget j,
      IsComp (B.firstGapLocalLabel j s) (B.firstGapCycle j)
        (B.firstGapCut j s) (B.firstGapCut j (s + 1)))
    (firstIsolated : ∀ j, ∀ s ∈ B.firstGapTarget j,
      IsIsolated D.fam (B.firstGapLocalLabel j s)
        (vertex B.firstBase B.chord (B.firstGapChordFinish j))
        (B.firstGapCycle j) (B.firstGapCut j s))
    (secondTarget : ∀ j, ∀ s ∈ B.secondGapTarget j,
      IsComp (B.secondGapLocalLabel j s) (B.secondGapCycle j)
        (B.secondGapCut j s) (B.secondGapCut j (s + 1)))
    (secondIsolated : ∀ j, ∀ s ∈ B.secondGapTarget j,
      IsIsolated D.fam (B.secondGapLocalLabel j s)
        (vertex B.firstBase B.chord (B.secondGapChordFinish j))
        (B.secondGapCycle j) (B.secondGapCut j s)) :
    Nonempty (GapComponentConfigurations hsymm hδ P B) := by
  exact ⟨B.gapComponentConfigurations_of_targetIsolated
    firstTarget firstIsolated secondTarget secondIsolated⟩

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
