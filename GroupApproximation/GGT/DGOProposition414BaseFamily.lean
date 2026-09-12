import GroupApproximation.GGT.DGOProposition414ComponentFamiliesAux

/-!
# Inherited-arc base families for Proposition 4.14

The first and second component-family records used by the balanced gap
construction have four fields.  Their inherited-arc fields are the base
family of the construction: they account for the parent components that
survive in a child cycle.  This module names that strictly smaller interface,
proves its assembly from the two endpoint-exclusion inputs in the DGO
Proposition 4.14 diagram, and provides the trivial empty-cycle test.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- The inherited first-gap component field, separated from chord and
connector components.  This is one field of `FirstGapComponentFamily`. -/
def FirstGapBaseFamily
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) : Prop :=
  ∀ (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ), s ∈ B.firstGapArcSources j →
      IsComp (B.firstGapLocalLabel j
          ((B.firstGapLeft j).length +
            (B.firstTargetSide s - B.firstGapStartSide j)))
        (B.firstGapCycle j)
        (B.firstGapCut j ((B.firstGapLeft j).length +
          (B.firstTargetSide s - B.firstGapStartSide j)))
        (B.firstGapCut j ((B.firstGapLeft j).length +
          (B.firstTargetSide s - B.firstGapStartSide j) + 1))

/-- The inherited wrapped-gap component field, separated from chord and
connector components.  This is one field of `SecondGapComponentFamily`. -/
def SecondGapBaseFamily
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) : Prop :=
  ∀ (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ), s ∈ B.secondGapArcSources j →
      IsComp (B.secondGapLocalLabel j
          ((B.secondGapLeft j).length +
            (B.secondTargetSide s - B.secondGapStartSide j)))
        (B.secondGapCycle j)
        (B.secondGapCut j ((B.secondGapLeft j).length +
          (B.secondTargetSide s - B.secondGapStartSide j)))
        (B.secondGapCut j ((B.secondGapLeft j).length +
          (B.secondTargetSide s - B.secondGapStartSide j) + 1))

/-- The pair of inherited-arc fields is the base family for both balanced
children. -/
def GapBaseFamily
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) : Prop :=
  FirstGapBaseFamily B ∧ SecondGapBaseFamily B

/-- The endpoint exclusions in the DGO diagram produce the first inherited
arc base family.  The cut alignment is supplied by the canonical source
alignment theorem. -/
theorem firstGapBaseFamily_of_boundaryExclusions
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hboundary : ∀ j s, s ∈ B.firstGapArcSources j →
      FirstGapArcBoundaryExclusion B j s) :
    FirstGapBaseFamily B := by
  intro j s hs
  exact firstGapArcSource_fullComponent_of_boundaryExclusion_auto B j s hs
    (hboundary j s hs)

/-- The reflected endpoint exclusions produce the wrapped inherited-arc base
family in the second child. -/
theorem secondGapBaseFamily_of_boundaryExclusions
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hboundary : ∀ j s, s ∈ B.secondGapArcSources j →
      SecondGapArcBoundaryExclusion B j s) :
    SecondGapBaseFamily B := by
  intro j s hs
  exact secondGapArcSource_fullComponent_of_boundaryExclusion_auto B j s hs
    (hboundary j s hs)

/-- Both endpoint-exclusion families assemble into the inherited-arc base
family used by the balanced split. -/
theorem gapBaseFamily_of_boundaryExclusions
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hfirst : ∀ j s, s ∈ B.firstGapArcSources j →
      FirstGapArcBoundaryExclusion B j s)
    (hsecond : ∀ j s, s ∈ B.secondGapArcSources j →
      SecondGapArcBoundaryExclusion B j s) :
    GapBaseFamily B := by
  exact ⟨firstGapBaseFamily_of_boundaryExclusions B hfirst,
    secondGapBaseFamily_of_boundaryExclusions B hsecond⟩

/-- The inherited-arc field is the first projection of a complete first-gap
component family. -/
theorem FirstGapComponentFamily.baseFamily
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (F : FirstGapComponentFamily B) : FirstGapBaseFamily B :=
  F.arcComponent

/-- The wrapped inherited-arc field is the first projection of a complete
second-gap component family. -/
theorem SecondGapComponentFamily.baseFamily
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (F : SecondGapComponentFamily B) : SecondGapBaseFamily B :=
  F.arcComponent

/-! ## Empty-cycle model -/

/-- If both child cycles are empty, the two inherited-arc base families hold
by the empty-cycle endpoint exclusion model. -/
theorem gapBaseFamily_emptyCycleModel
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hfirst : ∀ j, B.firstGapCycle j = [])
    (hsecond : ∀ j, B.secondGapCycle j = []) :
    GapBaseFamily B := by
  apply gapBaseFamily_of_boundaryExclusions B
  · intro j s hs
    exact firstGapArcBoundaryExclusion_emptyModel B j s (hfirst j)
  · intro j s hs
    exact secondGapArcBoundaryExclusion_emptyModel B j s (hsecond j)

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
