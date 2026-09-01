import GroupApproximation.GGT.DGOProposition414ArcQuasi
import GroupApproximation.GGT.DGOProposition414GapSideBounds

/-!
# Producing the balanced family of gap intervals

The inherited-arc quasigeodesic premises and the per-child side bounds are now
internal consequences of a balanced split.  A caller supplies only the full
component and isolation configuration of each auxiliary child cycle.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- Complete component geometry for a first-half gap child. -/
abbrev FirstGapComponentConfiguration
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :=
  AuxiliaryCycleComponentConfiguration D
    (vertex B.firstBase B.chord (B.firstGapChordFinish j))
    (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut
      (B.firstGapStartSide j) (B.firstGapFinishSide j))
    (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j))
    (B.firstGapFinishSide j - B.firstGapStartSide j)
    (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
      B.firstArcCut (B.firstGapStartSide j))
    (B.firstGapLocalTarget j ∪ auxiliaryCycleConnectorTarget
      (B.firstGapLeft j) (B.firstGapRight j)
      (B.firstGapFinishSide j - B.firstGapStartSide j))
    (B.firstGapLocalLabel j)

/-- Complete component geometry for a wrapped-half gap child. -/
abbrev SecondGapComponentConfiguration
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :=
  AuxiliaryCycleComponentConfiguration D
    (vertex B.firstBase B.chord (B.secondGapChordFinish j))
    (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut
      (B.secondGapStartSide j) (B.secondGapFinishSide j))
    (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j))
    (B.secondGapFinishSide j - B.secondGapStartSide j)
    (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
      B.secondArcCut (B.secondGapStartSide j))
    (B.secondGapLocalTarget j ∪ auxiliaryCycleConnectorTarget
      (B.secondGapLeft j) (B.secondGapRight j)
      (B.secondGapFinishSide j - B.secondGapStartSide j))
    (B.secondGapLocalLabel j)

/-- The exact remaining geometric input for the interval field of balanced
surgery. -/
structure GapComponentConfigurations
    {D : RelGenSet G Λ} (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {δ b n k R : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (P : SumBoundInput D (b : ℝ) n)
    (B : BalancedSplitData D hsymm b hδ P k R) where
  first : ∀ j, B.FirstGapComponentConfiguration j
  second : ∀ j, B.SecondGapComponentConfiguration j

/-- Produce both canonical interval families from complete child component
geometry. -/
noncomputable def gapIntervalsOfConfigurations
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B) :
    TwoHalfIntervalSurgery D hsymm b B.brokenAssignment.index B.firstBase
      (vertex P.basepoint P.word B.secondVertex) B.chord B.chord_geodesic :=
  B.gapIntervals B.firstArc_quasi B.secondArc_quasi C.first C.second

/-- Every produced first child has the canonical first-gap shape. -/
theorem gapIntervalsOfConfigurations_first_shape
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    let S := (B.gapIntervalsOfConfigurations C).first j
    S.left = B.firstGapLeft j ∧
      S.arcSides = B.firstGapFinishSide j - B.firstGapStartSide j ∧
      S.right = B.firstGapRight j ∧
      S.chordStart = B.firstGapChordStart j ∧
      S.chordFinish = B.firstGapChordFinish j := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Every produced wrapped child has the canonical complementary-gap shape. -/
theorem gapIntervalsOfConfigurations_second_shape
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    let S := (B.gapIntervalsOfConfigurations C).second j
    S.left = B.secondGapLeft j ∧
      S.arcSides = B.secondGapFinishSide j - B.secondGapStartSide j ∧
      S.right = B.secondGapRight j ∧
      S.chordStart = B.secondGapChordStart j ∧
      S.chordFinish = B.secondGapChordFinish j := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The produced first children satisfy the first per-child side bound of
balanced interval surgery. -/
theorem gapIntervalsOfConfigurations_first_side_bound
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    (((B.gapIntervalsOfConfigurations C).toPathInput).first j).sideCount ≤
      (B.secondSide - B.firstSide + 1) + B.chord.length := by
  let S := (B.gapIntervalsOfConfigurations C).first j
  have hshape := B.gapIntervalsOfConfigurations_first_shape C j
  exact B.firstGap_interval_side_bound j S hshape.1 hshape.2.1
    hshape.2.2.1 hshape.2.2.2.1 hshape.2.2.2.2

/-- The produced wrapped children satisfy the second per-child side bound of
balanced interval surgery. -/
theorem gapIntervalsOfConfigurations_second_side_bound
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    (((B.gapIntervalsOfConfigurations C).toPathInput).second j).sideCount ≤
      (n - B.secondSide) + B.firstSide + 1 + B.chord.length := by
  let S := (B.gapIntervalsOfConfigurations C).second j
  have hshape := B.gapIntervalsOfConfigurations_second_shape C j
  exact B.secondGap_interval_side_bound j S hshape.1 hshape.2.1
    hshape.2.2.1 hshape.2.2.2.1 hshape.2.2.2.2

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
