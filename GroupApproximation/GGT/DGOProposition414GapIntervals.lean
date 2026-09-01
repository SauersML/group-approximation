import GroupApproximation.GGT.DGOProposition414GapConnectorComponents
import GroupApproximation.GGT.DGOProposition414SubarcInterval

/-!
# Canonical auxiliary intervals of a balanced split

This file assembles the endpoint, cut, target, label, and connector data of
Dahmani--Guirardel--Osin Proposition 4.14 into the two families of auxiliary
intervals.  The remaining geometric inputs are stated at their exact scope:
off-target quasigeodesicity of each open parent arc and a complete component
configuration for each auxiliary cycle.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- Every canonical first-gap left connector is an admissible relative
letter word. -/
theorem firstGapLeft_letters
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    ∀ x ∈ B.firstGapLeft j, D.IsLetter x := by
  classical
  intro x hx
  cases hprev : HalfGap.previousEntry B.brokenAssignment.index.first j with
  | none =>
      simp [firstGapLeft, hprev] at hx
  | some e =>
      let s := HalfEntry.entrySource B.brokenAssignment.index.first e
      have hs := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
      let C := B.firstBrokenConnectors s hs
      by_cases hforward : B.firstGapRunsForward j
      · have hx' : x ∈ C.endConnector := by
          simpa only [firstGapLeft, hprev, hforward, ↓reduceIte] using hx
        exact C.end_letters x hx'
      · have hx' : x ∈ C.endThroughPartner := by
          simpa only [firstGapLeft, hprev, hforward, ↓reduceIte] using hx
        exact C.endThroughPartner_letters x hx'

/-- Every canonical first-gap right connector is an admissible relative
letter word. -/
theorem firstGapRight_letters
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    ∀ x ∈ B.firstGapRight j, D.IsLetter x := by
  classical
  intro x hx
  cases hnext : HalfGap.nextEntry B.brokenAssignment.index.first j with
  | none =>
      simp [firstGapRight, hnext] at hx
  | some e =>
      let s := HalfEntry.entrySource B.brokenAssignment.index.first e
      have hs := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
      let C := B.firstBrokenConnectors s hs
      by_cases hforward : B.firstGapRunsForward j
      · have hx' : x ∈ C.startConnector := by
          simpa only [firstGapRight, hnext, hforward, ↓reduceIte] using hx
        exact C.start_letters x hx'
      · have hx' : x ∈ C.startThroughPartner := by
          simpa only [firstGapRight, hnext, hforward, ↓reduceIte] using hx
        exact C.startThroughPartner_letters x hx'

/-- Every canonical wrapped-gap left connector is an admissible relative
letter word. -/
theorem secondGapLeft_letters
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    ∀ x ∈ B.secondGapLeft j, D.IsLetter x := by
  classical
  intro x hx
  cases hprev : HalfGap.previousEntry B.brokenAssignment.index.second j with
  | none =>
      simp [secondGapLeft, hprev] at hx
  | some e =>
      let s := HalfEntry.entrySource B.brokenAssignment.index.second e
      have hs := HalfEntry.entrySource_mem B.brokenAssignment.index.second e
      let C := B.secondBrokenConnectors s hs
      by_cases hforward : B.secondGapRunsForward j
      · have hx' : x ∈ C.endThroughPartner := by
          simpa only [secondGapLeft, hprev, hforward, ↓reduceIte] using hx
        exact C.endThroughPartner_letters x hx'
      · have hx' : x ∈ C.endConnector := by
          simpa only [secondGapLeft, hprev, hforward, ↓reduceIte] using hx
        exact C.end_letters x hx'

/-- Every canonical wrapped-gap right connector is an admissible relative
letter word. -/
theorem secondGapRight_letters
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    ∀ x ∈ B.secondGapRight j, D.IsLetter x := by
  classical
  intro x hx
  cases hnext : HalfGap.nextEntry B.brokenAssignment.index.second j with
  | none =>
      simp [secondGapRight, hnext] at hx
  | some e =>
      let s := HalfEntry.entrySource B.brokenAssignment.index.second e
      have hs := HalfEntry.entrySource_mem B.brokenAssignment.index.second e
      let C := B.secondBrokenConnectors s hs
      by_cases hforward : B.secondGapRunsForward j
      · have hx' : x ∈ C.startThroughPartner := by
          simpa only [secondGapRight, hnext, hforward, ↓reduceIte] using hx
        exact C.startThroughPartner_letters x hx'
      · have hx' : x ∈ C.startConnector := by
          simpa only [secondGapRight, hnext, hforward, ↓reduceIte] using hx
        exact C.start_letters x hx'

/-- Assemble one first-half gap into its raw auxiliary interval. -/
noncomputable def firstGapInterval
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (parentQuasi : ∀ s : ℕ, s < B.secondSide - B.firstSide + 1 →
      s ∉ B.firstArcTargetSides → ∀ p q : ℕ,
      B.firstArcCut s ≤ p → p ≤ q → q ≤ B.firstArcCut (s + 1) →
      ((q - p : ℕ) : ℝ) - b ≤
        ((wordDist D.alphabet.carrier
          (vertex B.firstBase B.firstArc p)
          (vertex B.firstBase B.firstArc q) : ℕ) : ℝ))
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (C : AuxiliaryCycleComponentConfiguration D
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
      (B.firstGapLocalLabel j)) :
    AuxiliaryIntervalOnChord D hsymm b B.firstBase
      (vertex P.basepoint P.word B.secondVertex) B.chord B.chord_geodesic :=
  auxiliaryIntervalOnChord_of_subarc D hsymm b B.firstArc_isCutPath
    B.firstArcTargetSides parentQuasi
    (B.firstGapStartSide j) (B.firstGapFinishSide j)
    (B.firstGap_side_order j) (B.firstGapFinishSide_le j)
    B.firstBase (vertex P.basepoint P.word B.secondVertex)
    B.chord B.chord_geodesic
    (B.firstGapChordStart j) (B.firstGapChordFinish j)
    (B.firstGapChordStart_le j) (B.firstGapChordFinish_le j)
    (B.firstGapLeft j) (B.firstGapRight j)
    (B.firstGapLeft_letters j) (B.firstGapRight_letters j)
    (B.firstGap_arcBase j) (B.firstGap_prefix_endpoint j)
    (B.firstGapLocalTarget j) (B.firstGapLocalLabel j)
    (B.firstGap_target_reflect j) (B.firstGapLocalTarget_lt j)
    (B.firstGapLocalTarget_edge j) C.targetComponent C.targetIsolated

/-- Assemble one wrapped-half gap into its raw auxiliary interval. -/
noncomputable def secondGapInterval
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (parentQuasi : ∀ s : ℕ,
      s < (n - B.secondSide) + B.firstSide + 1 →
      s ∉ B.secondArcTargetSides → ∀ p q : ℕ,
      B.secondArcCut s ≤ p → p ≤ q → q ≤ B.secondArcCut (s + 1) →
      ((q - p : ℕ) : ℝ) - b ≤
        ((wordDist D.alphabet.carrier
          (vertex B.secondBase B.secondArc p)
          (vertex B.secondBase B.secondArc q) : ℕ) : ℝ))
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (C : AuxiliaryCycleComponentConfiguration D
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
      (B.secondGapLocalLabel j)) :
    AuxiliaryIntervalOnChord D hsymm b B.firstBase
      (vertex P.basepoint P.word B.secondVertex) B.chord B.chord_geodesic := by
  apply auxiliaryIntervalOnChord_of_subarc D hsymm b B.secondArc_isCutPath
    B.secondArcTargetSides parentQuasi
    (B.secondGapStartSide j) (B.secondGapFinishSide j)
    (B.secondGap_side_order j) (B.secondGapFinishSide_le j)
    B.firstBase (vertex P.basepoint P.word B.secondVertex)
    B.chord B.chord_geodesic
    (B.secondGapChordStart j) (B.secondGapChordFinish j)
    (B.secondGapChordStart_le j) (B.secondGapChordFinish_le j)
    (B.secondGapLeft j) (B.secondGapRight j)
    (B.secondGapLeft_letters j) (B.secondGapRight_letters j)
    (B.secondGap_arcBase j) (B.secondGap_prefix_endpoint j)
    (B.secondGapLocalTarget j) (B.secondGapLocalLabel j)
    (B.secondGap_target_reflect j) (B.secondGapLocalTarget_lt j)
    (B.secondGapLocalTarget_edge j) C.targetComponent C.targetIsolated

/-- The two canonical gap families give the interval field of balanced
surgery once every child has its component configuration. -/
noncomputable def gapIntervals
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (firstQuasi : ∀ s : ℕ, s < B.secondSide - B.firstSide + 1 →
      s ∉ B.firstArcTargetSides → ∀ p q : ℕ,
      B.firstArcCut s ≤ p → p ≤ q → q ≤ B.firstArcCut (s + 1) →
      ((q - p : ℕ) : ℝ) - b ≤
        ((wordDist D.alphabet.carrier
          (vertex B.firstBase B.firstArc p)
          (vertex B.firstBase B.firstArc q) : ℕ) : ℝ))
    (secondQuasi : ∀ s : ℕ,
      s < (n - B.secondSide) + B.firstSide + 1 →
      s ∉ B.secondArcTargetSides → ∀ p q : ℕ,
      B.secondArcCut s ≤ p → p ≤ q → q ≤ B.secondArcCut (s + 1) →
      ((q - p : ℕ) : ℝ) - b ≤
        ((wordDist D.alphabet.carrier
          (vertex B.secondBase B.secondArc p)
          (vertex B.secondBase B.secondArc q) : ℕ) : ℝ))
    (firstComponents : ∀
      j : Fin B.brokenAssignment.index.first.pieceCount,
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
        (B.firstGapLocalLabel j))
    (secondComponents : ∀
      j : Fin B.brokenAssignment.index.second.pieceCount,
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
        (B.secondGapLocalLabel j)) :
    TwoHalfIntervalSurgery D hsymm b B.brokenAssignment.index B.firstBase
      (vertex P.basepoint P.word B.secondVertex) B.chord B.chord_geodesic where
  first := fun j => B.firstGapInterval firstQuasi j (firstComponents j)
  second := fun j => B.secondGapInterval secondQuasi j (secondComponents j)

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
