import GroupApproximation.GGT.DGOProposition414EntrySides
import GroupApproximation.GGT.DGOProposition414EntryOwner

/-!
# Canonical adjacent data of every greedy gap child

There is one child before the first broken source, one between consecutive
sources, and one after the last.  This file names the preceding and following
entries of every child and, without any supplied placement data, assigns its
inherited side interval, connector words, and oriented chord endpoints.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace HalfGap

/-- The broken source immediately before a gap child, when it exists. -/
def previousEntry
    {I : Finset ℕ} {pos partner : ℕ → ℕ} {L : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner L) (j : Fin A.pieceCount) :
    Option (Fin A.sources.length) :=
  if h : 0 < j.val then
    some ⟨j.val - 1, by
      have hj := j.isLt
      simp only [GreedyHalfFamilyIndex.pieceCount] at hj
      omega⟩
  else none

/-- The broken source immediately after a gap child, when it exists. -/
def nextEntry
    {I : Finset ℕ} {pos partner : ℕ → ℕ} {L : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner L) (j : Fin A.pieceCount) :
    Option (Fin A.sources.length) :=
  if h : j.val < A.sources.length then some ⟨j.val, h⟩ else none

theorem previousEntry_eq_none_iff
    {I : Finset ℕ} {pos partner : ℕ → ℕ} {L : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner L) (j : Fin A.pieceCount) :
    previousEntry A j = none ↔ j.val = 0 := by
  simp [previousEntry]

theorem nextEntry_eq_none_iff
    {I : Finset ℕ} {pos partner : ℕ → ℕ} {L : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner L) (j : Fin A.pieceCount) :
    nextEntry A j = none ↔ j.val = A.sources.length := by
  have hj := j.isLt
  simp only [GreedyHalfFamilyIndex.pieceCount] at hj
  simp [nextEntry]
  omega

end HalfGap

namespace BalancedSplitData

/-- First inherited side of a first-half gap. -/
noncomputable def firstGapStartSide
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) : ℕ :=
  match HalfGap.previousEntry B.brokenAssignment.index.first j with
  | none => 0
  | some e => B.firstTargetSide
      (HalfEntry.entrySource B.brokenAssignment.index.first e) + 1

/-- Last inherited side of a first-half gap. -/
noncomputable def firstGapFinishSide
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) : ℕ :=
  match HalfGap.nextEntry B.brokenAssignment.index.first j with
  | none => B.secondSide - B.firstSide + 1
  | some e => B.firstTargetSide
      (HalfEntry.entrySource B.brokenAssignment.index.first e)

/-- Left connector of a first-half gap. -/
noncomputable def firstGapLeft
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    List (RelLetter G Λ) :=
  match _h : HalfGap.previousEntry B.brokenAssignment.index.first j with
  | none => []
  | some e =>
      (B.firstBrokenConnectors
        (HalfEntry.entrySource B.brokenAssignment.index.first e)
        (HalfEntry.entrySource_mem B.brokenAssignment.index.first e)).endConnector

/-- Right connector of a first-half gap. -/
noncomputable def firstGapRight
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    List (RelLetter G Λ) :=
  match _h : HalfGap.nextEntry B.brokenAssignment.index.first j with
  | none => []
  | some e =>
      (B.firstBrokenConnectors
        (HalfEntry.entrySource B.brokenAssignment.index.first e)
        (HalfEntry.entrySource_mem B.brokenAssignment.index.first e)).startConnector

/-- Chord vertex at which a first-half gap begins before reading its reversed
left connector. -/
noncomputable def firstGapChordFinish
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) : ℕ :=
  match HalfGap.previousEntry B.brokenAssignment.index.first j with
  | none => 0
  | some e => B.brokenAssignment.first.partner
      (HalfEntry.entrySource B.brokenAssignment.index.first e)

/-- Chord vertex reached after the right connector of a first-half gap. -/
noncomputable def firstGapChordStart
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) : ℕ :=
  match HalfGap.nextEntry B.brokenAssignment.index.first j with
  | none => B.chord.length
  | some e => B.brokenAssignment.first.partner
      (HalfEntry.entrySource B.brokenAssignment.index.first e) + 1

/-- First inherited side of a wrapped-half gap. -/
noncomputable def secondGapStartSide
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) : ℕ :=
  match HalfGap.previousEntry B.brokenAssignment.index.second j with
  | none => 0
  | some e => B.secondTargetSide
      (HalfEntry.entrySource B.brokenAssignment.index.second e) + 1

/-- Last inherited side of a wrapped-half gap. -/
noncomputable def secondGapFinishSide
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) : ℕ :=
  match HalfGap.nextEntry B.brokenAssignment.index.second j with
  | none => (n - B.secondSide) + B.firstSide + 1
  | some e => B.secondTargetSide
      (HalfEntry.entrySource B.brokenAssignment.index.second e)

/-- Left connector of a wrapped-half gap. -/
noncomputable def secondGapLeft
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    List (RelLetter G Λ) :=
  match HalfGap.previousEntry B.brokenAssignment.index.second j with
  | none => []
  | some e =>
      (B.secondBrokenConnectors
        (HalfEntry.entrySource B.brokenAssignment.index.second e)
        (HalfEntry.entrySource_mem B.brokenAssignment.index.second e)).endConnector

/-- Right connector of a wrapped-half gap. -/
noncomputable def secondGapRight
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    List (RelLetter G Λ) :=
  match HalfGap.nextEntry B.brokenAssignment.index.second j with
  | none => []
  | some e =>
      (B.secondBrokenConnectors
        (HalfEntry.entrySource B.brokenAssignment.index.second e)
        (HalfEntry.entrySource_mem B.brokenAssignment.index.second e)).startConnector

/-- Wrapped gaps begin at the terminal vertex `y+1` of the preceding forward
chord component, or at the terminal chord endpoint for the initial gap. -/
noncomputable def secondGapChordFinish
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) : ℕ :=
  match HalfGap.previousEntry B.brokenAssignment.index.second j with
  | none => B.chord.length
  | some e => B.brokenAssignment.second.partner
      (HalfEntry.entrySource B.brokenAssignment.index.second e) + 1

/-- Wrapped gaps reach the initial vertex `y` of the following forward chord
component, or the initial chord endpoint for the terminal gap. -/
noncomputable def secondGapChordStart
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) : ℕ :=
  match HalfGap.nextEntry B.brokenAssignment.index.second j with
  | none => 0
  | some e => B.brokenAssignment.second.partner
      (HalfEntry.entrySource B.brokenAssignment.index.second e)

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
