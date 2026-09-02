import GroupApproximation.GGT.DGOProposition414GapConnectorTargetComponents
import GroupApproximation.GGT.DGOProposition414GapComponentAssembly

/-!
# Classwise assembly of complete gap component files

The target of one auxiliary cycle is the disjoint union of inherited-arc
targets, opposite-chord targets, and the two connector ranges.  This module
proves the finite-set transport which turns component and isolation proofs for
those four classes into the full-cycle target and isolation hypotheses used by
`AuxiliaryCycleComponentConfiguration.ofTargetIsolated`.  The classwise
hypotheses are exactly the four path cases in the bisection step of
Dahmani--Guirardel--Osin Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- Classwise component and isolation data for every first-half gap child.
The arc and chord fields are indexed by their source sets; the connector fields
are indexed by literal connector positions. -/
structure FirstGapTargetCertificate
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) where
  arcComponent : ∀ (j : Fin B.brokenAssignment.index.first.pieceCount)
      (s : ℕ), s ∈ B.firstGapArcSources j →
      IsComp (B.firstGapLocalLabel j
          ((B.firstGapLeft j).length +
            (B.firstTargetSide s - B.firstGapStartSide j)))
        (B.firstGapCycle j)
        (B.firstGapCut j ((B.firstGapLeft j).length +
          (B.firstTargetSide s - B.firstGapStartSide j)))
        (B.firstGapCut j ((B.firstGapLeft j).length +
          (B.firstTargetSide s - B.firstGapStartSide j) + 1))
  arcIsolated : ∀ (j : Fin B.brokenAssignment.index.first.pieceCount)
      (s : ℕ), s ∈ B.firstGapArcSources j →
      IsIsolated D.fam (B.firstGapLocalLabel j
          ((B.firstGapLeft j).length +
            (B.firstTargetSide s - B.firstGapStartSide j)))
        (vertex B.firstBase B.chord (B.firstGapChordFinish j))
        (B.firstGapCycle j)
        (B.firstGapCut j ((B.firstGapLeft j).length +
          (B.firstTargetSide s - B.firstGapStartSide j)))
  chordComponent : ∀ (j : Fin B.brokenAssignment.index.first.pieceCount)
      (s : ℕ), s ∈ B.firstGapChordSources j →
      IsComp (B.firstGapLocalLabel j
          (B.firstGapChordTargetIndex j
            (B.brokenAssignment.second.partner s)))
        (B.firstGapCycle j)
        (B.firstGapCut j (B.firstGapChordTargetIndex j
          (B.brokenAssignment.second.partner s)))
        (B.firstGapCut j (B.firstGapChordTargetIndex j
          (B.brokenAssignment.second.partner s) + 1))
  chordIsolated : ∀ (j : Fin B.brokenAssignment.index.first.pieceCount)
      (s : ℕ), s ∈ B.firstGapChordSources j →
      IsIsolated D.fam (B.firstGapLocalLabel j
          (B.firstGapChordTargetIndex j
            (B.brokenAssignment.second.partner s)))
        (vertex B.firstBase B.chord (B.firstGapChordFinish j))
        (B.firstGapCycle j)
        (B.firstGapCut j (B.firstGapChordTargetIndex j
          (B.brokenAssignment.second.partner s)))
  leftComponent : ∀ (j : Fin B.brokenAssignment.index.first.pieceCount)
      (r : ℕ), r < (B.firstGapLeft j).length →
      IsComp (B.firstGapLocalLabel j r) (B.firstGapCycle j)
        (B.firstGapCut j r) (B.firstGapCut j (r + 1))
  leftIsolated : ∀ (j : Fin B.brokenAssignment.index.first.pieceCount)
      (r : ℕ), r < (B.firstGapLeft j).length →
      IsIsolated D.fam (B.firstGapLocalLabel j r)
        (vertex B.firstBase B.chord (B.firstGapChordFinish j))
        (B.firstGapCycle j) (B.firstGapCut j r)
  rightComponent : ∀ (j : Fin B.brokenAssignment.index.first.pieceCount)
      (r : ℕ), r < (B.firstGapRight j).length →
      IsComp (B.firstGapLocalLabel j
          ((B.firstGapLeft j).length +
            (B.firstGapFinishSide j - B.firstGapStartSide j) + r))
        (B.firstGapCycle j)
        (B.firstGapCut j ((B.firstGapLeft j).length +
          (B.firstGapFinishSide j - B.firstGapStartSide j) + r))
        (B.firstGapCut j ((B.firstGapLeft j).length +
          (B.firstGapFinishSide j - B.firstGapStartSide j) + r + 1))
  rightIsolated : ∀ (j : Fin B.brokenAssignment.index.first.pieceCount)
      (r : ℕ), r < (B.firstGapRight j).length →
      IsIsolated D.fam (B.firstGapLocalLabel j
          ((B.firstGapLeft j).length +
            (B.firstGapFinishSide j - B.firstGapStartSide j) + r))
        (vertex B.firstBase B.chord (B.firstGapChordFinish j))
        (B.firstGapCycle j) (B.firstGapCut j ((B.firstGapLeft j).length +
          (B.firstGapFinishSide j - B.firstGapStartSide j) + r))

/-- Classwise component and isolation data for every wrapped-half gap child. -/
structure SecondGapTargetCertificate
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) where
  arcComponent : ∀ (j : Fin B.brokenAssignment.index.second.pieceCount)
      (s : ℕ), s ∈ B.secondGapArcSources j →
      IsComp (B.secondGapLocalLabel j
          ((B.secondGapLeft j).length +
            (B.secondTargetSide s - B.secondGapStartSide j)))
        (B.secondGapCycle j)
        (B.secondGapCut j ((B.secondGapLeft j).length +
          (B.secondTargetSide s - B.secondGapStartSide j)))
        (B.secondGapCut j ((B.secondGapLeft j).length +
          (B.secondTargetSide s - B.secondGapStartSide j) + 1))
  arcIsolated : ∀ (j : Fin B.brokenAssignment.index.second.pieceCount)
      (s : ℕ), s ∈ B.secondGapArcSources j →
      IsIsolated D.fam (B.secondGapLocalLabel j
          ((B.secondGapLeft j).length +
            (B.secondTargetSide s - B.secondGapStartSide j)))
        (vertex B.firstBase B.chord (B.secondGapChordFinish j))
        (B.secondGapCycle j)
        (B.secondGapCut j ((B.secondGapLeft j).length +
          (B.secondTargetSide s - B.secondGapStartSide j)))
  chordComponent : ∀ (j : Fin B.brokenAssignment.index.second.pieceCount)
      (s : ℕ), s ∈ B.secondGapChordSources j →
      IsComp (B.secondGapLocalLabel j
          (B.secondGapChordTargetIndex j
            (B.brokenAssignment.first.partner s)))
        (B.secondGapCycle j)
        (B.secondGapCut j (B.secondGapChordTargetIndex j
          (B.brokenAssignment.first.partner s)))
        (B.secondGapCut j (B.secondGapChordTargetIndex j
          (B.brokenAssignment.first.partner s) + 1))
  chordIsolated : ∀ (j : Fin B.brokenAssignment.index.second.pieceCount)
      (s : ℕ), s ∈ B.secondGapChordSources j →
      IsIsolated D.fam (B.secondGapLocalLabel j
          (B.secondGapChordTargetIndex j
            (B.brokenAssignment.first.partner s)))
        (vertex B.firstBase B.chord (B.secondGapChordFinish j))
        (B.secondGapCycle j)
        (B.secondGapCut j (B.secondGapChordTargetIndex j
          (B.brokenAssignment.first.partner s)))
  leftComponent : ∀ (j : Fin B.brokenAssignment.index.second.pieceCount)
      (r : ℕ), r < (B.secondGapLeft j).length →
      IsComp (B.secondGapLocalLabel j r) (B.secondGapCycle j)
        (B.secondGapCut j r) (B.secondGapCut j (r + 1))
  leftIsolated : ∀ (j : Fin B.brokenAssignment.index.second.pieceCount)
      (r : ℕ), r < (B.secondGapLeft j).length →
      IsIsolated D.fam (B.secondGapLocalLabel j r)
        (vertex B.firstBase B.chord (B.secondGapChordFinish j))
        (B.secondGapCycle j) (B.secondGapCut j r)
  rightComponent : ∀ (j : Fin B.brokenAssignment.index.second.pieceCount)
      (r : ℕ), r < (B.secondGapRight j).length →
      IsComp (B.secondGapLocalLabel j
          ((B.secondGapLeft j).length +
            (B.secondGapFinishSide j - B.secondGapStartSide j) + r))
        (B.secondGapCycle j)
        (B.secondGapCut j ((B.secondGapLeft j).length +
          (B.secondGapFinishSide j - B.secondGapStartSide j) + r))
        (B.secondGapCut j ((B.secondGapLeft j).length +
          (B.secondGapFinishSide j - B.secondGapStartSide j) + r + 1))
  rightIsolated : ∀ (j : Fin B.brokenAssignment.index.second.pieceCount)
      (r : ℕ), r < (B.secondGapRight j).length →
      IsIsolated D.fam (B.secondGapLocalLabel j
          ((B.secondGapLeft j).length +
            (B.secondGapFinishSide j - B.secondGapStartSide j) + r))
        (vertex B.firstBase B.chord (B.secondGapChordFinish j))
        (B.secondGapCycle j) (B.secondGapCut j ((B.secondGapLeft j).length +
          (B.secondGapFinishSide j - B.secondGapStartSide j) + r))

private theorem firstGap_targetComponent_of_certificate
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (H : FirstGapTargetCertificate B)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    ∀ s ∈ B.firstGapTarget j,
      IsComp (B.firstGapLocalLabel j s) (B.firstGapCycle j)
        (B.firstGapCut j s) (B.firstGapCut j (s + 1)) := by
  intro s hs
  change s ∈ B.firstGapLocalTarget j ∪
    auxiliaryCycleConnectorTarget (B.firstGapLeft j) (B.firstGapRight j)
      (B.firstGapFinishSide j - B.firstGapStartSide j) at hs
  rcases Finset.mem_union.mp hs with hsLocal | hsConnector
  · rcases Finset.mem_union.mp hsLocal with hsArc | hsChord
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hsArc
      exact H.arcComponent j t ht
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hsChord
      exact H.chordComponent j t ht
  · rcases Finset.mem_union.mp hsConnector with hsLeft | hsRight
    · exact H.leftComponent j _ (Finset.mem_range.mp hsLeft)
    · obtain ⟨r, hr, hindex⟩ := Finset.mem_image.mp hsRight
      rw [← hindex]
      exact H.rightComponent j r (Finset.mem_range.mp hr)

private theorem firstGap_targetIsolated_of_certificate
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (H : FirstGapTargetCertificate B)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    ∀ s ∈ B.firstGapTarget j,
      IsIsolated D.fam (B.firstGapLocalLabel j s)
        (vertex B.firstBase B.chord (B.firstGapChordFinish j))
        (B.firstGapCycle j) (B.firstGapCut j s) := by
  intro s hs
  change s ∈ B.firstGapLocalTarget j ∪
    auxiliaryCycleConnectorTarget (B.firstGapLeft j) (B.firstGapRight j)
      (B.firstGapFinishSide j - B.firstGapStartSide j) at hs
  rcases Finset.mem_union.mp hs with hsLocal | hsConnector
  · rcases Finset.mem_union.mp hsLocal with hsArc | hsChord
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hsArc
      exact H.arcIsolated j t ht
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hsChord
      exact H.chordIsolated j t ht
  · rcases Finset.mem_union.mp hsConnector with hsLeft | hsRight
    · exact H.leftIsolated j _ (Finset.mem_range.mp hsLeft)
    · obtain ⟨r, hr, hindex⟩ := Finset.mem_image.mp hsRight
      rw [← hindex]
      exact H.rightIsolated j r (Finset.mem_range.mp hr)

private theorem secondGap_targetComponent_of_certificate
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (H : SecondGapTargetCertificate B)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    ∀ s ∈ B.secondGapTarget j,
      IsComp (B.secondGapLocalLabel j s) (B.secondGapCycle j)
        (B.secondGapCut j s) (B.secondGapCut j (s + 1)) := by
  intro s hs
  change s ∈ B.secondGapLocalTarget j ∪
    auxiliaryCycleConnectorTarget (B.secondGapLeft j) (B.secondGapRight j)
      (B.secondGapFinishSide j - B.secondGapStartSide j) at hs
  rcases Finset.mem_union.mp hs with hsLocal | hsConnector
  · rcases Finset.mem_union.mp hsLocal with hsArc | hsChord
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hsArc
      exact H.arcComponent j t ht
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hsChord
      exact H.chordComponent j t ht
  · rcases Finset.mem_union.mp hsConnector with hsLeft | hsRight
    · exact H.leftComponent j _ (Finset.mem_range.mp hsLeft)
    · obtain ⟨r, hr, hindex⟩ := Finset.mem_image.mp hsRight
      rw [← hindex]
      exact H.rightComponent j r (Finset.mem_range.mp hr)

private theorem secondGap_targetIsolated_of_certificate
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (H : SecondGapTargetCertificate B)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    ∀ s ∈ B.secondGapTarget j,
      IsIsolated D.fam (B.secondGapLocalLabel j s)
        (vertex B.firstBase B.chord (B.secondGapChordFinish j))
        (B.secondGapCycle j) (B.secondGapCut j s) := by
  intro s hs
  change s ∈ B.secondGapLocalTarget j ∪
    auxiliaryCycleConnectorTarget (B.secondGapLeft j) (B.secondGapRight j)
      (B.secondGapFinishSide j - B.secondGapStartSide j) at hs
  rcases Finset.mem_union.mp hs with hsLocal | hsConnector
  · rcases Finset.mem_union.mp hsLocal with hsArc | hsChord
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hsArc
      exact H.arcIsolated j t ht
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hsChord
      exact H.chordIsolated j t ht
  · rcases Finset.mem_union.mp hsConnector with hsLeft | hsRight
    · exact H.leftIsolated j _ (Finset.mem_range.mp hsLeft)
    · obtain ⟨r, hr, hindex⟩ := Finset.mem_image.mp hsRight
      rw [← hindex]
      exact H.rightIsolated j r (Finset.mem_range.mp hr)

/-- Assemble the complete first-family configuration from classwise data. -/
noncomputable def firstGapConfiguration_of_certificate
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (H : FirstGapTargetCertificate B)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    B.FirstGapComponentConfiguration j :=
  B.firstGapConfiguration_of_targetIsolated j
    (B.firstGap_targetComponent_of_certificate H j)
    (B.firstGap_targetIsolated_of_certificate H j)

/-- Assemble the complete wrapped-family configuration from classwise data. -/
noncomputable def secondGapConfiguration_of_certificate
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (H : SecondGapTargetCertificate B)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    B.SecondGapComponentConfiguration j :=
  B.secondGapConfiguration_of_targetIsolated j
    (B.secondGap_targetComponent_of_certificate H j)
    (B.secondGap_targetIsolated_of_certificate H j)

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
