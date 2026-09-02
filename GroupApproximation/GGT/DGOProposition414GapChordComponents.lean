import GroupApproximation.GGT.DGOProposition414GapLocalLabel
import GroupApproximation.GGT.OsinTheorem54SepSplice
import GroupApproximation.GGT.OsinTheorem54SepFourGonGeneral

/-!
# Charged components in oriented gap chords

An opposite-half partner assigned to a gap is a labeled edge of the global
geodesic chord.  Restricting and possibly reversing the chord preserves
geodesicity, so that edge is a maximal isolated one-edge component in the
oriented child chord.  This is the type-(4) component fact in the bisection
step of Dahmani--Guirardel--Osin Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- A charged wrapped-half source is a maximal one-edge component in the
oriented chord of its first-half gap child. -/
theorem firstGapChordSource_segmentComponent
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapChordSources j) :
    IsComp (P.label s)
      (orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j))
      (orientedEdgeIndex (B.firstGapChordStart j)
        (B.firstGapChordFinish j) (B.brokenAssignment.second.partner s))
      (orientedEdgeIndex (B.firstGapChordStart j)
        (B.firstGapChordFinish j) (B.brokenAssignment.second.partner s) + 1) := by
  have hsBroken := (Finset.mem_filter.mp hs).1
  have hedge := B.secondPartnerFirstGapOwner_edge s hsBroken
  have howner := (Finset.mem_filter.mp hs).2
  rw [howner] at hedge
  have hgeo := isGeodesicWord_orientedSegment D hsymm B.chord_geodesic
    (B.firstGapChordStart_le j) (B.firstGapChordFinish_le j)
  have hletter := orientedEdgeIndex_isCompOf B.chord (P.label s)
    (B.firstGapChordStart_le j) (B.firstGapChordFinish_le j)
    (B.brokenAssignment.second.partner_lt s hsBroken) hedge
    (B.secondPartner_chordLetter_label s hsBroken)
  exact isComp_of_isCompOf_geodesic D (P.label s) hgeo
    (orientedEdgeIndex_lt B.chord (B.firstGapChordStart_le j)
      (B.firstGapChordFinish_le j) hedge) hletter

/-- The same charged component is isolated inside its oriented first-gap
chord segment. -/
theorem firstGapChordSource_segmentIsolated
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapChordSources j) :
    IsIsolated D.fam (P.label s)
      (vertex B.firstBase B.chord (B.firstGapChordStart j))
      (orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j))
      (orientedEdgeIndex (B.firstGapChordStart j)
        (B.firstGapChordFinish j) (B.brokenAssignment.second.partner s)) := by
  let i := orientedEdgeIndex (B.firstGapChordStart j)
    (B.firstGapChordFinish j) (B.brokenAssignment.second.partner s)
  have hcomp := B.firstGapChordSource_segmentComponent j s hs
  have hgeo := isGeodesicWord_orientedSegment D hsymm B.chord_geodesic
    (B.firstGapChordStart_le j) (B.firstGapChordFinish_le j)
  refine ⟨⟨i + 1, hcomp⟩, ?_⟩
  intro q hqi hqstart hconnected
  exact not_connected_of_isCompStart_of_geodesic D hgeo
    ⟨i + 1, hcomp⟩ hqstart hqi hconnected

/-- A charged first-half source is a maximal one-edge component in the
oriented chord of its wrapped-half gap child. -/
theorem secondGapChordSource_segmentComponent
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapChordSources j) :
    IsComp (P.label s)
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j))
      (orientedEdgeIndex (B.secondGapChordStart j)
        (B.secondGapChordFinish j) (B.brokenAssignment.first.partner s))
      (orientedEdgeIndex (B.secondGapChordStart j)
        (B.secondGapChordFinish j) (B.brokenAssignment.first.partner s) + 1) := by
  have hsBroken := (Finset.mem_filter.mp hs).1
  have hedge := B.firstPartnerSecondGapOwner_edge s hsBroken
  have howner := (Finset.mem_filter.mp hs).2
  rw [howner] at hedge
  have hgeo := isGeodesicWord_orientedSegment D hsymm B.chord_geodesic
    (B.secondGapChordStart_le j) (B.secondGapChordFinish_le j)
  have hletter := orientedEdgeIndex_isCompOf B.chord (P.label s)
    (B.secondGapChordStart_le j) (B.secondGapChordFinish_le j)
    (B.brokenAssignment.first.partner_lt s hsBroken) hedge
    (B.firstPartner_chordLetter_label s hsBroken)
  exact isComp_of_isCompOf_geodesic D (P.label s) hgeo
    (orientedEdgeIndex_lt B.chord (B.secondGapChordStart_le j)
      (B.secondGapChordFinish_le j) hedge) hletter

/-- The same charged component is isolated inside its oriented second-gap
chord segment. -/
theorem secondGapChordSource_segmentIsolated
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapChordSources j) :
    IsIsolated D.fam (P.label s)
      (vertex B.firstBase B.chord (B.secondGapChordStart j))
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j))
      (orientedEdgeIndex (B.secondGapChordStart j)
        (B.secondGapChordFinish j) (B.brokenAssignment.first.partner s)) := by
  let i := orientedEdgeIndex (B.secondGapChordStart j)
    (B.secondGapChordFinish j) (B.brokenAssignment.first.partner s)
  have hcomp := B.secondGapChordSource_segmentComponent j s hs
  have hgeo := isGeodesicWord_orientedSegment D hsymm B.chord_geodesic
    (B.secondGapChordStart_le j) (B.secondGapChordFinish_le j)
  refine ⟨⟨i + 1, hcomp⟩, ?_⟩
  intro q hqi hqstart hconnected
  exact not_connected_of_isCompStart_of_geodesic D hgeo
    ⟨i + 1, hcomp⟩ hqstart hqi hconnected

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
