import GroupApproximation.GGT.DGOProposition414SecondSeparationTransport
import GroupApproximation.GGT.DGOProposition414FirstSeparationTargets

/-!
# Transporting a first-half Proposition 4.14 gap child into its half word

Mirror of `DGOProposition414SecondSeparationTransport` for the first half.  The
inherited-arc block of the auxiliary cycle is read at the parent arc
coordinate, and the child chord is read at the chord coordinate; the difference
from the wrapped half is that the first half traverses the chord backwards, so
a chord vertex `z` sits at half-word position `firstArc.length + (chord.length
- z)` and the chord letter `y` at `firstChordPos y`.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-! ## Where the two inherited blocks of a first-half child sit -/

/-- The first-half child arc ends inside the inherited first arc. -/
theorem firstSeparation_arcCut_finish_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    B.firstArcCut (B.firstGapFinishSide j) ≤ B.firstArc.length :=
  B.firstArc_isCutPath.cut.le_length (B.firstGapFinishSide_le j)

/-- The first-half child arc starts no later than it finishes. -/
theorem firstSeparation_arcCut_mono
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    B.firstArcCut (B.firstGapStartSide j) ≤
      B.firstArcCut (B.firstGapFinishSide j) :=
  B.firstArc_isCutPath.cut.mono_le (B.firstGap_side_order j)

/-- The inherited-arc block of a first-half child has the length given by the
parent cut. -/
theorem firstSeparation_arcBlock_length
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)).length =
      B.firstArcCut (B.firstGapFinishSide j) -
        B.firstArcCut (B.firstGapStartSide j) :=
  length_arcWord B.firstArc B.firstArcCut
    (B.firstSeparation_arcCut_finish_le j)

/-- A first-half word vertex past the inherited arc is a chord vertex, counted
back from the far chord endpoint. -/
theorem firstSeparation_vertex_chordPos
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (z : ℕ) :
    vertex B.firstBase B.firstWord
        (B.firstArc.length + (B.chord.length - z)) =
      vertex B.firstBase B.chord z := by
  have hchord : B.firstBase * RelLetter.listVal B.chord = B.secondBase :=
    B.chord_geodesic.2.1
  rw [B.firstWord_eq_append, vertex_append_add, B.firstArc_endpoint, ← hchord]
  exact vertex_revWord_of_end B.chord B.firstBase z

/-- A first-half word letter inside the inherited arc is an arc letter. -/
theorem firstSeparation_isCompOf_arcPos
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (lam : Λ) {y : ℕ}
    (hy : y < B.firstArc.length) (hpos : y < B.firstWord.length) :
    (B.firstWord[y]'hpos).IsCompOf lam ↔ (B.firstArc[y]'hy).IsCompOf lam := by
  have hget : B.firstWord[y]'hpos = B.firstArc[y]'hy := by
    rw [List.getElem_of_eq B.firstWord_eq_append hpos,
      List.getElem_append_left hy]
  rw [hget]

/-! ## The inherited-arc block -/

/-- The cycle vertex at an inherited-arc index is the half-word vertex at the
parent arc coordinate. -/
theorem firstSeparation_vertex_arc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) {r : ℕ}
    (hr : r ≤ B.firstArcCut (B.firstGapFinishSide j) -
      B.firstArcCut (B.firstGapStartSide j)) :
    vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j))
        (B.firstGapCycle j) ((B.firstGapLeft j).length + r) =
      vertex B.firstBase B.firstWord
        (B.firstArcCut (B.firstGapStartSide j) + r) := by
  have hfin := B.firstSeparation_arcCut_finish_le j
  have hmono := B.firstSeparation_arcCut_mono j
  have hblock := B.firstSeparation_arcBlock_length j
  have hrle : r ≤ (arcWord B.firstArc B.firstArcCut
      (B.firstGapStartSide j) (B.firstGapFinishSide j)).length := by
    rw [hblock]
    exact hr
  have hcycle := vertex_auxiliaryCycle_arc
    (vertex B.firstBase B.chord (B.firstGapChordFinish j))
    (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j))
    (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j)) hrle
  rw [hcycle, B.firstGap_arcBase j,
    vertex_arcWord B.firstArc B.firstBase B.firstArcCut hr,
    B.firstWord_eq_append,
    vertex_append_left _ _ _
      (show B.firstArcCut (B.firstGapStartSide j) + r ≤ B.firstArc.length by
        omega)]

/-- The cycle letter at an inherited-arc index is the half-word letter at the
parent arc coordinate. -/
theorem firstSeparation_isCompOf_arc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) (lam : Λ) {r : ℕ}
    (hr : r < (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)).length)
    (hcyc : (B.firstGapLeft j).length + r < (B.firstGapCycle j).length)
    (hword : B.firstArcCut (B.firstGapStartSide j) + r <
      B.firstWord.length) :
    ((B.firstGapCycle j)[(B.firstGapLeft j).length + r]'hcyc).IsCompOf lam ↔
      (B.firstWord[B.firstArcCut (B.firstGapStartSide j) +
        r]'hword).IsCompOf lam := by
  have hfin := B.firstSeparation_arcCut_finish_le j
  have hblock := B.firstSeparation_arcBlock_length j
  have hrcut : r < B.firstArcCut (B.firstGapFinishSide j) -
      B.firstArcCut (B.firstGapStartSide j) := by
    rw [hblock] at hr
    exact hr
  have harcLt : B.firstArcCut (B.firstGapStartSide j) + r <
      B.firstArc.length := by omega
  rw [isCompOf_auxiliaryCycle_arc_iff lam (B.firstGapLeft j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)) (B.firstGapRight j)
      (orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j)) r hr hcyc,
    getElem_arcWord B.firstArc B.firstArcCut hfin hrcut hr,
    B.firstSeparation_isCompOf_arcPos lam harcLt hword]

/-! ## The chord block -/

/-- The cycle vertex at a forward chord index is the half-word vertex at the
chord coordinate counted up from the start of the block. -/
theorem firstSeparation_vertex_chord_of_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (hor : B.firstGapChordStart j ≤ B.firstGapChordFinish j) {r : ℕ}
    (hr : r ≤ B.firstGapChordFinish j - B.firstGapChordStart j) :
    vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j))
        (B.firstGapCycle j)
        ((B.firstGapLeft j).length +
          (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)).length +
          (B.firstGapRight j).length + r) =
      vertex B.firstBase B.firstWord
        (B.firstArc.length +
          (B.chord.length - (B.firstGapChordStart j + r))) := by
  have hcycle := vertex_auxiliaryCycle_chord
    (vertex B.firstBase B.chord (B.firstGapChordFinish j))
    (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j))
    (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j)) r
  rw [hcycle, B.firstGap_prefix_endpoint j,
    B.firstSeparation_vertex_chordPos]
  exact vertex_orientedSegment_of_le B.chord B.firstBase hor hr

/-- The cycle vertex at a backward chord index is the half-word vertex at the
chord coordinate counted down from the start of the block. -/
theorem firstSeparation_vertex_chord_of_not_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (hor : ¬ B.firstGapChordStart j ≤ B.firstGapChordFinish j) {r : ℕ}
    (hr : r ≤ B.firstGapChordStart j - B.firstGapChordFinish j) :
    vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j))
        (B.firstGapCycle j)
        ((B.firstGapLeft j).length +
          (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)).length +
          (B.firstGapRight j).length + r) =
      vertex B.firstBase B.firstWord
        (B.firstArc.length +
          (B.chord.length - (B.firstGapChordStart j - r))) := by
  have hcycle := vertex_auxiliaryCycle_chord
    (vertex B.firstBase B.chord (B.firstGapChordFinish j))
    (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j))
    (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j)) r
  rw [hcycle, B.firstGap_prefix_endpoint j,
    B.firstSeparation_vertex_chordPos]
  exact vertex_orientedSegment_of_not_le B.chord B.firstBase hor
    (B.firstGapChordStart_le j) hr

/-- The cycle letter at a forward chord index is the half-word letter at the
corresponding reversed chord position. -/
theorem firstSeparation_isCompOf_chord_of_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) (lam : Λ)
    (hor : B.firstGapChordStart j ≤ B.firstGapChordFinish j) {r : ℕ}
    (hr : r < (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j)).length)
    (hcyc : (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length + r < (B.firstGapCycle j).length)
    (hchordLt : B.firstGapChordStart j + r < B.chord.length)
    (hword : B.firstChordPos (B.firstGapChordStart j + r) <
      B.firstWord.length) :
    ((B.firstGapCycle j)[(B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length + r]'hcyc).IsCompOf lam ↔
      (B.firstWord[B.firstChordPos
        (B.firstGapChordStart j + r)]'hword).IsCompOf lam := by
  rw [isCompOf_auxiliaryCycle_chord_iff lam (B.firstGapLeft j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)) (B.firstGapRight j)
      (orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j)) r hr hcyc,
    B.isCompOf_firstWord_chordPos_iff lam
      (B.firstGapChordStart j + r) hchordLt hword]
  exact isCompOf_getElem_orientedSegment_of_le lam B.chord hor hr hchordLt

/-- The cycle letter at a backward chord index is the half-word letter at the
corresponding reversed chord position. -/
theorem firstSeparation_isCompOf_chord_of_not_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) (lam : Λ)
    (hor : ¬ B.firstGapChordStart j ≤ B.firstGapChordFinish j) {r : ℕ}
    (hr : r < (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j)).length)
    (hcyc : (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length + r < (B.firstGapCycle j).length)
    (hchordLt : B.firstGapChordStart j - 1 - r < B.chord.length)
    (hword : B.firstChordPos (B.firstGapChordStart j - 1 - r) <
      B.firstWord.length) :
    ((B.firstGapCycle j)[(B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length + r]'hcyc).IsCompOf lam ↔
      (B.firstWord[B.firstChordPos
        (B.firstGapChordStart j - 1 - r)]'hword).IsCompOf lam := by
  rw [isCompOf_auxiliaryCycle_chord_iff lam (B.firstGapLeft j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)) (B.firstGapRight j)
      (orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j)) r hr hcyc,
    B.isCompOf_firstWord_chordPos_iff lam
      (B.firstGapChordStart j - 1 - r) hchordLt hword]
  exact isCompOf_getElem_orientedSegment_of_not_le lam B.chord hor
    (B.firstGapChordStart_le j) hr hchordLt

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
