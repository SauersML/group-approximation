import GroupApproximation.GGT.DGOProposition414ComponentFamilyAssembly

/-!
# Reading a wrapped gap child inside the parent half word

Dahmani--Guirardel--Osin build the auxiliary cycle `c_j` of Proposition 4.14
from four blocks.  Two of them, the inherited arc and the child chord, are
subwords of the wrapped half word `secondArc ++ chord`, and both are read from
vertices of that half word.  The separation clause for a wrapped child asks
about an arbitrary component start of `c_j`, so the argument needs a dictionary
sending those two blocks back into the half word, agreeing with the cycle on
vertices and on labels.

This file supplies that dictionary.  The chord block is read in whichever
orientation the child uses, so the chord statements come in a forward and a
backward form; in the backward form the vertex index and the letter index of
the same step differ by one.  The two connector blocks are not subwords of the
half word and are treated elsewhere.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Oriented segments, vertex by vertex and letter by letter -/

/-- A forward oriented segment is the ordinary segment. -/
theorem orientedSegment_of_le (word : List (RelLetter G Λ)) {cs cf : ℕ}
    (h : cs ≤ cf) :
    orientedSegment word cs cf = (word.drop cs).take (cf - cs) := by
  rw [orientedSegment, if_pos h]

/-- A backward oriented segment is the reversal of the ordinary segment
between the same two indices. -/
theorem orientedSegment_of_not_le (word : List (RelLetter G Λ)) {cs cf : ℕ}
    (h : ¬ cs ≤ cf) :
    orientedSegment word cs cf = revWord ((word.drop cf).take (cs - cf)) := by
  rw [orientedSegment, if_neg h]

/-- Vertices of a forward oriented segment are vertices of the word, shifted
up by the starting index. -/
theorem vertex_orientedSegment_of_le (word : List (RelLetter G Λ)) (v : G)
    {cs cf r : ℕ} (h : cs ≤ cf) (hr : r ≤ cf - cs) :
    vertex (vertex v word cs) (orientedSegment word cs cf) r =
      vertex v word (cs + r) := by
  rw [orientedSegment_of_le word h, vertex_take _ _ hr]
  exact vertex_drop_from word v cs r

/-- Vertices of a backward oriented segment are vertices of the word, counted
down from the starting index. -/
theorem vertex_orientedSegment_of_not_le (word : List (RelLetter G Λ)) (v : G)
    {cs cf r : ℕ} (h : ¬ cs ≤ cf) (hcs : cs ≤ word.length)
    (hr : r ≤ cs - cf) :
    vertex (vertex v word cs) (orientedSegment word cs cf) r =
      vertex v word (cs - r) := by
  have hcf : cf ≤ cs := by omega
  have hulen : ((word.drop cf).take (cs - cf)).length = cs - cf := by
    rw [List.length_take, List.length_drop]
    omega
  have hval : vertex v word cf *
      RelLetter.listVal ((word.drop cf).take (cs - cf)) = vertex v word cs :=
    listVal_segment word v hcf
  have hkey := vertex_revWord_of_end ((word.drop cf).take (cs - cf))
    (vertex v word cf) (cs - cf - r)
  rw [hval, hulen] at hkey
  have hindex : cs - cf - (cs - cf - r) = r := by omega
  rw [hindex] at hkey
  rw [orientedSegment_of_not_le word h, hkey,
    vertex_take _ _ (show cs - cf - r ≤ cs - cf by omega),
    vertex_drop_from word v cf (cs - cf - r)]
  exact congrArg (vertex v word) (by omega)

/-- Letters of a forward oriented segment are letters of the word, at the
index shifted up by the starting index. -/
theorem isCompOf_getElem_orientedSegment_of_le (lam : Λ)
    (word : List (RelLetter G Λ)) {cs cf r : ℕ} (h : cs ≤ cf)
    (hrseg : r < (orientedSegment word cs cf).length)
    (hidx : cs + r < word.length) :
    ((orientedSegment word cs cf)[r]'hrseg).IsCompOf lam ↔
      (word[cs + r]'hidx).IsCompOf lam := by
  have hget : (orientedSegment word cs cf)[r]'hrseg = word[cs + r]'hidx := by
    rw [List.getElem_of_eq (orientedSegment_of_le word h) hrseg]
    simp
  rw [hget]

/-- Letters of a backward oriented segment are letters of the word, at the
index one below the vertex the step leaves. -/
theorem isCompOf_getElem_orientedSegment_of_not_le (lam : Λ)
    (word : List (RelLetter G Λ)) {cs cf r : ℕ} (h : ¬ cs ≤ cf)
    (hcs : cs ≤ word.length)
    (hrseg : r < (orientedSegment word cs cf).length)
    (hidx : cs - 1 - r < word.length) :
    ((orientedSegment word cs cf)[r]'hrseg).IsCompOf lam ↔
      (word[cs - 1 - r]'hidx).IsCompOf lam := by
  have hcf : cf ≤ cs := by omega
  have hseg : orientedSegment word cs cf =
      revWord ((word.drop cf).take (cs - cf)) :=
    orientedSegment_of_not_le word h
  have hulen : ((word.drop cf).take (cs - cf)).length = cs - cf := by
    rw [List.length_take, List.length_drop]
    omega
  have hrlt : r < cs - cf := by
    rw [hseg, length_revWord, hulen] at hrseg
    exact hrseg
  have hrlen : r < (revWord ((word.drop cf).take (cs - cf))).length := by
    rw [length_revWord, hulen]
    exact hrlt
  have hrsub : cs - cf - 1 - r < ((word.drop cf).take (cs - cf)).length := by
    rw [hulen]
    omega
  have hshift : cf + (cs - cf - 1 - r) < word.length := by omega
  have hstep := isCompOf_getElem_revWord' ((word.drop cf).take (cs - cf)) lam
    hrlen hrsub (by rw [hulen])
  have hcong : ((word.drop cf).take (cs - cf))[cs - cf - 1 - r]'hrsub =
      word[cf + (cs - cf - 1 - r)]'hshift := by
    simp
  have hidxeq : word[cf + (cs - cf - 1 - r)]'hshift =
      word[cs - 1 - r]'hidx :=
    getElem_congr_idx (by omega)
  have houter : (orientedSegment word cs cf)[r]'hrseg =
      (revWord ((word.drop cf).take (cs - cf)))[r]'hrlen :=
    List.getElem_of_eq hseg hrseg
  rw [houter, hstep, hcong, hidxeq]

namespace BalancedSplitData

/-! ## Where the two inherited blocks of a wrapped child sit -/

/-- The wrapped child arc ends inside the inherited wrapped arc. -/
theorem secondSeparation_arcCut_finish_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    B.secondArcCut (B.secondGapFinishSide j) ≤ B.secondArc.length :=
  B.secondArc_isCutPath.cut.le_length (B.secondGapFinishSide_le j)

/-- The wrapped child arc starts no later than it finishes. -/
theorem secondSeparation_arcCut_mono
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    B.secondArcCut (B.secondGapStartSide j) ≤
      B.secondArcCut (B.secondGapFinishSide j) :=
  B.secondArc_isCutPath.cut.mono_le (B.secondGap_side_order j)

/-- The inherited-arc block of a wrapped child has the length given by the
parent cut. -/
theorem secondSeparation_arcBlock_length
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)).length =
      B.secondArcCut (B.secondGapFinishSide j) -
        B.secondArcCut (B.secondGapStartSide j) :=
  length_arcWord B.secondArc B.secondArcCut
    (B.secondSeparation_arcCut_finish_le j)

/-- A half-word vertex past the inherited arc is a chord vertex. -/
theorem secondSeparation_vertex_chordPos
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (y : ℕ) :
    vertex B.secondBase B.secondWord (B.secondArc.length + y) =
      vertex B.firstBase B.chord y := by
  rw [B.secondWord_eq_append, vertex_append_add, B.secondArc_endpoint]

/-- A half-word letter past the inherited arc is a chord letter. -/
theorem secondSeparation_isCompOf_chordPos
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (lam : Λ) {y : ℕ}
    (hy : y < B.chord.length)
    (hpos : B.secondArc.length + y < B.secondWord.length) :
    (B.secondWord[B.secondArc.length + y]'hpos).IsCompOf lam ↔
      (B.chord[y]'hy).IsCompOf lam := by
  have hget : B.secondWord[B.secondArc.length + y]'hpos = B.chord[y]'hy := by
    rw [List.getElem_of_eq B.secondWord_eq_append hpos,
      List.getElem_append_right (by omega)]
    exact getElem_congr_idx (by omega)
  rw [hget]

/-- A half-word letter inside the inherited arc is an arc letter. -/
theorem secondSeparation_isCompOf_arcPos
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (lam : Λ) {y : ℕ}
    (hy : y < B.secondArc.length)
    (hpos : y < B.secondWord.length) :
    (B.secondWord[y]'hpos).IsCompOf lam ↔ (B.secondArc[y]'hy).IsCompOf lam := by
  have hget : B.secondWord[y]'hpos = B.secondArc[y]'hy := by
    rw [List.getElem_of_eq B.secondWord_eq_append hpos,
      List.getElem_append_left hy]
  rw [hget]

/-! ## The inherited-arc block -/

/-- The cycle vertex at an inherited-arc index is the half-word vertex at the
parent arc coordinate. -/
theorem secondSeparation_vertex_arc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) {r : ℕ}
    (hr : r ≤ B.secondArcCut (B.secondGapFinishSide j) -
      B.secondArcCut (B.secondGapStartSide j)) :
    vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j))
        (B.secondGapCycle j) ((B.secondGapLeft j).length + r) =
      vertex B.secondBase B.secondWord
        (B.secondArcCut (B.secondGapStartSide j) + r) := by
  have hfin := B.secondSeparation_arcCut_finish_le j
  have hblock := B.secondSeparation_arcBlock_length j
  have hrle : r ≤ (arcWord B.secondArc B.secondArcCut
      (B.secondGapStartSide j) (B.secondGapFinishSide j)).length := by
    rw [hblock]
    exact hr
  have hcycle := vertex_auxiliaryCycle_arc
    (vertex B.firstBase B.chord (B.secondGapChordFinish j))
    (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j))
    (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)) hrle
  rw [hcycle, B.secondGap_arcBase j,
    vertex_arcWord B.secondArc B.secondBase B.secondArcCut hr,
    B.secondWord_eq_append,
    vertex_append_left _ _ _
      (show B.secondArcCut (B.secondGapStartSide j) + r ≤ B.secondArc.length by
        omega)]

/-- The cycle letter at an inherited-arc index is the half-word letter at the
parent arc coordinate. -/
theorem secondSeparation_isCompOf_arc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) (lam : Λ) {r : ℕ}
    (hr : r < (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)).length)
    (hcyc : (B.secondGapLeft j).length + r < (B.secondGapCycle j).length)
    (hword : B.secondArcCut (B.secondGapStartSide j) + r <
      B.secondWord.length) :
    ((B.secondGapCycle j)[(B.secondGapLeft j).length + r]'hcyc).IsCompOf lam ↔
      (B.secondWord[B.secondArcCut (B.secondGapStartSide j) +
        r]'hword).IsCompOf lam := by
  have hfin := B.secondSeparation_arcCut_finish_le j
  have hblock := B.secondSeparation_arcBlock_length j
  have hrcut : r < B.secondArcCut (B.secondGapFinishSide j) -
      B.secondArcCut (B.secondGapStartSide j) := by
    rw [hblock] at hr
    exact hr
  have harcLt : B.secondArcCut (B.secondGapStartSide j) + r <
      B.secondArc.length := by omega
  rw [isCompOf_auxiliaryCycle_arc_iff lam (B.secondGapLeft j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)) (B.secondGapRight j)
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j)) r hr hcyc,
    getElem_arcWord B.secondArc B.secondArcCut hfin hrcut hr,
    B.secondSeparation_isCompOf_arcPos lam harcLt hword]

/-! ## The chord block, read forwards -/

/-- The cycle vertex at a forward chord index is the half-word vertex at the
chord coordinate counted up from the start of the block. -/
theorem secondSeparation_vertex_chord_of_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (hor : B.secondGapChordStart j ≤ B.secondGapChordFinish j) {r : ℕ}
    (hr : r ≤ B.secondGapChordFinish j - B.secondGapChordStart j) :
    vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j))
        (B.secondGapCycle j)
        ((B.secondGapLeft j).length +
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)).length +
          (B.secondGapRight j).length + r) =
      vertex B.secondBase B.secondWord
        (B.secondArc.length + (B.secondGapChordStart j + r)) := by
  have hcycle := vertex_auxiliaryCycle_chord
    (vertex B.firstBase B.chord (B.secondGapChordFinish j))
    (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j))
    (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)) r
  rw [hcycle, B.secondGap_prefix_endpoint j,
    B.secondSeparation_vertex_chordPos]
  exact vertex_orientedSegment_of_le B.chord B.firstBase hor hr

/-- The cycle letter at a forward chord index is the half-word letter at the
same chord coordinate. -/
theorem secondSeparation_isCompOf_chord_of_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) (lam : Λ)
    (hor : B.secondGapChordStart j ≤ B.secondGapChordFinish j) {r : ℕ}
    (hr : r < (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)).length)
    (hcyc : (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length + r < (B.secondGapCycle j).length)
    (hword : B.secondArc.length + (B.secondGapChordStart j + r) <
      B.secondWord.length) :
    ((B.secondGapCycle j)[(B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length + r]'hcyc).IsCompOf lam ↔
      (B.secondWord[B.secondArc.length +
        (B.secondGapChordStart j + r)]'hword).IsCompOf lam := by
  have hlenSeg := length_orientedSegment B.chord (B.secondGapChordStart_le j)
    (B.secondGapChordFinish_le j)
  have hchordLt : B.secondGapChordStart j + r < B.chord.length := by
    rw [hlenSeg, Nat.dist_eq_sub_of_le hor] at hr
    have hfin := B.secondGapChordFinish_le j
    omega
  rw [isCompOf_auxiliaryCycle_chord_iff lam (B.secondGapLeft j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)) (B.secondGapRight j)
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j)) r hr hcyc,
    B.secondSeparation_isCompOf_chordPos lam hchordLt hword]
  exact isCompOf_getElem_orientedSegment_of_le lam B.chord hor hr hchordLt

/-! ## The chord block, read backwards -/

/-- The cycle vertex at a backward chord index is the half-word vertex at the
chord coordinate counted down from the start of the block. -/
theorem secondSeparation_vertex_chord_of_not_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (hor : ¬ B.secondGapChordStart j ≤ B.secondGapChordFinish j) {r : ℕ}
    (hr : r ≤ B.secondGapChordStart j - B.secondGapChordFinish j) :
    vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j))
        (B.secondGapCycle j)
        ((B.secondGapLeft j).length +
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)).length +
          (B.secondGapRight j).length + r) =
      vertex B.secondBase B.secondWord
        (B.secondArc.length + (B.secondGapChordStart j - r)) := by
  have hcycle := vertex_auxiliaryCycle_chord
    (vertex B.firstBase B.chord (B.secondGapChordFinish j))
    (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j))
    (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)) r
  rw [hcycle, B.secondGap_prefix_endpoint j,
    B.secondSeparation_vertex_chordPos]
  exact vertex_orientedSegment_of_not_le B.chord B.firstBase hor
    (B.secondGapChordStart_le j) hr

/-- The cycle letter at a backward chord index is the half-word letter one
below the vertex the step leaves. -/
theorem secondSeparation_isCompOf_chord_of_not_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) (lam : Λ)
    (hor : ¬ B.secondGapChordStart j ≤ B.secondGapChordFinish j) {r : ℕ}
    (hr : r < (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)).length)
    (hcyc : (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length + r < (B.secondGapCycle j).length)
    (hword : B.secondArc.length + (B.secondGapChordStart j - 1 - r) <
      B.secondWord.length) :
    ((B.secondGapCycle j)[(B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length + r]'hcyc).IsCompOf lam ↔
      (B.secondWord[B.secondArc.length +
        (B.secondGapChordStart j - 1 - r)]'hword).IsCompOf lam := by
  have hstart := B.secondGapChordStart_le j
  have hlenSeg := length_orientedSegment B.chord hstart
    (B.secondGapChordFinish_le j)
  have hrlt : r < B.secondGapChordStart j - B.secondGapChordFinish j := by
    rw [hlenSeg, Nat.dist_comm,
      Nat.dist_eq_sub_of_le (show B.secondGapChordFinish j ≤
        B.secondGapChordStart j by omega)] at hr
    exact hr
  have hchordLt : B.secondGapChordStart j - 1 - r < B.chord.length := by omega
  rw [isCompOf_auxiliaryCycle_chord_iff lam (B.secondGapLeft j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)) (B.secondGapRight j)
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j)) r hr hcyc,
    B.secondSeparation_isCompOf_chordPos lam hchordLt hword]
  exact isCompOf_getElem_orientedSegment_of_not_le lam B.chord hor hstart hr
    hchordLt

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
