import GroupApproximation.GGT.DGOProposition414ComponentFamilyAssembly

/-!
# Reading a wrapped gap child inside the parent half word

Dahmani--Guirardel--Osin build the auxiliary cycle `c_j` of Proposition 4.14
from four blocks.  Two of them, the inherited arc and the child chord, are
subwords of the wrapped half word `secondArc ++ chord`, and both are read from
vertices of that half word.  The separation clause for a wrapped child asks
about an arbitrary component start of `c_j`, so the argument needs a single
dictionary sending those two blocks back into the half word: one map on
indices, agreeing with the cycle on vertices and on labels.

This file supplies that dictionary.  `secondSeparationSpot` is the index map,
`secondSeparationSpot_vertex` and `secondSeparationSpot_isCompOf` are its two
agreement statements, and `secondSeparationSpot_ne` records that distinct
indices of the two blocks have distinct images.  The connector blocks are not
in the half word and are treated separately.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Oriented segments, letter by letter and vertex by vertex -/

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
by the starting index. -/
theorem vertex_orientedSegment_of_le (word : List (RelLetter G Λ)) (v : G)
    {cs cf r : ℕ} (h : cs ≤ cf) (hr : r ≤ cf - cs) :
    vertex (vertex v word cs) (orientedSegment word cs cf) r =
      vertex v word (cs + r) := by
  rw [orientedSegment_of_le word h, vertex_take _ _ hr]
  exact vertex_drop_from word v cs r

/-- Vertices of a backward oriented segment are vertices of the word, counted
down from the starting index. -/
theorem vertex_orientedSegment_of_not_le (word : List (RelLetter G Λ)) (v : G)
    {cs cf r : ℕ} (h : ¬ cs ≤ cf) (hcs : cs ≤ word.length) (hr : r ≤ cs - cf) :
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
  rw [orientedSegment_of_not_le word h, hkey, vertex_take _ _ (by omega : cs - cf - r ≤ cs - cf),
    vertex_drop_from word v cf (cs - cf - r)]
  exact congrArg (vertex v word) (by omega)

/-- Letters of a forward oriented segment are letters of the word, at the
shifted index. -/
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
index counted down from the start. -/
theorem isCompOf_getElem_orientedSegment_of_not_le (lam : Λ)
    (word : List (RelLetter G Λ)) {cs cf r : ℕ} (h : ¬ cs ≤ cf)
    (hcs : cs ≤ word.length)
    (hrseg : r < (orientedSegment word cs cf).length)
    (hidx : cs - 1 - r < word.length) :
    ((orientedSegment word cs cf)[r]'hrseg).IsCompOf lam ↔
      (word[cs - 1 - r]'hidx).IsCompOf lam := by
  have hulen : ((word.drop cf).take (cs - cf)).length = cs - cf := by
    rw [List.length_take, List.length_drop]
    omega
  have hseg : orientedSegment word cs cf =
      revWord ((word.drop cf).take (cs - cf)) :=
    orientedSegment_of_not_le word h
  have hrlen : r < (revWord ((word.drop cf).take (cs - cf))).length := by
    rw [length_revWord, hulen]
    rw [hseg, length_revWord, hulen] at hrseg
    exact hrseg
  have hrsub : cs - cf - 1 - r < ((word.drop cf).take (cs - cf)).length := by
    rw [hulen]
    rw [hulen] at hrlen
    omega
  have hstep := isCompOf_getElem_revWord' ((word.drop cf).take (cs - cf)) lam
    hrlen hrsub (by rw [hulen])
  have hinner : ((word.drop cf).take (cs - cf))[cs - cf - 1 - r]'hrsub =
      word[cs - 1 - r]'hidx := by
    have hcong : ((word.drop cf).take (cs - cf))[cs - cf - 1 - r]'hrsub =
        word[cf + (cs - cf - 1 - r)]'(by rw [hulen] at hrsub; omega) := by
      simp
    rw [hcong]
    exact getElem_congr_idx (by rw [hulen] at hrsub; omega)
  have houter : (orientedSegment word cs cf)[r]'hrseg =
      (revWord ((word.drop cf).take (cs - cf)))[r]'hrlen :=
    List.getElem_of_eq hseg hrseg
  rw [houter, hstep, hinner]

namespace BalancedSplitData

/-! ## The two blocks of a wrapped child that live in the half word -/

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

/-- The wrapped child arc starts before it finishes. -/
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

/-- A vertex of the half word past the inherited arc is a vertex of the
chord. -/
theorem secondSeparation_vertex_chordPos
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (y : ℕ) :
    vertex B.secondBase B.secondWord (B.secondArc.length + y) =
      vertex B.firstBase B.chord y := by
  rw [B.secondWord_eq_append, vertex_append_add, B.secondArc_endpoint]

/-- A letter of the half word past the inherited arc is a letter of the
chord. -/
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
  have hget : B.secondWord[B.secondArc.length + y]'hpos =
      B.chord[y]'hy := by
    rw [List.getElem_of_eq B.secondWord_eq_append hpos,
      List.getElem_append_right (by omega)]
    exact getElem_congr_idx (by omega)
  rw [hget]

/-! ## The index dictionary -/

/-- The chord index of a wrapped child chord letter, in the orientation the
child reads it. -/
noncomputable def secondSeparationChordIndex
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) (r : ℕ) : ℕ :=
  if B.secondGapChordStart j ≤ B.secondGapChordFinish j then
    B.secondGapChordStart j + r
  else B.secondGapChordStart j - r

/-- The half-word index of a letter of a wrapped child, in the inherited arc
block and in the chord block.  The value on a connector index is not used. -/
noncomputable def secondSeparationSpot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) (q : ℕ) : ℕ :=
  if q < (B.secondGapLeft j).length +
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)).length then
    B.secondArcCut (B.secondGapStartSide j) + (q - (B.secondGapLeft j).length)
  else
    B.secondArc.length +
      B.secondSeparationChordIndex j
        (q - ((B.secondGapLeft j).length +
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)).length +
          (B.secondGapRight j).length))

/-- On the inherited arc block the dictionary is the parent arc coordinate. -/
theorem secondSeparationSpot_arc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) {r : ℕ}
    (hr : r < (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)).length) :
    B.secondSeparationSpot j ((B.secondGapLeft j).length + r) =
      B.secondArcCut (B.secondGapStartSide j) + r := by
  unfold secondSeparationSpot
  rw [if_pos (by omega)]
  exact congrArg (fun t => B.secondArcCut (B.secondGapStartSide j) + t)
    (by omega)

/-- On the chord block the dictionary is the chord coordinate shifted past the
inherited arc. -/
theorem secondSeparationSpot_chord
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) (r : ℕ) :
    B.secondSeparationSpot j
        ((B.secondGapLeft j).length +
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)).length +
          (B.secondGapRight j).length + r) =
      B.secondArc.length + B.secondSeparationChordIndex j r := by
  unfold secondSeparationSpot
  rw [if_neg (by omega)]
  exact congrArg (fun t => B.secondArc.length + B.secondSeparationChordIndex j t)
    (by omega)

/-! ## Agreement on vertices -/

/-- The cycle vertex at an inherited-arc index is the half-word vertex at its
dictionary index. -/
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
    vertex_append_left _ _ _ (by omega : B.secondArcCut
      (B.secondGapStartSide j) + r ≤ B.secondArc.length)]

/-- The cycle vertex at a chord index is the half-word vertex at its
dictionary index. -/
theorem secondSeparation_vertex_chord
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) {r : ℕ}
    (hr : r ≤ (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)).length) :
    vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j))
        (B.secondGapCycle j)
        ((B.secondGapLeft j).length +
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)).length +
          (B.secondGapRight j).length + r) =
      vertex B.secondBase B.secondWord
        (B.secondArc.length + B.secondSeparationChordIndex j r) := by
  have hstart := B.secondGapChordStart_le j
  have hlenSeg := length_orientedSegment B.chord hstart
    (B.secondGapChordFinish_le j)
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
  unfold secondSeparationChordIndex
  by_cases hor : B.secondGapChordStart j ≤ B.secondGapChordFinish j
  · rw [if_pos hor]
    refine vertex_orientedSegment_of_le B.chord B.firstBase hor ?_
    rw [hlenSeg, Nat.dist_eq_sub_of_le hor] at hr
    exact hr
  · rw [if_neg hor]
    refine vertex_orientedSegment_of_not_le B.chord B.firstBase hor hstart ?_
    rw [hlenSeg, Nat.dist_comm,
      Nat.dist_eq_sub_of_le (by omega : B.secondGapChordFinish j ≤
        B.secondGapChordStart j)] at hr
    exact hr

/-! ## Agreement on labels -/

/-- The cycle letter at an inherited-arc index is the half-word letter at its
dictionary index. -/
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
      (B.secondWord[B.secondArcCut (B.secondGapStartSide j) + r]'hword).IsCompOf
        lam := by
  have hfin := B.secondSeparation_arcCut_finish_le j
  have hblock := B.secondSeparation_arcBlock_length j
  have hrcut : r < B.secondArcCut (B.secondGapFinishSide j) -
      B.secondArcCut (B.secondGapStartSide j) := by
    rw [hblock] at hr
    exact hr
  have harcLt : B.secondArcCut (B.secondGapStartSide j) + r <
      B.secondArc.length := by omega
  have hgetArc := getElem_arcWord B.secondArc B.secondArcCut hfin hrcut hr
  have hgetWord : B.secondWord[B.secondArcCut (B.secondGapStartSide j) + r]'hword
      = B.secondArc[B.secondArcCut (B.secondGapStartSide j) + r]'harcLt := by
    rw [List.getElem_of_eq B.secondWord_eq_append hword,
      List.getElem_append_left harcLt]
  rw [isCompOf_auxiliaryCycle_arc_iff lam (B.secondGapLeft j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)) (B.secondGapRight j)
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j)) r hr hcyc,
    hgetArc, hgetWord]

/-- The cycle letter at a chord index is the half-word letter at its
dictionary index. -/
theorem secondSeparation_isCompOf_chord
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) (lam : Λ) {r : ℕ}
    (hr : r < (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)).length)
    (hcyc : (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length + r < (B.secondGapCycle j).length)
    (hword : B.secondArc.length + B.secondSeparationChordIndex j r <
      B.secondWord.length) :
    ((B.secondGapCycle j)[(B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length + r]'hcyc).IsCompOf lam ↔
      (B.secondWord[B.secondArc.length +
        B.secondSeparationChordIndex j r]'hword).IsCompOf lam := by
  have hstart := B.secondGapChordStart_le j
  have hfinish := B.secondGapChordFinish_le j
  have hlenSeg := length_orientedSegment B.chord hstart hfinish
  have hchordLt : B.secondSeparationChordIndex j r < B.chord.length := by
    unfold secondSeparationChordIndex
    by_cases hor : B.secondGapChordStart j ≤ B.secondGapChordFinish j
    · rw [if_pos hor]
      rw [hlenSeg, Nat.dist_eq_sub_of_le hor] at hr
      omega
    · rw [if_neg hor]
      omega
  rw [isCompOf_auxiliaryCycle_chord_iff lam (B.secondGapLeft j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)) (B.secondGapRight j)
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j)) r hr hcyc,
    B.secondSeparation_isCompOf_chordPos lam hchordLt hword]
  unfold secondSeparationChordIndex
  by_cases hor : B.secondGapChordStart j ≤ B.secondGapChordFinish j
  · rw [if_pos hor]
    refine isCompOf_getElem_orientedSegment_of_le lam B.chord hor hr ?_
  · rw [if_neg hor]
    refine isCompOf_getElem_orientedSegment_of_not_le lam B.chord hor
      hstart hr ?_

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
