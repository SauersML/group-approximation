import GroupApproximation.GGT.DGOProposition414ComponentFamilyAssembly

/-!
# The four blocks of a Proposition 4.14 auxiliary cycle

Dahmani--Guirardel--Osin list five types of side of `c_j`, which in the word
model are four consecutive blocks: the reversed left connector `e_{j-1}^{-1}`,
the inherited arc, the right connector `f_j`, and the child chord.  Both
target-separation clauses quantify over an *arbitrary* component start of the
cycle, so both need to know which block an index falls in and which letter of
that block it is.  This module states that classification once, together with
the label transfer in each block, so the two separation arguments can share it.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Length and index classification -/

/-- The auxiliary cycle is the concatenation of its four blocks. -/
theorem length_auxiliaryCycleWord
    (left arc right chord : List (RelLetter G Λ)) :
    (auxiliaryCycleWord left arc right chord).length =
      left.length + arc.length + right.length + chord.length := by
  simp only [auxiliaryCycleWord, List.length_append,
    OsinComponents.length_revWord]

/-- Every index of an auxiliary cycle lies in exactly one of its four blocks,
with an explicit offset. -/
theorem auxiliaryCycleWord_index_cases
    (left arc right chord : List (RelLetter G Λ)) {q : ℕ}
    (hq : q < (auxiliaryCycleWord left arc right chord).length) :
    q < left.length ∨
      (∃ r : ℕ, r < arc.length ∧ q = left.length + r) ∨
      (∃ r : ℕ, r < right.length ∧ q = left.length + arc.length + r) ∨
      (∃ r : ℕ, r < chord.length ∧
        q = left.length + arc.length + right.length + r) := by
  have hlen := length_auxiliaryCycleWord left arc right chord
  rcases Nat.lt_or_ge q left.length with h1 | h1
  · exact Or.inl h1
  · rcases Nat.lt_or_ge q (left.length + arc.length) with h2 | h2
    · exact Or.inr (Or.inl ⟨q - left.length, by omega, by omega⟩)
    · rcases Nat.lt_or_ge q (left.length + arc.length + right.length)
        with h3 | h3
      · exact Or.inr (Or.inr (Or.inl
          ⟨q - (left.length + arc.length), by omega, by omega⟩))
      · exact Or.inr (Or.inr (Or.inr
          ⟨q - (left.length + arc.length + right.length), by omega, by omega⟩))

/-! ## Label transfer in the two connector blocks -/

/-- The reversed left connector keeps its labels, at the mirrored index. -/
theorem isCompOf_auxiliaryCycle_left_iff
    (lam : Λ) (left arc right chord : List (RelLetter G Λ))
    (r : ℕ) (hr : r < left.length) (ht : left.length - 1 - r < left.length)
    (hrCycle : r < (auxiliaryCycleWord left arc right chord).length) :
    ((auxiliaryCycleWord left arc right chord)[r]'hrCycle).IsCompOf lam ↔
      (left[left.length - 1 - r]'ht).IsCompOf lam := by
  have hrRev : r < (revWord left).length := by
    rw [OsinComponents.length_revWord]
    exact hr
  unfold auxiliaryCycleWord
  rw [List.getElem_append_left
      (by simp only [List.length_append, OsinComponents.length_revWord]; omega),
    List.getElem_append_left
      (by simp only [List.length_append, OsinComponents.length_revWord]; omega),
    List.getElem_append_left hrRev]
  exact isCompOf_getElem_revWord' left lam hrRev ht rfl

/-- The right connector keeps its labels, at the shifted index. -/
theorem isCompOf_auxiliaryCycle_right_iff
    (lam : Λ) (left arc right chord : List (RelLetter G Λ))
    (r : ℕ) (hr : r < right.length)
    (hrCycle : left.length + arc.length + r <
      (auxiliaryCycleWord left arc right chord).length) :
    ((auxiliaryCycleWord left arc right chord)[
        left.length + arc.length + r]'hrCycle).IsCompOf lam ↔
      (right[r]'hr).IsCompOf lam := by
  have hrevLength : (revWord left).length = left.length :=
    OsinComponents.length_revWord left
  have hpre : (revWord left ++ arc).length ≤ left.length + arc.length + r := by
    simp only [List.length_append, hrevLength]
    omega
  have hidx : left.length + arc.length + r - (revWord left ++ arc).length =
      r := by
    simp only [List.length_append, hrevLength]
    omega
  unfold auxiliaryCycleWord
  rw [List.getElem_append_left
      (by simp only [List.length_append, hrevLength]; omega),
    List.getElem_append_right hpre]
  exact iff_of_eq
    (congrArg (RelLetter.IsCompOf lam) (getElem_congr_idx (c := right) hidx))

/-! ## The classification with labels -/

/-- A labelled letter of an auxiliary cycle is a labelled letter of exactly one
of the four blocks.  This is the shared entry point for both target-separation
arguments: `q` is the cycle index, and the disjunct names the block letter that
carries the same label. -/
theorem isCompOf_auxiliaryCycle_cases
    (lam : Λ) (left arc right chord : List (RelLetter G Λ)) {q : ℕ}
    (hq : q < (auxiliaryCycleWord left arc right chord).length)
    (hletter :
      ((auxiliaryCycleWord left arc right chord)[q]'hq).IsCompOf lam) :
    (∃ ht : left.length - 1 - q < left.length,
        q < left.length ∧ (left[left.length - 1 - q]'ht).IsCompOf lam) ∨
      (∃ r : ℕ, ∃ hr : r < arc.length,
        q = left.length + r ∧ (arc[r]'hr).IsCompOf lam) ∨
      (∃ r : ℕ, ∃ hr : r < right.length,
        q = left.length + arc.length + r ∧ (right[r]'hr).IsCompOf lam) ∨
      (∃ r : ℕ, ∃ hr : r < chord.length,
        q = left.length + arc.length + right.length + r ∧
          (chord[r]'hr).IsCompOf lam) := by
  have hlen := length_auxiliaryCycleWord left arc right chord
  rcases auxiliaryCycleWord_index_cases left arc right chord hq with
    hleft | ⟨r, hr, hqr⟩ | ⟨r, hr, hqr⟩ | ⟨r, hr, hqr⟩
  · refine Or.inl ⟨by omega, hleft, ?_⟩
    exact (isCompOf_auxiliaryCycle_left_iff lam left arc right chord q hleft
      (by omega) hq).mp hletter
  · refine Or.inr (Or.inl ⟨r, hr, hqr, ?_⟩)
    have hq' : left.length + r <
        (auxiliaryCycleWord left arc right chord).length := by omega
    have hgetEq : (auxiliaryCycleWord left arc right chord)[q]'hq =
        (auxiliaryCycleWord left arc right chord)[left.length + r]'hq' :=
      getElem_congr_idx hqr
    rw [hgetEq] at hletter
    exact (isCompOf_auxiliaryCycle_arc_iff lam left arc right chord r hr
      hq').mp hletter
  · refine Or.inr (Or.inr (Or.inl ⟨r, hr, hqr, ?_⟩))
    have hq' : left.length + arc.length + r <
        (auxiliaryCycleWord left arc right chord).length := by omega
    have hgetEq : (auxiliaryCycleWord left arc right chord)[q]'hq =
        (auxiliaryCycleWord left arc right chord)[
          left.length + arc.length + r]'hq' :=
      getElem_congr_idx hqr
    rw [hgetEq] at hletter
    exact (isCompOf_auxiliaryCycle_right_iff lam left arc right chord r hr
      hq').mp hletter
  · refine Or.inr (Or.inr (Or.inr ⟨r, hr, hqr, ?_⟩))
    have hq' : left.length + arc.length + right.length + r <
        (auxiliaryCycleWord left arc right chord).length := by omega
    have hgetEq : (auxiliaryCycleWord left arc right chord)[q]'hq =
        (auxiliaryCycleWord left arc right chord)[
          left.length + arc.length + right.length + r]'hq' :=
      getElem_congr_idx hqr
    rw [hgetEq] at hletter
    exact (isCompOf_auxiliaryCycle_chord_iff lam left arc right chord r hr
      hq').mp hletter

/-- A component start of an auxiliary cycle is in particular a labelled letter
of one of the four blocks. -/
theorem isCompOf_auxiliaryCycle_of_isCompStart
    (lam : Λ) (left arc right chord : List (RelLetter G Λ)) {q : ℕ}
    (hstart : IsCompStart lam (auxiliaryCycleWord left arc right chord) q) :
    ∃ hq : q < (auxiliaryCycleWord left arc right chord).length,
      ((auxiliaryCycleWord left arc right chord)[q]'hq).IsCompOf lam := by
  obtain ⟨kk, hcomp⟩ := hstart
  have hq : q < (auxiliaryCycleWord left arc right chord).length := by
    have h1 := hcomp.1
    have h2 := hcomp.2.1
    omega
  exact ⟨hq, hcomp.2.2.1 q le_rfl hcomp.1 hq⟩

namespace BalancedSplitData

/-- The block classification at a component start of a first-half gap cycle. -/
theorem firstGapCycle_isCompOf_cases
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (lam : Λ) {q : ℕ} (hstart : IsCompStart lam (B.firstGapCycle j) q) :
    (∃ ht : (B.firstGapLeft j).length - 1 - q < (B.firstGapLeft j).length,
        q < (B.firstGapLeft j).length ∧
          ((B.firstGapLeft j)[(B.firstGapLeft j).length - 1 - q]'ht).IsCompOf
            lam) ∨
      (∃ r : ℕ, ∃ hr : r < (arcWord B.firstArc B.firstArcCut
          (B.firstGapStartSide j) (B.firstGapFinishSide j)).length,
        q = (B.firstGapLeft j).length + r ∧
          ((arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j))[r]'hr).IsCompOf lam) ∨
      (∃ r : ℕ, ∃ hr : r < (B.firstGapRight j).length,
        q = (B.firstGapLeft j).length +
            (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
              (B.firstGapFinishSide j)).length + r ∧
          ((B.firstGapRight j)[r]'hr).IsCompOf lam) ∨
      (∃ r : ℕ, ∃ hr : r < (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)).length,
        q = (B.firstGapLeft j).length +
            (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
              (B.firstGapFinishSide j)).length +
            (B.firstGapRight j).length + r ∧
          ((orientedSegment B.chord (B.firstGapChordStart j)
            (B.firstGapChordFinish j))[r]'hr).IsCompOf lam) := by
  obtain ⟨hq, hletter⟩ := isCompOf_auxiliaryCycle_of_isCompStart lam
    (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)) (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j)) hstart
  exact isCompOf_auxiliaryCycle_cases lam (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)) (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j)) hq hletter

/-- The block classification at a component start of a wrapped gap cycle. -/
theorem secondGapCycle_isCompOf_cases
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (lam : Λ) {q : ℕ} (hstart : IsCompStart lam (B.secondGapCycle j) q) :
    (∃ ht : (B.secondGapLeft j).length - 1 - q < (B.secondGapLeft j).length,
        q < (B.secondGapLeft j).length ∧
          ((B.secondGapLeft j)[(B.secondGapLeft j).length - 1 - q]'ht).IsCompOf
            lam) ∨
      (∃ r : ℕ, ∃ hr : r < (arcWord B.secondArc B.secondArcCut
          (B.secondGapStartSide j) (B.secondGapFinishSide j)).length,
        q = (B.secondGapLeft j).length + r ∧
          ((arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j))[r]'hr).IsCompOf lam) ∨
      (∃ r : ℕ, ∃ hr : r < (B.secondGapRight j).length,
        q = (B.secondGapLeft j).length +
            (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
              (B.secondGapFinishSide j)).length + r ∧
          ((B.secondGapRight j)[r]'hr).IsCompOf lam) ∨
      (∃ r : ℕ, ∃ hr : r < (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)).length,
        q = (B.secondGapLeft j).length +
            (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
              (B.secondGapFinishSide j)).length +
            (B.secondGapRight j).length + r ∧
          ((orientedSegment B.chord (B.secondGapChordStart j)
            (B.secondGapChordFinish j))[r]'hr).IsCompOf lam) := by
  obtain ⟨hq, hletter⟩ := isCompOf_auxiliaryCycle_of_isCompStart lam
    (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)) (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)) hstart
  exact isCompOf_auxiliaryCycle_cases lam (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)) (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)) hq hletter

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
