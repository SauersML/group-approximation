import GroupApproximation.GGT.DGOProposition414SecondSeparationTransport
import GroupApproximation.GGT.DGOIsolatedSingletonLetter

/-!
# Separation of inherited second-half targets in the auxiliary cycles

The surviving source is isolated in its entire half word. Exact vertex and
letter dictionaries transport the auxiliary-cycle opponents to that word,
including letters whose maximal component changes after the cut.
-/

namespace GroupApproximation.GGT.DGOProposition414.BalancedSplitData

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- The actual vertex at an inherited target's local cut is its source vertex
in the second half word. -/
theorem secondGapArcSource_vertex
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j) :
    vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j)
        (B.secondGapCut j ((B.secondGapLeft j).length +
          (B.secondTargetSide s - B.secondGapStartSide j))) =
      vertex B.secondBase B.secondWord (B.secondTargetPos s) := by
  have hsData := Finset.mem_filter.mp hs
  have hstart := B.secondArc_isCutPath.cut.mono_le hsData.2.1
  have hfinish := B.secondArc_isCutPath.cut.mono_le hsData.2.2.le
  have hcut : B.secondGapCut j ((B.secondGapLeft j).length +
      (B.secondTargetSide s - B.secondGapStartSide j)) =
      (B.secondGapLeft j).length + (B.secondArcCut (B.secondTargetSide s) -
        B.secondArcCut (B.secondGapStartSide j)) := B.secondGapArcSource_auxiliaryCut j s hs
  rw [hcut, B.secondSeparation_vertex_arc j (Nat.sub_le_sub_right hfinish _),
    Nat.add_sub_of_le hstart, (B.secondArcCut_target hsData.1).1]

/-- An inherited target cannot connect to a distinct component start in the
inherited arc block of its auxiliary cycle. -/
theorem secondGapArcSource_not_connected_arc
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j) {r : ℕ}
    (hr : r < (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)).length)
    (hne : (B.secondGapLeft j).length + r ≠ B.secondGapCut j
      ((B.secondGapLeft j).length + (B.secondTargetSide s - B.secondGapStartSide j)))
    (hop : IsCompStart (P.label s) (B.secondGapCycle j) ((B.secondGapLeft j).length + r)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j)
      (B.secondGapCut j ((B.secondGapLeft j).length + (B.secondTargetSide s - B.secondGapStartSide j)))
      ((B.secondGapLeft j).length + r) := by
  intro hconn
  have hsurv := B.secondGapArcSource_survives j s hs
  have hfinish := B.secondSeparation_arcCut_finish_le j
  have hblock := B.secondSeparation_arcBlock_length j
  have hstart := B.secondSeparation_arcCut_mono j
  have hr' : r < B.secondArcCut (B.secondGapFinishSide j) -
      B.secondArcCut (B.secondGapStartSide j) := by rwa [hblock] at hr
  have hwordLen : B.secondWord.length = B.secondArc.length + B.chord.length := by
    rw [B.secondWord_eq_append]
    simp only [List.length_append]
  have hword : B.secondArcCut (B.secondGapStartSide j) + r < B.secondWord.length := by omega
  obtain ⟨endPos, hcomp⟩ := hop
  have hcycle : (B.secondGapLeft j).length + r < (B.secondGapCycle j).length :=
    hcomp.1.trans_le hcomp.2.1
  have hletter := (B.secondSeparation_isCompOf_arc j (P.label s) hr hcycle hword).mp
    (hcomp.2.2.1 _ le_rfl hcomp.1 hcycle)
  have hconnWord : Connected D.fam (P.label s) B.secondBase B.secondWord
      (B.secondTargetPos s) (B.secondArcCut (B.secondGapStartSide j) + r) := by
    change (vertex B.secondBase B.secondWord (B.secondTargetPos s))⁻¹ *
      vertex B.secondBase B.secondWord (B.secondArcCut (B.secondGapStartSide j) + r) ∈ D.fam (P.label s)
    change (vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j)
      (B.secondGapCut j ((B.secondGapLeft j).length + (B.secondTargetSide s - B.secondGapStartSide j))))⁻¹ *
      vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j)
        ((B.secondGapLeft j).length + r) ∈ D.fam (P.label s) at hconn
    rwa [B.secondGapArcSource_vertex j s hs, B.secondSeparation_vertex_arc j hr'.le] at hconn
  have heq := eq_of_isolated_singleton_of_connected_letter D B.secondWord_letters
    hsurv.1 hsurv.2 hword le_rfl (Nat.le_succ _) hletter hconnWord
  apply hne
  have hsData := Finset.mem_filter.mp hs
  change B.secondArcCut (B.secondGapStartSide j) + r = B.secondTargetPos s at heq
  have hcut : B.secondGapCut j ((B.secondGapLeft j).length +
      (B.secondTargetSide s - B.secondGapStartSide j)) =
      (B.secondGapLeft j).length + (B.secondArcCut (B.secondTargetSide s) -
        B.secondArcCut (B.secondGapStartSide j)) := B.secondGapArcSource_auxiliaryCut j s hs
  rw [hcut, (B.secondArcCut_target hsData.1).1]
  omega


/-- An inherited target cannot connect to a component in the chord block,
regardless of the orientation of that block. The transported opposing letter
may meet the transported vertex at either of its endpoints. -/
theorem secondGapArcSource_not_connected_chord
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j) {r : ℕ}
    (hr : r < (orientedSegment B.chord (B.secondGapChordStart j) (B.secondGapChordFinish j)).length)
    (hop : IsCompStart (P.label s) (B.secondGapCycle j)
      ((B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length + r)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j)
      (B.secondGapCut j ((B.secondGapLeft j).length + (B.secondTargetSide s - B.secondGapStartSide j)))
      ((B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length + r) := by
  intro hconn
  have hsurv := B.secondGapArcSource_survives j s hs
  have hsTarget := (Finset.mem_filter.mp hs).1
  have hsourceLt := B.secondTargetPos_lt hsTarget
  have hstartLe := B.secondGapChordStart_le j
  have hfinishLe := B.secondGapChordFinish_le j
  obtain ⟨endPos, hcomp⟩ := hop
  have hcycle := hcomp.1.trans_le hcomp.2.1
  have hletter := hcomp.2.2.1 _ le_rfl hcomp.1 hcycle
  change (vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j)
    (B.secondGapCut j ((B.secondGapLeft j).length + (B.secondTargetSide s - B.secondGapStartSide j))))⁻¹ *
    vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j)
      ((B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length + r) ∈ D.fam (P.label s) at hconn
  rw [B.secondGapArcSource_vertex j s hs] at hconn
  have hwordLen : B.secondWord.length = B.secondArc.length + B.chord.length := by
    rw [B.secondWord_eq_append, List.length_append]
  have hsourceLt' : B.secondTargetPos s < B.secondArc.length := by
    rwa [B.secondArc_length_eq]
  by_cases hor : B.secondGapChordStart j ≤ B.secondGapChordFinish j
  · have hwidth : r < B.secondGapChordFinish j - B.secondGapChordStart j := by
      rwa [length_orientedSegment B.chord hstartLe hfinishLe, Nat.dist_eq_sub_of_le hor] at hr
    have hword : B.secondArc.length + (B.secondGapChordStart j + r) < B.secondWord.length := by omega
    have hco := (B.secondSeparation_isCompOf_chord_of_le j (P.label s) hor hr hcycle hword).mp hletter
    rw [B.secondSeparation_vertex_chord_of_le j hor hwidth.le] at hconn
    have heq := eq_of_isolated_singleton_of_connected_letter D B.secondWord_letters hsurv.1 hsurv.2
      hword le_rfl (Nat.le_succ _) hco hconn
    change B.secondArc.length + (B.secondGapChordStart j + r) = B.secondTargetPos s at heq
    omega
  · have hwidth : r < B.secondGapChordStart j - B.secondGapChordFinish j := by
      rwa [length_orientedSegment B.chord hstartLe hfinishLe, Nat.dist_comm,
        Nat.dist_eq_sub_of_le (by omega)] at hr
    have hword : B.secondArc.length + (B.secondGapChordStart j - 1 - r) < B.secondWord.length := by omega
    have hco := (B.secondSeparation_isCompOf_chord_of_not_le j (P.label s) hor hr hcycle hword).mp hletter
    rw [B.secondSeparation_vertex_chord_of_not_le j hor hwidth.le] at hconn
    have heq := eq_of_isolated_singleton_of_connected_letter D B.secondWord_letters hsurv.1 hsurv.2
      hword (z := B.secondArc.length + (B.secondGapChordStart j - r))
      (by omega) (by omega) hco hconn
    change B.secondArc.length + (B.secondGapChordStart j - 1 - r) = B.secondTargetPos s at heq
    omega

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapArcSource_vertex
#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapArcSource_not_connected_arc

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapArcSource_not_connected_chord
