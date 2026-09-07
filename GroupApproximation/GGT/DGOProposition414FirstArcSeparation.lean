import GroupApproximation.GGT.DGOProposition414FirstSeparationTransport
import GroupApproximation.GGT.DGOIsolatedSingletonLetter

/-!
# Separation of inherited first-half targets in the auxiliary cycles

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
in the first half word. -/
theorem firstGapArcSource_vertex
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j) :
    vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
        (B.firstGapCut j ((B.firstGapLeft j).length +
          (B.firstTargetSide s - B.firstGapStartSide j))) =
      vertex B.firstBase B.firstWord (B.firstTargetPos s) := by
  have hsData := Finset.mem_filter.mp hs
  have hstart := B.firstArc_isCutPath.cut.mono_le hsData.2.1
  have hfinish := B.firstArc_isCutPath.cut.mono_le hsData.2.2.le
  have hcut : B.firstGapCut j ((B.firstGapLeft j).length +
      (B.firstTargetSide s - B.firstGapStartSide j)) =
      (B.firstGapLeft j).length + (B.firstArcCut (B.firstTargetSide s) -
        B.firstArcCut (B.firstGapStartSide j)) := B.firstGapArcSource_auxiliaryCut j s hs
  rw [hcut, B.firstSeparation_vertex_arc j (Nat.sub_le_sub_right hfinish _),
    Nat.add_sub_of_le hstart, (B.firstArcCut_target hsData.1).1]

/-- An inherited target cannot connect to a distinct component start in the
inherited arc block of its auxiliary cycle. -/
theorem firstGapArcSource_not_connected_arc
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j) {r : ℕ}
    (hr : r < (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)).length)
    (hne : (B.firstGapLeft j).length + r ≠ B.firstGapCut j
      ((B.firstGapLeft j).length + (B.firstTargetSide s - B.firstGapStartSide j)))
    (hop : IsCompStart (P.label s) (B.firstGapCycle j) ((B.firstGapLeft j).length + r)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
      (B.firstGapCut j ((B.firstGapLeft j).length + (B.firstTargetSide s - B.firstGapStartSide j)))
      ((B.firstGapLeft j).length + r) := by
  intro hconn
  have hsurv := B.firstGapArcSource_survives j s hs
  have hfinish := B.firstSeparation_arcCut_finish_le j
  have hblock := B.firstSeparation_arcBlock_length j
  have hstart := B.firstSeparation_arcCut_mono j
  have hr' : r < B.firstArcCut (B.firstGapFinishSide j) -
      B.firstArcCut (B.firstGapStartSide j) := by rwa [hblock] at hr
  have hwordLen : B.firstWord.length = B.firstArc.length + B.chord.length := by
    rw [B.firstWord_eq_append]
    simp only [List.length_append, GroupApproximation.GGT.OsinComponents.length_revWord]
  have hword : B.firstArcCut (B.firstGapStartSide j) + r < B.firstWord.length := by omega
  obtain ⟨endPos, hcomp⟩ := hop
  have hcycle : (B.firstGapLeft j).length + r < (B.firstGapCycle j).length :=
    hcomp.1.trans_le hcomp.2.1
  have hletter := (B.firstSeparation_isCompOf_arc j (P.label s) hr hcycle hword).mp
    (hcomp.2.2.1 _ le_rfl hcomp.1 hcycle)
  have hconnWord : Connected D.fam (P.label s) B.firstBase B.firstWord
      (B.firstTargetPos s) (B.firstArcCut (B.firstGapStartSide j) + r) := by
    change (vertex B.firstBase B.firstWord (B.firstTargetPos s))⁻¹ *
      vertex B.firstBase B.firstWord (B.firstArcCut (B.firstGapStartSide j) + r) ∈ D.fam (P.label s)
    change (vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
      (B.firstGapCut j ((B.firstGapLeft j).length + (B.firstTargetSide s - B.firstGapStartSide j))))⁻¹ *
      vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
        ((B.firstGapLeft j).length + r) ∈ D.fam (P.label s) at hconn
    rwa [B.firstGapArcSource_vertex j s hs, B.firstSeparation_vertex_arc j hr'.le] at hconn
  have heq := eq_of_isolated_singleton_of_connected_letter D B.firstWord_letters
    hsurv.1 hsurv.2 hword le_rfl (Nat.le_succ _) hletter hconnWord
  apply hne
  have hsData := Finset.mem_filter.mp hs
  change B.firstArcCut (B.firstGapStartSide j) + r = B.firstTargetPos s at heq
  have hcut : B.firstGapCut j ((B.firstGapLeft j).length +
      (B.firstTargetSide s - B.firstGapStartSide j)) =
      (B.firstGapLeft j).length + (B.firstArcCut (B.firstTargetSide s) -
        B.firstArcCut (B.firstGapStartSide j)) := B.firstGapArcSource_auxiliaryCut j s hs
  rw [hcut, (B.firstArcCut_target hsData.1).1]
  omega


/-- An inherited target cannot connect to a component in the chord block,
regardless of the orientation of that block. The transported opposing letter
may meet the transported vertex at either of its endpoints. -/
theorem firstGapArcSource_not_connected_chord
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j) {r : ℕ}
    (hr : r < (orientedSegment B.chord (B.firstGapChordStart j) (B.firstGapChordFinish j)).length)
    (hop : IsCompStart (P.label s) (B.firstGapCycle j)
      ((B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length + r)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
      (B.firstGapCut j ((B.firstGapLeft j).length + (B.firstTargetSide s - B.firstGapStartSide j)))
      ((B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length + r) := by
  intro hconn
  have hsurv := B.firstGapArcSource_survives j s hs
  have hsTarget := (Finset.mem_filter.mp hs).1
  have hsourceLt := B.firstTargetPos_lt hsTarget
  have hstartLe := B.firstGapChordStart_le j
  have hfinishLe := B.firstGapChordFinish_le j
  obtain ⟨endPos, hcomp⟩ := hop
  have hcycle := hcomp.1.trans_le hcomp.2.1
  have hletter := hcomp.2.2.1 _ le_rfl hcomp.1 hcycle
  change (vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
    (B.firstGapCut j ((B.firstGapLeft j).length + (B.firstTargetSide s - B.firstGapStartSide j))))⁻¹ *
    vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
      ((B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length + r) ∈ D.fam (P.label s) at hconn
  rw [B.firstGapArcSource_vertex j s hs] at hconn
  by_cases hor : B.firstGapChordStart j ≤ B.firstGapChordFinish j
  · have hwidth : r < B.firstGapChordFinish j - B.firstGapChordStart j := by
      rwa [length_orientedSegment B.chord hstartLe hfinishLe, Nat.dist_eq_sub_of_le hor] at hr
    have hy : B.firstGapChordStart j + r < B.chord.length := by omega
    have hword := B.firstChordPos_lt _ hy
    have hco := (B.firstSeparation_isCompOf_chord_of_le j (P.label s) hor hr hcycle hy hword).mp hletter
    rw [B.firstSeparation_vertex_chord_of_le j hor hwidth.le] at hconn
    have heq := eq_of_isolated_singleton_of_connected_letter D B.firstWord_letters hsurv.1 hsurv.2
      hword (z := B.firstArc.length + (B.chord.length - (B.firstGapChordStart j + r)))
      (by dsimp [firstChordPos]; rw [B.firstArc_length_eq]; omega)
      (by dsimp [firstChordPos]; rw [B.firstArc_length_eq]; omega) hco hconn
    change B.firstChordPos (B.firstGapChordStart j + r) = B.firstTargetPos s at heq
    dsimp [firstChordPos] at heq
    omega
  · have hwidth : r < B.firstGapChordStart j - B.firstGapChordFinish j := by
      rwa [length_orientedSegment B.chord hstartLe hfinishLe, Nat.dist_comm,
        Nat.dist_eq_sub_of_le (by omega)] at hr
    have hy : B.firstGapChordStart j - 1 - r < B.chord.length := by omega
    have hword := B.firstChordPos_lt _ hy
    have hco := (B.firstSeparation_isCompOf_chord_of_not_le j (P.label s) hor hr hcycle hy hword).mp hletter
    rw [B.firstSeparation_vertex_chord_of_not_le j hor hwidth.le] at hconn
    have heq := eq_of_isolated_singleton_of_connected_letter D B.firstWord_letters hsurv.1 hsurv.2
      hword (z := B.firstArc.length + (B.chord.length - (B.firstGapChordStart j - r)))
      (by dsimp [firstChordPos]; rw [B.firstArc_length_eq]; omega)
      (by dsimp [firstChordPos]; rw [B.firstArc_length_eq]; omega) hco hconn
    change B.firstChordPos (B.firstGapChordStart j - 1 - r) = B.firstTargetPos s at heq
    dsimp [firstChordPos] at heq
    omega

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapArcSource_vertex
#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapArcSource_not_connected_arc

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapArcSource_not_connected_chord
