import GroupApproximation.GGT.DGOProposition414SecondChargedAnchor

/-!
# Charged wrapped-gap targets do not meet the inherited arc

The common reduction permits an opponent connected to either endpoint of an
arc letter. This also supplies the source-isolation step for the two connector
blocks, whose endpoints are broken source vertices in the inherited arc.
-/

namespace GroupApproximation.GGT.DGOProposition414.BalancedSplitData

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- Transport through an arc-letter coset rules out a connection to a charged
target from the opposite half. -/
theorem secondGapChordSource_not_connected_of_arc_anchor
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapChordSources j) {q m z : ℕ}
    (hm : m < B.secondArc.length) (hmz : m ≤ z) (hzm : z ≤ m + 1)
    (hletter : (B.secondArc[m]'hm).IsCompOf (P.label s))
    (hlink : (vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j))
        (B.secondGapCycle j) q)⁻¹ * vertex B.secondBase B.secondArc z ∈ D.fam (P.label s)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j)
      (B.secondGapCut j (B.secondGapChordTargetIndex j
        (B.brokenAssignment.first.partner s))) q := by
  intro hconn
  have hsTarget := (mem_brokenSet_iff.mp (Finset.mem_filter.mp hs).1).1
  apply B.firstTarget_not_connected_secondArc_letter s hsTarget hm hmz hzm hletter
  have hm := (D.fam (P.label s)).mul_mem
    ((D.fam (P.label s)).mul_mem (B.secondGapChordSource_anchor_mem j s hs) hconn) hlink
  convert hm using 1
  group

/-- A charged target does not connect to any component start in the inherited
arc block, including a start newly created at the left cut. -/
theorem secondGapChordSource_not_connected_arc
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapChordSources j) {r : ℕ}
    (hr : r < (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)).length)
    (hop : IsCompStart (P.label s) (B.secondGapCycle j) ((B.secondGapLeft j).length + r)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j)
      (B.secondGapCut j (B.secondGapChordTargetIndex j
        (B.brokenAssignment.first.partner s))) ((B.secondGapLeft j).length + r) := by
  have hfinish := B.secondSeparation_arcCut_finish_le j
  have hr' : r < B.secondArcCut (B.secondGapFinishSide j) -
      B.secondArcCut (B.secondGapStartSide j) := by rwa [B.secondSeparation_arcBlock_length j] at hr
  have hm : B.secondArcCut (B.secondGapStartSide j) + r < B.secondArc.length := by omega
  obtain ⟨endPos, hcomp⟩ := hop
  have hcycle := hcomp.1.trans_le hcomp.2.1
  have hletter := (isCompOf_auxiliaryCycle_arc_iff (P.label s) (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j))
    (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j) (B.secondGapChordFinish j)) r hr hcycle).mp
      (hcomp.2.2.1 _ le_rfl hcomp.1 hcycle)
  rw [getElem_arcWord B.secondArc B.secondArcCut hfinish hr'] at hletter
  apply B.secondGapChordSource_not_connected_of_arc_anchor j s hs hm le_rfl
    (Nat.le_succ _) hletter
  rw [B.secondSeparation_vertex_arc j hr'.le]
  have hvert : vertex B.secondBase B.secondWord (B.secondArcCut (B.secondGapStartSide j) + r) =
      vertex B.secondBase B.secondArc (B.secondArcCut (B.secondGapStartSide j) + r) := by
    rw [B.secondWord_eq_append]
    exact vertex_append_left _ _ _ hm.le
  rw [hvert, inv_mul_cancel]
  exact (D.fam (P.label s)).one_mem

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapChordSource_not_connected_of_arc_anchor
#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapChordSource_not_connected_arc
