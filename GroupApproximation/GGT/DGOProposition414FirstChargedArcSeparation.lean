import GroupApproximation.GGT.DGOProposition414FirstChargedAnchor

/-!
# Charged first-gap targets do not meet the inherited arc

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
theorem firstGapChordSource_not_connected_of_arc_anchor
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapChordSources j) {q m z : ℕ}
    (hm : m < B.firstArc.length) (hmz : m ≤ z) (hzm : z ≤ m + 1)
    (hletter : (B.firstArc[m]'hm).IsCompOf (P.label s))
    (hlink : (vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j))
        (B.firstGapCycle j) q)⁻¹ * vertex B.firstBase B.firstArc z ∈ D.fam (P.label s)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
      (B.firstGapCut j (B.firstGapChordTargetIndex j
        (B.brokenAssignment.second.partner s))) q := by
  intro hconn
  have hsTarget := (mem_brokenSet_iff.mp (Finset.mem_filter.mp hs).1).1
  apply B.secondTarget_not_connected_firstArc_letter s hsTarget hm hmz hzm hletter
  have hm := (D.fam (P.label s)).mul_mem
    ((D.fam (P.label s)).mul_mem (B.firstGapChordSource_anchor_mem j s hs) hconn) hlink
  convert hm using 1
  group

/-- A charged target does not connect to any component start in the inherited
arc block, including a start newly created at the left cut. -/
theorem firstGapChordSource_not_connected_arc
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapChordSources j) {r : ℕ}
    (hr : r < (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)).length)
    (hop : IsCompStart (P.label s) (B.firstGapCycle j) ((B.firstGapLeft j).length + r)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
      (B.firstGapCut j (B.firstGapChordTargetIndex j
        (B.brokenAssignment.second.partner s))) ((B.firstGapLeft j).length + r) := by
  have hfinish := B.firstSeparation_arcCut_finish_le j
  have hr' : r < B.firstArcCut (B.firstGapFinishSide j) -
      B.firstArcCut (B.firstGapStartSide j) := by rwa [B.firstSeparation_arcBlock_length j] at hr
  have hm : B.firstArcCut (B.firstGapStartSide j) + r < B.firstArc.length := by omega
  obtain ⟨endPos, hcomp⟩ := hop
  have hcycle := hcomp.1.trans_le hcomp.2.1
  have hletter := (isCompOf_auxiliaryCycle_arc_iff (P.label s) (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j))
    (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j) (B.firstGapChordFinish j)) r hr hcycle).mp
      (hcomp.2.2.1 _ le_rfl hcomp.1 hcycle)
  rw [getElem_arcWord B.firstArc B.firstArcCut hfinish hr'] at hletter
  apply B.firstGapChordSource_not_connected_of_arc_anchor j s hs hm le_rfl
    (Nat.le_succ _) hletter
  rw [B.firstSeparation_vertex_arc j hr'.le]
  have hvert : vertex B.firstBase B.firstWord (B.firstArcCut (B.firstGapStartSide j) + r) =
      vertex B.firstBase B.firstArc (B.firstArcCut (B.firstGapStartSide j) + r) := by
    rw [B.firstWord_eq_append]
    exact vertex_append_left _ _ _ hm.le
  rw [hvert, inv_mul_cancel]
  exact (D.fam (P.label s)).one_mem

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapChordSource_not_connected_of_arc_anchor
#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapChordSource_not_connected_arc
