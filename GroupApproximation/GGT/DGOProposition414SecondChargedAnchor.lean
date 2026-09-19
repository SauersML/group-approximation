import GroupApproximation.GGT.DGOProposition414ChargedChordSeparation
import GroupApproximation.GGT.DGOProposition414ChordArcSeamProofWrapped

/-!
# The first-half source of a charged wrapped-gap target

The first half reads the chord backwards, so its partner connection initially
lands at the forward edge's terminal vertex. Traversing that component edge
backwards moves it to the initial vertex within the same peripheral coset.
-/

namespace GroupApproximation.GGT.DGOProposition414.BalancedSplitData

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- A charged wrapped-gap target lies in its first-half source's coset. -/
theorem secondGapChordSource_anchor_mem
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapChordSources j) :
    (vertex B.firstBase B.firstWord (B.firstTargetPos s))⁻¹ *
      vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j)
        (B.secondGapCut j (B.secondGapChordTargetIndex j
          (B.brokenAssignment.first.partner s))) ∈ D.fam (P.label s) := by
  have hsBroken := (Finset.mem_filter.mp hs).1
  have hedge := B.firstPartnerSecondGapOwner_edge s hsBroken
  rw [(Finset.mem_filter.mp hs).2] at hedge
  have hA := B.brokenAssignment.first.partner_connected s hsBroken
  change (vertex B.firstBase B.firstWord (B.firstTargetPos s))⁻¹ *
    vertex B.firstBase B.firstWord
      (B.firstChordPos (B.brokenAssignment.first.partner s)) ∈ D.fam (P.label s) at hA
  rw [B.firstBrokenConnectors_partnerStart_vertex s hsBroken] at hA
  have hspan := span_mem_fam_of_isComp D B.firstBase B.chord_geodesic.1
    (B.firstPartner_chord_isComp s hsBroken)
  have hB := orientedEdgeIndex_start_mem D B.firstBase B.chord_geodesic.1
    (B.secondGapChordStart_le j) hedge (B.firstPartner_chord_isComp s hsBroken)
  rw [B.secondGapChordSource_vertex j s]
  convert (D.fam (P.label s)).mul_mem
    ((D.fam (P.label s)).mul_mem hA ((D.fam (P.label s)).inv_mem hspan)) hB using 1
  group

/-- A first-half target cannot meet either endpoint of a same-label wrapped
arc letter. The rotated parent word contains both at distinct positions. -/
theorem firstTarget_not_connected_secondArc_letter
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ B.firstTarget) {m z : ℕ}
    (hm : m < B.secondArc.length) (hmz : m ≤ z) (hzm : z ≤ m + 1)
    (hletter : (B.secondArc[m]'hm).IsCompOf (P.label s)) :
    ¬ (vertex B.firstBase B.firstWord (B.firstTargetPos s))⁻¹ *
      vertex B.secondBase B.secondArc z ∈ D.fam (P.label s) := by
  intro hconn
  have hrot := B.rotWord_eq_secondArc_append_firstArc
  have hrotLen : (rotWord P.word B.secondVertex).length =
      B.secondArc.length + B.firstArc.length := by rw [hrot, List.length_append]
  have hposLt : B.firstTargetPos s < B.firstArc.length := by
    rw [B.firstArc_length_eq]
    exact B.firstTargetPos_lt hs
  have hmlt : m < (rotWord P.word B.secondVertex).length := by omega
  have hletterRot : ((rotWord P.word B.secondVertex)[m]'hmlt).IsCompOf (P.label s) := by
    rw [List.getElem_of_eq hrot hmlt, List.getElem_append_left hm]
    exact hletter
  have hsource : vertex B.secondBase (rotWord P.word B.secondVertex)
      (B.secondArc.length + B.firstTargetPos s) =
      vertex B.firstBase B.firstWord (B.firstTargetPos s) := by
    rw [hrot, vertex_append_add, B.secondArc_endpoint, B.firstWord_eq_append,
      vertex_append_left _ _ _ hposLt.le]
  have hconnRot : Connected D.fam (P.label s) B.secondBase (rotWord P.word B.secondVertex)
      (B.secondArc.length + B.firstTargetPos s) z := by
    change _ ∈ D.fam (P.label s)
    rwa [hsource, hrot, vertex_append_left _ _ _ (show z ≤ B.secondArc.length by omega)]
  exact B.firstTarget_rotated_not_isCompOf_of_connected s hs _ _ hmlt
    (by omega) hmz hzm (by omega) hconnRot hletterRot

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapChordSource_anchor_mem
#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstTarget_not_connected_secondArc_letter
