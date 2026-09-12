import GroupApproximation.GGT.DGOProposition414ChargedChordSeparation
import GroupApproximation.GGT.DGOProposition414FirstSeparationTransport
import GroupApproximation.GGT.DGOProposition414ChordArcSeamProof

/-!
# The opposite-half source of a charged first-gap target

The charged partner edge has the same peripheral coset as its original wrapped
source. Isolation in the rotated parent polygon excludes every same-label
letter in the first inherited arc, at either endpoint of that letter.
-/

namespace GroupApproximation.GGT.DGOProposition414.BalancedSplitData

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- A charged first-gap target lies in its wrapped source's coset. -/
theorem firstGapChordSource_anchor_mem
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapChordSources j) :
    (vertex B.secondBase B.secondWord (B.secondTargetPos s))⁻¹ *
      vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
        (B.firstGapCut j (B.firstGapChordTargetIndex j
          (B.brokenAssignment.second.partner s))) ∈ D.fam (P.label s) := by
  have hsBroken := (Finset.mem_filter.mp hs).1
  have hedge := B.secondPartnerFirstGapOwner_edge s hsBroken
  rw [(Finset.mem_filter.mp hs).2] at hedge
  have hA := B.brokenAssignment.second.partner_connected s hsBroken
  change (vertex B.secondBase B.secondWord (B.secondTargetPos s))⁻¹ *
    vertex B.secondBase B.secondWord
      (B.secondChordPos (B.brokenAssignment.second.partner s)) ∈ D.fam (P.label s) at hA
  rw [B.secondBrokenConnectors_partnerStart_vertex s hsBroken] at hA
  have hB := orientedEdgeIndex_start_mem D B.firstBase B.chord_geodesic.1
    (B.firstGapChordStart_le j) hedge (B.secondPartner_chord_isComp s hsBroken)
  rw [B.firstGapChordSource_vertex j s]
  convert (D.fam (P.label s)).mul_mem hA hB using 1
  group

/-- A wrapped target cannot meet either endpoint of a same-label first-arc
letter. The source and opponent are read in the same rotated parent polygon. -/
theorem secondTarget_not_connected_firstArc_letter
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ B.secondTarget) {m z : ℕ}
    (hm : m < B.firstArc.length) (hmz : m ≤ z) (hzm : z ≤ m + 1)
    (hletter : (B.firstArc[m]'hm).IsCompOf (P.label s)) :
    ¬ (vertex B.secondBase B.secondWord (B.secondTargetPos s))⁻¹ *
      vertex B.firstBase B.firstArc z ∈ D.fam (P.label s) := by
  intro hconn
  have hrot := B.rotWord_eq_secondArc_append_firstArc
  have hrotLen : (rotWord P.word B.secondVertex).length =
      B.secondArc.length + B.firstArc.length := by rw [hrot, List.length_append]
  have hposLt : B.secondTargetPos s < B.secondArc.length := by
    rw [B.secondArc_length_eq]
    exact B.secondTargetPos_lt hs
  have hmlt : B.secondArc.length + m < (rotWord P.word B.secondVertex).length := by omega
  have hletterRot : ((rotWord P.word B.secondVertex)[B.secondArc.length + m]'hmlt).IsCompOf
      (P.label s) := by
    rw [List.getElem_of_eq hrot hmlt, List.getElem_append_right (by omega),
      getElem_congr_idx (c := B.firstArc) (show B.secondArc.length + m - B.secondArc.length = m by omega)]
    exact hletter
  have hsource : vertex B.secondBase (rotWord P.word B.secondVertex) (B.secondTargetPos s) =
      vertex B.secondBase B.secondWord (B.secondTargetPos s) := by
    rw [hrot, B.secondWord_eq_append, vertex_append_left _ _ _ hposLt.le,
      vertex_append_left _ _ _ hposLt.le]
  have hconnRot : Connected D.fam (P.label s) B.secondBase (rotWord P.word B.secondVertex)
      (B.secondTargetPos s) (B.secondArc.length + z) := by
    change _ ∈ D.fam (P.label s)
    rwa [hsource, hrot, vertex_append_add, B.secondArc_endpoint]
  exact B.secondTarget_not_isCompOf_of_connected s hs _ _ hmlt
    (by omega) (by omega) (by omega) (by omega) hconnRot hletterRot

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapChordSource_anchor_mem
#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondTarget_not_connected_firstArc_letter
