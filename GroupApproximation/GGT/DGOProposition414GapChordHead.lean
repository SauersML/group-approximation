import GroupApproximation.GGT.DGOProposition414ArcTerminalSeam

/-!
# The head of the oriented child chord of a Proposition 4.14 gap

Each auxiliary cycle `c_j` of Dahmani--Guirardel--Osin's Proposition 4.14 ends
with a segment of the cutting chord `t`, read from one endpoint of the partner
edge `y_j` of the following broken source `p_{i_j}`.  Which endpoint, and which
direction, is recorded by `firstGapRunsForward`.  This file resolves that
branch and concludes, in every case, that the first letter of the child chord
does not carry the label of `p_{i_j}`: the partner edge is its own maximal
component of the geodesic chord, and the child chord starts on its far side.

That is DGO's

> if `f_j` or `e_j` is connected to `f_k`, `e_k`, or `y_k` for `k \ne j`, then
> `p_{i_j}` is connected to `p_{i_k}` and we get a contradiction

specialized to the one letter at the connector/chord seam (arXiv:1111.7048,
proof of Proposition 4.14).
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace HalfGap

/-- The two greedy entries adjacent to one gap are distinct list positions, so
they carry distinct broken sources. -/
theorem entrySource_ne_of_adjacent
    {I : Finset ℕ} {pos partner : ℕ → ℕ} {L : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner L) (j : Fin A.pieceCount)
    {p e : Fin A.sources.length}
    (hp : previousEntry A j = some p) (he : nextEntry A j = some e) :
    HalfEntry.entrySource A p ≠ HalfEntry.entrySource A e := by
  classical
  have hjpos : 0 < j.val := by
    rcases Nat.eq_zero_or_pos j.val with h0 | hpos
    · exfalso
      have hnone := (previousEntry_eq_none_iff A j).mpr h0
      rw [hp] at hnone
      simp at hnone
    · exact hpos
  have hjbound : j.val < A.sources.length + 1 := by
    have hj := j.isLt
    simpa only [GreedyHalfFamilyIndex.pieceCount] using hj
  have hpval : p.val = j.val - 1 := by
    have hdef : previousEntry A j = some ⟨j.val - 1, by omega⟩ := by
      simp [previousEntry, hjpos]
    rw [hp] at hdef
    exact congrArg Fin.val (Option.some.inj hdef)
  have hjlt : j.val < A.sources.length := by
    rcases Nat.lt_or_ge j.val A.sources.length with hlt | hge
    · exact hlt
    · exfalso
      have heq : j.val = A.sources.length := by omega
      have hnone := (nextEntry_eq_none_iff A j).mpr heq
      rw [he] at hnone
      simp at hnone
  have heval : e.val = j.val := by
    have hdef : nextEntry A j = some ⟨j.val, hjlt⟩ := by
      simp [nextEntry, hjlt]
    rw [he] at hdef
    exact congrArg Fin.val (Option.some.inj hdef)
  have hlt : p.val < e.val := by omega
  have hne : A.sources[p] ≠ A.sources[e] :=
    List.pairwise_iff_getElem.mp A.source_nodup p.val e.val p.isLt e.isLt hlt
  intro hEq
  apply hne
  rw [HalfEntry.source_getElem_eq_pos_entrySource A p,
    HalfEntry.source_getElem_eq_pos_entrySource A e, hEq]

end HalfGap

namespace BalancedSplitData

/-! ## Resolving the orientation branch of a first-half gap -/

/-- A forward first-half gap has a preceding broken entry. -/
theorem firstGapRunsForward_previousEntry_isSome
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (hfwd : B.firstGapRunsForward j) :
    HalfGap.previousEntry B.brokenAssignment.index.first j ≠ none := by
  intro hnone
  simp only [firstGapRunsForward, hnone] at hfwd

/-- The orientation flag of an interior first-half gap compares the two
adjacent chord partners. -/
theorem firstGapRunsForward_iff_of_adjacent
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (p e : Fin B.brokenAssignment.index.first.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.first j = some p)
    (he : HalfGap.nextEntry B.brokenAssignment.index.first j = some e) :
    B.firstGapRunsForward j ↔
      B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first e) <
        B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first p) := by
  simp only [firstGapRunsForward, hp, he]

/-- A forward first-half gap leaves the chord at the far end of the next
partner edge. -/
theorem firstGapChordStart_of_next_forward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.first j = some e)
    (hfwd : B.firstGapRunsForward j) :
    B.firstGapChordStart j =
      B.brokenAssignment.first.partner
        (HalfEntry.entrySource B.brokenAssignment.index.first e) + 1 := by
  classical
  simp only [firstGapChordStart]
  rw [he]
  simp [hfwd]

/-- A backward first-half gap leaves the chord at the near end of the next
partner edge, the connector having absorbed that edge. -/
theorem firstGapChordStart_of_next_backward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.first j = some e)
    (hfwd : ¬ B.firstGapRunsForward j) :
    B.firstGapChordStart j =
      B.brokenAssignment.first.partner
        (HalfEntry.entrySource B.brokenAssignment.index.first e) := by
  classical
  simp only [firstGapChordStart]
  rw [he]
  simp [hfwd]

/-- The initial first-half gap reaches the initial chord endpoint. -/
theorem firstGapChordFinish_of_prev_none
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.first j = none) :
    B.firstGapChordFinish j = 0 := by
  classical
  simp only [firstGapChordFinish]
  rw [hp]

/-- A forward interior first-half gap reaches the near end of the previous
partner edge. -/
theorem firstGapChordFinish_of_prev_forward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (p : Fin B.brokenAssignment.index.first.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.first j = some p)
    (hfwd : B.firstGapRunsForward j) :
    B.firstGapChordFinish j =
      B.brokenAssignment.first.partner
        (HalfEntry.entrySource B.brokenAssignment.index.first p) := by
  classical
  simp only [firstGapChordFinish]
  rw [hp]
  simp [hfwd]

/-- A backward interior first-half gap reaches the far end of the previous
partner edge. -/
theorem firstGapChordFinish_of_prev_backward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (p : Fin B.brokenAssignment.index.first.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.first j = some p)
    (hfwd : ¬ B.firstGapRunsForward j) :
    B.firstGapChordFinish j =
      B.brokenAssignment.first.partner
        (HalfEntry.entrySource B.brokenAssignment.index.first p) + 1 := by
  classical
  simp only [firstGapChordFinish]
  rw [hp]
  simp [hfwd]

/-! ## The chord head never carries the next entry's label -/

/-- The first letter of the oriented child chord of a first-half gap with a
following broken entry does not carry that entry's peripheral label.  The
child chord is anchored at one end of the partner edge, which is a maximal
component of the geodesic chord, so the letter on its far side has a different
label. -/
theorem firstGap_chordHead_not_isCompOf_nextEntry
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.first j = some e)
    (hseg : 0 < (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j)).length) :
    ¬ ((orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j))[0]'hseg).IsCompOf
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.first e)) := by
  classical
  intro hletter
  have htBroken := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
  have hcomp := B.firstPartner_chord_isComp
    (HalfEntry.entrySource B.brokenAssignment.index.first e) htBroken
  by_cases hfwd : B.firstGapRunsForward j
  · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp
      (B.firstGapRunsForward_previousEntry_isSome j hfwd)
    have hlt := (B.firstGapRunsForward_iff_of_adjacent j p e hp he).mp hfwd
    have hsegEq : orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j) =
        orientedSegment B.chord
          (B.brokenAssignment.first.partner
            (HalfEntry.entrySource B.brokenAssignment.index.first e) + 1)
          (B.brokenAssignment.first.partner
            (HalfEntry.entrySource B.brokenAssignment.index.first p)) := by
      rw [B.firstGapChordStart_of_next_forward j e he hfwd,
        B.firstGapChordFinish_of_prev_forward j p hp hfwd]
    have hseg' : 0 < (orientedSegment B.chord
        (B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first e) + 1)
        (B.brokenAssignment.first.partner
          (HalfEntry.entrySource
            B.brokenAssignment.index.first p))).length := by
      rw [← hsegEq]
      exact hseg
    rw [List.getElem_of_eq hsegEq hseg] at hletter
    exact not_isCompOf_head_orientedSegment_succ _ B.chord hcomp (by omega)
      hseg' hletter
  · have hfinishLe : B.firstGapChordFinish j ≤
        B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first e) := by
      cases hp : HalfGap.previousEntry B.brokenAssignment.index.first j with
      | none =>
          rw [B.firstGapChordFinish_of_prev_none j hp]
          exact Nat.zero_le _
      | some p =>
          have hnotlt : ¬ (B.brokenAssignment.first.partner
              (HalfEntry.entrySource B.brokenAssignment.index.first e) <
              B.brokenAssignment.first.partner
                (HalfEntry.entrySource B.brokenAssignment.index.first p)) := by
            intro hlt
            exact hfwd
              ((B.firstGapRunsForward_iff_of_adjacent j p e hp he).mpr hlt)
          have hpBroken := HalfEntry.entrySource_mem
            B.brokenAssignment.index.first p
          have hpartnerNe : B.brokenAssignment.first.partner
              (HalfEntry.entrySource B.brokenAssignment.index.first p) ≠
              B.brokenAssignment.first.partner
                (HalfEntry.entrySource B.brokenAssignment.index.first e) := by
            intro hEq
            exact HalfGap.entrySource_ne_of_adjacent
              B.brokenAssignment.index.first j hp he
              (B.brokenAssignment.first.partner_injective hpBroken htBroken hEq)
          rw [B.firstGapChordFinish_of_prev_backward j p hp hfwd]
          omega
    have hsegEq : orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j) =
        orientedSegment B.chord
          (B.brokenAssignment.first.partner
            (HalfEntry.entrySource B.brokenAssignment.index.first e))
          (B.firstGapChordFinish j) := by
      rw [B.firstGapChordStart_of_next_backward j e he hfwd]
    have hseg' : 0 < (orientedSegment B.chord
        (B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first e))
        (B.firstGapChordFinish j)).length := by
      rw [← hsegEq]
      exact hseg
    rw [List.getElem_of_eq hsegEq hseg] at hletter
    exact not_isCompOf_head_orientedSegment_pred _ B.chord hcomp hfinishLe
      hseg' hletter

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
