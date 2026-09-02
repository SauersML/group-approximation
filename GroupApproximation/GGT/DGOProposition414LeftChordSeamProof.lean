import GroupApproximation.GGT.DGOProposition414ArcChordSeamProofWrapped

/-!
# The degenerate left-connector seam of a Proposition 4.14 gap child

When the inherited arc and the right connector of a gap child are both empty,
the auxiliary cycle is the reversed left connector `e_{j-1}^{-1}` followed by
the child chord, and the maximality of `e_{j-1}` turns on the first chord
letter.  Dahmani--Guirardel--Osin exclude it with

> If `f_j` or `e_j` is connected to a component `x` of a side of type (5),
> i.e., to a component of `t`, then `y_j` is connected to `x`.  This
> contradicts the assumption that `t` is geodesic.

(arXiv:1111.7048, proof of Proposition 4.14).  The formal shape is cheaper
than the source's: the closure identity `firstGap_prefix_endpoint` already
says that in this degenerate configuration the connector spells the span
between the two named chord vertices, so the connector's own peripheral label
makes those two chord vertices connected, and a same-label first chord letter
would give two distinct connected components of the geodesic chord.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- A forward child segment opens with the letter at its start index. -/
theorem isCompOf_head_orientedSegment_forward_iff
    (lam : Λ) (word : List (RelLetter G Λ)) {cs cf : ℕ}
    (hle : cs ≤ cf) (hcs : cs < word.length)
    (hseg : 0 < (orientedSegment word cs cf).length) :
    ((orientedSegment word cs cf)[0]'hseg).IsCompOf lam ↔
      (word[cs]'hcs).IsCompOf lam := by
  have heq : orientedSegment word cs cf = (word.drop cs).take (cf - cs) := by
    rw [orientedSegment, if_pos hle]
  rw [List.getElem_of_eq heq hseg]
  simp

namespace BalancedSplitData

/-! ## The left connector of a first-half gap -/

/-- A forward first-half gap opens with the end connector of its preceding
broken source. -/
theorem firstGapLeft_of_prev_forward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (p : Fin B.brokenAssignment.index.first.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.first j = some p)
    (hfwd : B.firstGapRunsForward j) :
    B.firstGapLeft j =
      (B.firstBrokenConnectors
        (HalfEntry.entrySource B.brokenAssignment.index.first p)
        (HalfEntry.entrySource_mem
          B.brokenAssignment.index.first p)).endConnector := by
  classical
  simp only [firstGapLeft]
  rw [hp]
  simp [hfwd]

/-- A backward first-half gap opens with the compressed through-partner end
connector of its preceding broken source. -/
theorem firstGapLeft_of_prev_backward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (p : Fin B.brokenAssignment.index.first.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.first j = some p)
    (hfwd : ¬ B.firstGapRunsForward j) :
    B.firstGapLeft j =
      (B.firstBrokenConnectors
        (HalfEntry.entrySource B.brokenAssignment.index.first p)
        (HalfEntry.entrySource_mem
          B.brokenAssignment.index.first p)).endThroughPartner := by
  classical
  simp only [firstGapLeft]
  rw [hp]
  simp [hfwd]

/-- Every letter of a first-half left connector carries the label of the
preceding broken source. -/
theorem firstGapLeft_label
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (p : Fin B.brokenAssignment.index.first.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.first j = some p) :
    ∀ x ∈ B.firstGapLeft j,
      x.IsCompOf (P.label (HalfEntry.entrySource
        B.brokenAssignment.index.first p)) := by
  classical
  by_cases hfwd : B.firstGapRunsForward j
  · rw [B.firstGapLeft_of_prev_forward j p hp hfwd]
    exact (B.firstBrokenConnectors
      (HalfEntry.entrySource B.brokenAssignment.index.first p)
      (HalfEntry.entrySource_mem
        B.brokenAssignment.index.first p)).end_label
  · rw [B.firstGapLeft_of_prev_backward j p hp hfwd]
    exact ComponentConnectorPair.endThroughPartner_label
      (B.firstBrokenConnectors
        (HalfEntry.entrySource B.brokenAssignment.index.first p)
        (HalfEntry.entrySource_mem B.brokenAssignment.index.first p))

/-- A forward first-half gap has a following broken entry. -/
theorem firstGapRunsForward_nextEntry_isSome
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (hfwd : B.firstGapRunsForward j) :
    HalfGap.nextEntry B.brokenAssignment.index.first j ≠ none := by
  intro hnone
  cases hp : HalfGap.previousEntry B.brokenAssignment.index.first j with
  | none => simp only [firstGapRunsForward, hp] at hfwd
  | some p => simp only [firstGapRunsForward, hp, hnone] at hfwd

/-! ## The seam, closed -/

/-- The residual chord seam of the left-connector maximality clause holds
outright whenever the connector is present. -/
theorem firstGapLeftConnectorChordSeam_of_left
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (hzero : 0 < (B.firstGapLeft j).length) :
    FirstGapLeftConnectorChordSeam B j := by
  classical
  intro hA0 hR0 hn hletter
  have hone : (B.firstGapLeft j).length = 1 := by
    have hle := B.firstGapLeft_length_le_one j
    omega
  have hprevNe : HalfGap.previousEntry B.brokenAssignment.index.first j
      ≠ none := by
    intro hnone
    have h0 : (B.firstGapLeft j).length = 0 := by
      simp only [firstGapLeft]
      rw [hnone]
      simp
    omega
  obtain ⟨p, hp'⟩ := Option.ne_none_iff_exists'.mp hprevNe
  have hp : HalfGap.previousEntry B.brokenAssignment.index.first j =
      some p := by simpa using hp'
  have hpBroken := HalfEntry.entrySource_mem B.brokenAssignment.index.first p
  have hlab : B.firstGapLocalLabel j 0 =
      P.label (HalfEntry.entrySource B.brokenAssignment.index.first p) :=
    B.firstGapLocalLabel_leftConnector j p hp 0 hzero
  rw [hlab] at hletter
  -- the degenerate cycle is the reversed connector followed by the chord
  have hArcNil : arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j) = [] := List.length_eq_zero_iff.mp hA0
  have hRightNil : B.firstGapRight j = [] := List.length_eq_zero_iff.mp hR0
  have hcycleLen : (B.firstGapCycle j).length =
      (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length +
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)).length := by
    simp only [firstGapCycle, auxiliaryCycleWord, List.length_append,
      OsinComponents.length_revWord]
  have hsegPos : 0 < (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j)).length := by omega
  have hn' : (B.firstGapLeft j).length +
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)).length +
      (B.firstGapRight j).length + 0 < (B.firstGapCycle j).length := by omega
  have hgetEq : (B.firstGapCycle j)[1]'hn =
      (B.firstGapCycle j)[(B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length + 0]'hn' :=
    getElem_congr_idx (by omega)
  rw [hgetEq] at hletter
  have hchordHead := (isCompOf_auxiliaryCycle_chord_iff
    (P.label (HalfEntry.entrySource B.brokenAssignment.index.first p))
    (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)) (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j)) 0 hsegPos hn').mp hletter
  -- the connector spells the span between the two named chord vertices
  have hclose := B.firstGap_prefix_endpoint j
  rw [hArcNil, hRightNil] at hclose
  simp only [List.append_nil, listVal_revWord] at hclose
  have hleftMem : RelLetter.listVal (B.firstGapLeft j) ∈
      D.fam (P.label (HalfEntry.entrySource
        B.brokenAssignment.index.first p)) :=
    listVal_mem_fam_of_isCompOf D _ _ (B.firstGapLeft_letters j)
      (B.firstGapLeft_label j p hp)
  have hconnB : Connected D.fam
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.first p))
      B.firstBase B.chord (B.firstGapChordFinish j)
      (B.firstGapChordStart j) := by
    show (vertex B.firstBase B.chord (B.firstGapChordFinish j))⁻¹ *
      vertex B.firstBase B.chord (B.firstGapChordStart j) ∈ D.fam _
    rw [← hclose]
    have hfac : (vertex B.firstBase B.chord (B.firstGapChordFinish j))⁻¹ *
        (vertex B.firstBase B.chord (B.firstGapChordFinish j) *
          (RelLetter.listVal (B.firstGapLeft j))⁻¹) =
        (RelLetter.listVal (B.firstGapLeft j))⁻¹ := by group
    rw [hfac]
    exact inv_mem hleftMem
  -- the partner edge of the preceding source
  have hpartnerLt : B.brokenAssignment.first.partner
      (HalfEntry.entrySource B.brokenAssignment.index.first p) <
      B.chord.length :=
    B.brokenAssignment.first.partner_lt _ hpBroken
  have hcompY := B.firstPartner_chord_isComp
    (HalfEntry.entrySource B.brokenAssignment.index.first p) hpBroken
  have hspanY : Connected D.fam
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.first p))
      B.firstBase B.chord
      (B.brokenAssignment.first.partner
        (HalfEntry.entrySource B.brokenAssignment.index.first p))
      (B.brokenAssignment.first.partner
        (HalfEntry.entrySource B.brokenAssignment.index.first p) + 1) :=
    span_mem_fam_of_isComp D B.firstBase B.chord_geodesic.1 hcompY
  have hstartLe : B.firstGapChordStart j ≤ B.chord.length :=
    B.firstGapChordStart_le j
  -- which chord vertex the child chord ends at
  have hfinishVal :
      (B.firstGapRunsForward j ∧ B.firstGapChordFinish j =
        B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first p)) ∨
      (¬ B.firstGapRunsForward j ∧ B.firstGapChordFinish j =
        B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first p) + 1) := by
    by_cases hfwd : B.firstGapRunsForward j
    · exact Or.inl ⟨hfwd, B.firstGapChordFinish_of_prev_forward j p hp hfwd⟩
    · exact Or.inr ⟨hfwd, B.firstGapChordFinish_of_prev_backward j p hp hfwd⟩
  have hconnC : Connected D.fam
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.first p))
      B.firstBase B.chord (B.firstGapChordFinish j)
      (B.brokenAssignment.first.partner
        (HalfEntry.entrySource B.brokenAssignment.index.first p)) := by
    rcases hfinishVal with ⟨-, heq⟩ | ⟨-, heq⟩
    · rw [heq]
      exact connected_refl _ _ _ _ _
    · rw [heq]
      exact connected_symm hspanY
  -- the head of the child chord, and the contradiction with geodesicity
  by_cases hdir : B.firstGapChordStart j ≤ B.firstGapChordFinish j
  · have hcs : B.firstGapChordStart j < B.chord.length := by
      by_contra hcon
      have hzero : (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)).length = 0 := by
        rw [orientedSegment, if_pos hdir, List.length_take, List.length_drop]
        omega
      omega
    have hlt : B.firstGapChordStart j < B.firstGapChordFinish j := by
      rcases Nat.lt_or_ge (B.firstGapChordStart j) (B.firstGapChordFinish j)
        with hlt | hge
      · exact hlt
      · exfalso
        have hzero : (orientedSegment B.chord (B.firstGapChordStart j)
            (B.firstGapChordFinish j)).length = 0 := by
          rw [orientedSegment, if_pos hdir, List.length_take, List.length_drop]
          omega
        omega
    have hhead := (isCompOf_head_orientedSegment_forward_iff
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.first p))
      B.chord hdir hcs hsegPos).mp hchordHead
    have hcompHead := isComp_of_isCompOf_geodesic D
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.first p))
      B.chord_geodesic hcs hhead
    have hne : B.firstGapChordStart j ≠
        B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first p) := by
      rcases hfinishVal with ⟨-, heq⟩ | ⟨hfwd, heq⟩
      · omega
      · intro hEq
        obtain ⟨e, he'⟩ := Option.ne_none_iff_exists'.mp
          (by
            intro hnone
            have hcs' : B.firstGapChordStart j = B.chord.length := by
              simp only [firstGapChordStart]
              rw [hnone]
            omega :
            HalfGap.nextEntry B.brokenAssignment.index.first j ≠ none)
        have he : HalfGap.nextEntry B.brokenAssignment.index.first j =
            some e := by simpa using he'
        have hstartEq := B.firstGapChordStart_of_next_backward j e he hfwd
        have hpartnerEq : B.brokenAssignment.first.partner
            (HalfEntry.entrySource B.brokenAssignment.index.first p) =
            B.brokenAssignment.first.partner
              (HalfEntry.entrySource
                B.brokenAssignment.index.first e) := by omega
        exact HalfGap.entrySource_ne_of_adjacent
          B.brokenAssignment.index.first j hp he
          (B.brokenAssignment.first.partner_injective hpBroken
            (HalfEntry.entrySource_mem B.brokenAssignment.index.first e)
            hpartnerEq)
    exact not_connected_of_isCompStart_of_geodesic D B.chord_geodesic
      ⟨_, hcompHead⟩ ⟨_, hcompY⟩ hne
      (connected_trans (connected_symm hconnB) hconnC)
  · have hlt : B.firstGapChordFinish j < B.firstGapChordStart j := by omega
    have hpos : 0 < B.firstGapChordStart j := by omega
    have hcs : B.firstGapChordStart j - 1 < B.chord.length := by omega
    have hhead := (isCompOf_head_orientedSegment_pred_iff
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.first p))
      B.chord (by omega) hstartLe hcs hsegPos).mp hchordHead
    have hcompHead := isComp_of_isCompOf_geodesic D
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.first p))
      B.chord_geodesic hcs hhead
    have hheadSpan : Connected D.fam
        (P.label (HalfEntry.entrySource B.brokenAssignment.index.first p))
        B.firstBase B.chord (B.firstGapChordStart j - 1)
        (B.firstGapChordStart j - 1 + 1) :=
      span_mem_fam_of_isComp D B.firstBase B.chord_geodesic.1 hcompHead
    have hheadConn : Connected D.fam
        (P.label (HalfEntry.entrySource B.brokenAssignment.index.first p))
        B.firstBase B.chord (B.firstGapChordStart j - 1)
        (B.firstGapChordStart j) := by
      have hidx : B.firstGapChordStart j - 1 + 1 =
          B.firstGapChordStart j := by omega
      rw [← hidx]
      exact hheadSpan
    have hne : B.firstGapChordStart j - 1 ≠
        B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first p) := by
      rcases hfinishVal with ⟨hfwd, heq⟩ | ⟨-, heq⟩
      · intro hEq
        obtain ⟨e, he'⟩ := Option.ne_none_iff_exists'.mp
          (B.firstGapRunsForward_nextEntry_isSome j hfwd)
        have he : HalfGap.nextEntry B.brokenAssignment.index.first j =
            some e := by simpa using he'
        have hstartEq := B.firstGapChordStart_of_next_forward j e he hfwd
        have hpartnerEq : B.brokenAssignment.first.partner
            (HalfEntry.entrySource B.brokenAssignment.index.first p) =
            B.brokenAssignment.first.partner
              (HalfEntry.entrySource
                B.brokenAssignment.index.first e) := by omega
        exact HalfGap.entrySource_ne_of_adjacent
          B.brokenAssignment.index.first j hp he
          (B.brokenAssignment.first.partner_injective hpBroken
            (HalfEntry.entrySource_mem B.brokenAssignment.index.first e)
            hpartnerEq)
      · omega
    exact not_connected_of_isCompStart_of_geodesic D B.chord_geodesic
      ⟨_, hcompHead⟩ ⟨_, hcompY⟩ hne
      (connected_trans hheadConn
        (connected_trans (connected_symm hconnB) hconnC))

/-! ## The left connector component field -/

/-- The `leftComponent` field of `FirstGapComponentFamily`, with no residual
hypothesis. -/
theorem firstGapLeftComponentField
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (r : ℕ) (hr : r < (B.firstGapLeft j).length) :
    IsComp (B.firstGapLocalLabel j r) (B.firstGapCycle j)
      (B.firstGapCut j r) (B.firstGapCut j (r + 1)) :=
  B.firstGap_leftComponent j r hr
    (B.firstGapLeftConnectorChordSeam_of_left j (by omega))

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
