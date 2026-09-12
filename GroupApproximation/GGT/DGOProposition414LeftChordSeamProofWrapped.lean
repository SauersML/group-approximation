import GroupApproximation.GGT.DGOProposition414LeftChordSeamProof

/-!
# The degenerate left-connector seam of a wrapped Proposition 4.14 gap child

Wrapped counterpart of `DGOProposition414LeftChordSeamProof`.  The wrapped half
exchanges which of the two compressed connectors each orientation uses, and its
boundary children take the opposite default orientation, but the argument is
the same: in the degenerate configuration the connector spells the span between
the two named chord vertices, so a same-label first chord letter would connect
two distinct components of the geodesic chord.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-! ## The left connector of a wrapped gap -/

/-- A forward wrapped gap opens with the compressed through-partner end
connector of its preceding broken source. -/
theorem secondGapLeft_of_prev_forward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (p : Fin B.brokenAssignment.index.second.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.second j = some p)
    (hfwd : B.secondGapRunsForward j) :
    B.secondGapLeft j =
      (B.secondBrokenConnectors
        (HalfEntry.entrySource B.brokenAssignment.index.second p)
        (HalfEntry.entrySource_mem
          B.brokenAssignment.index.second p)).endThroughPartner := by
  classical
  simp only [secondGapLeft]
  rw [hp]
  simp [hfwd]

/-- A backward wrapped gap opens with the end connector of its preceding
broken source. -/
theorem secondGapLeft_of_prev_backward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (p : Fin B.brokenAssignment.index.second.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.second j = some p)
    (hfwd : ¬ B.secondGapRunsForward j) :
    B.secondGapLeft j =
      (B.secondBrokenConnectors
        (HalfEntry.entrySource B.brokenAssignment.index.second p)
        (HalfEntry.entrySource_mem
          B.brokenAssignment.index.second p)).endConnector := by
  classical
  simp only [secondGapLeft]
  rw [hp]
  simp [hfwd]

/-- Every letter of a wrapped left connector carries the label of the
preceding broken source. -/
theorem secondGapLeft_label
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (p : Fin B.brokenAssignment.index.second.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.second j = some p) :
    ∀ x ∈ B.secondGapLeft j,
      x.IsCompOf (P.label (HalfEntry.entrySource
        B.brokenAssignment.index.second p)) := by
  classical
  by_cases hfwd : B.secondGapRunsForward j
  · rw [B.secondGapLeft_of_prev_forward j p hp hfwd]
    exact ComponentConnectorPair.endThroughPartner_label
      (B.secondBrokenConnectors
        (HalfEntry.entrySource B.brokenAssignment.index.second p)
        (HalfEntry.entrySource_mem B.brokenAssignment.index.second p))
  · rw [B.secondGapLeft_of_prev_backward j p hp hfwd]
    exact (B.secondBrokenConnectors
      (HalfEntry.entrySource B.brokenAssignment.index.second p)
      (HalfEntry.entrySource_mem
        B.brokenAssignment.index.second p)).end_label

/-- A backward wrapped gap has a following broken entry. -/
theorem secondGapNotRunsForward_nextEntry_isSome
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (hfwd : ¬ B.secondGapRunsForward j) :
    HalfGap.nextEntry B.brokenAssignment.index.second j ≠ none := by
  intro hnone
  apply hfwd
  cases hp : HalfGap.previousEntry B.brokenAssignment.index.second j with
  | none => simp only [secondGapRunsForward, hp]
  | some p => simp only [secondGapRunsForward, hp, hnone]

/-! ## The wrapped seam, closed -/

/-- Wrapped counterpart of `firstGapLeftConnectorChordSeam_of_left`. -/
theorem secondGapLeftConnectorChordSeam_of_left
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (hzero : 0 < (B.secondGapLeft j).length) :
    SecondGapLeftConnectorChordSeam B j := by
  classical
  intro hA0 hR0 hn hletter
  have hone : (B.secondGapLeft j).length = 1 := by
    have hle := B.secondGapLeft_length_le_one j
    omega
  have hprevNe : HalfGap.previousEntry B.brokenAssignment.index.second j
      ≠ none := by
    intro hnone
    have h0 : (B.secondGapLeft j).length = 0 := by
      simp only [secondGapLeft]
      rw [hnone]
      simp
    omega
  obtain ⟨p, hp'⟩ := Option.ne_none_iff_exists'.mp hprevNe
  have hp : HalfGap.previousEntry B.brokenAssignment.index.second j =
      some p := by simpa using hp'
  have hpBroken := HalfEntry.entrySource_mem B.brokenAssignment.index.second p
  have hlab : B.secondGapLocalLabel j 0 =
      P.label (HalfEntry.entrySource B.brokenAssignment.index.second p) :=
    B.secondGapLocalLabel_leftConnector j p hp 0 hzero
  rw [hlab] at hletter
  have hArcNil : arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j) = [] := List.length_eq_zero_iff.mp hA0
  have hRightNil : B.secondGapRight j = [] := List.length_eq_zero_iff.mp hR0
  have hcycleLen : (B.secondGapCycle j).length =
      (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length +
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)).length := by
    simp only [secondGapCycle, auxiliaryCycleWord, List.length_append,
      OsinComponents.length_revWord]
  have hsegPos : 0 < (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)).length := by omega
  have hn' : (B.secondGapLeft j).length +
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)).length +
      (B.secondGapRight j).length + 0 <
      (B.secondGapCycle j).length := by omega
  have hgetEq : (B.secondGapCycle j)[1]'hn =
      (B.secondGapCycle j)[(B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length + 0]'hn' :=
    getElem_congr_idx (by omega)
  rw [hgetEq] at hletter
  have hchordHead := (isCompOf_auxiliaryCycle_chord_iff
    (P.label (HalfEntry.entrySource B.brokenAssignment.index.second p))
    (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)) (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)) 0 hsegPos hn').mp hletter
  have hclose := B.secondGap_prefix_endpoint j
  rw [hArcNil, hRightNil] at hclose
  simp only [List.append_nil, listVal_revWord] at hclose
  have hleftMem : RelLetter.listVal (B.secondGapLeft j) ∈
      D.fam (P.label (HalfEntry.entrySource
        B.brokenAssignment.index.second p)) :=
    listVal_mem_fam_of_isCompOf D _ _ (B.secondGapLeft_letters j)
      (B.secondGapLeft_label j p hp)
  have hconnB : Connected D.fam
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.second p))
      B.firstBase B.chord (B.secondGapChordFinish j)
      (B.secondGapChordStart j) := by
    show (vertex B.firstBase B.chord (B.secondGapChordFinish j))⁻¹ *
      vertex B.firstBase B.chord (B.secondGapChordStart j) ∈ D.fam _
    rw [← hclose]
    have hfac : (vertex B.firstBase B.chord (B.secondGapChordFinish j))⁻¹ *
        (vertex B.firstBase B.chord (B.secondGapChordFinish j) *
          (RelLetter.listVal (B.secondGapLeft j))⁻¹) =
        (RelLetter.listVal (B.secondGapLeft j))⁻¹ := by group
    rw [hfac]
    exact inv_mem hleftMem
  have hpartnerLt : B.brokenAssignment.second.partner
      (HalfEntry.entrySource B.brokenAssignment.index.second p) <
      B.chord.length :=
    B.brokenAssignment.second.partner_lt _ hpBroken
  have hcompY := B.secondPartner_chord_isComp
    (HalfEntry.entrySource B.brokenAssignment.index.second p) hpBroken
  have hspanY : Connected D.fam
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.second p))
      B.firstBase B.chord
      (B.brokenAssignment.second.partner
        (HalfEntry.entrySource B.brokenAssignment.index.second p))
      (B.brokenAssignment.second.partner
        (HalfEntry.entrySource B.brokenAssignment.index.second p) + 1) :=
    span_mem_fam_of_isComp D B.firstBase B.chord_geodesic.1 hcompY
  have hstartLe : B.secondGapChordStart j ≤ B.chord.length :=
    B.secondGapChordStart_le j
  have hfinishVal :
      (B.secondGapRunsForward j ∧ B.secondGapChordFinish j =
        B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second p)) ∨
      (¬ B.secondGapRunsForward j ∧ B.secondGapChordFinish j =
        B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second p) + 1) := by
    by_cases hfwd : B.secondGapRunsForward j
    · exact Or.inl ⟨hfwd, B.secondGapChordFinish_of_prev_forward j p hp hfwd⟩
    · exact Or.inr ⟨hfwd, B.secondGapChordFinish_of_prev_backward j p hp hfwd⟩
  have hconnC : Connected D.fam
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.second p))
      B.firstBase B.chord (B.secondGapChordFinish j)
      (B.brokenAssignment.second.partner
        (HalfEntry.entrySource B.brokenAssignment.index.second p)) := by
    rcases hfinishVal with ⟨-, heq⟩ | ⟨-, heq⟩
    · rw [heq]
      exact connected_refl _ _ _ _ _
    · rw [heq]
      exact connected_symm hspanY
  by_cases hdir : B.secondGapChordStart j ≤ B.secondGapChordFinish j
  · have hcs : B.secondGapChordStart j < B.chord.length := by
      by_contra hcon
      have hzero : (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)).length = 0 := by
        rw [orientedSegment, if_pos hdir, List.length_take, List.length_drop]
        omega
      omega
    have hlt : B.secondGapChordStart j < B.secondGapChordFinish j := by
      rcases Nat.lt_or_ge (B.secondGapChordStart j) (B.secondGapChordFinish j)
        with hlt | hge
      · exact hlt
      · exfalso
        have hzero : (orientedSegment B.chord (B.secondGapChordStart j)
            (B.secondGapChordFinish j)).length = 0 := by
          rw [orientedSegment, if_pos hdir, List.length_take, List.length_drop]
          omega
        omega
    have hhead := (isCompOf_head_orientedSegment_forward_iff
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.second p))
      B.chord hdir hcs hsegPos).mp hchordHead
    have hcompHead := isComp_of_isCompOf_geodesic D
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.second p))
      B.chord_geodesic hcs hhead
    have hne : B.secondGapChordStart j ≠
        B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second p) := by
      rcases hfinishVal with ⟨-, heq⟩ | ⟨hfwd, heq⟩
      · omega
      · intro hEq
        obtain ⟨e, he'⟩ := Option.ne_none_iff_exists'.mp
          (B.secondGapNotRunsForward_nextEntry_isSome j hfwd)
        have he : HalfGap.nextEntry B.brokenAssignment.index.second j =
            some e := by simpa using he'
        have hstartEq := B.secondGapChordStart_of_next_backward j e he hfwd
        have hpartnerEq : B.brokenAssignment.second.partner
            (HalfEntry.entrySource B.brokenAssignment.index.second p) =
            B.brokenAssignment.second.partner
              (HalfEntry.entrySource
                B.brokenAssignment.index.second e) := by omega
        exact HalfGap.entrySource_ne_of_adjacent
          B.brokenAssignment.index.second j hp he
          (B.brokenAssignment.second.partner_injective hpBroken
            (HalfEntry.entrySource_mem B.brokenAssignment.index.second e)
            hpartnerEq)
    exact not_connected_of_isCompStart_of_geodesic D B.chord_geodesic
      ⟨_, hcompHead⟩ ⟨_, hcompY⟩ hne
      (connected_trans (connected_symm hconnB) hconnC)
  · have hlt : B.secondGapChordFinish j < B.secondGapChordStart j := by omega
    have hpos : 0 < B.secondGapChordStart j := by omega
    have hcs : B.secondGapChordStart j - 1 < B.chord.length := by omega
    have hhead := (isCompOf_head_orientedSegment_pred_iff
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.second p))
      B.chord (by omega) hstartLe hcs hsegPos).mp hchordHead
    have hcompHead := isComp_of_isCompOf_geodesic D
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.second p))
      B.chord_geodesic hcs hhead
    have hheadSpan : Connected D.fam
        (P.label (HalfEntry.entrySource B.brokenAssignment.index.second p))
        B.firstBase B.chord (B.secondGapChordStart j - 1)
        (B.secondGapChordStart j - 1 + 1) :=
      span_mem_fam_of_isComp D B.firstBase B.chord_geodesic.1 hcompHead
    have hheadConn : Connected D.fam
        (P.label (HalfEntry.entrySource B.brokenAssignment.index.second p))
        B.firstBase B.chord (B.secondGapChordStart j - 1)
        (B.secondGapChordStart j) := by
      have hidx : B.secondGapChordStart j - 1 + 1 =
          B.secondGapChordStart j := by omega
      rw [← hidx]
      exact hheadSpan
    have hne : B.secondGapChordStart j - 1 ≠
        B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second p) := by
      rcases hfinishVal with ⟨hfwd, heq⟩ | ⟨-, heq⟩
      · intro hEq
        obtain ⟨e, he'⟩ := Option.ne_none_iff_exists'.mp
          (by
            intro hnone
            have hcs' : B.secondGapChordStart j = 0 := by
              simp only [secondGapChordStart]
              rw [hnone]
            omega :
            HalfGap.nextEntry B.brokenAssignment.index.second j ≠ none)
        have he : HalfGap.nextEntry B.brokenAssignment.index.second j =
            some e := by simpa using he'
        have hstartEq := B.secondGapChordStart_of_next_forward j e he hfwd
        have hpartnerEq : B.brokenAssignment.second.partner
            (HalfEntry.entrySource B.brokenAssignment.index.second p) =
            B.brokenAssignment.second.partner
              (HalfEntry.entrySource
                B.brokenAssignment.index.second e) := by omega
        exact HalfGap.entrySource_ne_of_adjacent
          B.brokenAssignment.index.second j hp he
          (B.brokenAssignment.second.partner_injective hpBroken
            (HalfEntry.entrySource_mem B.brokenAssignment.index.second e)
            hpartnerEq)
      · omega
    exact not_connected_of_isCompStart_of_geodesic D B.chord_geodesic
      ⟨_, hcompHead⟩ ⟨_, hcompY⟩ hne
      (connected_trans hheadConn
        (connected_trans (connected_symm hconnB) hconnC))

/-! ## The wrapped left connector component field -/

/-- The `leftComponent` field of `SecondGapComponentFamily`, with no residual
hypothesis. -/
theorem secondGapLeftComponentField
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (r : ℕ) (hr : r < (B.secondGapLeft j).length) :
    IsComp (B.secondGapLocalLabel j r) (B.secondGapCycle j)
      (B.secondGapCut j r) (B.secondGapCut j (r + 1)) :=
  B.secondGap_leftComponent j r hr
    (B.secondGapLeftConnectorChordSeam_of_left j (by omega))

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
