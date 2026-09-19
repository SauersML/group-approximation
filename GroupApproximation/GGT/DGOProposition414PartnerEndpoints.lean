import GroupApproximation.GGT.DGOProposition414ConnectorProducer
import GroupApproximation.GGT.DGOProposition414HalfCutPath

/-!
# Terminal chord coordinates of the canonical broken-component connectors

The partner named by the greedy assignment starts in the geodesic chord block
of a balanced half.  Although the whole half need not be geodesic, the suffix
from that start is: a component which starts in an appended geodesic word must
therefore have length one.  This pins the terminal vertex used by the compressed
entry and exit connectors to an exact global-chord coordinate.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- A component which starts inside an appended geodesic suffix has one edge.
Only the suffix is required to be geodesic. -/
theorem isComp_end_eq_succ_of_geodesic_suffix
    (D : RelGenSet G Λ) {lam : Λ} {f g : G}
    (pre suf : List (RelLetter G Λ))
    (hgeo : IsGeodesicWord D f g suf)
    {word : List (RelLetter G Λ)} {start i k : ℕ}
    (hword : word = pre ++ suf) (hstart : start = pre.length + i)
    (hi : i < suf.length)
    (hcomp : IsComp lam word start k) :
    k = pre.length + i + 1 := by
  subst word
  subst start
  have hletter : (suf[i]'hi).IsCompOf lam := by
    have htotal : pre.length + i < (pre ++ suf).length := by
      simpa only [List.length_append] using Nat.add_lt_add_left hi pre.length
    have h := hcomp.2.2.1 (pre.length + i) le_rfl hcomp.1 htotal
    simpa using h
  have hsingle := isComp_of_isCompOf_geodesic D lam hgeo hi hletter
  have hupper : k ≤ pre.length + i + 1 := by
    by_contra hnot
    have hiSucc : i + 1 < suf.length := by
      have hklen := hcomp.2.1
      simp only [List.length_append] at hklen
      omega
    have htotalSucc : pre.length + (i + 1) <
        (pre ++ suf).length := by
      simpa only [List.length_append] using
        Nat.add_lt_add_left hiSucc pre.length
    have happ := hcomp.2.2.1 (pre.length + (i + 1))
      (by omega) (by omega) htotalSucc
    have hsuffix : (suf[i + 1]'hiSucc).IsCompOf lam := by
      simpa [Nat.add_assoc] using happ
    exact hsingle.2.2.2.2 hiSucc hsuffix
  have hlower := hcomp.1
  omega

namespace BalancedSplitData

private theorem firstArc_length
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.firstArc.length = B.firstArcLength := by
  have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  rw [firstArc, length_arcWord P.word B.refinedCut]
  · simp [firstArcLength, hleft, hright]
  · rw [hright]
    exact B.secondVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))

private theorem secondArc_length
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.secondArc.length = B.secondArcLength := by
  have hfirstLe : B.firstVertex ≤ P.word.length :=
    B.firstVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr
        (B.side_order.trans B.secondSide_lt)))
  have hsecondLe : B.secondVertex ≤ P.word.length :=
    B.secondVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
  rw [secondArc, List.length_append, List.length_drop, List.length_take]
  simp only [min_eq_left hfirstLe, secondArcLength]

/-- In the first half, forward chord coordinate `y` is read backwards and its
one-edge component terminates at global chord vertex `y`. -/
theorem firstBrokenConnectors_partnerEnd
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    (B.firstBrokenConnectors s hs).partnerEnd =
      B.firstChordPos (B.brokenAssignment.first.partner s) + 1 := by
  let C := B.firstBrokenConnectors s hs
  simpa [C] using C.partner_end_eq

/-- In the wrapped half, forward chord coordinate `y` is read forwards and its
one-edge component terminates at global chord vertex `y + 1`. -/
theorem secondBrokenConnectors_partnerEnd
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    (B.secondBrokenConnectors s hs).partnerEnd =
      B.secondChordPos (B.brokenAssignment.second.partner s) + 1 := by
  let C := B.secondBrokenConnectors s hs
  simpa [C] using C.partner_end_eq

/-- The first inherited arc runs from the initial to the terminal chord
vertex. -/
theorem firstArc_endpoint
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.firstBase * RelLetter.listVal B.firstArc = B.secondBase := by
  have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  have hspan := listVal_arcWord P.word P.basepoint B.refinedCut
    (show B.refinedCut (B.firstSide + 1) ≤
        B.refinedCut (B.secondSide + 2) by
      rw [hleft, hright]
      exact B.split_vertices_ordered)
  rw [hleft, hright] at hspan
  simp only [firstBase, secondBase, firstArc]
  rw [hspan]
  group

/-- The wrapped inherited arc returns from the terminal to the initial chord
vertex. -/
theorem secondArc_endpoint
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.secondBase * RelLetter.listVal B.secondArc = B.firstBase := by
  have hword : B.secondWord = B.secondArc ++ B.chord := by
    have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
      simp [refinedCut, splitPairCut_left B.side_order]
    have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
      simp [refinedCut, splitPairCut_right]
    unfold secondWord secondArc
    simp only [secondHalf]
    rw [hleft, hright]
  have hclosed := B.second_closed
  change RelLetter.listVal B.secondWord = 1 at hclosed
  rw [hword, listVal_append] at hclosed
  have hchord := B.chord_geodesic.2.1
  change B.firstBase * RelLetter.listVal B.chord = B.secondBase at hchord
  have hchordVal : RelLetter.listVal B.chord = B.firstBase⁻¹ * B.secondBase := by
    apply mul_left_cancel (a := B.firstBase)
    simpa only [mul_assoc, mul_inv_cancel_left] using hchord
  rw [hchordVal] at hclosed
  change RelLetter.listVal B.secondArc * (B.firstBase⁻¹ * B.secondBase) = 1 at hclosed
  have harcVal : RelLetter.listVal B.secondArc =
      (B.firstBase⁻¹ * B.secondBase)⁻¹ := by
    apply mul_right_cancel (b := B.firstBase⁻¹ * B.secondBase)
    rw [hclosed]
    simp
  rw [harcVal]
  group

/-- The compressed first-half connectors end at the exact forward chord
vertex selected by the greedy assignment. -/
theorem firstBrokenConnectors_partnerEnd_vertex
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    vertex B.firstBase B.firstWord (B.firstBrokenConnectors s hs).partnerEnd =
      vertex B.firstBase B.chord (B.brokenAssignment.first.partner s) := by
  let y := B.brokenAssignment.first.partner s
  have hy : y < B.chord.length := B.brokenAssignment.first.partner_lt s hs
  rw [B.firstBrokenConnectors_partnerEnd s hs]
  have hpos : B.firstChordPos y + 1 = B.firstArc.length +
      (B.chord.length - y) := by
    simp [firstChordPos, B.firstArc_length]
    omega
  rw [show B.brokenAssignment.first.partner s = y from rfl, hpos]
  change vertex B.firstBase (B.firstArc ++ revWord B.chord)
      (B.firstArc.length + (B.chord.length - y)) = _
  rw [vertex_append_add, B.firstArc_endpoint]
  have hchord := B.chord_geodesic.2.1
  change B.firstBase * RelLetter.listVal B.chord = B.secondBase at hchord
  rw [← hchord]
  exact vertex_revWord_of_end B.chord B.firstBase y

/-- The compressed wrapped-half connectors end one vertex after their forward
chord start, as dictated by the one-edge geodesic component. -/
theorem secondBrokenConnectors_partnerEnd_vertex
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    vertex B.secondBase B.secondWord (B.secondBrokenConnectors s hs).partnerEnd =
      vertex B.firstBase B.chord
        (B.brokenAssignment.second.partner s + 1) := by
  let y := B.brokenAssignment.second.partner s
  rw [B.secondBrokenConnectors_partnerEnd s hs]
  have hpos : B.secondChordPos y + 1 = B.secondArc.length + (y + 1) := by
    simp [secondChordPos, B.secondArc_length, Nat.add_assoc]
  rw [show B.brokenAssignment.second.partner s = y from rfl, hpos]
  have hword : B.secondWord = B.secondArc ++ B.chord := by
    have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
      simp [refinedCut, splitPairCut_left B.side_order]
    have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
      simp [refinedCut, splitPairCut_right]
    unfold secondWord secondArc
    simp only [secondHalf]
    rw [hleft, hright]
  rw [hword]
  change vertex B.secondBase (B.secondArc ++ B.chord)
      (B.secondArc.length + (y + 1)) = _
  rw [vertex_append_add, B.secondArc_endpoint]

/-- The first-half chord partner starts at global forward-chord vertex
`y + 1`, because the first half reads the chord backwards. -/
theorem firstBrokenConnectors_partnerStart_vertex
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    vertex B.firstBase B.firstWord
        (B.firstChordPos (B.brokenAssignment.first.partner s)) =
      vertex B.firstBase B.chord
        (B.brokenAssignment.first.partner s + 1) := by
  let y := B.brokenAssignment.first.partner s
  have hy : y < B.chord.length := B.brokenAssignment.first.partner_lt s hs
  have hpos : B.firstChordPos y = B.firstArc.length +
      (B.chord.length - (y + 1)) := by
    simp [firstChordPos, B.firstArc_length]
    omega
  rw [show B.brokenAssignment.first.partner s = y from rfl, hpos]
  change vertex B.firstBase (B.firstArc ++ revWord B.chord)
      (B.firstArc.length + (B.chord.length - (y + 1))) = _
  rw [vertex_append_add, B.firstArc_endpoint]
  have hchord := B.chord_geodesic.2.1
  change B.firstBase * RelLetter.listVal B.chord = B.secondBase at hchord
  rw [← hchord]
  exact vertex_revWord_of_end B.chord B.firstBase (y + 1)

/-- The wrapped-half chord partner starts at its global forward coordinate
`y`. -/
theorem secondBrokenConnectors_partnerStart_vertex
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (_hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    vertex B.secondBase B.secondWord
        (B.secondChordPos (B.brokenAssignment.second.partner s)) =
      vertex B.firstBase B.chord
        (B.brokenAssignment.second.partner s) := by
  let y := B.brokenAssignment.second.partner s
  have hpos : B.secondChordPos y = B.secondArc.length + y := by
    simp [secondChordPos, B.secondArc_length]
  rw [show B.brokenAssignment.second.partner s = y from rfl, hpos]
  have hword : B.secondWord = B.secondArc ++ B.chord := by
    have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
      simp [refinedCut, splitPairCut_left B.side_order]
    have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
      simp [refinedCut, splitPairCut_right]
    unfold secondWord secondArc
    simp only [secondHalf]
    rw [hleft, hright]
  rw [hword]
  change vertex B.secondBase (B.secondArc ++ B.chord)
      (B.secondArc.length + y) = _
  rw [vertex_append_add, B.secondArc_endpoint]

/-- The first-half entry connector runs from the broken source start to its
exact global-chord terminal coordinate. -/
theorem firstBrokenConnectors_start_value_global
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    RelLetter.listVal (B.firstBrokenConnectors s hs).startConnector =
      (vertex B.firstBase B.firstWord (B.componentPlacement.firstPos s))⁻¹ *
        vertex B.firstBase B.chord
          (B.brokenAssignment.first.partner s + 1) := by
  rw [(B.firstBrokenConnectors s hs).start_value,
    B.firstBrokenConnectors_partnerStart_vertex s hs]

/-- The first-half exit connector runs from the broken source end to the same
global-chord terminal coordinate. -/
theorem firstBrokenConnectors_end_value_global
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    RelLetter.listVal (B.firstBrokenConnectors s hs).endConnector =
      (vertex B.firstBase B.firstWord
        (B.firstBrokenConnectors s hs).sourceEnd)⁻¹ *
        vertex B.firstBase B.chord (B.brokenAssignment.first.partner s) := by
  rw [(B.firstBrokenConnectors s hs).end_value,
    B.firstBrokenConnectors_partnerEnd_vertex s hs]

/-- The wrapped-half entry connector runs from the broken source start to
global chord vertex `y + 1`. -/
theorem secondBrokenConnectors_start_value_global
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    RelLetter.listVal (B.secondBrokenConnectors s hs).startConnector =
      (vertex B.secondBase B.secondWord (B.componentPlacement.secondPos s))⁻¹ *
        vertex B.firstBase B.chord
          (B.brokenAssignment.second.partner s) := by
  rw [(B.secondBrokenConnectors s hs).start_value,
    B.secondBrokenConnectors_partnerStart_vertex s hs]

/-- The wrapped-half exit connector runs from the broken source end to the
same global chord vertex `y + 1`. -/
theorem secondBrokenConnectors_end_value_global
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    RelLetter.listVal (B.secondBrokenConnectors s hs).endConnector =
      (vertex B.secondBase B.secondWord
        (B.secondBrokenConnectors s hs).sourceEnd)⁻¹ *
        vertex B.firstBase B.chord
          (B.brokenAssignment.second.partner s + 1) := by
  rw [(B.secondBrokenConnectors s hs).end_value,
    B.secondBrokenConnectors_partnerEnd_vertex s hs]

/-- Compressing the first-half entry connector together with its adjacent
partner edge moves the endpoint from `y + 1` to `y`. -/
theorem firstBrokenConnectors_startThroughPartner_value_global
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    RelLetter.listVal (B.firstBrokenConnectors s hs).startThroughPartner =
      (vertex B.firstBase B.firstWord (B.componentPlacement.firstPos s))⁻¹ *
        vertex B.firstBase B.chord
          (B.brokenAssignment.first.partner s) := by
  rw [(B.firstBrokenConnectors s hs).startThroughPartner_value,
    B.firstBrokenConnectors_partnerEnd_vertex s hs]

/-- Compressing the first-half exit connector together with the reversed
partner edge moves the endpoint from `y` to `y + 1`. -/
theorem firstBrokenConnectors_endThroughPartner_value_global
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    RelLetter.listVal (B.firstBrokenConnectors s hs).endThroughPartner =
      (vertex B.firstBase B.firstWord
        (B.firstBrokenConnectors s hs).sourceEnd)⁻¹ *
        vertex B.firstBase B.chord
          (B.brokenAssignment.first.partner s + 1) := by
  rw [(B.firstBrokenConnectors s hs).endThroughPartner_value,
    B.firstBrokenConnectors_partnerStart_vertex s hs]

/-- Compressing the wrapped-half entry connector with its forward partner
edge moves the endpoint from `y` to `y + 1`. -/
theorem secondBrokenConnectors_startThroughPartner_value_global
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    RelLetter.listVal (B.secondBrokenConnectors s hs).startThroughPartner =
      (vertex B.secondBase B.secondWord (B.componentPlacement.secondPos s))⁻¹ *
        vertex B.firstBase B.chord
          (B.brokenAssignment.second.partner s + 1) := by
  rw [(B.secondBrokenConnectors s hs).startThroughPartner_value,
    B.secondBrokenConnectors_partnerEnd_vertex s hs]

/-- Compressing the wrapped-half exit connector with the reversed partner
edge moves the endpoint from `y + 1` to `y`. -/
theorem secondBrokenConnectors_endThroughPartner_value_global
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    RelLetter.listVal (B.secondBrokenConnectors s hs).endThroughPartner =
      (vertex B.secondBase B.secondWord
        (B.secondBrokenConnectors s hs).sourceEnd)⁻¹ *
        vertex B.firstBase B.chord
          (B.brokenAssignment.second.partner s) := by
  rw [(B.secondBrokenConnectors s hs).endThroughPartner_value,
    B.secondBrokenConnectors_partnerStart_vertex s hs]

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
