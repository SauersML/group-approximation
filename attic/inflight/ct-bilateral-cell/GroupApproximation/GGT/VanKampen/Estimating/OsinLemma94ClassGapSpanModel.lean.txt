import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassGapEndpointModel
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassPairTransfer
import GroupApproximation.Meta.AxiomGuard

/-!
# The spanning shape of a class-word connector pair: model tests

Osin (math/0411039v3, §9), proof of Lemma 9.4, Cases 1 and 2, on class words
(`OsinLemma94ClassCaseGapSpanStatement`, module `OsinLemma94ClassPairShapes`).  A pair of this shape
is not single-side and has no endpoint strictly inside a gap, so its source segment, or its target
positions, run across a corner between two sides of one class, over the gap between them.

Model tests of the spelling, before any producer:

* `vertex_gap_end_eq`: **a gap does not move a vertex.**  The vertex of a class word at the end of
  the gap after side `s` is the vertex at its start, since the gap has value one.  So the endpoints
  of a spanning pair are the endpoints of the reading of the face walk with the gaps deleted, and
  a spanning segment is no longer, as a distance, than its parts on the sides.  A source segment of
  distance near `2 ε` whose two side parts are each at most `ε` long is legal, and no side-level
  pair has either part as its source; that is the reason these pairs are a residual, and it is no
  refutation.
* `ofSides_sideAt`, `ofSides_singleSidePair`, `ofSides_not_span`: on the singleton classes
  `ofSides P` every pair is single-side, so `OsinLemma94ClassCaseGapSpanStatement` holds there
  vacuously.  This calibration exercises nothing of the shape.

What the model shows about a producer.  Across the gap the face walk of the polygon passes straight
from one side to the next at one vertex `x`, while the boundary of the cell (or `∂Δ`) runs around the
gap and back to `x`.  A backwards spanning pair bounds a quadrilateral inside the polygon face whose
source side is a face-walk segment across one cell, but whose darts across are two arcs of that cell
separated by the gap, not one `CyclicArc`.  `GFaceWordInsertion.exists_quadrilateral_region_rotate`
needs one arc, and splitting the pair at `x` needs a connector from `x` of length at most `ε`, which
the hyperbolic thinness of the quadrilateral bounds only by `ε` plus a constant.  So a producer either
builds the region pinched at `x`, with the faces behind the gap (the pinch geometry of
`PocketFaceSet`), or runs the side-level cases with two thresholds.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1636, "Hull's small cancellation theorem", through
Osin's Lemma 9.4 inside the proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

namespace OsinLemma94ClassPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- **A gap does not move a vertex.**  On class word `i`, the vertex at the end of the gap after
side `s` is the vertex at the end of side `s`. -/
theorem vertex_gap_end_eq (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i s off : ℕ}
    (hi : i < Q.classCount k) (h : Q.SideAt k i s off) :
    OsinComponents.vertex (Q.corner k i) (Q.word k i)
        (off + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length) =
      OsinComponents.vertex (Q.corner k i) (Q.word k i) (off + (P.word k s).length) := by
  have hs := Q.mem_of_sideAt h
  have hg := Q.gap_value k i hi s hs
  obtain ⟨A, R, hw, hA⟩ := h.word_split
  subst hA
  have e1 : (A ++ (P.word k s ++ Embedded.dartWord S.diagram (Q.gap k s) ++ R)).take
      (A.length + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length) =
      A ++ P.word k s ++ Embedded.dartWord S.diagram (Q.gap k s) := by
    have e : A ++ (P.word k s ++ Embedded.dartWord S.diagram (Q.gap k s) ++ R) =
        (A ++ P.word k s ++ Embedded.dartWord S.diagram (Q.gap k s)) ++ R := by
      simp only [List.append_assoc]
    rw [e]
    exact List.take_left' (by simp only [List.length_append])
  have e2 : (A ++ (P.word k s ++ Embedded.dartWord S.diagram (Q.gap k s) ++ R)).take
      (A.length + (P.word k s).length) = A ++ P.word k s := by
    have e : A ++ (P.word k s ++ Embedded.dartWord S.diagram (Q.gap k s) ++ R) =
        (A ++ P.word k s) ++ (Embedded.dartWord S.diagram (Q.gap k s) ++ R) := by
      simp only [List.append_assoc]
    rw [e]
    exact List.take_left' (by simp only [List.length_append])
  rw [HullSC.vertex_eq_mul_listVal_take, HullSC.vertex_eq_mul_listVal_take, hw, e1, e2,
    HullSC.RelWord.listVal_append, hg, mul_one]

/-- On singleton classes, side `i` sits in class `i` at offset `0`. -/
theorem ofSides_sideAt (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (i : ℕ) :
    (ofSides P).SideAt k i i 0 :=
  ⟨[], [], rfl, rfl⟩

/-- **Model test: on singleton classes every class-word pair is single-side.** -/
theorem ofSides_singleSidePair (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) ((ofSides P).corner k) ((ofSides P).word k)
      ((ofSides P).classCount k) ((ofSides P).relatorClasses k) ((ofSides P).longClasses k) eps) :
    (ofSides P).SingleSidePair k C := by
  have hw : ∀ i, i < (ofSides P).classCount k →
      ((ofSides P).word k i).length = (P.word k i).length :=
    fun i hi => by rw [(ofSides P).word_eq_of_eq_singleton k i hi rfl]
  refine ⟨⟨C.source, 0, ofSides_sideAt P k C.source, Nat.zero_le _, ?_⟩,
    C.target, 0, ofSides_sideAt P k C.target, Nat.zero_le _, Nat.zero_le _, ?_, ?_⟩
  · rw [Nat.zero_add, ← hw C.source C.source_lt]
    exact C.a'_le
  · rw [Nat.zero_add, ← hw C.target C.target_lt]
    exact C.b_le
  · rw [Nat.zero_add, ← hw C.target C.target_lt]
    exact C.b'_le

/-- **Model test: on singleton classes the spanning shape is empty**, so
`OsinLemma94ClassCaseGapSpanStatement` holds there vacuously. -/
theorem ofSides_not_span (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) ((ofSides P).corner k) ((ofSides P).word k)
      ((ofSides P).classCount k) ((ofSides P).relatorClasses k) ((ofSides P).longClasses k) eps) :
    ¬ (¬ (ofSides P).GapEndpoint k C ∧ ¬ (ofSides P).SingleSidePair k C) :=
  fun h => h.2 (ofSides_singleSidePair P k C)

end OsinLemma94ClassPolygons

end GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen

#audit_axioms OsinLemma94ClassPolygons.vertex_gap_end_eq
#audit_axioms OsinLemma94ClassPolygons.ofSides_singleSidePair
#audit_axioms OsinLemma94ClassPolygons.ofSides_not_span
