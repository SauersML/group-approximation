import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassGapEndpointModel
import GroupApproximation.Meta.AxiomGuard

/-!
# The gap-endpoint shape at a cutting target: the piece statement and model tests

Osin (math/0411039v3, §9), proof of Lemma 9.4, Case 2, on class words.  Piece (v) of
`OsinLemma94ClassCaseGapEndpointStatement` (module `OsinLemma94ClassPairShapes`): a backwards
class-word connector pair with an endpoint strictly inside a gap, whose target class is a cutting
path.  It is to be refuted against `DartMinimal`, as the side-level Case 2 is
(`osinLemma94CaseTwoInput`).

* `OsinLemma94ClassCaseGapEndpointCuttingStatement` (residual): the piece.
  `osinLemma94ClassCaseGapEndpointCutting_of_gapEndpoint` checks the spelling: the whole gap-endpoint
  residual implies it.

Model tests of the shape, before any producer:

* `two_le_length_classSides_of_inGap`: a gap position needs a class with at least two sides, since a
  class ends with a side (`gap_last`).
* `not_inGap_of_single`: cutting and short classes are single sides (`single`), so they have no gap
  positions.
* `gapEndpoint_iff_of_target_cutting`: when the target class is a cutting path, the gap endpoint is
  a source endpoint, `GapEndpoint ↔ InGap at a ∨ InGap at a'`.  This is why piece (v) has
  source-side gaps only.
* `source_cell_two_le_of_target_cutting`: in that case the source class is an (A1) class of a
  polygon with at least two classes, and it has at least two sides.
* `vertex_after_gap_eq`: a gap closes, so the vertices before and after it agree.
* `two_mul_wordDist_gapCorner_le`: twice the distance from a gap position to the corner of its gap
  is at most the length of the gap.
* `two_mul_wordDist_target_gapCorner_lt`: for a pair whose source position `a` lies inside a gap,
  `2 d(b, corner) < 2 ε + ⌈(c + 2) / λ⌉₊`.

What the model shows about a producer.  The side-level Case 2 inserts one connector across the
polygon face (`SeparatedCornerInsertionInput`, at most `2 |connector|` more darts) and removes the
target segment of the cutting path (`2 (b − b')` fewer darts), and it needs `|connector| < b − b'`.
A source endpoint inside a gap is off the face walk.  Moving it to the corner of its gap lengthens the
connector by up to half the gap (`two_mul_wordDist_target_gapCorner_lt`), while the target segment is
only known to be longer than `ε`.  So at one threshold the dart count does not close.  When the source
gap is a hair of a relator cell, no region surgery reaches the tip either
(`OsinLemma94ClassGapHairModel`, `Surgery.InnerGRegion.hair_not_mem_cycle`).  This is an obstruction
to the route, not a refutation of the statement; the producer route waits for the ruling on hair gaps.

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

/-- **A gap position needs two sides.**  A class ends with a side, not with a gap (`gap_last`), so a
position strictly inside a gap lies after a side that is not the last. -/
theorem two_le_length_classSides_of_inGap (Q : OsinLemma94ClassPolygons P) {k : Fin P.count}
    {i x : ℕ} (hi : i < Q.classCount k) (h : Q.InGap k i x) :
    2 ≤ (Q.classSides k i).length := by
  obtain ⟨s, off, ⟨L1, L2, hL, -⟩, h1, h2⟩ := h
  by_contra hlt
  have hlen : (L1 ++ s :: L2).length ≤ 1 := by rw [← hL]; omega
  rw [List.length_append, List.length_cons] at hlen
  obtain rfl : L1 = [] := List.eq_nil_of_length_eq_zero (by omega)
  obtain rfl : L2 = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hgap : Q.gap k s = [] := Q.gap_last k i hi s (by rw [hL]; simp)
  rw [hgap] at h2
  simp only [Embedded.dartWord, List.map_nil, List.length_nil, add_zero] at h2
  omega

/-- **Single-side classes have no gap positions**: cutting and short classes are single sides. -/
theorem not_inGap_of_single (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i x : ℕ}
    (hi : i < Q.classCount k)
    (hsingle : Q.classKind k i = .cutting ∨ Q.classKind k i = .short) : ¬ Q.InGap k i x := by
  intro h
  have h2 := Q.two_le_length_classSides_of_inGap hi h
  rw [Q.single k i hi hsingle] at h2
  omega

/-- **At a cutting target the gap endpoint is a source endpoint.** -/
theorem gapEndpoint_iff_of_target_cutting (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps)
    (hcut : Q.classKind k C.target = .cutting) :
    Q.GapEndpoint k C ↔ Q.InGap k C.source C.a ∨ Q.InGap k C.source C.a' := by
  have hb : ¬ Q.InGap k C.target C.b := Q.not_inGap_of_single C.target_lt (Or.inl hcut)
  have hb' : ¬ Q.InGap k C.target C.b' := Q.not_inGap_of_single C.target_lt (Or.inl hcut)
  simp only [GapEndpoint]
  tauto

/-- **The source class of a gap-endpoint pair at a cutting target** is an (A1) class of a polygon
with at least two classes, and it has at least two sides. -/
theorem source_cell_two_le_of_target_cutting (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps)
    (hcut : Q.classKind k C.target = .cutting) (hgap : Q.GapEndpoint k C) :
    (∃ j, Q.classKind k C.source = .cell j) ∧ 2 ≤ Q.classCount k ∧
      2 ≤ (Q.classSides k C.source).length := by
  have hsrc : 2 ≤ Q.classCount k ∧ ∃ j, Q.classKind k C.source = .cell j := C.source_mem
  obtain ⟨hcount, j, hj⟩ := hsrc
  refine ⟨⟨j, hj⟩, hcount, ?_⟩
  rcases (Q.gapEndpoint_iff_of_target_cutting k C hcut).mp hgap with h | h
  · exact Q.two_le_length_classSides_of_inGap C.source_lt h
  · exact Q.two_le_length_classSides_of_inGap C.source_lt h

/-- **A gap closes.**  At `SideAt k i s off` the vertex after the gap after side `s` is the vertex
before it, since the gap has value one (`gap_value`). -/
theorem vertex_after_gap_eq (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i s off : ℕ}
    (hi : i < Q.classCount k) (h : Q.SideAt k i s off) :
    OsinComponents.vertex (Q.corner k i) (Q.word k i)
        (off + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length) =
      OsinComponents.vertex (Q.corner k i) (Q.word k i) (off + (P.word k s).length) := by
  have hs : s ∈ Q.classSides k i := by
    obtain ⟨L1, L2, hL, -⟩ := h
    rw [hL]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨A, R, hw, hA⟩ := h.word_split
  rw [HullSC.vertex_eq_mul_listVal_take, HullSC.vertex_eq_mul_listVal_take, hw]
  have h1 : (A ++ (P.word k s ++ Embedded.dartWord S.diagram (Q.gap k s) ++ R)).take
      (off + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length) =
        A ++ P.word k s ++ Embedded.dartWord S.diagram (Q.gap k s) := by
    rw [show A ++ (P.word k s ++ Embedded.dartWord S.diagram (Q.gap k s) ++ R) =
      (A ++ P.word k s ++ Embedded.dartWord S.diagram (Q.gap k s)) ++ R by
        simp only [List.append_assoc]]
    exact List.take_left' (by simp only [List.length_append]; omega)
  have h2 : (A ++ (P.word k s ++ Embedded.dartWord S.diagram (Q.gap k s) ++ R)).take
      (off + (P.word k s).length) = A ++ P.word k s := by
    rw [show A ++ (P.word k s ++ Embedded.dartWord S.diagram (Q.gap k s) ++ R) =
      (A ++ P.word k s) ++ (Embedded.dartWord S.diagram (Q.gap k s) ++ R) by
        simp only [List.append_assoc]]
    exact List.take_left' (by simp only [List.length_append]; omega)
  rw [h1, h2, HullSC.RelWord.listVal_append (A ++ P.word k s), Q.gap_value k i hi s hs, mul_one]

/-- **A gap position is close to the corner of its gap.**  Its vertex is at most the length of the
gap before it, and at most the length of the gap after it, from the corner, so twice its distance to
the corner is at most the length of the gap. -/
theorem two_mul_wordDist_gapCorner_le (Q : OsinLemma94ClassPolygons P) {k : Fin P.count}
    {i s off x : ℕ} (hi : i < Q.classCount k)
    (hlet : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (Q.word k i))
    (h : Q.SideAt k i s off) (h1 : off + (P.word k s).length < x)
    (h2 : x < off + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length) :
    2 * WordMetric.wordDist (symmetricLabelAlphabet D).alphabet.carrier
        (OsinComponents.vertex (Q.corner k i) (Q.word k i) (off + (P.word k s).length))
        (OsinComponents.vertex (Q.corner k i) (Q.word k i) x) ≤
      (Embedded.dartWord S.diagram (Q.gap k s)).length := by
  obtain ⟨A, R, hw, hA⟩ := h.word_split
  have hlen : off + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length ≤
      (Q.word k i).length := by
    rw [hw]
    simp only [List.length_append]
    omega
  have hd1 := OsinComponents.wordDist_vertex_le' (symmetricLabelAlphabet D) hlet (Q.corner k i)
    h1.le (by omega : x ≤ (Q.word k i).length)
  have hd2 := OsinComponents.wordDist_vertex_le' (symmetricLabelAlphabet D) hlet (Q.corner k i)
    h2.le hlen
  rw [Q.vertex_after_gap_eq hi h,
    WordMetric.wordDist_comm (symmetricLabelAlphabet D).alphabet.symmetricGenerating] at hd2
  omega

/-- **Moving a source endpoint to the corner of its gap.**  For a class-word pair whose source
position `a` lies strictly inside the gap after side `s`, the target vertex at `b` lies within
`|startConnector| + ⌈(c + 2) / λ⌉₊ / 2` of the corner of that gap.  At threshold `ε` this gives
only `2 d(b, corner) < 2 ε + ⌈(c + 2) / λ⌉₊`, while the target segment is only longer than `ε`. -/
theorem two_mul_wordDist_target_gapCorner_lt (Q : OsinLemma94ClassPolygons P)
    (hlambda : 0 < lambda) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps)
    {s off : ℕ} (h : Q.SideAt k C.source s off) (h1 : off + (P.word k s).length < C.a)
    (h2 : C.a < off + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length) :
    2 * WordMetric.wordDist (symmetricLabelAlphabet D).alphabet.carrier
        (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b)
        (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source)
          (off + (P.word k s).length)) <
      2 * eps + ⌈(c + 2) / lambda⌉₊ := by
  have hgap := Q.gap_length_le hlambda C.source_lt (Or.inl C.source_mem) h
  have hcorner := Q.two_mul_wordDist_gapCorner_le C.source_lt C.source_admissible h h1 h2
  have htri := WordMetric.wordDist_triangle
    (symmetricLabelAlphabet D).alphabet.symmetricGenerating
    (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b)
    (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a)
    (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) (off + (P.word k s).length))
  rw [WordMetric.wordDist_comm (symmetricLabelAlphabet D).alphabet.symmetricGenerating
    (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a)] at htri
  have hconn : C.startConnector.length =
      WordMetric.wordDist (symmetricLabelAlphabet D).alphabet.carrier
        (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b)
        (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a) :=
    C.start_geodesic.2.2
  have hshort := C.start_short
  omega

end OsinLemma94ClassPolygons

/-- **Piece (v) of the gap-endpoint shape: a cutting target (residual).**  The quantifiers are those
of `OsinLemma94ClassCaseGapEndpointStatement`: no backwards connector pair on the class words whose
target class is a cutting path has an endpoint strictly inside a gap.  By
`OsinLemma94ClassPolygons.gapEndpoint_iff_of_target_cutting` that endpoint is a source endpoint. -/
def OsinLemma94ClassCaseGapEndpointCuttingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    ∀ (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
                      (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k)
                        (Q.classCount k) (Q.relatorClasses k) (Q.longClasses k) eps),
                      C.b' < C.b → Q.classKind k C.target = .cutting → Q.GapEndpoint k C → False

/-- **The spelling of piece (v).**  The whole gap-endpoint residual implies the piece. -/
theorem osinLemma94ClassCaseGapEndpointCutting_of_gapEndpoint
    (h : OsinLemma94ClassCaseGapEndpointStatement.{u, w, v}) :
    OsinLemma94ClassCaseGapEndpointCuttingStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e, he⟩ := h D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨e, fun eps heps => ?_⟩
  obtain ⟨r, hr, hrho⟩ := he eps heps
  exact ⟨r, hr, fun rho hq W hW Delta cuts hleast hcells hbelow S hcard hmin P hmax Q k C hback _
    hgap => hrho rho hq W hW Delta cuts hleast hcells hbelow S hcard hmin P hmax Q k C hback hgap⟩

end GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen

#audit_axioms OsinLemma94ClassPolygons.two_le_length_classSides_of_inGap
#audit_axioms OsinLemma94ClassPolygons.not_inGap_of_single
#audit_axioms OsinLemma94ClassPolygons.gapEndpoint_iff_of_target_cutting
#audit_axioms OsinLemma94ClassPolygons.source_cell_two_le_of_target_cutting
#audit_axioms OsinLemma94ClassPolygons.vertex_after_gap_eq
#audit_axioms OsinLemma94ClassPolygons.two_mul_wordDist_gapCorner_le
#audit_axioms OsinLemma94ClassPolygons.two_mul_wordDist_target_gapCorner_lt
#audit_axioms osinLemma94ClassCaseGapEndpointCutting_of_gapEndpoint
