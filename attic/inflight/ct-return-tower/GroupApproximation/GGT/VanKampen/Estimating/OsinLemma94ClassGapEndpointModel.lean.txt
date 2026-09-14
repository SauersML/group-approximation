import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassPairShapes
import GroupApproximation.GGT.VanKampen.Estimating.QuasiGeodesicValueOneGap
import GroupApproximation.Meta.AxiomGuard

/-!
# The gap-endpoint shape of a class-word connector pair: model tests

Osin (math/0411039v3, §9), proof of Lemma 9.4, Cases 1 and 2, on class words
(`OsinLemma94ClassCaseGapEndpointStatement`, module `OsinLemma94ClassPairShapes`).  A gap after side
`s` of a class is a closed path of value one along the cell (or along `∂Δ`), based at the vertex
where the face walk passes from side `s` straight to the next side; a position strictly inside it
(`InGap`) is a vertex of that loop, off the face walk of the polygon.

Model tests of the spelling, before any producer:

* `SideAt.word_split`: at `SideAt k i s off` the class word reads `A ++ (side word ++ gap word ++ R)`
  with `A.length = off`, so the gap word is the infix at `off + |side word|`.
* `gap_length_le`, `inGap_gap_length_le`: **gaps are short.**  A class in `N1 ∪ N2` has a
  `(λ, c + 2)`-quasi-geodesic word and every gap has value one, so every gap has at most
  `⌈(c + 2) / λ⌉₊` letters (`IsLambdaCQuasiGeodesicWord.le_ceil_of_listVal_eq_one`).  A gap-interior
  position therefore lies within `⌈(c + 2) / λ⌉₊` letters of both corners of its gap.
* `ofSides_not_inGap`, `ofSides_not_gapEndpoint`: on the singleton classes `ofSides P` there are no
  gaps, so the gap-endpoint shape is empty and the residual holds there vacuously.

What the model shows about a producer.  Moving a gap endpoint to a corner of its gap moves its vertex
by at most `B = ⌈(c + 2) / λ⌉₊`, so a gap-endpoint pair at `ε` gives endpoints on sides only with the
connectors below `ε + B` and the segments above `ε − B`.  `WordConnectorPair` carries one threshold for
both, and the side-level surgery `GFaceWordInsertion.exists_quadrilateral_region` needs the connectors
at most `ε` and a face walk `X ++ T ++ Y ++ P` of the polygon, which a gap vertex is not on.  So the
residual does not reduce to single-side pairs at the same `ε`: a producer either absorbs the bubble
enclosed by the gap into the new region, or runs the side-level cases with two thresholds.

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

/-- **The class word around side `s`.**  At `SideAt k i s off` the class word reads
`A ++ (side word ++ gap word ++ R)`, with `A.length = off`. -/
theorem SideAt.word_split {Q : OsinLemma94ClassPolygons P} {k : Fin P.count} {i s off : ℕ}
    (h : Q.SideAt k i s off) :
    ∃ A R : List (RelLetter G Lambda),
      Q.word k i = A ++ (P.word k s ++ Embedded.dartWord S.diagram (Q.gap k s) ++ R) ∧
        A.length = off := by
  obtain ⟨L1, L2, hL, hoff⟩ := h
  refine ⟨L1.flatMap fun t => P.word k t ++ Embedded.dartWord S.diagram (Q.gap k t),
    L2.flatMap fun t => P.word k t ++ Embedded.dartWord S.diagram (Q.gap k t), ?_, hoff.symm⟩
  rw [Q.word_eq, hL, List.flatMap_append, List.flatMap_cons]

/-- **Gaps are short.**  A class in `N1 ∪ N2` has a `(λ, c + 2)`-quasi-geodesic word, and every gap
has value one, so every gap of the class has at most `⌈(c + 2) / λ⌉₊` letters. -/
theorem gap_length_le (Q : OsinLemma94ClassPolygons P) (hlambda : 0 < lambda) {k : Fin P.count}
    {i s off : ℕ} (hi : i < Q.classCount k)
    (hmem : i ∈ Q.relatorClasses k ∨ i ∈ Q.longClasses k) (h : Q.SideAt k i s off) :
    (Embedded.dartWord S.diagram (Q.gap k s)).length ≤ ⌈(c + 2) / lambda⌉₊ := by
  have hs : s ∈ Q.classSides k i := by
    obtain ⟨L1, L2, hL, -⟩ := h
    rw [hL]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨A, R, hw, -⟩ := h.word_split
  have hq := Q.quasiGeodesic_of_mem k i hi hmem
  have hdrop : (Q.word k i).drop (A.length + (P.word k s).length) =
      Embedded.dartWord S.diagram (Q.gap k s) ++ R := by
    rw [hw, ← List.drop_drop, List.drop_left, List.append_assoc, List.drop_left]
  refine hq.le_ceil_of_listVal_eq_one hlambda (i := A.length + (P.word k s).length) ?_ ?_
  · rw [hw]
    simp only [List.length_append]
    omega
  · rw [hdrop, List.take_left]
    exact Q.gap_value k i hi s hs

/-- **A gap-interior position lies in a short gap.** -/
theorem inGap_gap_length_le (Q : OsinLemma94ClassPolygons P) (hlambda : 0 < lambda)
    {k : Fin P.count} {i x : ℕ} (hi : i < Q.classCount k)
    (hmem : i ∈ Q.relatorClasses k ∨ i ∈ Q.longClasses k) (h : Q.InGap k i x) :
    ∃ s off, Q.SideAt k i s off ∧ off + (P.word k s).length < x ∧
      x < off + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length ∧
        (Embedded.dartWord S.diagram (Q.gap k s)).length ≤ ⌈(c + 2) / lambda⌉₊ := by
  obtain ⟨s, off, hside, h1, h2⟩ := h
  exact ⟨s, off, hside, h1, h2, Q.gap_length_le hlambda hi hmem hside⟩

/-- **Model test: singleton classes have no gap positions.** -/
theorem ofSides_not_inGap (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (i x : ℕ) :
    ¬ (ofSides P).InGap k i x := by
  rintro ⟨s, off, -, h1, h2⟩
  have hnil : Embedded.dartWord S.diagram ((ofSides P).gap k s) = [] := rfl
  rw [hnil, List.length_nil, add_zero] at h2
  omega

/-- **Model test: on singleton classes the gap-endpoint shape is empty**, so
`OsinLemma94ClassCaseGapEndpointStatement` holds there vacuously. -/
theorem ofSides_not_gapEndpoint (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) ((ofSides P).corner k) ((ofSides P).word k)
      ((ofSides P).classCount k) ((ofSides P).relatorClasses k) ((ofSides P).longClasses k) eps) :
    ¬ (ofSides P).GapEndpoint k C := by
  rintro (h | h | h | h) <;> exact ofSides_not_inGap P k _ _ h

end OsinLemma94ClassPolygons

end GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen

#audit_axioms OsinLemma94ClassPolygons.gap_length_le
#audit_axioms OsinLemma94ClassPolygons.inGap_gap_length_le
#audit_axioms OsinLemma94ClassPolygons.ofSides_not_gapEndpoint
