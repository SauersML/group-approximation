import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonRealization
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixCutSections
import GroupApproximation.Meta.AxiomGuard

/-!
# The boundary arcs of Lemma 9.4

Osin (math/0411039v3, §9), Lemma 9.4.  The polygons of the proof are bounded by cutting paths,
arcs of relator cells and arcs of `∂Δ`, and each of these is `(λ, c + 2)`-quasi-geodesic.  This
file proves the claim for the arcs of `∂Δ` (`osinLemma94BoundaryArcsInput`).

An arc of `∂Δ` inside the section `q_j` is a subpath of `q_j`, and `q_j` is
`(λ, c)`-quasi-geodesic.  The vertices of a subpath are a left translate of a run of the vertices
of `q_j`, so the defining inequality of the subpath is an instance of the one of `q_j`
(`CutSections.isLambdaCQuasiGeodesicWord_drop_take`).  So the arc is `(λ, c)`-quasi-geodesic, and
so `(λ, c + 2)`-quasi-geodesic.  Neither `0 ≤ c` nor a bound on `c` against `λ` is used: a
backtrack in the arc is a backtrack in `q_j`.

Two identifications put the arc inside the section word.

* The optimal diagram is O-equivalent to `Δ`, so its oriented outer darts spell `Δ.boundaryWord`
  (`Embedded.dartWord_outerDarts`, `OEquivalentDiscDiagram.boundaryWord_eq`), and the positions
  of the arc are positions of that word.
* The arc ends at or before the end of the section, so it does not wrap around the base point.

The conclusion is over `symmetricLabelAlphabet D`, which admits every letter of `D` and has the
same generators (`symmetricLabelAlphabet.carrier_eq`).
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

/-- A `(λ, c)`-quasi-geodesic word over `D` is `(λ, c')`-quasi-geodesic over
`symmetricLabelAlphabet D` for every `c' ≥ c`. -/
theorem isLambdaCQuasiGeodesicWord_symmetricLabelAlphabet_of_le {G : Type u} [Group G]
    {Lambda : Type w} {D : RelGenSet G Lambda} {lambda c c' : ℝ}
    {word : List (RelLetter G Lambda)} (h : IsLambdaCQuasiGeodesicWord D lambda c word)
    (hc : c ≤ c') :
    IsLambdaCQuasiGeodesicWord (symmetricLabelAlphabet D) lambda c' word := by
  refine ⟨symmetricLabelAlphabet.admissible D h.1, ?_⟩
  intro i j hij hj
  rw [symmetricLabelAlphabet.carrier_eq]
  linarith [h.2 i j hij hj]

/-- The word of an arc of the oriented outer boundary that ends at or before the base point is
a run of the boundary word. -/
theorem dartWord_outerArc_eq_drop_take {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (Delta : DiscDiagram.{u, w, v} W)
    (arc : CyclicArc (targetDarts Delta none))
    (hend : arc.start.1 + arc.length ≤ Delta.boundaryWord.length) :
    dartWord Delta arc.darts = (Delta.boundaryWord.drop arc.start.1).take arc.length := by
  have hword : (targetDarts Delta none).map Delta.label = Delta.boundaryWord :=
    dartWord_outerDarts Delta
  have hlen : (targetDarts Delta none).length = Delta.boundaryWord.length := by
    rw [← hword, List.length_map]
  have hdrop : arc.length ≤ ((targetDarts Delta none).drop arc.start.1).length := by
    rw [List.length_drop]
    omega
  rw [CyclicArc.darts, CyclicArc.rotated, List.take_append_of_le_length hdrop, dartWord,
    List.map_take, List.map_drop, hword]

/-- A run of the boundary word inside section `j` is a run of the word of section `j`. -/
theorem SectionCuts.drop_take_eq_sectionRun {G : Type u} [Group G] {Lambda : Type w}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {word : List (RelLetter G Lambda)}
    (cuts : SectionCuts D lambda c word) (j : Fin cuts.count) {start length : ℕ}
    (hstart : cuts.cut j.castSucc ≤ start) (hend : start + length ≤ cuts.cut j.succ) :
    (word.drop start).take length =
      (((word.drop (cuts.cut j.castSucc)).take (cuts.cut j.succ - cuts.cut j.castSucc)).drop
        (start - cuts.cut j.castSucc)).take length := by
  rw [List.drop_take, List.drop_drop, List.take_take,
    show cuts.cut j.castSucc + (start - cuts.cut j.castSucc) = start by omega,
    show min length (cuts.cut j.succ - cuts.cut j.castSucc - (start - cuts.cut j.castSucc)) =
      length by omega]

/-- **`OsinLemma94BoundaryArcsInput` holds.**  An arc of `∂Δ` inside the section `q_j` is a run
of `q_j`, so it is `(λ, c)`-quasi-geodesic, and so `(λ, c + 2)`-quasi-geodesic over the
symmetrized alphabet. -/
theorem osinLemma94BoundaryArcsInput : OsinLemma94BoundaryArcsInput.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ cuts S _ j hj arc hstart hend
  have hstart' : cuts.cut (⟨j, hj⟩ : Fin cuts.count).castSucc ≤ arc.start.1 := hstart
  have hend' : arc.start.1 + arc.length ≤ cuts.cut (⟨j, hj⟩ : Fin cuts.count).succ := hend
  have hlast : cuts.cut (⟨j, hj⟩ : Fin cuts.count).succ ≤ S.diagram.boundaryWord.length := by
    rw [S.equiv.boundaryWord_eq, ← cuts.cut_last]
    exact cuts.cut_mono (Fin.le_last _)
  rw [dartWord_outerArc_eq_drop_take S.diagram arc (hend'.trans hlast),
    S.equiv.boundaryWord_eq, SectionCuts.drop_take_eq_sectionRun cuts ⟨j, hj⟩ hstart' hend']
  exact isLambdaCQuasiGeodesicWord_symmetricLabelAlphabet_of_le
    (CutSections.isLambdaCQuasiGeodesicWord_drop_take (cuts.quasiGeodesic ⟨j, hj⟩) _ _)
    (by linarith)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.isLambdaCQuasiGeodesicWord_symmetricLabelAlphabet_of_le
#audit_axioms GroupApproximation.GGT.VanKampen.dartWord_outerArc_eq_drop_take
#audit_axioms GroupApproximation.GGT.VanKampen.SectionCuts.drop_take_eq_sectionRun
#audit_closed_axioms GroupApproximation.GGT.VanKampen.osinLemma94BoundaryArcsInput
