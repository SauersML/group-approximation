import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassGapEndpointModel
import GroupApproximation.GGT.VanKampen.SurgeryInnerCollapse
import GroupApproximation.Meta.AxiomGuard

/-!
# Hair gaps: where the merged-region route to the gap-endpoint case stops

Osin (math/0411039v3, §9), proof of Lemma 9.4, Case 1, on class words
(`OsinLemma94ClassCaseGapEndpointStatement`, module `OsinLemma94ClassPairShapes`).  The natural
producer for a connector pair with an endpoint strictly inside a gap merges the polygon face with the
faces enclosed by the gap loop into one G-face (`Surgery.InnerGRegion`), so that the gap vertices become
corners of the merged face and the quadrilateral surgery of Case 1
(`GFaceWordInsertion.exists_quadrilateral_region_rotate`) can insert the connectors there.

This module records where that route stops.

* `isLambdaCQuasiGeodesicWord_hair`: a letter followed by its inverse is a `(λ, c)`-quasi-geodesic word
  once `2 λ ≤ c`.  So the quasi-geodesic clause of `OsinCCondition` and of `SectionCuts` admits relator
  words and boundary sections with a hair, and `isLambdaCQuasiGeodesicWord_hair_add_two` shows that the
  class words, `(λ, c + 2)`-quasi-geodesic with `λ ≤ 1`, always admit one.
* A hair of relator cell `Π` is a gap.  If `Π` reads the darts `p, h, α h, q`, with `h` and `α h` both on
  `Π`, then the reversed arc is `[α q, h, α h, α p]`.  Its sides `[α q]` and `[α p]` follow one another on
  the walk of the polygon across `Π`, and the walk across turns away at their common vertex
  (`facePerm p = h ≠ q`), as `OsinLemma94RealizedPolygons.Maximal` asks.  The gap `[h, α h]` has value
  one, and the position between `h` and `α h`, the tip of the hair, lies strictly inside it (`InGap`).
  A boundary class has the same shape along a hair of `∂Δ`, with the gap darts on the exterior face.
* `Surgery.InnerGRegion.not_mem_cycle_of_relatorCell`, `not_mem_cycle_of_outer`, `hair_not_mem_cycle`:
  a dart on a relator cell, or on the exterior face, lies on the boundary cycle of no region to collapse.
  So no merged face has a vertex of a hair gap as a corner, and the surgery cannot place a connector at a
  hair tip.

Consequence for `OsinLemma94ClassCaseGapEndpointStatement`.  Moving a hair-tip endpoint to the base of
its hair shifts the connector by up to half the gap, at most `⌈(c + 2) / λ⌉₊ / 2` letters
(`OsinLemma94ClassPolygons.gap_length_le`), while `WordConnectorPair` and the family carry one threshold
`ε` for both.  The hair case of the gap-endpoint shape is therefore not reached by region surgery at one
threshold.  This is an obstruction to the route, not a refutation of the statement.  The bubble case,
whose gap darts lie on G-faces inside the loop, is untouched.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1636, "Hull's small cancellation theorem", through
Osin's Lemma 9.4 inside the proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.HullSC

section HairWord

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **A hair word is quasi-geodesic.**  A letter followed by its inverse is a `(λ, c)`-quasi-geodesic
word once `0 ≤ λ` and `2 λ ≤ c`: every index gap is at most `2`, so the lower bound is non-positive. -/
theorem isLambdaCQuasiGeodesicWord_hair {D : RelGenSet G Lambda} {lambda c : ℝ}
    {x : RelLetter G Lambda} (hx : D.IsLetter x) (hinv : D.IsLetter (RelWord.inv x))
    (hlambda : 0 ≤ lambda) (hc : 2 * lambda ≤ c) :
    IsLambdaCQuasiGeodesicWord D lambda c [x, RelWord.inv x] := by
  unfold IsLambdaCQuasiGeodesicWord
  refine ⟨?_, ?_⟩
  · intro a ha
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact hx
    · have hEq := List.mem_singleton.1 ha'
      subst hEq
      exact hinv
  · intro i j _ hj
    have hj2 : j ≤ 2 := by simpa using hj
    have hsub : ((j - i : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (Nat.sub_le j i).trans hj2
    refine le_trans ?_ (Nat.cast_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left hsub hlambda
    linarith

/-- **Class words admit hairs.**  At the parameters of Lemma 9.4 (`0 ≤ λ ≤ 1`, `0 ≤ c`) a letter followed
by its inverse is `(λ, c + 2)`-quasi-geodesic, the quasi-geodesic clause of the class words. -/
theorem isLambdaCQuasiGeodesicWord_hair_add_two {D : RelGenSet G Lambda} {lambda c : ℝ}
    {x : RelLetter G Lambda} (hx : D.IsLetter x) (hinv : D.IsLetter (RelWord.inv x))
    (hlambda : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) :
    IsLambdaCQuasiGeodesicWord D lambda (c + 2) [x, RelWord.inv x] :=
  isLambdaCQuasiGeodesicWord_hair hx hinv hlambda (by linarith)

end HairWord

section Merged

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- **A dart on a relator cell lies on no merged boundary.**  The faces of a region to collapse avoid
the relator cells, and a boundary dart of the region lies on a face of the region. -/
theorem Surgery.InnerGRegion.not_mem_cycle_of_relatorCell (R : Surgery.InnerGRegion Delta)
    {C : RelatorCell Delta.toCombMap Delta.outerFace W} (hC : C ∈ Delta.relatorCells)
    {d : Delta.toCombMap.Dart} (hd : Delta.toCombMap.faceOf d = C.face) :
    d ∉ R.boundary.cycle := by
  intro hmem
  obtain ⟨hface, -⟩ := (R.boundary.cycle_mem_iff d).1 hmem
  rw [hd] at hface
  exact R.cells_avoid C hC hface

/-- **A dart on the exterior face lies on no merged boundary.** -/
theorem Surgery.InnerGRegion.not_mem_cycle_of_outer (R : Surgery.InnerGRegion Delta)
    {d : Delta.toCombMap.Dart} (hd : Delta.toCombMap.faceOf d = Delta.outerFace) :
    d ∉ R.boundary.cycle := by
  intro hmem
  obtain ⟨hface, -⟩ := (R.boundary.cycle_mem_iff d).1 hmem
  rw [hd] at hface
  exact R.outer_not_mem hface

/-- **Hair gaps are unreachable.**  If both darts of an edge lie on a relator cell, a hair of the cell,
neither lies on the boundary cycle of any region to collapse. -/
theorem Surgery.InnerGRegion.hair_not_mem_cycle (R : Surgery.InnerGRegion Delta)
    {C : RelatorCell Delta.toCombMap Delta.outerFace W} (hC : C ∈ Delta.relatorCells)
    {d : Delta.toCombMap.Dart} (hd : Delta.toCombMap.faceOf d = C.face)
    (hd' : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = C.face) :
    d ∉ R.boundary.cycle ∧ Delta.toCombMap.alpha d ∉ R.boundary.cycle :=
  ⟨R.not_mem_cycle_of_relatorCell hC hd, R.not_mem_cycle_of_relatorCell hC hd'⟩

end Merged

end GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen

#audit_axioms isLambdaCQuasiGeodesicWord_hair
#audit_axioms isLambdaCQuasiGeodesicWord_hair_add_two
#audit_axioms Surgery.InnerGRegion.not_mem_cycle_of_relatorCell
#audit_axioms Surgery.InnerGRegion.not_mem_cycle_of_outer
#audit_axioms Surgery.InnerGRegion.hair_not_mem_cycle
