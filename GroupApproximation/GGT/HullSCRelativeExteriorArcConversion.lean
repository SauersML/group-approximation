import GroupApproximation.GGT.HullSCRelativeExteriorArcConversionStatement
import GroupApproximation.GGT.VanKampen.Estimating.PieceBridge
import GroupApproximation.GGT.OsinGeodesicWord
import GroupApproximation.Meta.AxiomGuard

/-!
# Converting a cyclic exterior arc to boundary contiguity

The two boundary cycles have independent basepoints.  Rotate the source
relator to its exposed arc and record the outer rotation in the contiguity.
The G-region's face shelling supplies the boundary-value equation; geodesic
spellings supply admissible connectors with the same short-side bounds.
-/

namespace GroupApproximation.HullSC

open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.WordMetric

universe u w v

/-- Conversion preserves the source-arc length exactly. -/
theorem exists_relativeBoundaryContiguity_rotated
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces) (htarget : Gamma.target = none)
    (boundaryWord : List G)
    (hboundary : Delta.boundaryWord.map GGT.RelLetter.val = boundaryWord) :
    ∃ C : RelativeBoundaryContiguity D eps boundaryWord
        ((cell Delta Gamma.source).word.rotate Gamma.sourceArc.start.1),
      C.exterior.length = Gamma.sourceArc.length := by
  let outerArc : CyclicArc (outerDarts Delta) :=
    cast (congrArg CyclicArc (congrArg (targetDarts Delta) htarget)) Gamma.targetArc
  have htargetDarts :
      targetBoundaryDarts Delta Gamma.target Gamma.targetArc = outerArc.darts :=
    targetBoundaryDarts_cast htarget Gamma.targetArc
  obtain ⟨sourceRemainder, hsource⟩ := Gamma.sourceArc.exists_dartWord_suffix
  obtain ⟨boundaryAfter, houter⟩ := outerArc.exists_dartWord_suffix
  rw [Gamma.sourceArc.dartWord_rotated, dartWord_cellDarts] at hsource
  rw [outerArc.dartWord_rotated, dartWord_outerDarts] at houter
  obtain ⟨left, hleft⟩ := GGT.OsinComponents.existsGeodesicWord D 1
    (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))
  obtain ⟨right, hright⟩ := GGT.OsinComponents.existsGeodesicWord D 1
    (GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide))
  obtain ⟨l, shelling⟩ := Gamma.pasting
  have harcs := Gamma.arcs_value_of_pasting (faceSetWordHomotopy_of_shelling shelling)
  rw [htargetDarts] at harcs
  refine ⟨{
    exterior := dartWord Delta Gamma.sourceArc.darts
    remainder := sourceRemainder
    relator_decomposition := hsource
    rotation := outerArc.start.1
    boundaryBefore := []
    boundaryArc := (dartWord Delta outerArc.darts).map GGT.RelLetter.val
    boundaryAfter := boundaryAfter.map GGT.RelLetter.val
    boundary_decomposition := ?_
    leftSide := left
    rightSide := right
    leftSide_admissible := hleft.1
    rightSide_admissible := hright.1
    leftSide_short := ?_
    rightSide_short := ?_
    exterior_value := ?_ }, ?_⟩
  · rw [← hboundary, ← List.map_rotate, houter, List.map_append, List.nil_append]
  · rw [hleft.2.2, wordDist_one_left]
    exact Gamma.rightSide_norm_le
  · rw [hright.2.2, wordDist_one_left]
    exact Gamma.leftSide_norm_le
  · have hl := hleft.2.1
    have hr := hright.2.1
    simp only [one_mul] at hl hr
    rw [hl, hr]
    exact harcs
  · exact (List.length_map _).trans Gamma.sourceArc.darts_length

/-- The repaired exterior-arc conversion, with the source relator's rotation
returned explicitly.  No small-cancellation assumption is needed for this
word-level extraction from an embedded region. -/
theorem relativeExteriorArcConversionAtWordRotatedStatement :
    RelativeExteriorArcConversionAtWordRotatedStatement.{u, w} := by
  intro G _ Lambda D W eps Delta boundaryWord outer houter hmap j Gamma relator hrelator
  have hconverted := exists_relativeBoundaryContiguity_rotated Gamma.region
    Gamma.target_eq boundaryWord (by rw [houter, hmap])
  have hword : (cell Delta Gamma.region.source).word = relator := by
    rw [Gamma.source_eq, hrelator]
  rw [hword] at hconverted
  obtain ⟨C, hC⟩ := hconverted
  exact ⟨Gamma.region.sourceArc.start.1, C, hC.ge⟩

end GroupApproximation.HullSC

#audit_closed_axioms GroupApproximation.HullSC.relativeExteriorArcConversionAtWordRotatedStatement
