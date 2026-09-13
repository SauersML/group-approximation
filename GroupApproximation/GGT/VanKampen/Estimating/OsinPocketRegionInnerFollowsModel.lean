import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionInnerFollows
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeLabelledModel
import GroupApproximation.Meta.AxiomGuard

/-!
# Model test: the lake rose has a pocket region although its outer cycle does not follow

A model test for `PocketRegion.ofNoncrossingClosedWalkInner`
(`Estimating/OsinPocketRegionInnerFollows.lean`) on the labelled lake rose of
`Estimating/OsinPocketLakeLabelledModel.lean`: four darts, the edges `{0,1}` and `{2,3}`, one
vertex, the faces `K = [0,2]`, `Π = [1]` and the exterior face `O = [3]`, and the walk `[0,2]`
passing twice through the vertex.

* The exterior face lies off the side of the walk (`lakeCycle_outerFace_not_mem_sideFaces`).
* The builder fires on the walk (`lakePocketRegion`): its inner cycle follows
  (`OsinPocketLakeModel.lakeCycle_innerCycle_followsBoundary`), while its outer cycle does not
  (`OsinPocketLakeModel.lakeCycle_outerCycle_not_followsBoundary`), so
  `PocketRegion.ofNoncrossingClosedWalk` does not apply there.
* `LakeInnerFollowsPocketModel` records both: a pocket region on the side of the walk with the walk
  as its cycle and the reversed walk `[3,1]` as its complement cycle, on a map where the reversed
  walk does not follow its boundary.

The model carries two relator cells, so it tests only the pocket region, not the collapse.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketLakeLabelledModel

open SimpleClosedWalkSides

/-- The exterior face `O = [3]` of the rose lies off the side of the lake walk: the dart `2` is a
boundary dart of the side, and the face across it is `O`. -/
theorem lakeCycle_outerFace_not_mem_sideFaces :
    roseDiagram.outerFace ∉ sideFaces roseDiagram.toCombMap ([0, 2] : List (Fin 4)) := by
  obtain ⟨-, h2⟩ :=
    (OsinPocketLakeModel.isNoncrossingClosedWalk_lakeCycle.isBoundaryDart_sideFaces_iff
      OsinPocketLakeModel.planar 2).mpr (by decide)
  have halpha : OsinPocketLakeModel.M.alpha 2 = 3 := by decide
  rw [halpha] at h2
  exact h2

/-- **The pocket region of the lake walk**, from inner following. -/
noncomputable def lakePocketRegion : PocketRegion roseDiagram :=
  PocketRegion.ofNoncrossingClosedWalkInner (Delta := roseDiagram)
    (walk := ([0, 2] : List (Fin 4)))
    OsinPocketLakeModel.isNoncrossingClosedWalk_lakeCycle
    lakeCycle_outerFace_not_mem_sideFaces
    OsinPocketLakeModel.lakeCycle_innerCycle_followsBoundary

theorem lakePocketRegion_inner_cycle :
    lakePocketRegion.inner.cycle = ([0, 2] : List (Fin 4)) :=
  rfl

theorem lakePocketRegion_outer_cycle :
    lakePocketRegion.outer.cycle = ([3, 1] : List (Fin 4)) := by
  decide

/-- **The lake rose, pocket form.**  The walk `[0,2]` has a pocket region on its side with the walk
as its cycle and `[3,1]` as its complement cycle, while its outer cycle does not follow its
boundary. -/
def LakeInnerFollowsPocketModel : Prop :=
  (∃ P : PocketRegion roseDiagram,
      P.faces = sideFaces roseDiagram.toCombMap ([0, 2] : List (Fin 4)) ∧
        P.inner.cycle = ([0, 2] : List (Fin 4)) ∧ P.outer.cycle = ([3, 1] : List (Fin 4))) ∧
    ¬ (OsinPocketLakeModel.isNoncrossingClosedWalk_lakeCycle.outerCycle
        OsinPocketLakeModel.planar).FollowsBoundary

theorem lakeInnerFollowsPocketModel : LakeInnerFollowsPocketModel :=
  ⟨⟨lakePocketRegion, rfl, lakePocketRegion_inner_cycle, lakePocketRegion_outer_cycle⟩,
    OsinPocketLakeModel.lakeCycle_outerCycle_not_followsBoundary⟩

end GroupApproximation.GGT.VanKampen.OsinPocketLakeLabelledModel

#audit_closed_axioms GroupApproximation.GGT.VanKampen.OsinPocketLakeLabelledModel.lakeInnerFollowsPocketModel
