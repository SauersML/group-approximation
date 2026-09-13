import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchedTwoGonNoncrossing
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchedTwoGonLobe
import GroupApproximation.Meta.AxiomGuard

/-!
# The outer side of the pinched two-gon pocket follows its boundary

A model test for the prediction put to this lane in `notes/nm-swarm/reports/dgo-analytic.md`
("R2 with kh-ejz's `IsNoncrossingClosedWalk` as `Simple`"). At a vertex that a noncrossing closed
walk passes twice, the side whose sectors lie inside the passages follows its boundary, and the
other side does not. In Configuration A the pocket sectors lie between the passages, so the inner
boundary cycle does not follow and the outer one follows.

On the pinched two-gon model (`Estimating/OsinPocketPinchedTwoGonModel.lean`) the pocket cycle
`[5,3,4,6]` passes twice through the vertex `{1,3,6,8}`.

* The inner cycle does not follow (`not_followsBoundary`).
* The reversed walk `[9,8,0,1]` is the boundary cycle of `IsNoncrossingClosedWalk.outerCycle` on
  the relator cell and the exterior face (`sideOutside_pinchCycle`, `outerCycle_pinchCycle`). It
  follows: `9 ↦ 8` and `0 ↦ 1` are face steps, and `8 ↦ 7 ↦ 0` and `1 ↦ 2 ↦ 9` skip the internal
  edge `{2,7}` (`pinchCycle_outerCycle_followsBoundary`).

So the prediction holds on this model (`pocket_inner_not_follows_outer_follows`). The pocket face
set `pinchedK` of `Estimating/OsinPocketPinchedTwoGonLobe.lean` meets the hypothesis of
`PocketPinchPinchedStatement` and is not `PocketFaceSet.Simple`. Its cycle is still a noncrossing
closed walk whose outer cycle follows (`pinchedPocketNoncrossingOuterFollowsModel`), so under the
proposed noncrossing `Simple` this pocket needs no pinch.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1636,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketPinchedTwoGonModel

open Surgery.MapCollapse (BoundaryWalk Unpinched)

/-- The faces on the other side of the pocket cycle are the relator cell and the exterior face. -/
theorem sideOutside_pinchCycle :
    SimpleClosedWalkSides.sideOutside diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10)) =
      outsideFaces := by
  ext f
  rw [SimpleClosedWalkSides.mem_sideOutside_iff, sideFaces_pinchCycle]
  exact (mem_outsideFaces_iff_not_mem f).symm

/-- The face step `9 ↦ 8` of the exterior face. -/
theorem outerWalk_nine_eight : BoundaryWalk diagram.toCombMap outsideFaces 9 8 := by
  change Relation.ReflTransGen _ (diagram.toCombMap.facePerm 9) 8
  exact (show diagram.toCombMap.facePerm 9 = 8 by decide) ▸ Relation.ReflTransGen.refl

/-- The face step `8 ↦ 7` of the exterior face, then the rotation `7 ↦ 0` across the internal
edge `{2,7}`. -/
theorem outerWalk_eight_zero : BoundaryWalk diagram.toCombMap outsideFaces 8 0 := by
  change Relation.ReflTransGen _ (diagram.toCombMap.facePerm 8) 0
  rw [show diagram.toCombMap.facePerm 8 = 7 by decide]
  exact Relation.ReflTransGen.single
    ⟨(internalDart_outside_iff 7).mpr (Or.inr rfl), show diagram.toCombMap.sigma 7 = 0 by decide⟩

/-- The face step `0 ↦ 1` of the relator cell. -/
theorem outerWalk_zero_one : BoundaryWalk diagram.toCombMap outsideFaces 0 1 := by
  change Relation.ReflTransGen _ (diagram.toCombMap.facePerm 0) 1
  exact (show diagram.toCombMap.facePerm 0 = 1 by decide) ▸ Relation.ReflTransGen.refl

/-- The face step `1 ↦ 2` of the relator cell, then the rotation `2 ↦ 9` across the internal
edge `{2,7}`. -/
theorem outerWalk_one_nine : BoundaryWalk diagram.toCombMap outsideFaces 1 9 := by
  change Relation.ReflTransGen _ (diagram.toCombMap.facePerm 1) 9
  rw [show diagram.toCombMap.facePerm 1 = 2 by decide]
  exact Relation.ReflTransGen.single
    ⟨(internalDart_outside_iff 2).mpr (Or.inl rfl), show diagram.toCombMap.sigma 2 = 9 by decide⟩

theorem outerCycle_pinchCycle :
    (isNoncrossingClosedWalk_pinchCycle.outerCycle diagram.planar).cycle =
      ([9, 8, 0, 1] : List (Fin 10)) := by
  decide

theorem outerCycle_pinchCycle_getLast :
    (isNoncrossingClosedWalk_pinchCycle.outerCycle diagram.planar).cycle.getLast
      (isNoncrossingClosedWalk_pinchCycle.outerCycle diagram.planar).cycle_nonempty = 1 := by
  decide

theorem outerCycle_pinchCycle_head :
    (isNoncrossingClosedWalk_pinchCycle.outerCycle diagram.planar).cycle.head
      (isNoncrossingClosedWalk_pinchCycle.outerCycle diagram.planar).cycle_nonempty = 9 := by
  decide

/-- **The outer cycle of the pinched pocket cycle follows its boundary.** -/
theorem pinchCycle_outerCycle_followsBoundary :
    (isNoncrossingClosedWalk_pinchCycle.outerCycle diagram.planar).FollowsBoundary := by
  refine Surgery.MapCollapse.BoundaryCycle.followsBoundary_of_chain _ ?_ ?_
  · rw [outerCycle_pinchCycle, sideOutside_pinchCycle]
    exact List.isChain_cons_cons.mpr ⟨outerWalk_nine_eight,
      List.isChain_cons_cons.mpr ⟨outerWalk_eight_zero,
        List.isChain_cons_cons.mpr ⟨outerWalk_zero_one, List.isChain_singleton _⟩⟩⟩
  · rw [outerCycle_pinchCycle_getLast, outerCycle_pinchCycle_head, sideOutside_pinchCycle]
    exact outerWalk_one_nine

/-- **The prediction on the pinched pocket region:** the inner boundary cycle does not follow the
boundary, and the pocket cycle is a noncrossing closed walk whose outer cycle follows. -/
theorem pocket_inner_not_follows_outer_follows :
    ¬ pocket.inner.toBoundaryCycle.FollowsBoundary ∧
      ∃ hw : IsNoncrossingClosedWalk diagram.toCombMap pocket.inner.cycle,
        (hw.outerCycle diagram.planar).FollowsBoundary :=
  ⟨not_followsBoundary, pocket_isNoncrossingClosedWalk, pinchCycle_outerCycle_followsBoundary⟩

/-- **Model test of the noncrossing `Simple` on a pinched pocket face set.** There is a pocket face
set of the lobe diagram that meets the hypothesis of `PocketPinchPinchedStatement` and is not
`PocketFaceSet.Simple`, but whose cycle is a noncrossing closed walk with a following outer
cycle. -/
def PinchedPocketNoncrossingOuterFollowsModel : Prop :=
  ∃ K : PocketFaceSet D 0 lobeDiagram 0 2,
    ¬(K.boundary.FollowsBoundary ∧ Unpinched lobeDiagram.toCombMap K.faces) ∧ ¬ K.Simple ∧
      ∃ hw : IsNoncrossingClosedWalk lobeDiagram.toCombMap K.boundary.cycle,
        (hw.outerCycle lobeDiagram.planar).FollowsBoundary

theorem pinchedPocketNoncrossingOuterFollowsModel : PinchedPocketNoncrossingOuterFollowsModel :=
  ⟨pinchedK, fun h => pinchedK_not_followsBoundary h.1, pinchedK_not_simple,
    isNoncrossingClosedWalk_pinchCycle, pinchCycle_outerCycle_followsBoundary⟩

#audit_closed_axioms sideOutside_pinchCycle
#audit_closed_axioms outerWalk_eight_zero
#audit_closed_axioms outerWalk_one_nine
#audit_closed_axioms outerCycle_pinchCycle
#audit_closed_axioms pinchCycle_outerCycle_followsBoundary
#audit_axioms pocket_inner_not_follows_outer_follows
#audit_closed_axioms pinchedPocketNoncrossingOuterFollowsModel

end GroupApproximation.GGT.VanKampen.OsinPocketPinchedTwoGonModel
