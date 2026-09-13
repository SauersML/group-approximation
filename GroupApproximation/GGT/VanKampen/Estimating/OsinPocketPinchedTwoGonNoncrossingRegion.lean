import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchedTwoGonOuterFollows
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionNoncrossingWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# The noncrossing pocket region builder on the pinched two-gon

A model test of lane dgo-analytic's `PocketRegion.ofNoncrossingClosedWalk`
(`Estimating/OsinPocketRegionNoncrossingWalk.lean`). The builder has four hypotheses:
- a noncrossing closed walk;
- the outer face not on the walk's side;
- the reversed walk following the boundary of the other side;
- the Euler equality for the reclosed map of the walk's side.

The module checks that all four hold together on a pocket whose cycle passes twice through a
vertex. So the builder covers Configuration A, where `PocketRegion.ofSimpleClosedWalk` does not
apply.

On the pinched two-gon model the pocket cycle `[5,3,4,6]` gives:
* `isNoncrossingClosedWalk_pinchCycle` (kh-ejz);
* `outerFace_not_mem_sideFaces_pinchCycle`: the exterior face is not on the walk's side;
* `pinchCycle_outerCycle_followsBoundary`;
* `pinchCycle_reclosed_euler`: the Euler equality. It is `innerMap_euler`, carried along
  `sideFaces_pinchCycle` by `reclosedMap_euler_congr`.

The endpoint `pinchedPocketNoncrossingRegionModel` shows that the pocket region built this way has
an inner cycle that does not follow its boundary and is not a simple closed walk.

On the rose of `Estimating/OsinPocketLakeModel.lean` the reversed walk does not follow
(`lakeCycle_outerCycle_not_followsBoundary`). So the builder does not reach a lake, which stays in
the pinch Prop.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1636,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketPinchedTwoGonModel

open Surgery.MapCollapse (BoundaryCycle reclosedMap)

/-- The Euler characteristic of a reclosed map depends only on the face set and on the listed
boundary cycle. -/
theorem reclosedMap_euler_congr {M : CombMap} {faces₁ faces₂ : Finset M.Face}
    (h : faces₁ = faces₂) (b₁ : BoundaryCycle M faces₁) (b₂ : BoundaryCycle M faces₂)
    (hc : b₁.cycle = b₂.cycle) :
    (reclosedMap M faces₁ b₁).eulerCharacteristic =
      (reclosedMap M faces₂ b₂).eulerCharacteristic := by
  subst h
  obtain ⟨c₁, _, _, _⟩ := b₁
  obtain ⟨c₂, _, _, _⟩ := b₂
  obtain rfl : c₁ = c₂ := hc
  rfl

/-- **The Euler equality of `PocketRegion.ofNoncrossingClosedWalk` on the pocket cycle**, from
`innerMap_euler`. -/
theorem pinchCycle_reclosed_euler :
    (reclosedMap diagram.toCombMap
        (SimpleClosedWalkSides.sideFaces diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10)))
        (isNoncrossingClosedWalk_pinchCycle.innerCycle diagram.planar)).eulerCharacteristic =
      diagram.toCombMap.eulerCharacteristic :=
  (reclosedMap_euler_congr sideFaces_pinchCycle
      (isNoncrossingClosedWalk_pinchCycle.innerCycle diagram.planar) innerCycle
      (by decide)).trans
    innerMap_euler

/-- The exterior face is not on the side of the pocket cycle. -/
theorem outerFace_not_mem_sideFaces_pinchCycle :
    diagram.outerFace ∉
      SimpleClosedWalkSides.sideFaces diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10)) := by
  rw [sideFaces_pinchCycle]
  exact (mem_outsideFaces_iff_not_mem _).mp pocket.outerFace_mem

/-- **Model test of `PocketRegion.ofNoncrossingClosedWalk` on a pinched pocket.** The pocket cycle
of the pinched two-gon meets all four hypotheses of the builder. The inner cycle of the pocket
region it builds does not follow its boundary and is not a simple closed walk. -/
def PinchedPocketNoncrossingRegionModel : Prop :=
  ∃ (hw : IsNoncrossingClosedWalk diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10)))
    (hout : diagram.outerFace ∉
      SimpleClosedWalkSides.sideFaces diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10)))
    (hfollows : (hw.outerCycle diagram.planar).FollowsBoundary)
    (heuler : (reclosedMap diagram.toCombMap
        (SimpleClosedWalkSides.sideFaces diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10)))
        (hw.innerCycle diagram.planar)).eulerCharacteristic =
      diagram.toCombMap.eulerCharacteristic),
    ¬ (PocketRegion.ofNoncrossingClosedWalk hw hout hfollows
        heuler).inner.toBoundaryCycle.FollowsBoundary ∧
      ¬ IsSimpleClosedWalk diagram.toCombMap
        (PocketRegion.ofNoncrossingClosedWalk hw hout hfollows heuler).inner.cycle

theorem pinchedPocketNoncrossingRegionModel : PinchedPocketNoncrossingRegionModel :=
  ⟨isNoncrossingClosedWalk_pinchCycle, outerFace_not_mem_sideFaces_pinchCycle,
    pinchCycle_outerCycle_followsBoundary, pinchCycle_reclosed_euler,
    pinchCycle_innerCycle_not_followsBoundary, by
      rw [PocketRegion.ofNoncrossingClosedWalk_inner_cycle]
      exact not_isSimpleClosedWalk⟩

#audit_axioms reclosedMap_euler_congr
#audit_closed_axioms pinchCycle_reclosed_euler
#audit_axioms outerFace_not_mem_sideFaces_pinchCycle
#audit_closed_axioms pinchedPocketNoncrossingRegionModel

end GroupApproximation.GGT.VanKampen.OsinPocketPinchedTwoGonModel
