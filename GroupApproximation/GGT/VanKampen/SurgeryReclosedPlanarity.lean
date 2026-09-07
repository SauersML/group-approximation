import GroupApproximation.GGT.VanKampen.CombMapRestrictionPlanarity
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryReclosed

/-!
# Produce the topology of a reclosed region from its genuine boundary

The boundary walk determines the actual first-return vertex rotation.
General connected restriction planarity now proves the missing Euler equation.
Thus an existing embedded face-set boundary supplies the historical disc-region
record with both topology fields proved, rather than supplied as hypotheses.
-/

namespace GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

universe v

/-- Reclosing along the genuine boundary of a face set preserves planarity. -/
theorem reclosedMap_planar (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) (hwalk : boundary.FollowsBoundary)
    (hM : M.IsPlanar) : (reclosedMap M faces boundary).IsPlanar := by
  obtain ⟨b⟩ := nonempty_boundaryDart M faces boundary
  let d : (reclosedMap M faces boundary).Dart := ⟨b.1, fun hi => b.2.2 hi.2⟩
  exact (reclosed_isRestriction M faces boundary hwalk).planar hM
    (reclosedMap_connected M faces boundary hM.1) d

/-- The Euler equation follows from the actual boundary walk and source
planarity, including regions with internally paired darts. -/
theorem reclosedMap_euler_preserved (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) (hwalk : boundary.FollowsBoundary)
    (hM : M.IsPlanar) :
    (reclosedMap M faces boundary).eulerCharacteristic = M.eulerCharacteristic :=
  (reclosedMap_planar M faces boundary hwalk hM).2.trans hM.2.symm

/-- Construct the historical disc-region record from a genuine cyclic
boundary walk. No connectedness or Euler equation for the output is assumed. -/
def BoundaryCycle.toDiscRegion_of_followsBoundary (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) (hwalk : boundary.FollowsBoundary)
    (hM : M.IsPlanar) : IsDiscRegion M faces where
  toBoundaryCycle := boundary
  reclosed_connected := reclosedMap_connected M faces boundary hM.1
  euler_preserved := reclosedMap_euler_preserved M faces boundary hwalk hM

end GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

namespace GroupApproximation.GGT.VanKampen.Embedded

open Surgery.MapCollapse
universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
  {faces : Finset Delta.toCombMap.Face}

/-- The existing embedded boundary already contains the walk needed to
construct a disc region in the source planar diagram. -/
def FaceSetBoundary.toDiscRegion (B : FaceSetBoundary Delta faces) :
    IsDiscRegion Delta.toCombMap faces :=
  B.mapBoundaryCycle.toDiscRegion_of_followsBoundary _ _ B.mapBoundaryCycle_follows Delta.planar

end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.reclosedMap_planar
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.reclosedMap_euler_preserved
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.toDiscRegion_of_followsBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.FaceSetBoundary.toDiscRegion
