import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionRotate
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryEnumeration
import GroupApproximation.GGT.VanKampen.SurgeryReclosedPlanarity
import GroupApproximation.Meta.AxiomGuard

/-!
# Pocket boundary cycles that follow the boundary walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7.  The pocket `Ξ` is cut out along its
boundary, and collapsing the pocket reads the complement's boundary cycle as an actual walk
around the face set.  `BoundaryCycle.FollowsBoundary` records that the listing is such a walk.
The disc condition does not include it, so it has to be carried through every step that
rebuilds a listing.

* `BoundaryCycle.followsBoundary_congr`: the condition depends on the listing only through its
  cyclic successor;
* `BoundaryCycle.followsBoundary_ofIsRotated_iff` and
  `IsDiscRegion.followsBoundary_ofIsRotated_iff`: starting the listing at another dart does not
  change it;
* `FaceSetCircuits.toDiscRegion_followsBoundary`: the disc region built from the single boundary
  circuit of a planar source follows the boundary;
* `PocketRegion.withOuter_outer_followsBoundary_iff`: restarting the complement cycle of a pocket
  does not change it.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

namespace Surgery.MapCollapse

namespace BoundaryCycle

variable {M : CombMap.{v}} {faces : Finset M.Face}

/-- Following the boundary depends on a boundary cycle only through its cyclic successor. -/
theorem followsBoundary_congr {boundary boundary' : BoundaryCycle M faces}
    (h : boundary.boundaryPerm = boundary'.boundaryPerm) :
    boundary.FollowsBoundary ↔ boundary'.FollowsBoundary := by
  unfold FollowsBoundary
  rw [h]

/-- Starting a boundary cycle at another dart does not change whether it follows the
boundary. -/
theorem followsBoundary_ofIsRotated_iff (boundary : BoundaryCycle M faces) {l : List M.Dart}
    (h : boundary.cycle ~r l) :
    (boundary.ofIsRotated h).FollowsBoundary ↔ boundary.FollowsBoundary :=
  followsBoundary_congr (boundary.boundaryPerm_ofIsRotated h)

end BoundaryCycle

/-- Starting the cycle of a disc region at another dart does not change whether it follows the
boundary. -/
theorem IsDiscRegion.followsBoundary_ofIsRotated_iff {M : CombMap.{v}} {faces : Finset M.Face}
    (region : IsDiscRegion M faces) {l : List M.Dart} (h : region.cycle ~r l) :
    (region.ofIsRotated h).FollowsBoundary ↔ region.FollowsBoundary :=
  region.toBoundaryCycle.followsBoundary_ofIsRotated_iff h

namespace FaceSetCircuits

variable (M : CombMap.{v}) (faces : Finset M.Face)

/-- The disc region built from the single boundary circuit of a planar source follows the
boundary. -/
theorem toDiscRegion_followsBoundary (c : Component M faces)
    (hall : ∀ d : BoundaryDart M faces, (Quotient.mk'' d : Component M faces) = c)
    (hM : M.IsPlanar) : (toDiscRegion M faces c hall hM).FollowsBoundary :=
  toBoundaryCycle_follows M faces c hall

end FaceSetCircuits

end Surgery.MapCollapse

namespace PocketRegion

open Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- Restarting the complement cycle of a pocket does not change whether it follows the
boundary. -/
theorem withOuter_outer_followsBoundary_iff (P : PocketRegion Delta)
    {l : List Delta.toCombMap.Dart} (h : Embedded.invDarts Delta P.outer.cycle ~r l) :
    (P.withOuter h).outer.FollowsBoundary ↔ P.outer.FollowsBoundary :=
  P.outer.followsBoundary_ofIsRotated_iff _

end PocketRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.followsBoundary_congr
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.followsBoundary_ofIsRotated_iff
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.IsDiscRegion.followsBoundary_ofIsRotated_iff
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.FaceSetCircuits.toDiscRegion_followsBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.withOuter_outer_followsBoundary_iff
