import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionSimpleWalk
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSideFaces
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket region of a simple pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of
`Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

The boundary cycle of a simple pocket face set is a simple closed walk.  The walk's side is a
pocket region (`PocketRegion.ofSimpleClosedWalk`), both of whose cycles follow the boundary, and
the inverse of its complement cycle is the walk itself.  So the split `s_1 t_1 s_2 t_2` of the
boundary cycle is the split of the carrier.  The map of a disc diagram is connected and the
exterior face is off the face set, so the walk's side is the face set
(`SimpleClosedWalkSides.sideFaces_boundaryCycle_eq`): the kept cell stays inside and the source
cell outside.

* `PocketFaceSet.toPocketCarrier`: the carrier of a simple pocket face set whose faces are the
  walk's side.
* `PocketFaceSet.nonempty_pocketCarrier_of_sideFaces_eq`: the carrier exists.
* `pocketRegionOfSimple`: every simple pocket face set has a pocket carrier
  (`PocketRegionOfSimpleStatement`).

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- The exterior face is not on the walk's side when that side is the face set. -/
theorem outerFace_not_mem_sideFaces (K : PocketFaceSet D eps X lo hi)
    (hfaces : sideFaces X.toCombMap K.boundary.cycle = K.faces) :
    X.outerFace ∉ sideFaces X.toCombMap K.boundary.cycle := by
  rw [hfaces]
  exact K.outerFace_not_mem

/-- **The carrier of a simple pocket.**  The pocket region on the side of the boundary cycle,
with the cells, arcs, sides and bounds of the face set. -/
noncomputable def toPocketCarrier (K : PocketFaceSet D eps X lo hi) (hK : K.Simple)
    (hfaces : sideFaces X.toCombMap K.boundary.cycle = K.faces) :
    PocketCarrier D eps X lo hi where
  pocket := PocketRegion.ofSimpleClosedWalk hK.isSimpleClosedWalk
    (K.outerFace_not_mem_sideFaces hfaces)
  inner_follows := (PocketRegion.ofSimpleClosedWalk_followsBoundary hK.isSimpleClosedWalk
    (K.outerFace_not_mem_sideFaces hfaces)).1
  outer_follows := (PocketRegion.ofSimpleClosedWalk_followsBoundary hK.isSimpleClosedWalk
    (K.outerFace_not_mem_sideFaces hfaces)).2
  source := K.source
  source_not_mem := by
    show (cell X K.source).face ∉ sideFaces X.toCombMap K.boundary.cycle
    rw [hfaces]
    exact K.source_not_mem
  kept := K.kept
  kept_mem := by
    show (cell X K.kept).face ∈ sideFaces X.toCombMap K.boundary.cycle
    rw [hfaces]
    exact K.kept_mem
  sourceArc := K.sourceArc
  targetArc := K.targetArc
  firstSide := K.firstSide
  secondSide := K.secondSide
  decomposition := (PocketRegion.ofSimpleClosedWalk_invDarts_outer hK.isSimpleClosedWalk
    (K.outerFace_not_mem_sideFaces hfaces)).trans K.decomposition
  firstSide_length_le := K.firstSide_length_le
  secondSide_length_le := K.secondSide_length_le
  firstSide_norm_le := K.firstSide_norm_le
  secondSide_norm_le := K.secondSide_norm_le
  lo_le := K.lo_le
  le_hi := K.le_hi

theorem toPocketCarrier_faces (K : PocketFaceSet D eps X lo hi) (hK : K.Simple)
    (hfaces : sideFaces X.toCombMap K.boundary.cycle = K.faces) :
    (K.toPocketCarrier hK hfaces).pocket.faces = K.faces :=
  hfaces

/-- A simple pocket face set whose faces are the walk's side is a pocket carrier. -/
theorem nonempty_pocketCarrier_of_sideFaces_eq (K : PocketFaceSet D eps X lo hi)
    (hK : K.Simple) (hfaces : sideFaces X.toCombMap K.boundary.cycle = K.faces) :
    Nonempty (PocketCarrier D eps X lo hi) :=
  ⟨K.toPocketCarrier hK hfaces⟩

/-- The walk's side of the boundary cycle is the face set: the map is connected and the exterior
face is off the face set. -/
theorem sideFaces_boundary_cycle_eq_faces (K : PocketFaceSet D eps X lo hi) :
    sideFaces X.toCombMap K.boundary.cycle = K.faces :=
  sideFaces_boundaryCycle_eq (CombMap.connected_of_planar _ X.planar) K.boundary
    K.outerFace_not_mem

end PocketFaceSet

/-- **The region piece.**  Every simple pocket face set has a pocket carrier, on the side of its
boundary cycle. -/
theorem pocketRegionOfSimple : PocketRegionOfSimpleStatement.{u, w, v} :=
  fun _D _eps _W _X _lo _hi K hK => ⟨K.toPocketCarrier hK K.sideFaces_boundary_cycle_eq_faces⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.outerFace_not_mem_sideFaces
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.toPocketCarrier
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.toPocketCarrier_faces
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.nonempty_pocketCarrier_of_sideFaces_eq
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.sideFaces_boundary_cycle_eq_faces
#audit_closed_axioms GroupApproximation.GGT.VanKampen.pocketRegionOfSimple
