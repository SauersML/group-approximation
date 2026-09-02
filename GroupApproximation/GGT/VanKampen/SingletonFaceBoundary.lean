import GroupApproximation.GGT.VanKampen.CombMapStars
import GroupApproximation.GGT.VanKampen.SurgeryMap

/-!
# Singleton face boundaries

`Surgery.MapCollapse.IsDiscRegion` separates the boundary-cycle condition from
the two global topological conditions (connectedness of the reclosed map and
Euler preservation).  This file proves the boundary-cycle part for a single
face.  The only local obstruction is an edge whose two darts belong to that
face: such an edge is deleted by `reclosedMap`, so its darts cannot be the
boundary of the singleton region.

The resulting theorem is the exact map-level input needed by a one-face
deletion certificate.  It intentionally leaves the two global fields visible;
they are not consequences of the current `DiscDiagram` record.  The final
model theorem checks the local certificate on the six-dart one-triangle map.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Surgery
namespace MapCollapse

universe u w v

open GroupApproximation.HullSC

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

noncomputable local instance faceDecidableEq : DecidableEq Delta.toCombMap.Face :=
  Classical.decEq _

/-! ## The local singleton boundary calculation -/

/-- The no-internal-edge condition for a face. -/
def NoInternalFaceDart (M : CombMap) (f : M.Face) : Prop :=
  ∀ d, M.faceOf d = f → M.faceOf (M.alpha d) ≠ f

theorem singleton_boundary_iff_of_noInternalFaceDart
    {M : CombMap} (f : M.Face) (hno : NoInternalFaceDart M f)
    (d : M.Dart) :
    IsBoundaryDart M ({f} : Finset M.Face) d ↔ M.faceOf d = f := by
  constructor
  · intro hd
    exact Finset.mem_singleton.mp hd.1
  · intro hdf
    refine ⟨?_, ?_⟩
    · exact Finset.mem_singleton.mpr hdf
    · intro halpha
      exact hno d hdf (Finset.mem_singleton.mp halpha)

/-- A stored face boundary is the map-collapse boundary cycle of a singleton
face whenever that face has no internally paired dart. -/
noncomputable def singletonBoundaryCycle_of_faceBoundary
    (M : CombMap) (f : M.Face) (B : FaceBoundary M f)
    (hno : NoInternalFaceDart M f) :
    BoundaryCycle M ({f} : Finset M.Face) where
  cycle := B.darts
  cycle_nonempty := B.nonempty
  cycle_nodup := B.nodup
  cycle_mem_iff := by
    intro d
    rw [B.mem_iff]
    exact (singleton_boundary_iff_of_noInternalFaceDart f hno d).symm

/-- The disc-diagram specialization uses its canonical face boundary. -/
noncomputable def singletonBoundaryCycle
    (f : Delta.toCombMap.Face) (hno : NoInternalFaceDart Delta.toCombMap f) :
    BoundaryCycle Delta.toCombMap ({f} : Finset Delta.toCombMap.Face) :=
  singletonBoundaryCycle_of_faceBoundary Delta.toCombMap f
    (Delta.faceBoundary f) hno

@[simp]
theorem singletonBoundaryCycle_cycle
    (f : Delta.toCombMap.Face) (hno : NoInternalFaceDart Delta.toCombMap f) :
    (singletonBoundaryCycle (Delta := Delta) f hno).cycle =
      (Delta.faceBoundary f).darts :=
  rfl

/-! ## The narrowed `IsDiscRegion` constructor -/

/-- The genuinely remaining topological data for a singleton collapse.  The
boundary cycle itself is constructed by `singletonBoundaryCycle`; only the
two fields already named by `IsDiscRegion` remain. -/
structure SingletonDiscRegionData
    (f : Delta.toCombMap.Face) (hno : NoInternalFaceDart Delta.toCombMap f) where
  reclosed_connected :
    (reclosedMap Delta.toCombMap ({f} : Finset Delta.toCombMap.Face)
      (singletonBoundaryCycle (Delta := Delta) f hno)).IsConnected
  euler_preserved :
    (reclosedMap Delta.toCombMap ({f} : Finset Delta.toCombMap.Face)
      (singletonBoundaryCycle (Delta := Delta) f hno)).eulerCharacteristic =
      Delta.toCombMap.eulerCharacteristic

noncomputable def SingletonDiscRegionData.toIsDiscRegion
    {f : Delta.toCombMap.Face} {hno : NoInternalFaceDart Delta.toCombMap f}
    (data : SingletonDiscRegionData (Delta := Delta) f hno) :
    IsDiscRegion Delta.toCombMap ({f} : Finset Delta.toCombMap.Face) where
  cycle := (singletonBoundaryCycle (Delta := Delta) f hno).cycle
  cycle_nonempty := (singletonBoundaryCycle (Delta := Delta) f hno).cycle_nonempty
  cycle_nodup := (singletonBoundaryCycle (Delta := Delta) f hno).cycle_nodup
  cycle_mem_iff := (singletonBoundaryCycle (Delta := Delta) f hno).cycle_mem_iff
  reclosed_connected := data.reclosed_connected
  euler_preserved := data.euler_preserved

theorem singleton_discRegion_boundary_eq
    {f : Delta.toCombMap.Face} {hno : NoInternalFaceDart Delta.toCombMap f}
    (data : SingletonDiscRegionData (Delta := Delta) f hno) :
    (data.toIsDiscRegion.toBoundaryCycle).cycle =
      (Delta.faceBoundary f).darts :=
  rfl

/-! ## The exact singleton-face producer interface -/

/-- Every stored relator face is assigned a singleton map-collapse region whose
boundary is the stored face cycle.  This is the topological producer needed by
the one-face path-deletion step. -/
def RelatorFaceSingletonProducer : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, 0} W)
    (C : RelatorCell Delta.toCombMap Delta.outerFace W),
    C ∈ Delta.relatorCells →
    ∃ region : IsDiscRegion Delta.toCombMap {C.face},
      region.toBoundaryCycle.cycle = (Delta.faceBoundary C.face).darts

/-- The local singleton construction discharges the exact producer once the
two topological fields of `IsDiscRegion` are supplied for each relator face.
The two fields are deliberately quantified here: neither is present in the
bare `DiscDiagram` record. -/
theorem relatorFaceSingletonProducer_of_topology
    (hdata : ∀ (Delta : DiscDiagram.{u, w, 0} W)
      (C : RelatorCell Delta.toCombMap Delta.outerFace W),
      C ∈ Delta.relatorCells →
      ∃ hno : NoInternalFaceDart Delta.toCombMap C.face,
        Nonempty (SingletonDiscRegionData (Delta := Delta) C.face hno)) :
    RelatorFaceSingletonProducer (W := W) := by
  change ∀ (Delta : DiscDiagram.{u, w, 0} W)
    (C : RelatorCell Delta.toCombMap Delta.outerFace W),
    C ∈ Delta.relatorCells →
    ∃ region : IsDiscRegion Delta.toCombMap {C.face},
      region.toBoundaryCycle.cycle = (Delta.faceBoundary C.face).darts
  intro Delta C hC
  obtain ⟨hno, ⟨data⟩⟩ := hdata Delta C hC
  exact ⟨data.toIsDiscRegion, singleton_discRegion_boundary_eq data⟩

/-! ## The one-triangle local model -/

noncomputable section OneTriangleModel

local instance oneTriangleDartDecidableEq : DecidableEq OneTriangleDart :=
  Classical.decEq _

private theorem oneTriangle_face_false_ne_true (i j : ZMod 3) :
    oneTriangleCombMap.faceOf (i, false) ≠
      oneTriangleCombMap.faceOf (j, true) := by
  intro h
  rw [oneTriangleCombMap.faceOf_eq_iff] at h
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hbool : ∀ n : ℕ,
      (oneTriangleCombMap.facePerm ^ n) (i, false) =
        ((i + n), false) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, ih]
        rw [oneTriangle_facePerm_false]
        congr 1
        simp [add_assoc]
  have := congrArg Prod.snd (hbool n)
  rw [hn] at this
  cases this

theorem oneTriangle_noInternalFaceDart (i : ZMod 3) :
    NoInternalFaceDart oneTriangleCombMap
      (oneTriangleCombMap.faceOf (i, false)) := by
  intro d hd
  obtain ⟨j, b⟩ := d
  cases b with
  | false =>
      change oneTriangleCombMap.faceOf (j, true) ≠
        oneTriangleCombMap.faceOf (i, false)
      intro h
      exact oneTriangle_face_false_ne_true i j h.symm
  | true =>
      change oneTriangleCombMap.faceOf (j, false) ≠
        oneTriangleCombMap.faceOf (i, false)
      intro _
      exact (oneTriangle_face_false_ne_true i j hd.symm).elim

theorem oneTriangle_singletonBoundaryCycle_model (i : ZMod 3) :
    (singletonBoundaryCycle_of_faceBoundary oneTriangleCombMap
      (oneTriangleCombMap.faceOf (i, false))
      (FaceBoundary.based oneTriangleCombMap (i, false))
      (oneTriangle_noInternalFaceDart i)).cycle =
      ((FaceBoundary.based oneTriangleCombMap (i, false)).darts) :=
  rfl

end OneTriangleModel

end MapCollapse
end Surgery
end VanKampen
end GGT
end GroupApproximation
