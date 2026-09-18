import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.GGT.VanKampen.CombMapRestrictionPlanarity
import GroupApproximation.GGT.VanKampen.SurgeryPinchSplitMap
import GroupApproximation.GGT.VanKampen.FaceCycle
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepGenusSplit
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBridgeFirstReturn
import Mathlib.Data.List.Rotate
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-65: restricting a map to a successor walk

Lane gl-p07-65.  Certifies no printed sentence on its own.  NOT COMPILED.

Route (genus zero, first return).  Let `L` be a duplicate-free walk of a map `M` whose cyclic
steps are successor steps (`WitnessStepGenusSucc M L`).  Restrict `M` to the edges of `L`
(`SimpleClosedWalkSides.walkMap`, an actual restriction).
* `witnessStepSub_succ_lift`: a successor step of `M` relative to `l` between retained darts is
  a successor step of the restriction relative to the lift of `l`.  The restricted rotation is
  the first return of `σ`, so its intermediate darts are intermediate darts of the old step.
* `witnessStepSub_facePerm_of_succ`: in the restriction to `L` every dart or its reverse is on
  the lift of `L`, so a successor step there has no intermediate dart: it is one face step.
* `witnessStepSub_isFaceCycle_of_steps`: hence the lift of `L` is a face cycle.
* `witnessStepSub_connected`: every dart is on that face or reverses a dart on it, so the
  restriction is connected, hence planar when `M` is (`CombMap.IsRestriction.planar`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u

open SimpleClosedWalkSides

namespace FourPieceWitness

/-- Every entry of `L` is kept by the restriction to `L`. -/
theorem witnessStepSub_keepSelf (M : CombMap.{u}) (L : List M.Dart) :
    ∀ e ∈ L, walkKeep M L e :=
  fun _ he => Or.inl he

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSub_keepSelf

/-- **The lift of a list of retained darts** to the restriction to `L`. -/
def witnessStepSub_lift (M : CombMap.{u}) (L l : List M.Dart)
    (hl : ∀ e ∈ l, walkKeep M L e) : List (walkMap M L).Dart :=
  l.attachWith (walkKeep M L) hl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSub_lift

/-- The lift reads back as the list. -/
theorem witnessStepSub_lift_map (M : CombMap.{u}) (L l : List M.Dart)
    (hl : ∀ e ∈ l, walkKeep M L e) :
    (witnessStepSub_lift M L l hl).map Subtype.val = l :=
  List.attachWith_map_subtype_val hl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSub_lift_map

/-- A retained dart is on the lift iff its value is on the list. -/
theorem witnessStepSub_mem_lift (M : CombMap.{u}) (L l : List M.Dart)
    (hl : ∀ e ∈ l, walkKeep M L e) (z : (walkMap M L).Dart) :
    z ∈ witnessStepSub_lift M L l hl ↔ z.1 ∈ l :=
  List.mem_attachWith hl z

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSub_mem_lift

/-- The lift has the length of the list. -/
theorem witnessStepSub_lift_length (M : CombMap.{u}) (L l : List M.Dart)
    (hl : ∀ e ∈ l, walkKeep M L e) :
    (witnessStepSub_lift M L l hl).length = l.length :=
  List.length_attachWith

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSub_lift_length

/-- The lift of a duplicate-free list is duplicate free. -/
theorem witnessStepSub_lift_nodup (M : CombMap.{u}) (L l : List M.Dart)
    (hl : ∀ e ∈ l, walkKeep M L e) (hnd : l.Nodup) :
    (witnessStepSub_lift M L l hl).Nodup :=
  List.Nodup.of_map Subtype.val (by rw [witnessStepSub_lift_map]; exact hnd)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSub_lift_nodup

/-- **A successor step between retained darts lifts to the restriction.** -/
theorem witnessStepSub_succ_lift (M : CombMap.{u}) (L l : List M.Dart)
    (hl : ∀ e ∈ l, walkKeep M L e) (c d : (walkMap M L).Dart)
    (h : WitnessStepGenusSucc M l c.1 d.1) :
    WitnessStepGenusSucc (walkMap M L) (witnessStepSub_lift M L l hl) c d := by
  obtain ⟨m, hm, hσ, hnot⟩ := h
  obtain ⟨m', hm', hq, hmid⟩ := witnessStepBridge_firstReturn_iterate
    (walkMap_isRestriction M L).sigma_firstReturn m ((walkMap M L).alpha c) d hm hσ
  refine ⟨m', hm', hq, ?_⟩
  intro k hk hkm
  obtain ⟨j, hj, hjm, hje⟩ := hmid k hk hkm
  have hval : (((walkMap M L).sigma ^ k) ((walkMap M L).alpha c)).1 =
      (M.sigma ^ j) (M.alpha c.1) := hje
  obtain ⟨h1, h2⟩ := hnot j hj hjm
  refine ⟨fun hz => h1 ?_, fun hz => h2 ?_⟩
  · have h3 : (((walkMap M L).sigma ^ k) ((walkMap M L).alpha c)).1 ∈ l :=
      (witnessStepSub_mem_lift M L l hl _).mp hz
    exact Eq.mp (congrArg (fun z => z ∈ l) hval) h3
  · have h3 : M.alpha (((walkMap M L).sigma ^ k) ((walkMap M L).alpha c)).1 ∈ l :=
      (witnessStepSub_mem_lift M L l hl _).mp hz
    exact Eq.mp (congrArg (fun z => M.alpha z ∈ l) hval) h3

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSub_succ_lift
