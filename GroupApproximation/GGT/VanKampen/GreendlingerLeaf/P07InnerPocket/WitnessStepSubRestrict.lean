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
  List.Nodup.of_map Subtype.val
    (Eq.mpr (congrArg List.Nodup (witnessStepSub_lift_map M L l hl)) hnd)

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

/-- **A successor step relative to a covering list is one face step.**  If every dart or its
reverse is on `Γ`, a successor step relative to `Γ` has no intermediate dart. -/
theorem witnessStepSub_facePerm_of_succ (N : CombMap.{u}) (Γ : List N.Dart)
    (hcov : ∀ z, z ∈ Γ ∨ N.alpha z ∈ Γ) {c d : N.Dart}
    (h : WitnessStepGenusSucc N Γ c d) : N.facePerm c = d := by
  obtain ⟨m, hm, hmd, hmid⟩ := h
  rcases Nat.lt_or_ge 1 m with h1 | h1
  · obtain ⟨ha, hb⟩ := hmid 1 Nat.one_pos h1
    rcases hcov ((N.sigma ^ 1) (N.alpha c)) with hz | hz
    · exact absurd hz ha
    · exact absurd hz hb
  · obtain rfl : m = 1 := by omega
    rw [pow_one] at hmd
    rw [CombMap.facePerm, Equiv.Perm.mul_apply]
    exact hmd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSub_facePerm_of_succ

/-- In the restriction to `L`, every dart or its reverse is on the lift of `L`. -/
theorem witnessStepSub_cover (M : CombMap.{u}) (L : List M.Dart) (z : (walkMap M L).Dart) :
    z ∈ witnessStepSub_lift M L L (witnessStepSub_keepSelf M L) ∨
      (walkMap M L).alpha z ∈ witnessStepSub_lift M L L (witnessStepSub_keepSelf M L) := by
  have h2 : z.1 ∈ L ∨ M.alpha z.1 ∈ L := z.2
  rcases h2 with hz | hz
  · exact Or.inl ((witnessStepSub_mem_lift M L L (witnessStepSub_keepSelf M L) z).mpr hz)
  · exact Or.inr ((witnessStepSub_mem_lift M L L (witnessStepSub_keepSelf M L)
      ((walkMap M L).alpha z)).mpr hz)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSub_cover

/-- A list with two distinct entries has length at least two. -/
theorem witnessStepSub_two_le_length {α : Type*} {L : List α} {x y : α} (hx : x ∈ L)
    (hy : y ∈ L) (hxy : x ≠ y) : 2 ≤ L.length := by
  rcases L with _ | ⟨a, _ | ⟨b, r⟩⟩
  · simp at hx
  · rw [List.mem_singleton] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  · simp only [List.length_cons]
    omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSub_two_le_length

/-- **A duplicate-free list whose cyclic steps are face steps is a face cycle.** -/
theorem witnessStepSub_isFaceCycle_of_steps (N : CombMap.{u}) {Γ : List N.Dart}
    (hlen : 2 ≤ Γ.length) (hnd : Γ.Nodup)
    (h : ∀ (n : ℕ) (s t : List N.Dart) (x y : N.Dart), Γ.rotate n = s ++ x :: y :: t →
      N.facePerm x = y) : N.IsFaceCycle Γ := by
  rcases Γ with _ | ⟨x, r⟩
  · simp at hlen
  have hr : r ≠ [] := by
    rintro rfl
    simp at hlen
  refine ⟨List.cons_ne_nil x r, hnd, ?_, ?_⟩
  · exact List.isChain_iff_forall_rel_of_append_cons_cons.mpr fun a b l₁ l₂ he =>
      h 0 l₁ l₂ a b (by rw [List.rotate_zero]; exact he)
  · have e : x :: r = (x :: r.dropLast) ++ [r.getLast hr] := by
      rw [List.cons_append, List.dropLast_append_getLast hr]
    have hrot : (x :: r).rotate (x :: r.dropLast).length =
        r.getLast hr :: (x :: r.dropLast) := by
      rw [e, List.rotate_append_length_eq, List.singleton_append]
    rw [List.getLast_cons hr, List.head_cons]
    exact h (x :: r.dropLast).length [] r.dropLast (r.getLast hr) x
      (by rw [List.nil_append]; exact hrot)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSub_isFaceCycle_of_steps

/-- **A map covered by one face cycle and its reverse is connected.** -/
theorem witnessStepSub_connected (N : CombMap.{u}) {Γ : List N.Dart} (hΓ : N.IsFaceCycle Γ)
    (hcov : ∀ z, z ∈ Γ ∨ N.alpha z ∈ Γ) : N.IsConnected := by
  have hface : ∀ z, z ∈ Γ → Relation.EqvGen N.Adjacent z (Γ.head hΓ.ne_nil) := fun z hz =>
    PinchSplit.eqvGen_of_sameCycle_facePerm N ((N.faceOf_eq_iff _ _).mp ((hΓ.mem_iff z).mp hz))
  have hall : ∀ z, Relation.EqvGen N.Adjacent z (Γ.head hΓ.ne_nil) := by
    intro z
    rcases hcov z with hz | hz
    · exact hface z hz
    · exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl)) (hface _ hz)
  intro d e
  exact Relation.EqvGen.trans _ _ _ (hall d) (Relation.EqvGen.symm _ _ (hall e))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSub_connected

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
