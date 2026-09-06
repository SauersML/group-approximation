import GroupApproximation.GGT.VanKampen.CactusBoundary
import GroupApproximation.GGT.VanKampen.FiniteCycleSplit

/-!
# Coordinates for one cycle, retaining every other permutation orbit

A closed orbit list gives consecutive finite coordinates on the chosen cycle.
Its complement is invariant. The resulting equivalence identifies the whole
permutation with the sum of that rotation and its unchanged complement.
-/

namespace GroupApproximation.GGT.VanKampen.PermCycleCoordinates

open Equiv
universe u
variable {D : Type u} [Fintype D] [DecidableEq D]

theorem length_pos (p : Perm D) (a : D) : 0 < (closedOrbitList p a).length := by
  exact List.length_pos_iff.mpr (closedOrbitList.nonempty p a)

theorem get_zero (p : Perm D) (a : D) :
    (closedOrbitList p a).get ⟨0, length_pos p a⟩ = a := by
  by_cases ha : p a = a
  · simp [closedOrbitList, ha]
  · simp only [closedOrbitList, if_neg ha, List.get_eq_getElem]
    rw [Perm.getElem_toList]
    rfl

theorem get_rotate (p : Perm D) (a : D) (i : Fin (closedOrbitList p a).length) :
    p ((closedOrbitList p a).get i) =
      (closedOrbitList p a).get (finRotate _ i) := by
  have hi := i.isLt
  by_cases hlast : i.val + 1 = (closedOrbitList p a).length
  · have hzero : finRotate (closedOrbitList p a).length i = ⟨0, length_pos p a⟩ := by
      apply Fin.ext
      rw [FiniteCycleSplit.rotate_val, if_pos hlast]
    rw [hzero]
    have h := closedOrbitList.closes p a
    simpa only [List.getLast_eq_getElem, List.head_eq_getElem, List.get_eq_getElem,
      show (closedOrbitList p a).length - 1 = i.val by omega] using h
  · have hnext : finRotate (closedOrbitList p a).length i = ⟨i.val + 1, by omega⟩ := by
      apply Fin.ext
      rw [FiniteCycleSplit.rotate_val, if_neg hlast]
    rw [hnext]
    exact (List.isChain_iff_getElem.1 (closedOrbitList.chain p a)) i.val (by omega)

abbrev Outside (p : Perm D) (a : D) := {x : D // x ∉ closedOrbitList p a}

def outsidePerm (p : Perm D) (a : D) : Perm (Outside p a) :=
  p.subtypeEquiv (fun x => by
    simp only [closedOrbitList.mem_iff_sameCycle, Perm.sameCycle_apply_right])

noncomputable def coordinates (p : Perm D) (a : D) :
    Fin (closedOrbitList p a).length ⊕ Outside p a ≃ D :=
  (Equiv.sumCongr ((closedOrbitList.nodup p a).getEquiv _) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun x => x ∈ closedOrbitList p a))

@[simp] theorem coordinates_inl (p : Perm D) (a : D)
    (i : Fin (closedOrbitList p a).length) :
    coordinates p a (Sum.inl i) = (closedOrbitList p a).get i := rfl

@[simp] theorem coordinates_inr (p : Perm D) (a : D) (x : Outside p a) :
    coordinates p a (Sum.inr x) = x.val := rfl

/-- The entire permutation in chosen-cycle/complement coordinates. -/
theorem perm_eq (p : Perm D) (a : D) :
    p = (coordinates p a).permCongr
      (Equiv.sumCongr (finRotate (closedOrbitList p a).length) (outsidePerm p a)) := by
  apply Equiv.ext
  intro d
  obtain ⟨x, rfl⟩ := (coordinates p a).surjective d
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  cases x with
  | inl i => exact get_rotate p a i
  | inr x => rfl

theorem orbit_card (p : Perm D) (a : D) :
    Nat.card (CombMap.Orbit p) = 1 + Nat.card (CombMap.Orbit (outsidePerm p a)) := by
  have hlen := length_pos p a
  letI : Nonempty (Fin (closedOrbitList p a).length) := Fin.pos_iff_nonempty.mp hlen
  have h := Nat.card_congr
    ((orbitPermCongr (coordinates p a)
      (Equiv.sumCongr (finRotate (closedOrbitList p a).length) (outsidePerm p a))).symm.trans
        (orbitSumCongr (finRotate (closedOrbitList p a).length) (outsidePerm p a)))
  rw [← perm_eq, Nat.card_sum] at h
  rw [Nat.card_congr (orbitEquivPUnit _ (CactusShape.finRotate_sameCycle hlen))] at h
  simpa using h

end GroupApproximation.GGT.VanKampen.PermCycleCoordinates

#audit_axioms GroupApproximation.GGT.VanKampen.PermCycleCoordinates.get_rotate
#audit_axioms GroupApproximation.GGT.VanKampen.PermCycleCoordinates.perm_eq
#audit_axioms GroupApproximation.GGT.VanKampen.PermCycleCoordinates.orbit_card
