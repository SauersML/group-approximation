import GroupApproximation.GGT.VanKampen.PermCycleCoordinates

/-!
# Splitting an arbitrary permutation cycle adds exactly one orbit

The chosen cycle is put in consecutive finite coordinates; all other cycles
are retained by an invariant complement. The two-block rotation calculation
therefore counts every orbit of the whole new permutation.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv

namespace FiniteCycleSplit

theorem orbit_card_swap_rotate {n : ℕ} (hn : 0 < n) (j : Fin n) (hj : 0 < j.val) :
    Nat.card (CombMap.Orbit (Equiv.swap (⟨0, hn⟩ : Fin n) j * finRotate n)) = 2 := by
  rcases j with ⟨k, hk⟩
  obtain ⟨l, hl, hlen⟩ : ∃ l, 0 < l ∧ n = k + l := ⟨n - k, by omega, by omega⟩
  subst n
  exact orbit_card_cut k l hj hl

end FiniteCycleSplit

namespace PermCycleCoordinates

universe u
variable {D : Type u} [Fintype D] [DecidableEq D]

/-- Exact conjugation after swapping two successors in the chosen cycle. -/
theorem swap_perm_eq (p : Perm D) (a b : D)
    (j : Fin (closedOrbitList p a).length) (hj : (closedOrbitList p a).get j = b) :
    Equiv.swap a b * p = (coordinates p a).permCongr
      (Equiv.sumCongr
        (Equiv.swap (⟨0, length_pos p a⟩ : Fin (closedOrbitList p a).length) j *
          finRotate (closedOrbitList p a).length) (outsidePerm p a)) := by
  apply Equiv.ext
  intro d
  obtain ⟨x, rfl⟩ := (coordinates p a).surjective d
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  cases x with
  | inl i =>
      change Equiv.swap a b (p ((closedOrbitList p a).get i)) =
        (closedOrbitList p a).get (Equiv.swap ⟨0, length_pos p a⟩ j (finRotate _ i))
      have hinj : Function.Injective (closedOrbitList p a).get :=
        fun _ _ h => (closedOrbitList.nodup p a).get_inj_iff.mp h
      rw [get_rotate, hinj.map_swap, get_zero, hj]
  | inr x =>
      change Equiv.swap a b (p x.val) = p x.val
      have hx : p x.val ∉ closedOrbitList p a := (outsidePerm p a x).property
      have ha : a ∈ closedOrbitList p a :=
        (closedOrbitList.mem_iff_sameCycle p a a).mpr Perm.SameCycle.rfl
      have hb : b ∈ closedOrbitList p a := hj ▸ List.get_mem _ j
      exact Equiv.swap_apply_of_ne_of_ne
        (fun h => hx (h.symm ▸ ha)) (fun h => hx (h.symm ▸ hb))

/-- A transposition at distinct points of one cycle splits it into exactly
two; no other orbit changes. -/
theorem orbit_card_swap_mul (p : Perm D) (a b : D) (hab : a ≠ b)
    (hcycle : p.SameCycle a b) :
    Nat.card (CombMap.Orbit (Equiv.swap a b * p)) = Nat.card (CombMap.Orbit p) + 1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((closedOrbitList.mem_iff_sameCycle p a b).mpr hcycle)
  have hjpos : 0 < j.val := by
    by_contra h
    have hjzero : j = ⟨0, length_pos p a⟩ := Fin.ext (by change j.val = 0; omega)
    rw [hjzero, get_zero] at hj
    exact hab hj
  have h := Nat.card_congr
    ((orbitPermCongr (coordinates p a)
      (Equiv.sumCongr
        (Equiv.swap (⟨0, length_pos p a⟩ : Fin (closedOrbitList p a).length) j *
          finRotate (closedOrbitList p a).length) (outsidePerm p a))).symm.trans
        (orbitSumCongr _ _))
  rw [← swap_perm_eq p a b j hj, Nat.card_sum,
    FiniteCycleSplit.orbit_card_swap_rotate (length_pos p a) j hjpos] at h
  rw [h, orbit_card p a]
  omega

end PermCycleCoordinates
end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.FiniteCycleSplit.orbit_card_swap_rotate
#audit_axioms GroupApproximation.GGT.VanKampen.PermCycleCoordinates.swap_perm_eq
#audit_axioms GroupApproximation.GGT.VanKampen.PermCycleCoordinates.orbit_card_swap_mul
