import GroupApproximation.GGT.VanKampen.PermOrbitSplit

/-!
# Joining two permutation cycles by a transposition

The complementary case to cycle splitting joins two distinct cycles into
one. Traversing the old cycle of the first point now ends at the second
point. Applying the proved splitting theorem to the new permutation gives
the exact count, including fixed-point cycles.
-/

namespace GroupApproximation.GGT.VanKampen.PermCycleCoordinates

open Equiv
universe u
variable {D : Type u} [Fintype D] [DecidableEq D]

theorem sameCycle_swap_mul_of_not_sameCycle (p : Perm D) (a b : D)
    (hab : ¬ p.SameCycle a b) : (Equiv.swap a b * p).SameCycle a b := by
  let l := closedOrbitList p a
  let q := Equiv.swap a b * p
  have hpos : 0 < l.length := length_pos p a
  have ha : l.get ⟨0, hpos⟩ = a := get_zero p a
  have hb : b ∉ l := fun h => hab ((closedOrbitList.mem_iff_sameCycle p a b).mp h)
  have hreach : ∀ (i : ℕ) (hi : i < l.length), q.SameCycle a (l.get ⟨i, hi⟩) := by
    intro i
    induction i with
    | zero => intro hi; rw [ha]
    | succ i ih =>
        intro hi
        have hip : i < l.length := by omega
        have hp : p (l.get ⟨i, hip⟩) = l.get ⟨i + 1, hi⟩ :=
          (List.isChain_iff_getElem.mp (closedOrbitList.chain p a)) i hi
        have hna : l.get ⟨i + 1, hi⟩ ≠ a := by
          intro heq
          have hidx : (⟨i + 1, hi⟩ : Fin l.length) = ⟨0, hpos⟩ :=
            (closedOrbitList.nodup p a).get_inj_iff.mp (heq.trans ha.symm)
          have : i + 1 = 0 := congrArg Fin.val hidx
          omega
        have hnb : l.get ⟨i + 1, hi⟩ ≠ b :=
          fun heq => hb (heq ▸ List.get_mem l ⟨i + 1, hi⟩)
        have hq : q (l.get ⟨i, hip⟩) = l.get ⟨i + 1, hi⟩ := by
          change Equiv.swap a b (p (l.get ⟨i, hip⟩)) = _
          rw [hp, Equiv.swap_apply_of_ne_of_ne hna hnb]
        simpa only [hq] using (ih hip).apply_right
  have hlast : p (l.get ⟨l.length - 1, by omega⟩) = a := by
    have h : p (l.get ⟨l.length - 1, by omega⟩) = l.get ⟨0, hpos⟩ := by
      simpa only [List.getLast_eq_getElem, List.head_eq_getElem, List.get_eq_getElem]
        using closedOrbitList.closes p a
    exact h.trans ha
  have hq : q (l.get ⟨l.length - 1, by omega⟩) = b := by
    change Equiv.swap a b (p (l.get _)) = b
    rw [hlast, Equiv.swap_apply_left]
  simpa only [hq] using (hreach (l.length - 1) (by omega)).apply_right

/-- Swapping successors in distinct cycles removes exactly one orbit. -/
theorem orbit_card_swap_mul_of_not_sameCycle (p : Perm D) (a b : D)
    (hab : ¬ p.SameCycle a b) :
    Nat.card (CombMap.Orbit (Equiv.swap a b * p)) + 1 = Nat.card (CombMap.Orbit p) := by
  have hne : a ≠ b := fun heq => hab (heq.sameCycle p)
  have h := orbit_card_swap_mul (Equiv.swap a b * p) a b hne
    (sameCycle_swap_mul_of_not_sameCycle p a b hab)
  simpa only [← mul_assoc, Equiv.swap_mul_self, one_mul] using h.symm

omit [Fintype D] in
/-- Moving the transposition to the other side conjugates the permutation. -/
theorem orbit_card_mul_swap_eq (p : Perm D) (a b : D) :
    Nat.card (CombMap.Orbit (p * Equiv.swap a b)) =
      Nat.card (CombMap.Orbit (Equiv.swap a b * p)) := by
  have he : p.permCongr (Equiv.swap a b * p) = p * Equiv.swap a b := by
    ext x
    simp only [Equiv.permCongr_apply, Perm.mul_apply, Equiv.apply_symm_apply]
  have h := Nat.card_congr (orbitPermCongr p (Equiv.swap a b * p))
  rw [he] at h
  exact h.symm

end GroupApproximation.GGT.VanKampen.PermCycleCoordinates

#audit_axioms GroupApproximation.GGT.VanKampen.PermCycleCoordinates.sameCycle_swap_mul_of_not_sameCycle
#audit_axioms GroupApproximation.GGT.VanKampen.PermCycleCoordinates.orbit_card_swap_mul_of_not_sameCycle
