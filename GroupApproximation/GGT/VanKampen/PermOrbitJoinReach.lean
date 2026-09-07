import GroupApproximation.GGT.VanKampen.PermOrbitJoin

/-!
# Reachability through a joined pair of permutation cycles

When a transposition joins distinct cycles, every old cycle remains connected
in the new permutation. This lets ambient face paths survive edge deletion.
-/

namespace GroupApproximation.GGT.VanKampen.PermCycleCoordinates

open Equiv
universe u
variable {D : Type u} [Fintype D] [DecidableEq D]

theorem sameCycle_mul_swap_of_not_sameCycle (p : Perm D) (a b : D)
    (hab : ¬ p.SameCycle a b) : (p * Equiv.swap a b).SameCycle a b := by
  have hi := sameCycle_swap_mul_of_not_sameCycle p⁻¹ a b (by
    simpa only [Perm.sameCycle_inv] using hab)
  have h : ((p * Equiv.swap a b)⁻¹).SameCycle a b := by
    simpa only [mul_inv_rev, Equiv.swap_inv] using hi
  exact Perm.sameCycle_inv.mp h

omit [Fintype D] in
/-- If the transposed points belong to one new cycle, every old successor
step can be followed inside a new cycle. -/
theorem sameCycle_old_step_mul_swap (p : Perm D) (a b : D)
    (hab : (p * Equiv.swap a b).SameCycle a b) (x : D) :
    (p * Equiv.swap a b).SameCycle x (p x) := by
  by_cases hxa : x = a
  · subst x
    simpa only [Perm.mul_apply, Equiv.swap_apply_right] using hab.apply_right
  · by_cases hxb : x = b
    · subst x
      simpa only [Perm.mul_apply, Equiv.swap_apply_left] using hab.symm.apply_right
    · have h : (p * Equiv.swap a b).SameCycle x ((p * Equiv.swap a b) x) :=
        Perm.SameCycle.rfl.apply_right
      simpa only [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb] using h

/-- Joining cycles preserves the reachability of every pair in an old cycle. -/
theorem sameCycle_mul_swap_of_sameCycle (p : Perm D) (a b : D)
    (hab : (p * Equiv.swap a b).SameCycle a b) {x y : D} (hxy : p.SameCycle x y) :
    (p * Equiv.swap a b).SameCycle x y := by
  exact Quotient.exact (OrbitClassifier.eq_of_sameCycle p
    (fun x => (Quotient.mk'' x : CombMap.Orbit (p * Equiv.swap a b)))
    (fun x => Quotient.sound (sameCycle_old_step_mul_swap p a b hab x).symm) hxy)

end GroupApproximation.GGT.VanKampen.PermCycleCoordinates

#audit_axioms GroupApproximation.GGT.VanKampen.PermCycleCoordinates.sameCycle_mul_swap_of_not_sameCycle
#audit_axioms GroupApproximation.GGT.VanKampen.PermCycleCoordinates.sameCycle_mul_swap_of_sameCycle
