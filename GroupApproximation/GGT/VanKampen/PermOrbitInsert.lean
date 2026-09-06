import GroupApproximation.GGT.VanKampen.CactusTopology
import Mathlib.Logic.Equiv.Option
import GroupApproximation.Meta.AxiomGuard

/-!
# Inserting a new dart into a permutation orbit

The new point `none` is inserted immediately before a chosen old point.
It joins that point's orbit, while all old orbit identifications are
preserved. Applying this operation twice inserts the two darts of an edge
at chosen corners without changing the map's vertex set.
-/

namespace GroupApproximation.GGT.VanKampen.PermOrbitInsert

open Equiv
universe u
variable {D : Type u}

noncomputable def insertBefore (p : Perm D) (a : D) : Perm (Option D) := by
  classical
  exact Equiv.swap none (some a) * Equiv.optionCongr p

@[simp] theorem insertBefore_none (p : Perm D) (a : D) : insertBefore p a none = some a := by
  classical
  simp [insertBefore, Perm.mul_apply, Equiv.optionCongr_apply]

theorem insertBefore_some [DecidableEq D] (p : Perm D) (a x : D) :
    insertBefore p a (some x) = if p x = a then none else some (p x) := by
  classical
  simp [insertBefore, Perm.mul_apply, Equiv.optionCongr_apply, Equiv.swap_apply_def]

theorem sameCycle_none (p : Perm D) (a : D) :
    (insertBefore p a).SameCycle none (some a) := by
  rw [← insertBefore_none p a]
  exact Perm.SameCycle.rfl.apply_right

/-- An old successor move becomes either one or two moves in the new cycle. -/
theorem sameCycle_old_step (p : Perm D) (a x : D) :
    (insertBefore p a).SameCycle (some x) (some (p x)) := by
  classical
  have hstep : (insertBefore p a).SameCycle (some x) (insertBefore p a (some x)) :=
    Perm.SameCycle.rfl.apply_right
  by_cases hx : p x = a
  · rw [insertBefore_some, if_pos hx] at hstep
    exact hstep.trans (by simpa only [hx] using sameCycle_none p a)
  · simpa only [insertBefore_some, if_neg hx] using hstep

theorem sameCycle_some_of_sameCycle [Finite D] (p : Perm D) (a : D)
    {x y : D} (hxy : p.SameCycle x y) :
    (insertBefore p a).SameCycle (some x) (some y) := by
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  have hpow : ∀ (m : ℕ) (z : D),
      (insertBefore p a).SameCycle (some z) (some ((p ^ m) z)) := by
    intro m
    induction m with
    | zero => intro z; exact Perm.SameCycle.rfl
    | succ m ih =>
        intro z
        rw [pow_succ, Perm.mul_apply]
        exact (sameCycle_old_step p a z).trans (ih (p z))
  simpa only [hn] using hpow n x

/-- The new dart is classified by the old orbit into which it was inserted. -/
def orbitClass (p : Perm D) (a : D) : Option D → CombMap.Orbit p
  | none => Quotient.mk'' a
  | some x => Quotient.mk'' x

theorem orbitClass_invariant (p : Perm D) (a : D) (x : Option D) :
    orbitClass p a (insertBefore p a x) = orbitClass p a x := by
  classical
  cases x with
  | none => rw [insertBefore_none]; rfl
  | some x =>
      rw [insertBefore_some]
      split_ifs with hx
      · change (Quotient.mk'' a : CombMap.Orbit p) = Quotient.mk'' x
        rw [← hx]
        exact Quotient.sound Perm.SameCycle.rfl.apply_left
      · exact Quotient.sound Perm.SameCycle.rfl.apply_left

theorem sameCycle_some_iff [Finite D] (p : Perm D) (a x y : D) :
    (insertBefore p a).SameCycle (some x) (some y) ↔ p.SameCycle x y := by
  constructor
  · intro hxy
    exact Quotient.exact (OrbitClassifier.eq_of_sameCycle (insertBefore p a)
      (orbitClass p a) (orbitClass_invariant p a) hxy)
  · exact sameCycle_some_of_sameCycle p a

/-- The actual orbit equivalence: insertion changes no old orbit and
introduces no new orbit. -/
noncomputable def orbitEquiv [Finite D] (p : Perm D) (a : D) :
    CombMap.Orbit (insertBefore p a) ≃ CombMap.Orbit p where
  toFun := Quotient.lift (orbitClass p a) (fun _ _ h =>
    OrbitClassifier.eq_of_sameCycle (insertBefore p a) (orbitClass p a)
      (orbitClass_invariant p a) h)
  invFun := Quotient.map some (fun _ _ h => sameCycle_some_of_sameCycle p a h)
  left_inv q := by
    refine Quotient.inductionOn' q ?_
    intro x
    cases x with
    | none => exact Quotient.sound (sameCycle_none p a).symm
    | some x => rfl
  right_inv q := by
    refine Quotient.inductionOn' q ?_
    intro x
    rfl

end GroupApproximation.GGT.VanKampen.PermOrbitInsert

#audit_axioms GroupApproximation.GGT.VanKampen.PermOrbitInsert.sameCycle_old_step
#audit_axioms GroupApproximation.GGT.VanKampen.PermOrbitInsert.sameCycle_some_iff
#audit_axioms GroupApproximation.GGT.VanKampen.PermOrbitInsert.orbitEquiv
