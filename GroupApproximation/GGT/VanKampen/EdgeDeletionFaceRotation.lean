import GroupApproximation.GGT.VanKampen.EdgeDeletionFaces
import GroupApproximation.GGT.VanKampen.FaceCycle
import GroupApproximation.Meta.AxiomGuard

/-!
# Face rotation after deleting an edge, at every face degree

`EdgeDeletion.value_facePerm_of_ne` (`EdgeDeletionFaces`) computes the face
rotation of `EdgeDeletion.toCombMap M a` when both sides of the deleted edge have
degree at least two.  The planar van Kampen induction deletes an edge between the
outer face and an arbitrary neighbouring face, of any degree, so this file states
the rotation at every degree.

* `EdgeDeletion.value_facePerm_general`: a surviving dart whose old successor was
  `a` jumps to the successor of `alpha a`, or to the successor of `a` when the face
  of `alpha a` was the single dart `alpha a`; one whose old successor was `alpha a`
  jumps symmetrically; every other dart keeps its successor.
* `EdgeDeletion.value_facePerm_of_ne_of_ne`: the unchanged case.
* `orbitWalk_add`: walks along a permutation split additively.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv PermOrbitErasePoint

universe u

/-- Walks along a permutation split additively. -/
theorem orbitWalk_add {D : Type u} (p : Perm D) (x : D) (m : ℕ) :
    ∀ n : ℕ, orbitWalk p x (m + n) = orbitWalk p x m ++ orbitWalk p ((p ^ m) x) n
  | 0 => by simp [orbitWalk_zero]
  | n + 1 => by
      have hpow : (p ^ (m + n)) x = (p ^ n) ((p ^ m) x) := by
        rw [← Perm.mul_apply, ← pow_add, Nat.add_comm n m]
      rw [← Nat.add_assoc, orbitWalk_succ' p x (m + n), orbitWalk_add p x m n,
        orbitWalk_succ' p _ n, List.append_assoc, hpow]

namespace EdgeDeletion

open EdgeDeletionFaces

variable (M : CombMap.{u}) [DecidableEq M.Dart] (a : M.Dart)

/-- **Face rotation after deleting an edge, at every degree.** -/
theorem value_facePerm_general (x : Dart M a) :
    value M a ((toCombMap M a).facePerm x) =
      if M.facePerm (value M a x) = a then
        (if M.facePerm (M.alpha a) = M.alpha a then M.facePerm a
          else M.facePerm (M.alpha a))
      else if M.facePerm (value M a x) = M.alpha a then
        (if M.facePerm a = a then M.facePerm (M.alpha a) else M.facePerm a)
      else M.facePerm (value M a x) := by
  have hp : ∀ z : M.Dart, (M.sigma * unpair M a) z =
      M.sigma (M.alpha (Equiv.swap a (M.alpha a) z)) := fun z => rfl
  have hpa : (M.sigma * unpair M a) a = M.facePerm (M.alpha a) := by
    rw [hp, Equiv.swap_apply_left, M.alpha_involutive]
    exact M.sigma_eq_facePerm_alpha a
  have hpαa : (M.sigma * unpair M a) (M.alpha a) = M.facePerm a := by
    rw [hp, Equiv.swap_apply_right]
    rfl
  have hpz : ∀ z, z ≠ a → z ≠ M.alpha a → (M.sigma * unpair M a) z = M.facePerm z := by
    intro z h1 h2
    rw [hp, Equiv.swap_apply_of_ne_of_ne h1 h2]
    rfl
  have hfirst : ∀ y : FirstDart M a, ((erase (M.sigma * unpair M a) a) y).1 =
      if (M.sigma * unpair M a) y.1 = a then M.facePerm (M.alpha a)
      else (M.sigma * unpair M a) y.1 := by
    intro y
    rw [erase_val_ite, hpa]
  have hx1 : ((erase (M.sigma * unpair M a) a) x.1).1 =
      if M.facePerm (value M a x) = a then M.facePerm (M.alpha a)
      else M.facePerm (value M a x) := by
    rw [hfirst, hpz x.1.1 (value_ne M a x) (value_ne_reverse M a x)]
    rfl
  have hra : ((erase (M.sigma * unpair M a) a) (reverseDart M a)).1 =
      if M.facePerm a = a then M.facePerm (M.alpha a) else M.facePerm a := by
    rw [hfirst]
    change (if (M.sigma * unpair M a) (M.alpha a) = a then M.facePerm (M.alpha a)
      else (M.sigma * unpair M a) (M.alpha a)) = _
    rw [hpαa]
  rw [facePerm_eq]
  change ((erase (erase (M.sigma * unpair M a) a) (reverseDart M a)) x).1.1 = _
  rw [erase_val_ite]
  by_cases h1 : M.facePerm (value M a x) = a
  · have hfa : M.facePerm a ≠ a := by
      intro h
      exact value_ne M a x (M.facePerm.injective (h1.trans h.symm))
    by_cases hb : M.facePerm (M.alpha a) = M.alpha a
    · have heq : (erase (M.sigma * unpair M a) a) x.1 = reverseDart M a := by
        apply Subtype.ext
        rw [hx1, if_pos h1]
        exact hb
      rw [if_pos heq, hra, if_neg hfa, if_pos h1, if_pos hb]
    · have hne : (erase (M.sigma * unpair M a) a) x.1 ≠ reverseDart M a := by
        intro h
        have h' := congrArg Subtype.val h
        rw [hx1, if_pos h1] at h'
        exact hb h'
      rw [if_neg hne, hx1, if_pos h1, if_pos h1, if_neg hb]
  · by_cases h2 : M.facePerm (value M a x) = M.alpha a
    · have heq : (erase (M.sigma * unpair M a) a) x.1 = reverseDart M a := by
        apply Subtype.ext
        rw [hx1, if_neg h1]
        exact h2
      rw [if_pos heq, hra, if_neg h1, if_pos h2]
    · have hne : (erase (M.sigma * unpair M a) a) x.1 ≠ reverseDart M a := by
        intro h
        have h' := congrArg Subtype.val h
        rw [hx1, if_neg h1] at h'
        exact h2 h'
      rw [if_neg hne, hx1, if_neg h1, if_neg h1, if_neg h2]

/-- **A dart whose successor avoids the deleted edge keeps its successor.** -/
theorem value_facePerm_of_ne_of_ne (x : Dart M a)
    (h1 : M.facePerm (value M a x) ≠ a) (h2 : M.facePerm (value M a x) ≠ M.alpha a) :
    value M a ((toCombMap M a).facePerm x) = M.facePerm (value M a x) := by
  rw [value_facePerm_general, if_neg h1, if_neg h2]

end EdgeDeletion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.orbitWalk_add
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.value_facePerm_general
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.value_facePerm_of_ne_of_ne
