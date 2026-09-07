import GroupApproximation.GGT.VanKampen.PermOrbitErasePoint
import GroupApproximation.GGT.VanKampen.PermOrbitJoin

/-!
# Actual deletion of one edge and its rotation counts

Both darts of the chosen edge are deleted from vertex rotation by first
return. Edge reversal restricts to the other darts. The face rotation is the
two-point deletion of the old face permutation with the edge transposed.
The vertex/face count balance keeps track of disappearing vertices rather
than assuming all vertices survive.
-/

namespace GroupApproximation.GGT.VanKampen.EdgeDeletion

open Equiv PermOrbitErasePoint
universe u
variable (M : CombMap.{u}) (a : M.Dart)

abbrev FirstDart := {d : M.Dart // d ≠ a}

def reverseDart : FirstDart M a := ⟨M.alpha a, M.alpha_fixedPointFree a⟩

abbrev Dart := {d : FirstDart M a // d ≠ reverseDart M a}

def value (d : Dart M a) : M.Dart := d.1.1

theorem value_ne (d : Dart M a) : value M a d ≠ a := d.1.2

theorem value_ne_reverse (d : Dart M a) : value M a d ≠ M.alpha a := by
  intro h
  exact d.2 (Subtype.ext h)

variable [DecidableEq M.Dart]

/-- Cancel the selected edge reversal on its own two darts. -/
def unpair : Perm M.Dart := M.alpha * Equiv.swap a (M.alpha a)

theorem unpair_fixed : unpair M a a = a := by
  change M.alpha (Equiv.swap a (M.alpha a) a) = a
  rw [Equiv.swap_apply_left, M.alpha_involutive]

theorem unpair_fixed_reverse : unpair M a (M.alpha a) = M.alpha a := by
  change M.alpha (Equiv.swap a (M.alpha a) (M.alpha a)) = M.alpha a
  rw [Equiv.swap_apply_right]

def firstAlpha : Perm (FirstDart M a) :=
  restrictFixed (unpair M a) a (unpair_fixed M a)

theorem firstAlpha_fixed_reverse : firstAlpha M a (reverseDart M a) = reverseDart M a :=
  Subtype.ext (unpair_fixed_reverse M a)

def alpha : Perm (Dart M a) :=
  restrictFixed (firstAlpha M a) (reverseDart M a) (firstAlpha_fixed_reverse M a)

theorem alpha_val (d : Dart M a) : value M a (alpha M a d) = M.alpha (value M a d) := by
  change M.alpha (Equiv.swap a (M.alpha a) (value M a d)) = M.alpha (value M a d)
  rw [Equiv.swap_apply_of_ne_of_ne (value_ne M a d) (value_ne_reverse M a d)]

theorem alpha_involutive : Function.Involutive (alpha M a) := by
  intro d
  apply Subtype.ext
  apply Subtype.ext
  change value M a (alpha M a (alpha M a d)) = value M a d
  rw [alpha_val, alpha_val, M.alpha_involutive]

theorem alpha_fixedPointFree (d : Dart M a) : alpha M a d ≠ d := by
  intro h
  apply M.alpha_fixedPointFree (value M a d)
  exact (alpha_val M a d).symm.trans (congrArg (value M a) h)

def sigma : Perm (Dart M a) := erase (erase M.sigma a) (reverseDart M a)

def toCombMap : CombMap.{u} where
  Dart := Dart M a
  dartFintype := inferInstance
  alpha := alpha M a
  sigma := sigma M a
  alpha_involutive := alpha_involutive M a
  alpha_fixedPointFree := alpha_fixedPointFree M a

/-- The exact face permutation, including cases where a vertex disappears. -/
theorem facePerm_eq : (toCombMap M a).facePerm =
    erase (erase (M.sigma * unpair M a) a) (reverseDart M a) := by
  change erase (erase M.sigma a) (reverseDart M a) * alpha M a = _
  rw [erase_mul_of_fixed M.sigma (unpair M a) a (unpair_fixed M a)]
  exact (erase_mul_of_fixed (erase M.sigma a) (firstAlpha M a) (reverseDart M a)
    (firstAlpha_fixed_reverse M a)).symm

/-- Deleting two points from old vertex rotation preserves all identifications
among the retained darts. -/
theorem vertexOf_eq_iff (d e : Dart M a) :
    (toCombMap M a).vertexOf d = (toCombMap M a).vertexOf e ↔
      M.vertexOf (value M a d) = M.vertexOf (value M a e) := by
  rw [CombMap.vertexOf_eq_iff, M.vertexOf_eq_iff]
  exact (PermFirstReturn.sameCycle_iff _ _ _
    (firstReturn (erase M.sigma a) (reverseDart M a)) d e).trans
      (PermFirstReturn.sameCycle_iff _ _ _ (firstReturn M.sigma a) d.1 e.1)

theorem dartCount_add_two : (toCombMap M a).dartCount + 2 = M.dartCount := by
  have h₁ : Nat.card (FirstDart M a) + 1 = Nat.card M.Dart := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_option]
      using Nat.card_congr (Equiv.optionSubtypeNe a)
  have h₂ : Nat.card (Dart M a) + 1 = Nat.card (FirstDart M a) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_option]
      using Nat.card_congr (Equiv.optionSubtypeNe (reverseDart M a))
  change Nat.card (Dart M a) + 2 = Nat.card M.Dart
  omega

theorem edgeCount_add_one : (toCombMap M a).edgeCount + 1 = M.edgeCount := by
  have h := dartCount_add_two M a
  rw [(toCombMap M a).dartCount_eq_two_mul_edgeCount,
    M.dartCount_eq_two_mul_edgeCount] at h
  omega

/-- Vertex and face deletion lose the same complete cycles. The remaining
face change is precisely the transposition of the two edge darts. -/
theorem vertex_face_balance :
    (toCombMap M a).faceCount + M.vertexCount =
      (toCombMap M a).vertexCount + Nat.card (CombMap.Orbit (M.sigma * unpair M a)) := by
  have h := orbit_card_balance_twice M.sigma (M.sigma * unpair M a) a
    (reverseDart M a) (by rw [Perm.mul_apply, unpair_fixed]) (by
      change M.sigma (M.alpha a) = M.sigma (unpair M a (M.alpha a))
      rw [unpair_fixed_reverse])
  change Nat.card (CombMap.Orbit (toCombMap M a).facePerm) +
      Nat.card (CombMap.Orbit M.sigma) =
    Nat.card (CombMap.Orbit (erase (erase M.sigma a) (reverseDart M a))) +
      Nat.card (CombMap.Orbit (M.sigma * unpair M a))
  rw [facePerm_eq]
  exact h.symm

theorem unpair_face_orbit_card :
    Nat.card (CombMap.Orbit (M.sigma * unpair M a)) =
      Nat.card (CombMap.Orbit (Equiv.swap a (M.alpha a) * M.facePerm)) := by
  have hp : M.sigma * unpair M a = M.facePerm * Equiv.swap a (M.alpha a) := by
    change M.sigma * (M.alpha * Equiv.swap a (M.alpha a)) =
      (M.sigma * M.alpha) * Equiv.swap a (M.alpha a)
    exact (mul_assoc _ _ _).symm
  rw [hp, PermCycleCoordinates.orbit_card_mul_swap_eq]

theorem faceCount_balance_of_sameFace (hface : M.faceOf a = M.faceOf (M.alpha a)) :
    (toCombMap M a).faceCount + M.vertexCount =
      (toCombMap M a).vertexCount + M.faceCount + 1 := by
  rw [vertex_face_balance, unpair_face_orbit_card,
    PermCycleCoordinates.orbit_card_swap_mul M.facePerm a (M.alpha a)
      (M.alpha_fixedPointFree a).symm ((M.faceOf_eq_iff _ _).mp hface)]
  change (toCombMap M a).vertexCount + (M.faceCount + 1) = _
  omega

theorem faceCount_balance_of_neFace (hface : M.faceOf a ≠ M.faceOf (M.alpha a)) :
    (toCombMap M a).faceCount + M.vertexCount + 1 =
      (toCombMap M a).vertexCount + M.faceCount := by
  have h := vertex_face_balance M a
  rw [unpair_face_orbit_card] at h
  have hswap := PermCycleCoordinates.orbit_card_swap_mul_of_not_sameCycle
    M.facePerm a (M.alpha a) (fun h => hface ((M.faceOf_eq_iff _ _).mpr h))
  change _ + 1 = M.faceCount at hswap
  omega

end GroupApproximation.GGT.VanKampen.EdgeDeletion

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.facePerm_eq
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.vertexOf_eq_iff
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.edgeCount_add_one
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.vertex_face_balance
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.faceCount_balance_of_sameFace
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.faceCount_balance_of_neFace
