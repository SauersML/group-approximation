import GroupApproximation.GGT.VanKampen.CombMapEdgePlanarity
import GroupApproximation.GGT.VanKampen.PermOrbitJoin

/-!
# Exact Euler change for an edge inserted at arbitrary corners

Insertion in one face splits it and preserves Euler characteristic. Insertion
between distinct faces joins them and lowers Euler characteristic by two.
These are counts of the actual constructed map. The distinction is needed
when reversing insertions to justify a planar edge-deletion argument.
-/

namespace GroupApproximation.GGT.VanKampen.EdgeInsertion

open Equiv PermOrbitInsert
universe u

/-- Corners on distinct faces join those two faces into one. -/
theorem faceCount_add_one_of_ne (M : CombMap.{u}) (a b : M.Dart)
    (hface : M.faceOf a ≠ M.faceOf b) :
    (toCombMap M a b).faceCount + 1 = M.faceCount := by
  classical
  have hab : a ≠ b := fun h => hface (congrArg M.faceOf h)
  change Nat.card (@CombMap.Orbit (Option (Option M.Dart)) (toCombMap M a b).facePerm) + 1 =
    Nat.card (CombMap.Orbit M.facePerm)
  rw [facePerm_eq_of_ne M a b hab,
    Nat.card_congr (PermOrbitInsert.orbitEquiv
      (insertBefore (Equiv.swap a b * M.facePerm) b) (some a)),
    Nat.card_congr (PermOrbitInsert.orbitEquiv (Equiv.swap a b * M.facePerm) b)]
  exact PermCycleCoordinates.orbit_card_swap_mul_of_not_sameCycle M.facePerm a b
    (fun h => hface ((M.faceOf_eq_iff a b).mpr h))

theorem eulerCharacteristic_add_two_of_ne (M : CombMap.{u}) (a b : M.Dart)
    (hface : M.faceOf a ≠ M.faceOf b) :
    (toCombMap M a b).eulerCharacteristic + 2 = M.eulerCharacteristic := by
  have hf : ((toCombMap M a b).faceCount : ℤ) + 1 = (M.faceCount : ℤ) := by
    exact_mod_cast faceCount_add_one_of_ne M a b hface
  rw [CombMap.eulerCharacteristic, CombMap.eulerCharacteristic,
    vertexCount_eq, edgeCount_eq]
  push_cast
  omega

/-- Restoring an edge between existing vertices cannot increase Euler
characteristic, regardless of the chosen corners. -/
theorem eulerCharacteristic_le (M : CombMap.{u}) (a b : M.Dart) :
    (toCombMap M a b).eulerCharacteristic ≤ M.eulerCharacteristic := by
  by_cases hface : M.faceOf a = M.faceOf b
  · exact (eulerCharacteristic_eq M a b hface).le
  · have h := eulerCharacteristic_add_two_of_ne M a b hface
    omega

/-- Euler preservation detects the common-face condition exactly. -/
theorem eulerCharacteristic_eq_iff (M : CombMap.{u}) (a b : M.Dart) :
    (toCombMap M a b).eulerCharacteristic = M.eulerCharacteristic ↔
      M.faceOf a = M.faceOf b := by
  constructor
  · intro heuler
    by_contra hface
    have h := eulerCharacteristic_add_two_of_ne M a b hface
    omega
  · exact eulerCharacteristic_eq M a b

/-- In a planar ambient map, the actual insertion is planar precisely when
the two chosen corners lie on a common face. -/
theorem planar_iff (M : CombMap.{u}) (a b : M.Dart) (hM : M.IsPlanar) :
    (toCombMap M a b).IsPlanar ↔ M.faceOf a = M.faceOf b := by
  constructor
  · intro hN
    exact (eulerCharacteristic_eq_iff M a b).mp (hN.2.trans hM.2.symm)
  · exact planar M a b hM

end GroupApproximation.GGT.VanKampen.EdgeInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.faceCount_add_one_of_ne
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.eulerCharacteristic_le
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.planar_iff
