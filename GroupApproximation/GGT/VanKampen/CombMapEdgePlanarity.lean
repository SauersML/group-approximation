import GroupApproximation.GGT.VanKampen.CombMapEdgeFaces
import GroupApproximation.GGT.VanKampen.PermOrbitSplit
import GroupApproximation.GGT.VanKampen.PermOrbitOption

/-!
# Inserting an edge within a face preserves planarity

The new map is the explicit corner insertion already constructed. Its face
count follows from the proved permutation splitting, including equal corners
where a monogon is created. Euler's formula is derived from the actual counts.
-/

namespace GroupApproximation.GGT.VanKampen.EdgeInsertion

open Equiv PermOrbitInsert
universe u

theorem faceCount_eq (M : CombMap.{u}) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) :
    (toCombMap M a b).faceCount = M.faceCount + 1 := by
  classical
  change Nat.card (@CombMap.Orbit (Option (Option M.Dart)) (toCombMap M a b).facePerm) =
    Nat.card (CombMap.Orbit M.facePerm) + 1
  by_cases hab : a = b
  · subst b
    rw [facePerm_eq_of_eq, PermOrbitOption.orbit_card,
      Nat.card_congr (PermOrbitInsert.orbitEquiv M.facePerm a)]
  · rw [facePerm_eq_of_ne M a b hab,
      Nat.card_congr (PermOrbitInsert.orbitEquiv
        (insertBefore (Equiv.swap a b * M.facePerm) b) (some a)),
      Nat.card_congr (PermOrbitInsert.orbitEquiv (Equiv.swap a b * M.facePerm) b)]
    exact PermCycleCoordinates.orbit_card_swap_mul M.facePerm a b hab
      ((M.faceOf_eq_iff a b).mp hface)

theorem eulerCharacteristic_eq (M : CombMap.{u}) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) :
    (toCombMap M a b).eulerCharacteristic = M.eulerCharacteristic := by
  rw [CombMap.eulerCharacteristic, CombMap.eulerCharacteristic,
    vertexCount_eq, edgeCount_eq, faceCount_eq M a b hface]
  push_cast
  ring

/-- Inserting the actual edge at any two corners of one face, including
coincident corners, produces a planar map. -/
theorem planar (M : CombMap.{u}) (a b : M.Dart) (hM : M.IsPlanar)
    (hface : M.faceOf a = M.faceOf b) : (toCombMap M a b).IsPlanar := by
  refine ⟨connected M a b hM.1, ?_⟩
  rw [eulerCharacteristic_eq M a b hface]
  exact hM.2

end GroupApproximation.GGT.VanKampen.EdgeInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.faceCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.eulerCharacteristic_eq
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.planar
