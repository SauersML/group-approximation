import GroupApproximation.GGT.VanKampen.CombMapUnderlyingGraph
import GroupApproximation.GGT.VanKampen.CombMapEdgeDeletionConnected

/-!
# Euler characteristic of an arbitrary connected combinatorial map

Delete an edge between distinct faces while more than one face remains.
Actual deletion preserves connectedness and Euler characteristic, except
when it removes the entire map; the exact count balance handles that case.
For at most one face, the underlying connected graph bound finishes the proof.
Thus the upper bound does not presuppose planarity or a surface certificate.
-/

namespace GroupApproximation.GGT.VanKampen.CombMap

universe u
variable (M : CombMap.{u})

/-- Dual connectedness finds an edge separating distinct faces whenever
there is more than one face. -/
theorem exists_edge_neFace (hM : M.IsConnected) (hf : 1 < M.faceCount) :
    ∃ a : M.Dart, M.faceOf a ≠ M.faceOf (M.alpha a) := by
  classical
  by_contra h
  push Not at h
  have hv : M.faceCount ≤ 1 :=
    M.dual.vertexCount_le_one_of_same_endpoints (M.dual_connected hM) h
  omega

/-- The Euler characteristic of a connected orientable combinatorial map
is at most two. This includes empty maps and permits loops and parallel edges. -/
theorem eulerCharacteristic_le_two (hM : M.IsConnected) :
    M.eulerCharacteristic ≤ 2 := by
  classical
  have hall : ∀ n : ℕ, ∀ N : CombMap.{u}, N.edgeCount = n → N.IsConnected →
      N.eulerCharacteristic ≤ 2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro N hcount hN
        by_cases hf : N.faceCount ≤ 1
        · have hv := N.vertexCount_le_edgeCount_add_one hN
          dsimp only [eulerCharacteristic]
          omega
        · obtain ⟨a, ha⟩ := N.exists_edge_neFace hN (by omega)
          have he := EdgeDeletion.edgeCount_add_one N a
          cases isEmpty_or_nonempty (EdgeDeletion.Dart N a) with
          | inl h0 =>
              letI : IsEmpty (EdgeDeletion.toCombMap N a).Dart := h0
              have he0 : (EdgeDeletion.toCombMap N a).edgeCount = 0 := by
                simp [edgeCount]
              have hv0 : (EdgeDeletion.toCombMap N a).vertexCount = 0 := by
                simp [vertexCount]
              have hf0 : (EdgeDeletion.toCombMap N a).faceCount = 0 := by
                simp [faceCount]
              have hbalance := EdgeDeletion.faceCount_balance_of_neFace N a ha
              rw [hf0, hv0] at hbalance
              have hdual : N.faceCount ≤ N.edgeCount + 1 :=
                N.dual.vertexCount_le_edgeCount_add_one (N.dual_connected hN)
              dsimp only [eulerCharacteristic]
              omega
          | inr hne =>
              obtain ⟨d⟩ := hne
              have hlt : (EdgeDeletion.toCombMap N a).edgeCount < n := by omega
              have hbound := ih _ hlt (EdgeDeletion.toCombMap N a) rfl
                (EdgeDeletion.connected_of_neFace N a hN ha)
              rw [EdgeDeletion.euler_eq_of_neFace N a hN d ha] at hbound
              exact hbound
  exact hall M.edgeCount M rfl hM

end GroupApproximation.GGT.VanKampen.CombMap

namespace GroupApproximation.GGT.VanKampen.EdgeDeletion

universe u
variable (M : CombMap.{u}) [DecidableEq M.Dart] (a : M.Dart)

/-- Deleting any edge of a planar map preserves planarity when the actual
remainder is connected and nonempty. The edge sides may lie on the same face. -/
theorem planar_of_connected (hM : M.IsPlanar) (d : Dart M a)
    (hN : (toCombMap M a).IsConnected) : (toCombMap M a).IsPlanar := by
  refine ⟨hN, le_antisymm ((toCombMap M a).eulerCharacteristic_le_two hN) ?_⟩
  have h := eulerCharacteristic_le_deleted M a hM.1 d
  rw [hM.2] at h
  exact h

end GroupApproximation.GGT.VanKampen.EdgeDeletion

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.exists_edge_neFace
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.eulerCharacteristic_le_two
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.planar_of_connected
