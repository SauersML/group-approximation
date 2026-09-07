import GroupApproximation.GGT.VanKampen.FaceSetBoundaryReclosed
import GroupApproximation.GGT.VanKampen.SurgeryReclosedConnected
import GroupApproximation.GGT.VanKampen.SingletonCollapseCounterexample

/-!
# A genuine collapse of the internally paired bridge example

The face with stored boundary `[0, 2, 1]` has actual region boundary `[2]`.
Reclosing along this genuine walk deletes the bridge and its isolated end
vertex. The first-return vertex theorem gives the new vertex count, and the
resulting map is planar. Thus the counterexample to the historical exact
singleton producer still has a valid collapse with its actual boundary.
-/

namespace GroupApproximation.GGT.VanKampen.BridgeFaceReclosedModel

open Surgery.MapCollapse ExteriorArcCounterexample

theorem internal_iff (d : Fin 6) :
    InternalDart M {face 0} d ↔ d = 0 ∨ d = 1 := by
  simp only [InternalDart, Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

theorem boundary_iff (d : Fin 6) :
    Surgery.MapCollapse.IsBoundaryDart M {face 0} d ↔ d = 2 := by
  simp only [Surgery.MapCollapse.IsBoundaryDart, Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

def actualBoundary : BoundaryCycle M {face 0} where
  cycle := [(2 : Fin 6)]
  cycle_nonempty := by decide
  cycle_nodup := by decide
  cycle_mem_iff := by
    intro d
    rw [List.mem_singleton]
    exact (boundary_iff d).symm

theorem actualBoundary_follows : actualBoundary.FollowsBoundary := by
  apply BoundaryCycle.followsBoundary_of_chain
  · exact List.isChain_singleton _
  · apply Relation.ReflTransGen.single
    refine ⟨?_, rfl⟩
    exact (internal_iff 1).mpr (Or.inr rfl)

noncomputable def reclosed : CombMap := reclosedMap M {face 0} actualBoundary

def keptTwo : KeptDart M {face 0} :=
  ⟨2, by rw [internal_iff]; decide⟩

/-- The step starting at dart three skips the internal dart one. -/
theorem rotation_skips_bridge : (reclosed.sigma
    ⟨3, by rw [internal_iff]; decide⟩).1 = (2 : Fin 6) := by
  have h := reclosedMap_facePerm_val_of_mem M {face 0} actualBoundary
    (reclosed.alpha ⟨3, by rw [internal_iff]; decide⟩)
    (Finset.mem_singleton.mpr ((faceOf_eq_face 2 0).mpr rfl))
  have hb : (actualBoundary.boundaryPerm
      ⟨2, (boundary_iff 2).mpr rfl⟩).1 = (2 : Fin 6) :=
    (boundary_iff _).mp (actualBoundary.boundaryPerm
      ⟨2, (boundary_iff 2).mpr rfl⟩).property
  have hs : reclosed.facePerm (reclosed.alpha
      ⟨3, by rw [internal_iff]; decide⟩) =
      reclosed.sigma ⟨3, by rw [internal_iff]; decide⟩ := by
    change reclosed.sigma (reclosed.alpha (reclosed.alpha _)) = _
    rw [reclosed.alpha_involutive]
  exact (congrArg Subtype.val hs).symm.trans (h.trans hb)

theorem kept_vertex (d : KeptDart M {face 0}) :
    M.vertexOf d.1 = M.vertexOf (2 : Fin 6) := by
  rcases d with ⟨d, hd⟩
  have hne := (not_congr (internal_iff d)).mp hd
  apply vertexEquiv.injective
  change (![0, 1, 1, 1, 1, 1] : Fin 6 → Fin 2) d = 1
  fin_cases d <;> simp_all

theorem vertexCount_eq_one : reclosed.vertexCount = 1 := by
  let V := {c : M.Vertex // ∃ d : KeptDart M {face 0}, M.vertexOf d.1 = c}
  have hall : ∀ c : V, c.1 = M.vertexOf (2 : Fin 6) := by
    rintro ⟨c, d, hd⟩
    exact hd.symm.trans (kept_vertex d)
  letI : Unique V :=
    { default := ⟨M.vertexOf 2, keptTwo, rfl⟩
      uniq := fun c => Subtype.ext (hall c) }
  rw [show reclosed.vertexCount = Nat.card V from
    reclosedMap_vertexCount M {face 0} actualBoundary actualBoundary_follows]
  exact Nat.card_unique

theorem dartCount_eq_four : reclosed.dartCount = 4 := by
  let e : KeptDart M {face 0} ≃ {d : Fin 6 // ¬ (d = 0 ∨ d = 1)} :=
    Equiv.subtypeEquivRight fun d => not_congr (internal_iff d)
  have h := Nat.card_congr e
  change Nat.card (KeptDart M {face 0}) = 4
  rw [h, Nat.card_eq_fintype_card]
  decide

theorem edgeCount_eq_two : reclosed.edgeCount = 2 := by
  have h := reclosed.dartCount_eq_two_mul_edgeCount
  rw [dartCount_eq_four] at h
  omega

theorem faceCount_eq_three : reclosed.faceCount = 3 := by
  have h := reclosedMap_faceCount_of_card_eq_one M {face 0} actualBoundary
    (Finset.card_singleton _)
  have hM : M.faceCount = 3 := (Nat.card_congr faceEquiv).trans (by simp)
  exact h.trans hM

theorem euler_preserved : reclosed.eulerCharacteristic = M.eulerCharacteristic := by
  rw [planar.2]
  unfold CombMap.eulerCharacteristic
  rw [vertexCount_eq_one, edgeCount_eq_two, faceCount_eq_three]
  norm_num

/-- The bridge is removed using the actual boundary, without an unpinched-face
assumption and without supplying Euler preservation as an input. -/
noncomputable def actualRegion : IsDiscRegion M {face 0} :=
  BoundaryCycle.toDiscRegion_of_euler M {face 0} actualBoundary planar.1 euler_preserved

theorem exists_planar_actual_collapse :
    ∃ region : IsDiscRegion M {face 0},
      region.toBoundaryCycle.cycle = [2] ∧
      (replaceGRegion M {face 0} region).IsPlanar ∧
      (replaceGRegion M {face 0} region).vertexCount = 1 ∧
      (replaceGRegion M {face 0} region).edgeCount = 2 :=
  ⟨actualRegion, rfl, replaceGRegion_planar _ _ _ planar,
    vertexCount_eq_one, edgeCount_eq_two⟩

end GroupApproximation.GGT.VanKampen.BridgeFaceReclosedModel

#audit_closed_axioms GroupApproximation.GGT.VanKampen.BridgeFaceReclosedModel.actualBoundary_follows
#audit_closed_axioms GroupApproximation.GGT.VanKampen.BridgeFaceReclosedModel.rotation_skips_bridge
#audit_closed_axioms GroupApproximation.GGT.VanKampen.BridgeFaceReclosedModel.exists_planar_actual_collapse
