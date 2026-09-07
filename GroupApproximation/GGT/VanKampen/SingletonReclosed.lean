import GroupApproximation.GGT.VanKampen.SingletonCollapseNecessary
import GroupApproximation.GGT.VanKampen.SurgeryReclosedConnected
import GroupApproximation.GGT.VanKampen.CyclicFaceBoundary
import GroupApproximation.GGT.VanKampen.SurgeryFaceNew

/-!
# Construct the exact singleton collapse when no dart is internal

Every dart is retained. The supplied face boundary gives precisely the old
face rotation, so the dart equivalence intertwines both map permutations.
Vertex, edge and face counts are unchanged. This proves Euler preservation
and constructs the historical singleton disc-region data from the one local
condition which the bridge counterexample shows is necessary.
-/

namespace GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

open Equiv
universe u w v

namespace SingletonReclosed

variable (M : CombMap.{v}) (f : M.Face) (B : FaceBoundary M f)
  (hno : NoInternalFaceDart M f)

noncomputable def dartEquiv : M.Dart ≃
    (reclosedMap M {f} (singletonBoundaryCycle_of_faceBoundary M f B hno)).Dart where
  toFun d := ⟨d, fun h => hno d (Finset.mem_singleton.mp h.1) (Finset.mem_singleton.mp h.2)⟩
  invFun d := d.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

theorem alpha_map (d : M.Dart) :
    (reclosedMap M {f} (singletonBoundaryCycle_of_faceBoundary M f B hno)).alpha
      (dartEquiv M f B hno d) = dartEquiv M f B hno (M.alpha d) :=
  Subtype.ext rfl

theorem boundaryPerm_val (d : BoundaryDart M {f}) :
    ((singletonBoundaryCycle_of_faceBoundary M f B hno).boundaryPerm d).val =
      M.facePerm d.val := by
  let boundary := singletonBoundaryCycle_of_faceBoundary M f B hno
  obtain ⟨i, hi⟩ := boundary.positionEquiv.surjective d
  rw [← hi, boundaryPerm_positionEquiv_val, positionEquiv_val]
  exact (FaceBoundary.cyclic_get_rotate M.facePerm B.darts B.nonempty B.chain B.closes i).symm

theorem facePerm_map (d : M.Dart) :
    (reclosedMap M {f} (singletonBoundaryCycle_of_faceBoundary M f B hno)).facePerm
      (dartEquiv M f B hno d) = dartEquiv M f B hno (M.facePerm d) := by
  classical
  apply Subtype.ext
  by_cases hd : M.faceOf d ∈ ({f} : Finset M.Face)
  · exact (reclosedMap_facePerm_val_of_mem M {f}
      (singletonBoundaryCycle_of_faceBoundary M f B hno) (dartEquiv M f B hno d) hd).trans
        (boundaryPerm_val M f B hno _)
  · exact reclosedMap_facePerm_val_of_notMem M {f}
      (singletonBoundaryCycle_of_faceBoundary M f B hno) (dartEquiv M f B hno d) hd

theorem sigma_map (d : M.Dart) :
    (reclosedMap M {f} (singletonBoundaryCycle_of_faceBoundary M f B hno)).sigma
      (dartEquiv M f B hno d) = dartEquiv M f B hno (M.sigma d) := by
  let N := reclosedMap M {f} (singletonBoundaryCycle_of_faceBoundary M f B hno)
  have h := facePerm_map M f B hno (M.alpha d)
  rw [← alpha_map M f B hno] at h
  change N.facePerm (N.alpha (dartEquiv M f B hno d)) =
    dartEquiv M f B hno (M.facePerm (M.alpha d)) at h
  change N.sigma (N.alpha (N.alpha (dartEquiv M f B hno d))) =
    dartEquiv M f B hno (M.sigma (M.alpha (M.alpha d))) at h
  rw [N.alpha_involutive, M.alpha_involutive] at h
  exact h

theorem sigma_eq_permCongr :
    (reclosedMap M {f} (singletonBoundaryCycle_of_faceBoundary M f B hno)).sigma =
      (dartEquiv M f B hno).permCongr M.sigma := by
  apply Equiv.ext
  intro x
  obtain ⟨d, rfl⟩ := (dartEquiv M f B hno).surjective x
  simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using sigma_map M f B hno d

theorem vertexCount_eq :
    (reclosedMap M {f} (singletonBoundaryCycle_of_faceBoundary M f B hno)).vertexCount =
      M.vertexCount := by
  change Nat.card (CombMap.Orbit _) = Nat.card (CombMap.Orbit M.sigma)
  rw [sigma_eq_permCongr]
  exact (Nat.card_congr (orbitPermCongr (dartEquiv M f B hno) M.sigma)).symm

theorem edgeCount_eq :
    (reclosedMap M {f} (singletonBoundaryCycle_of_faceBoundary M f B hno)).edgeCount =
      M.edgeCount := by
  let N := reclosedMap M {f} (singletonBoundaryCycle_of_faceBoundary M f B hno)
  have hd : N.dartCount = M.dartCount := (Nat.card_congr (dartEquiv M f B hno)).symm
  have hn := N.dartCount_eq_two_mul_edgeCount
  have hm := M.dartCount_eq_two_mul_edgeCount
  rw [hn, hm] at hd
  change N.edgeCount = M.edgeCount
  omega

theorem faceCount_eq :
    (reclosedMap M {f} (singletonBoundaryCycle_of_faceBoundary M f B hno)).faceCount =
      M.faceCount := by
  have h := reclosedMap_faceCount M {f} (singletonBoundaryCycle_of_faceBoundary M f B hno)
  simpa only [Finset.card_singleton, Nat.add_right_cancel_iff] using h

theorem euler_preserved :
    (reclosedMap M {f} (singletonBoundaryCycle_of_faceBoundary M f B hno)).eulerCharacteristic =
      M.eulerCharacteristic := by
  unfold CombMap.eulerCharacteristic
  rw [vertexCount_eq, edgeCount_eq, faceCount_eq]

/-- Both historical topological fields are constructed from the actual map. -/
noncomputable def discRegion (hM : M.IsConnected) : IsDiscRegion M {f} :=
  BoundaryCycle.toDiscRegion_of_euler M {f}
    (singletonBoundaryCycle_of_faceBoundary M f B hno) hM (euler_preserved M f B hno)

theorem discRegion_cycle (hM : M.IsConnected) :
    (discRegion M f B hno hM).toBoundaryCycle.cycle = B.darts := rfl

end SingletonReclosed

/-- Exact preservation of a singleton face boundary is equivalent to the
local condition, with no outstanding connectedness or Euler inputs. -/
theorem exists_exact_singleton_discRegion_iff
    (M : CombMap.{v}) (f : M.Face) (B : FaceBoundary M f) (hM : M.IsConnected) :
    (∃ region : IsDiscRegion M {f}, region.toBoundaryCycle.cycle = B.darts) ↔
      NoInternalFaceDart M f := by
  constructor
  · rintro ⟨region, hcycle⟩
    exact region.toBoundaryCycle.noInternalFaceDart_of_cycle_eq B hcycle
  · intro hno
    exact ⟨SingletonReclosed.discRegion M f B hno hM,
      SingletonReclosed.discRegion_cycle M f B hno hM⟩

/-- Fill the historical data record for every actual disc diagram whose
chosen face has no internally paired edge. -/
theorem singletonDiscRegionData_of_noInternal
    {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
    (hno : NoInternalFaceDart Delta.toCombMap f) : SingletonDiscRegionData (Delta := Delta) f hno := {
  reclosed_connected := reclosedMap_connected Delta.toCombMap {f}
    (singletonBoundaryCycle (Delta := Delta) f hno) Delta.planar.1
  euler_preserved := SingletonReclosed.euler_preserved Delta.toCombMap f (Delta.faceBoundary f) hno }

end GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.SingletonReclosed.facePerm_map
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.SingletonReclosed.sigma_map
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.SingletonReclosed.euler_preserved
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.exists_exact_singleton_discRegion_iff
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.singletonDiscRegionData_of_noInternal
