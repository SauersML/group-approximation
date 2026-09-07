import GroupApproximation.GGT.VanKampen.CombMap
import GroupApproximation.Meta.AxiomGuard

/-! # The dual finite orientable map -/

namespace GroupApproximation.GGT.VanKampen.CombMap

open Equiv
universe u

/-- Exchange vertices and faces while retaining the paired darts. -/
def dual (M : CombMap.{u}) : CombMap.{u} where
  Dart := M.Dart
  dartFintype := M.dartFintype
  alpha := M.alpha
  sigma := M.facePerm
  alpha_involutive := M.alpha_involutive
  alpha_fixedPointFree := M.alpha_fixedPointFree

theorem dual_facePerm (M : CombMap.{u}) : M.dual.facePerm = M.sigma := by
  apply Equiv.ext
  intro d
  change M.sigma (M.alpha (M.alpha d)) = M.sigma d
  rw [M.alpha_involutive]

theorem dual_reachable (M : CombMap.{u}) {d e : M.Dart}
    (h : Relation.EqvGen M.Adjacent d e) : Relation.EqvGen M.dual.Adjacent d e := by
  induction h with
  | rel d e h =>
      rcases h with h | h
      · exact Relation.EqvGen.rel _ _ (Or.inl h)
      · rw [← h]
        refine Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.rel _ _ (Or.inl (rfl : M.dual.alpha d = M.alpha d))) ?_
        apply Relation.EqvGen.rel
        right
        change M.sigma (M.alpha (M.alpha d)) = M.sigma d
        rw [M.alpha_involutive]
  | refl d => exact Relation.EqvGen.refl _
  | symm d e h ih => exact Relation.EqvGen.symm _ _ ih
  | trans d e f h₁ h₂ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem dual_connected (M : CombMap.{u}) (h : M.IsConnected) : M.dual.IsConnected :=
  fun d e => M.dual_reachable (h d e)

theorem dual_vertexCount (M : CombMap.{u}) : M.dual.vertexCount = M.faceCount := rfl
theorem dual_edgeCount (M : CombMap.{u}) : M.dual.edgeCount = M.edgeCount := rfl

theorem dual_faceCount (M : CombMap.{u}) : M.dual.faceCount = M.vertexCount := by
  change Nat.card (@Orbit M.Dart M.dual.facePerm) = Nat.card (Orbit M.sigma)
  rw [dual_facePerm]

theorem dual_eulerCharacteristic (M : CombMap.{u}) :
    M.dual.eulerCharacteristic = M.eulerCharacteristic := by
  rw [eulerCharacteristic, eulerCharacteristic, dual_vertexCount, dual_edgeCount, dual_faceCount]
  omega

theorem dual_planar (M : CombMap.{u}) (h : M.IsPlanar) : M.dual.IsPlanar := by
  refine ⟨M.dual_connected h.1, ?_⟩
  rw [dual_eulerCharacteristic]
  exact h.2

end GroupApproximation.GGT.VanKampen.CombMap

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.dual_facePerm
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.dual_connected
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.dual_planar
