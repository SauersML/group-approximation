import GroupApproximation.Matching.FinitePartialClusterGroupoid
import GroupApproximation.Matching.PartialClusterCandidates

/-!
# Building a finite partial-intertwiner cluster groupoid

All groupoid bookkeeping is discharged once every composite of two
low-defect candidates admits a low-defect improvement within radius `2m`.
This module makes that remaining mathematical obligation explicit and turns
it into the concrete `FinitePartialClusterData` used by the counting layer.
-/

namespace GroupApproximation

universe u

/-- Uniform finite component data together with the sole composition
improvement theorem needed to construct the cluster groupoid. -/
structure PartialClusterSystem (I : Type u) [Fintype I]
    (L : Type*) [Fintype L] [DecidableEq L] where
  model : I → FiniteModel
  act : ∀ X, L → Equiv.Perm (model X)
  h : ℝ
  h_pos : 0 < h
  scale : ℕ
  scale_pos : 0 < scale
  expands : ∀ X,
    FinitePartialBijection.HasTaggedExpansionAtScale (act X) h scale
  size : ∀ X, 17 * scale ≤ Fintype.card (model X)
  improveExists : ∀ {X Y Z}
    (f : FinitePartialBijection (model X) (model Y)),
    f.IsClusterCandidate (act X) (act Y) h scale →
    ∀ (g : FinitePartialBijection (model Y) (model Z)),
    g.IsClusterCandidate (act Y) (act Z) h scale →
      ∃ r : FinitePartialBijection (model X) (model Z),
        r.IsClusterCandidate (act X) (act Z) h scale ∧
          r.twoSidedDisagreement (f.trans g) < 2 * scale

namespace PartialClusterSystem

variable {I : Type u} [Fintype I]
variable {L : Type*} [Fintype L] [DecidableEq L]
variable (D : PartialClusterSystem I L)

private def emptyPartial (Y Z : FiniteModel) : FinitePartialBijection Y Z where
  source := ∅
  target := ∅
  equiv :=
    { toFun := fun y ↦ (Finset.notMem_empty y.1 y.2).elim
      invFun := fun z ↦ (Finset.notMem_empty z.1 z.2).elim
      left_inv := fun y ↦ (Finset.notMem_empty y.1 y.2).elim
      right_inv := fun z ↦ (Finset.notMem_empty z.1 z.2).elim }

/-- Canonical improving representative, chosen from the proved nonempty
finite candidate class. -/
noncomputable def improve {X Y Z : I}
    (f : FinitePartialBijection (D.model X) (D.model Y))
    (g : FinitePartialBijection (D.model Y) (D.model Z)) :
    FinitePartialBijection (D.model X) (D.model Z) := by
  classical
  by_cases hf : f.IsClusterCandidate (D.act X) (D.act Y) D.h D.scale
  · by_cases hg : g.IsClusterCandidate (D.act Y) (D.act Z) D.h D.scale
    · exact Classical.choose (D.improveExists f hf g hg)
    · exact emptyPartial (D.model X) (D.model Z)
  · exact emptyPartial (D.model X) (D.model Z)

theorem improve_spec {X Y Z : I}
    (f : FinitePartialBijection (D.model X) (D.model Y))
    (hf : f.IsClusterCandidate (D.act X) (D.act Y) D.h D.scale)
    (g : FinitePartialBijection (D.model Y) (D.model Z))
    (hg : g.IsClusterCandidate (D.act Y) (D.act Z) D.h D.scale) :
    (D.improve f g).IsClusterCandidate (D.act X) (D.act Z) D.h D.scale ∧
      (D.improve f g).twoSidedDisagreement (f.trans g) < 2 * D.scale := by
  classical
  simp only [improve, dif_pos hf, dif_pos hg]
  exact Classical.choose_spec (D.improveExists f hf g hg)

/-- The fully populated finite cluster data. -/
noncomputable def clusterData : FinitePartialClusterData I where
  model := D.model
  radius := 2 * D.scale
  radius_pos := Nat.mul_pos (by norm_num) D.scale_pos
  candidate X Y := FinitePartialBijection.clusterCandidates
    (D.act X) (D.act Y) D.h D.scale
  one_mem X := by
    rw [FinitePartialBijection.mem_clusterCandidates]
    exact FinitePartialBijection.isClusterCandidate_refl
      (D.act X) D.h_pos D.scale_pos
  symm_mem := by
    intro X Y f hf
    rw [FinitePartialBijection.mem_clusterCandidates] at hf ⊢
    exact hf.symm
  improve := D.improve
  improve_mem := by
    intro X Y Z f hf g hg
    rw [FinitePartialBijection.mem_clusterCandidates] at hf hg ⊢
    exact (D.improve_spec f hf g hg).1
  improve_close := by
    intro X Y Z f hf g hg
    rw [FinitePartialBijection.mem_clusterCandidates] at hf hg
    exact (D.improve_spec f hf g hg).2
  self_small := by
    intro X Y f hf
    rw [FinitePartialBijection.mem_clusterCandidates] at hf
    exact hf.selfSmall
  gap := by
    intro X Y f hf g hg
    rw [FinitePartialBijection.mem_clusterCandidates] at hf hg
    exact hf.gap (D.act X) (D.act Y) (D.expands X) (D.expands Y)
      (D.size X) (D.size Y) f g hg

/-- The finite groupoid presentation of improved partial-intertwiner
clusters. -/
noncomputable def presentation : GroupoidPresentation I :=
  D.clusterData.presentation

end PartialClusterSystem
end GroupApproximation
