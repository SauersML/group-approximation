import GroupApproximation.KunThom.CentralizerNormalizationPairImprove
import GroupApproximation.Matching.ScaledPartialClusterGroupoid

/-!
# Scaled partial cluster systems

A `ScaledPartialClusterSystem I L` is a finite family of models with label
actions, a candidate threshold `h`, a per-object scale
`scale X = |model X| / 18`, and the two repair statements at the pair scale
`min (scale X) (scale Y)`: improvement of composites of two candidates, and
repair of single arrows whose equivariance defects are below `K₀` times the
pair threshold.  Both come with the distance bound `d * |model X|`.

A candidate between two objects forces their scales to agree up to a factor
`11 / 10` (`scale_comparable`), which is the comparability the per-pair radius
groupoid needs.  `clusterData` is the `ScaledFinitePartialClusterData` at the
pair radius `2 * min (scale X) (scale Y)`, and `presentation` is its groupoid
presentation.  `ComponentFamily.clusterSystem` builds a system at each index
from the eventual statements of `CentralizerNormalizationPairImprove`.
-/

namespace GroupApproximation

universe u

open FinitePartialBijection
open CentralizerNormalizationImprove

theorem hasTaggedExpansionAtScale_mono {L : Type*} [Fintype L] {Y : FiniteModel}
    {act : L → Equiv.Perm Y} {h : ℝ} {m m' : ℕ}
    (hexp : HasTaggedExpansionAtScale act h m) (hm : m ≤ m') :
    HasTaggedExpansionAtScale act h m' :=
  ⟨hexp.1, fun A hA hcard ↦ hexp.2 A (hm.trans hA) hcard⟩

/-- Finite component data with per-object scales and the repair statements at
pair scales. -/
structure ScaledPartialClusterSystem (I : Type u) [Fintype I]
    (L : Type*) [Fintype L] [DecidableEq L] [Nonempty L] where
  model : I → FiniteModel
  act : ∀ X, L → Equiv.Perm (model X)
  h : ℝ
  h_pos : 0 < h
  h_small : h ≤ 1 / 100000
  d : ℝ
  K₀ : ℝ
  scale : I → ℕ
  scale_large : ∀ X, 20 ≤ scale X
  scale_eq : ∀ X, scale X = Fintype.card (model X) / 18
  expands : ∀ X, HasTaggedExpansionAtScale (act X) h 1
  improveExists : ∀ {X Y Z} (f : FinitePartialBijection (model X) (model Y)),
    f.IsClusterCandidate (act X) (act Y) h (min (scale X) (scale Y)) →
    ∀ g : FinitePartialBijection (model Y) (model Z),
    g.IsClusterCandidate (act Y) (act Z) h (min (scale Y) (scale Z)) →
    ∃ r : FinitePartialBijection (model X) (model Z),
      r.IsClusterCandidate (act X) (act Z) h (min (scale X) (scale Z)) ∧
        r.twoSidedDisagreement (f.trans g) < 2 * min (scale X) (scale Z) ∧
        (r.twoSidedDisagreement (f.trans g) : ℝ) ≤ d * Fintype.card (model X)
  repairExists : ∀ {X Y} (b : FinitePartialBijection (model X) (model Y)),
    ((b.equivarianceDefect (act X) (act Y)).card : ℝ) <
      K₀ * h * ((min (scale X) (scale Y) : ℕ) : ℝ) / 2 →
    ((b.symm.equivarianceDefect (act Y) (act X)).card : ℝ) <
      K₀ * h * ((min (scale X) (scale Y) : ℕ) : ℝ) / 2 →
    ∃ r : FinitePartialBijection (model X) (model Y),
      r.IsClusterCandidate (act X) (act Y) h (min (scale X) (scale Y)) ∧
        r.twoSidedDisagreement b < 2 * min (scale X) (scale Y) ∧
        (r.twoSidedDisagreement b : ℝ) ≤ d * Fintype.card (model X)

namespace ScaledPartialClusterSystem

variable {I : Type u} [Fintype I]
variable {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
variable (D : ScaledPartialClusterSystem I L)

/-- The partial bijection with empty source and target. -/
def emptyPartial (Y Z : FiniteModel) : FinitePartialBijection Y Z where
  source := ∅
  target := ∅
  equiv :=
    { toFun := fun y ↦ (Finset.notMem_empty y.1 y.2).elim
      invFun := fun z ↦ (Finset.notMem_empty z.1 z.2).elim
      left_inv := fun y ↦ (Finset.notMem_empty y.1 y.2).elim
      right_inv := fun z ↦ (Finset.notMem_empty z.1 z.2).elim }

/-- Canonical improving representative of a composite of candidates. -/
noncomputable def improve {X Y Z : I}
    (f : FinitePartialBijection (D.model X) (D.model Y))
    (g : FinitePartialBijection (D.model Y) (D.model Z)) :
    FinitePartialBijection (D.model X) (D.model Z) := by
  classical
  by_cases hf : f.IsClusterCandidate (D.act X) (D.act Y) D.h (min (D.scale X) (D.scale Y))
  · by_cases hg : g.IsClusterCandidate (D.act Y) (D.act Z) D.h
        (min (D.scale Y) (D.scale Z))
    · exact Classical.choose (D.improveExists f hf g hg)
    · exact emptyPartial (D.model X) (D.model Z)
  · exact emptyPartial (D.model X) (D.model Z)

theorem improve_spec {X Y Z : I}
    (f : FinitePartialBijection (D.model X) (D.model Y))
    (hf : f.IsClusterCandidate (D.act X) (D.act Y) D.h (min (D.scale X) (D.scale Y)))
    (g : FinitePartialBijection (D.model Y) (D.model Z))
    (hg : g.IsClusterCandidate (D.act Y) (D.act Z) D.h (min (D.scale Y) (D.scale Z))) :
    (D.improve f g).IsClusterCandidate (D.act X) (D.act Z) D.h
        (min (D.scale X) (D.scale Z)) ∧
      (D.improve f g).twoSidedDisagreement (f.trans g) < 2 * min (D.scale X) (D.scale Z) ∧
      ((D.improve f g).twoSidedDisagreement (f.trans g) : ℝ) ≤
        D.d * Fintype.card (D.model X) := by
  classical
  simp only [improve, dif_pos hf, dif_pos hg]
  exact Classical.choose_spec (D.improveExists f hf g hg)

/-- Canonical repaired representative of an arrow with small defects. -/
noncomputable def repair {X Y : I} (b : FinitePartialBijection (D.model X) (D.model Y)) :
    FinitePartialBijection (D.model X) (D.model Y) := by
  classical
  by_cases hb : ((b.equivarianceDefect (D.act X) (D.act Y)).card : ℝ) <
      D.K₀ * D.h * ((min (D.scale X) (D.scale Y) : ℕ) : ℝ) / 2
  · by_cases hb' : ((b.symm.equivarianceDefect (D.act Y) (D.act X)).card : ℝ) <
        D.K₀ * D.h * ((min (D.scale X) (D.scale Y) : ℕ) : ℝ) / 2
    · exact Classical.choose (D.repairExists b hb hb')
    · exact emptyPartial (D.model X) (D.model Y)
  · exact emptyPartial (D.model X) (D.model Y)

theorem repair_spec {X Y : I} (b : FinitePartialBijection (D.model X) (D.model Y))
    (hb : ((b.equivarianceDefect (D.act X) (D.act Y)).card : ℝ) <
      D.K₀ * D.h * ((min (D.scale X) (D.scale Y) : ℕ) : ℝ) / 2)
    (hb' : ((b.symm.equivarianceDefect (D.act Y) (D.act X)).card : ℝ) <
      D.K₀ * D.h * ((min (D.scale X) (D.scale Y) : ℕ) : ℝ) / 2) :
    (D.repair b).IsClusterCandidate (D.act X) (D.act Y) D.h
        (min (D.scale X) (D.scale Y)) ∧
      (D.repair b).twoSidedDisagreement b < 2 * min (D.scale X) (D.scale Y) ∧
      ((D.repair b).twoSidedDisagreement b : ℝ) ≤ D.d * Fintype.card (D.model X) := by
  classical
  simp only [repair, dif_pos hb, dif_pos hb']
  exact Classical.choose_spec (D.repairExists b hb hb')

/-- A candidate between two objects forces their scales to agree up to the
factor `11 / 10`. -/
theorem scale_comparable {X Y : I} {f : FinitePartialBijection (D.model X) (D.model Y)}
    (hf : f.IsClusterCandidate (D.act X) (D.act Y) D.h (min (D.scale X) (D.scale Y))) :
    10 * D.scale X ≤ 11 * D.scale Y := by
  obtain ⟨hs, _⟩ := hundred_mul_defects_le_of_candidate hf D.h_small
  have hcard := card_source_le_card_target_add f
  have hX := D.scale_eq X
  have hY := D.scale_eq Y
  have hlY := D.scale_large Y
  obtain ⟨hm1, hm2, _⟩ := nat_min_facts (D.scale X) (D.scale Y)
  omega

theorem size_min_left (X Y : I) :
    17 * min (D.scale X) (D.scale Y) ≤ Fintype.card (D.model X) := by
  have hX := D.scale_eq X
  obtain ⟨hm1, _, _⟩ := nat_min_facts (D.scale X) (D.scale Y)
  omega

theorem size_min_right (X Y : I) :
    17 * min (D.scale X) (D.scale Y) ≤ Fintype.card (D.model Y) := by
  have hY := D.scale_eq Y
  obtain ⟨_, hm2, _⟩ := nat_min_facts (D.scale X) (D.scale Y)
  omega

theorem one_le_min_scale (X Y : I) : 1 ≤ min (D.scale X) (D.scale Y) := by
  obtain ⟨_, _, hm3⟩ := nat_min_facts (D.scale X) (D.scale Y)
  have hX := D.scale_large X
  have hY := D.scale_large Y
  omega

/-- The cluster data at the pair radius `2 * min (scale X) (scale Y)`. -/
noncomputable def clusterData : ScaledFinitePartialClusterData I where
  model := D.model
  radius X Y := 2 * min (D.scale X) (D.scale Y)
  radius_pos X Y := by
    have h1 := D.one_le_min_scale X Y
    omega
  radius_symm X Y := by rw [min_comm]
  candidate X Y := FinitePartialBijection.clusterCandidates (D.act X) (D.act Y) D.h
    (min (D.scale X) (D.scale Y))
  one_mem X := by
    rw [FinitePartialBijection.mem_clusterCandidates, min_self]
    exact FinitePartialBijection.isClusterCandidate_refl (D.act X) D.h_pos
      (by have h1 := D.scale_large X; omega)
  symm_mem := by
    intro X Y f hf
    rw [FinitePartialBijection.mem_clusterCandidates] at hf ⊢
    rw [min_comm]
    exact hf.symm
  improve := D.improve
  improve_mem := by
    intro X Y Z f hf g hg
    rw [FinitePartialBijection.mem_clusterCandidates] at hf hg ⊢
    exact (D.improve_spec f hf g hg).1
  improve_close := by
    intro X Y Z f hf g hg
    rw [FinitePartialBijection.mem_clusterCandidates] at hf hg
    exact (D.improve_spec f hf g hg).2.1
  self_small := by
    intro X Y f hf
    rw [FinitePartialBijection.mem_clusterCandidates] at hf
    exact hf.selfSmall
  gap := by
    intro X Y f hf g hg
    rw [FinitePartialBijection.mem_clusterCandidates] at hf hg
    have hpos := D.one_le_min_scale X Y
    exact hf.gap (D.act X) (D.act Y) (hasTaggedExpansionAtScale_mono (D.expands X) hpos)
      (hasTaggedExpansionAtScale_mono (D.expands Y) hpos) (D.size_min_left X Y)
      (D.size_min_right X Y) f g hg
  radius_comparable := by
    intro X Y f hf Z
    rw [FinitePartialBijection.mem_clusterCandidates] at hf
    have hcomp := D.scale_comparable hf
    obtain ⟨hXZ1, hXZ2, hXZ3⟩ := nat_min_facts (D.scale X) (D.scale Z)
    obtain ⟨hYZ1, hYZ2, hYZ3⟩ := nat_min_facts (D.scale Y) (D.scale Z)
    omega

/-- The finite groupoid presentation of pair-scale clusters. -/
noncomputable def presentation : GroupoidPresentation I :=
  D.clusterData.presentation

theorem presentation_rel {X Y : I} (f g : D.clusterData.Rep X Y) :
    (D.presentation.rel X Y).r f g ↔
      f.1.twoSidedDisagreement g.1 < 2 * min (D.scale X) (D.scale Y) :=
  Iff.rfl

end ScaledPartialClusterSystem

namespace CentralizerNormalizationImprove
namespace ComponentFamily

variable {K : Type} [Group K] {T : Finset K}

open Classical in
/-- The scaled cluster system of a component family at index `n`, for a
threshold at most the Cheeger constant and repair statements at that
threshold. -/
noncomputable def clusterSystem (F : ComponentFamily K T) (n : ℕ)
    [Fintype (F.index n)] [Nonempty T] {K₀ h d : ℝ} (hh : 0 < h)
    (hhsmall : h ≤ 1 / 100000) (hhc : h ≤ F.cheeger)
    (hscale : ∀ i, 20 ≤ F.scale n i)
    (hrep : F.PairRepairAt K₀ h d n) (himp : F.PairImproveCloseAt h d n) :
    ScaledPartialClusterSystem (F.index n) T where
  model := F.model n
  act := F.tags n
  h := h
  h_pos := hh
  h_small := hhsmall
  d := d
  K₀ := K₀
  scale := F.scale n
  scale_large := hscale
  scale_eq := fun _ ↦ rfl
  expands := fun i ↦ hasTaggedExpansionAtScale_of_cheeger (F.expands n i) hh hhc 1
  improveExists := fun f hf g hg ↦ himp _ _ _ f hf g hg
  repairExists := fun b hb hb' ↦ hrep _ _ b hb hb'

end ComponentFamily
end CentralizerNormalizationImprove

end GroupApproximation
