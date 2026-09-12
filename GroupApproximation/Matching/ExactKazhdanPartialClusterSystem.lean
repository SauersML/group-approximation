import GroupApproximation.Matching.ExactPartialKazhdanRepair
import GroupApproximation.Matching.PartialClusterPresentation

/-!
# Exact Kazhdan finite cluster systems

This module discharges `PartialClusterSystem.improveExists` for a finite
family of exact transitive actions of one group.  The improving arrow is the
invariant singleton-fiber core constructed by exact Kazhdan rounding; no
choice of an improvement theorem remains in the resulting system.
-/

namespace GroupApproximation
namespace PartialClusterSystem

open ExactPartialKazhdanRepair

universe u

/-- A finite family of exact transitive actions with uniform expansion and
size bounds forms a `PartialClusterSystem` whenever the cluster expansion
constant lies below the explicit Kazhdan repair threshold. -/
noncomputable def ofExactTransitiveKazhdanActions
    {I : Type u} [Fintype I]
    {G : Type u} [Group G]
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (hε : 0 < ε)
    (decEqQ : DecidableEq ↥Q := Classical.decEq ↥Q)
    (model : I → FiniteModel)
    (action : ∀ X, G →* Equiv.Perm (model X))
    (transitive : ∀ X, ∀ x y : model X, ∃ g : G, action X g x = y)
    (h : ℝ) (h_pos : 0 < h) (numeric : 48 * h < ε ^ 2)
    (scale : ℕ) (scale_pos : 0 < scale)
    (expands : ∀ X,
      FinitePartialBijection.HasTaggedExpansionAtScale
        (fun q : ↥Q ↦ action X q.1) h scale)
    (size : ∀ X, 17 * scale ≤ Fintype.card (model X)) :
    @PartialClusterSystem I _ ↥Q _ decEqQ where
  model := model
  act X := fun q ↦ action X q.1
  h := h
  h_pos := h_pos
  scale := scale
  scale_pos := scale_pos
  expands := expands
  size := size
  improveExists := by
    intro X Y Z f hf g hg
    let r := exactCoreRepair (action X) (action Z) (f.trans g)
    refine ⟨r, ?_⟩
    simpa only [r] using exactCoreRepair_trans_candidate_and_close
      hQ hε (action X) (action Y) (action Z)
      (transitive X) (transitive Z) h_pos scale_pos numeric
      (size X) f hf g hg

/-- The corresponding finite groupoid presentation, obtained without an
abstract `improveExists` premise. -/
noncomputable def exactKazhdanPresentation
    {I : Type u} [Fintype I]
    {G : Type u} [Group G]
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (hε : 0 < ε)
    (model : I → FiniteModel)
    (action : ∀ X, G →* Equiv.Perm (model X))
    (transitive : ∀ X, ∀ x y : model X, ∃ g : G, action X g x = y)
    (h : ℝ) (h_pos : 0 < h) (numeric : 48 * h < ε ^ 2)
    (scale : ℕ) (scale_pos : 0 < scale)
    (expands : ∀ X,
      FinitePartialBijection.HasTaggedExpansionAtScale
        (fun q : ↥Q ↦ action X q.1) h scale)
    (size : ∀ X, 17 * scale ≤ Fintype.card (model X)) :
    GroupoidPresentation I := by
  letI : DecidableEq ↥Q := Classical.decEq _
  exact (ofExactTransitiveKazhdanActions hQ hε (decEqQ := inferInstance)
    model action transitive
    h h_pos numeric scale scale_pos expands size).presentation

end PartialClusterSystem
end GroupApproximation
