import GroupApproximation.KunThom.RetainedComponentExpansion
import GroupApproximation.Matching.ComponentLabelCompletion

/-!
# Pruned cores of expander components

The completed component labels of `ComponentLabelCompletion` expand only at a
scale.  `CentralizerNormalizationImprove.ComponentFamily` needs an exact directed
Cheeger bound.  This module specializes `RetainedComponentExpansion` to one
component `C` of an `ExpanderDecomposition`:

* `prunedCore`: the retained set of the maximum sparse cut at constant
  `cheeger / 4` of the completed generator graph on `C`;
* `prunedCoreAct`: the completed labels, completed again on the core;
* `prunedCore_hasCheegerLowerBound`: if the local edit budget `b` satisfies
  `b (8 cheeger + 32 |T|) ≤ cheeger² |C|`, the core labels have directed
  Cheeger constant `cheeger / 4 / |T|`;
* `prunedCore_removed_le`: `cheeger (|C| - |core|) ≤ 2 b`.
-/

namespace GroupApproximation
namespace ExpanderDecomposition

open RetainedComponentExpansion

/-- The pruned core of a component. -/
noncomputable abbrev prunedCore {G : Type} [Group G] {S : SoficApproximation G}
    {T : Finset G} (D : ExpanderDecomposition S T) (n : ℕ) (C : D.componentIndex n) :
    Finset (indexedBlockModel (D.blocks n) C) :=
  retainedSet (indexedBlockModel (D.blocks n) C) T (D.componentCompletedAction n C)
    (D.cheeger / 4)

/-- The pruned core as a finite model. -/
noncomputable abbrev prunedCoreModel {G : Type} [Group G] {S : SoficApproximation G}
    {T : Finset G} (D : ExpanderDecomposition S T) (n : ℕ) (C : D.componentIndex n) :
    FiniteModel :=
  retainedModel (indexedBlockModel (D.blocks n) C) T (D.componentCompletedAction n C)
    (D.cheeger / 4)

/-- The completed component labels, completed again on the pruned core. -/
noncomputable def prunedCoreAct {G : Type} [Group G] {S : SoficApproximation G}
    {T : Finset G} (D : ExpanderDecomposition S T) (n : ℕ) (C : D.componentIndex n)
    (g : G) : Equiv.Perm (prunedCore D n C) :=
  Classical.choose
    (Localization.exists_completion (prunedCore D n C) (D.componentCompletedAction n C g))

/-- The core labels agree with the completed labels whenever the image stays in
the core. -/
theorem prunedCoreAct_agrees {G : Type} [Group G] {S : SoficApproximation G}
    {T : Finset G} (D : ExpanderDecomposition S T) (n : ℕ) (C : D.componentIndex n)
    (g : G) (x : prunedCore D n C)
    (hx : D.componentCompletedAction n C g (x : indexedBlockModel (D.blocks n) C) ∈
      prunedCore D n C) :
    (D.prunedCoreAct n C g x : indexedBlockModel (D.blocks n) C) =
      D.componentCompletedAction n C g x := by
  exact Classical.choose_spec
    (Localization.exists_completion (prunedCore D n C) (D.componentCompletedAction n C g))
      x hx

/-- The additive Cheeger inequality of the completed labels on a component. -/
theorem componentCompleted_additiveCheeger {G : Type} [Group G] {S : SoficApproximation G}
    {T : Finset G} (D : ExpanderDecomposition S T) (n : ℕ) (C : D.componentIndex n) :
    ∀ U : Finset (indexedBlockModel (D.blocks n) C), U.Nonempty →
      2 * U.card ≤ Fintype.card (indexedBlockModel (D.blocks n) C) →
        D.cheeger / 2 * (U.card : ℝ) ≤
          ((generatorGraph (indexedBlockModel (D.blocks n) C) T
            (D.componentCompletedAction n C)).boundaryCard U : ℝ) +
            (D.componentLabelEditBudget n C : ℝ) / 2 :=
  additiveCheeger_of_edit (indexedBlockModel (D.blocks n) C) T
    (D.componentCompletedAction n C) (D.directIndexedComponentGraph n C) (Equiv.refl _)
    (D.directIndexedComponentGraph_expands n C)
    (by exact_mod_cast D.componentCompletedGraph_editDistance_le n C)

/-- **Exact directed expansion on the pruned core.** -/
theorem prunedCore_hasCheegerLowerBound {G : Type} [Group G] {S : SoficApproximation G}
    {T : Finset G} (D : ExpanderDecomposition S T) (n : ℕ) (C : D.componentIndex n)
    (hT : T.Nonempty)
    (hbudget : (D.componentLabelEditBudget n C : ℝ) * (8 * D.cheeger + 32 * T.card) ≤
      D.cheeger ^ 2 * C.block.card) :
    DirectedCoarea.HasCheegerLowerBound (prunedCoreModel D n C)
      (T.image (D.prunedCoreAct n C)) (D.cheeger / 4 / T.card) := by
  have hc := D.cheeger_pos
  have hNnat : Fintype.card (indexedBlockModel (D.blocks n) C) = C.block.card := by
    simp [indexedBlockModel]
  have hN : (Fintype.card (indexedBlockModel (D.blocks n) C) : ℝ) = C.block.card := by
    exact_mod_cast hNnat
  have hsmall : 4 * ((D.componentLabelEditBudget n C : ℝ) / 2) *
        (D.cheeger / 2 - D.cheeger / 4) +
      2 * ((2 * T.card : ℕ) : ℝ) * ((D.componentLabelEditBudget n C : ℝ) / 2) ≤
      (D.cheeger / 2 - D.cheeger / 4) * (D.cheeger / 2 - D.cheeger / 4) *
        (Fintype.card (indexedBlockModel (D.blocks n) C) : ℝ) := by
    rw [hN]
    push_cast
    nlinarith [hbudget]
  exact retained_completion_directedCheeger (indexedBlockModel (D.blocks n) C) T hT
    (D.componentCompletedAction n C) (γ := D.cheeger / 2) (c := D.cheeger / 4)
    (E := (D.componentLabelEditBudget n C : ℝ) / 2)
    (div_pos hc (by norm_num)) (by linarith) (by positivity)
    (D.componentCompleted_additiveCheeger n C) hsmall (D.prunedCoreAct n C)
    (fun t x hx ↦ D.prunedCoreAct_agrees n C t.1 x hx)

/-- **Removed mass.**  At most `2 b / cheeger` points leave the component. -/
theorem prunedCore_removed_le {G : Type} [Group G] {S : SoficApproximation G}
    {T : Finset G} (D : ExpanderDecomposition S T) (n : ℕ) (C : D.componentIndex n) :
    D.cheeger * ((C.block.card : ℝ) - (prunedCore D n C).card) ≤
      2 * (D.componentLabelEditBudget n C : ℝ) := by
  have hb : (D.cheeger / 2 - D.cheeger / 4) *
      ((MaximalCutRepair.sparseCut (generatorGraph (indexedBlockModel (D.blocks n) C) T
        (D.componentCompletedAction n C)) (D.cheeger / 4)).card : ℝ) ≤
      (D.componentLabelEditBudget n C : ℝ) / 2 :=
    sparseCut_card_mul_le (indexedBlockModel (D.blocks n) C) T
      (D.componentCompletedAction n C) (c := D.cheeger / 4) (by positivity)
      (D.componentCompleted_additiveCheeger n C)
  have hpart := card_retainedSet_add_sparseCut (indexedBlockModel (D.blocks n) C) T
    (D.componentCompletedAction n C) (D.cheeger / 4)
  have hNnat : Fintype.card (indexedBlockModel (D.blocks n) C) = C.block.card := by
    simp [indexedBlockModel]
  have hcast : ((prunedCore D n C).card : ℝ) +
      ((MaximalCutRepair.sparseCut (generatorGraph (indexedBlockModel (D.blocks n) C) T
        (D.componentCompletedAction n C)) (D.cheeger / 4)).card : ℝ) = C.block.card := by
    exact_mod_cast hpart.trans hNnat
  have hmul : D.cheeger * (((prunedCore D n C).card : ℝ) +
      ((MaximalCutRepair.sparseCut (generatorGraph (indexedBlockModel (D.blocks n) C) T
        (D.componentCompletedAction n C)) (D.cheeger / 4)).card : ℝ)) =
      D.cheeger * C.block.card := by
    rw [hcast]
  linarith [hb, hmul]

end ExpanderDecomposition
end GroupApproximation
