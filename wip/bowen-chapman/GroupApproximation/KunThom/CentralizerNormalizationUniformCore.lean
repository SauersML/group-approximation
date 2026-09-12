import GroupApproximation.KunThom.CentralizerNormalizationUniformSelection
import GroupApproximation.KunThom.CentralizerNormalizationPrunedCore

/-!
# Core components: good components with expanding pruned cores

A *core component* is a good component (`goodComponent`) whose local edit
budget satisfies the inequality under which its pruned core
(`ExpanderDecomposition.prunedCore`) carries an exact directed Cheeger bound.
These are the objects of the component family built from an expander
decomposition.

* `coreComponent_hasCheegerLowerBound`: the pruned core of a core component
  has the directed Cheeger bound `cheeger / 4 / |T|` for the completed core
  labels.
* `coreComponent_badMass`: components that are not core components carry
  negligible mass.
* `coreComponent_removedMass`: the points removed from core components by
  pruning carry negligible mass.
* `coreComponent_size`: pruned cores of core components are uniformly large.
-/

namespace GroupApproximation
namespace CentralizerNormalizationUniform

open scoped BigOperators

/-- Good components whose edit budget is small enough for the pruned core to
expand. -/
def IsCoreComponent {K : Type} [Group K] [Countable K] [Infinite K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T) (hgen : Subgroup.closure (T : Set K) = ⊤)
    (n : ℕ) (C : D.componentIndex n) : Prop :=
  goodComponent D hsymm hgen n C ∧
    (D.componentLabelEditBudget n C : ℝ) * (8 * D.cheeger + 32 * T.card) ≤
      D.cheeger ^ 2 * C.block.card

theorem coreComponent_cheeger_pos {K : Type} [Group K] {S : SoficApproximation K}
    {T : Finset K} (D : ExpanderDecomposition S T) (hT : T.Nonempty) :
    0 < D.cheeger / 4 / T.card :=
  div_pos (div_pos D.cheeger_pos (by norm_num))
    (by exact_mod_cast Finset.card_pos.mpr hT)

/-- Exact directed expansion of the pruned core of a core component. -/
theorem coreComponent_hasCheegerLowerBound {K : Type} [Group K] [Countable K] [Infinite K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T) (hgen : Subgroup.closure (T : Set K) = ⊤)
    (hT : T.Nonempty) (n : ℕ) (C : D.componentIndex n)
    (hC : IsCoreComponent D hsymm hgen n C) :
    DirectedCoarea.HasCheegerLowerBound (D.prunedCoreModel n C)
      (T.image (D.prunedCoreAct n C)) (D.cheeger / 4 / T.card) :=
  D.prunedCore_hasCheegerLowerBound n C hT hC.2

open Classical in
/-- Components that are not core components carry negligible mass. -/
theorem coreComponent_badMass {K : Type} [Group K] [Countable K] [Infinite K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T) (hgen : Subgroup.closure (T : Set K) = ⊤) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n,
        if IsCoreComponent D hsymm hgen n C then 0 else (C.block.card : ℝ)) := by
  have hb : (0 : ℝ) ≤ 8 * D.cheeger + 32 * T.card :=
    add_nonneg (mul_nonneg (by norm_num) D.cheeger_pos.le)
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  obtain ⟨M, hM⟩ := eventually_budget_mul_le D (goodComponent D hsymm hgen)
    (goodComponent_errors D hsymm hgen) (pow_pos D.cheeger_pos 2) hb
  refine Vanishing.squeeze_eventually (goodComponent_badMass D hsymm hgen) M
    fun n hn ↦ ⟨?_, ?_⟩
  · apply div_nonneg _ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro C _
    split_ifs
    · exact le_rfl
    · exact Nat.cast_nonneg _
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro C _
    by_cases hC : goodComponent D hsymm hgen n C
    · rw [if_pos (show IsCoreComponent D hsymm hgen n C from ⟨hC, hM n hn C hC⟩),
        if_pos hC]
    · rw [if_neg (show ¬ IsCoreComponent D hsymm hgen n C from fun hcore ↦ hC hcore.1),
        if_neg hC]

/-- A component with budget at most `cheeger |C| / 4` keeps at least half of its
points in the pruned core. -/
theorem card_le_two_mul_card_prunedCore {K : Type} [Group K] {S : SoficApproximation K}
    {T : Finset K} (D : ExpanderDecomposition S T) (n : ℕ) (C : D.componentIndex n)
    (hbudget : (D.componentLabelEditBudget n C : ℝ) * 4 ≤ D.cheeger * C.block.card) :
    (C.block.card : ℝ) ≤ 2 * (D.prunedCore n C).card := by
  have hrem := D.prunedCore_removed_le n C
  have hc := D.cheeger_pos
  nlinarith [hrem, hbudget, hc]

/-- Pruned cores of core components are uniformly large. -/
theorem coreComponent_size {K : Type} [Group K] [Countable K] [Infinite K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T) (hgen : Subgroup.closure (T : Set K) = ⊤) :
    ∀ M₀ : ℕ, ∃ M : ℕ, ∀ n ≥ M, ∀ C, IsCoreComponent D hsymm hgen n C →
      M₀ ≤ (D.prunedCore n C).card := by
  intro M₀
  obtain ⟨M1, hM1⟩ := goodComponent_size D hsymm hgen (2 * M₀)
  obtain ⟨M2, hM2⟩ := eventually_budget_mul_le D (goodComponent D hsymm hgen)
    (goodComponent_errors D hsymm hgen) (a := D.cheeger) (b := 4) D.cheeger_pos
    (by norm_num)
  refine ⟨max M1 M2, fun n hn C hC ↦ ?_⟩
  have hsize : 2 * M₀ ≤ C.block.card := hM1 n ((le_max_left _ _).trans hn) C hC.1
  have hhalf := card_le_two_mul_card_prunedCore D n C
    (hM2 n ((le_max_right _ _).trans hn) C hC.1)
  have hsizeR : (2 * M₀ : ℝ) ≤ C.block.card := by exact_mod_cast hsize
  have hreal : (M₀ : ℝ) ≤ (D.prunedCore n C).card := by linarith
  exact_mod_cast hreal

open Classical in
/-- Points removed from core components by pruning carry negligible mass. -/
theorem coreComponent_removedMass {K : Type} [Group K] [Countable K] [Infinite K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T) (hgen : Subgroup.closure (T : Set K) = ⊤) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n,
        if IsCoreComponent D hsymm hgen n C then
          ((C.block.card : ℝ) - (D.prunedCore n C).card) else 0) := by
  have hbudget := Negligible.const_mul (2 / D.cheeger)
    D.componentLabelEditBudget_sum_negligible
  refine Negligible.mono_nonneg (fun _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_) (fun n ↦ ?_)
    hbudget
  · apply Finset.sum_nonneg
    intro C _
    split_ifs
    · have hle : (D.prunedCore n C).card ≤ C.block.card := by
        have h1 := Finset.card_le_univ (D.prunedCore n C)
        rwa [card_indexedBlockModel] at h1
      have hleR : ((D.prunedCore n C).card : ℝ) ≤ C.block.card := by exact_mod_cast hle
      linarith
    · exact le_rfl
  · show (∑ C : D.componentIndex n,
        if IsCoreComponent D hsymm hgen n C then
          ((C.block.card : ℝ) - (D.prunedCore n C).card) else 0) ≤
      2 / D.cheeger * ∑ C : D.componentIndex n, (D.componentLabelEditBudget n C : ℝ)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro C _
    have hc := D.cheeger_pos
    have hB0 : (0 : ℝ) ≤ D.componentLabelEditBudget n C := Nat.cast_nonneg _
    split_ifs
    · have hrem := D.prunedCore_removed_le n C
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      linarith
    · exact mul_nonneg (div_nonneg (by norm_num) hc.le) hB0

end CentralizerNormalizationUniform
end GroupApproximation
