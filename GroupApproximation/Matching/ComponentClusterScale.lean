import GroupApproximation.Matching.ComponentLabelCompletion
import GroupApproximation.Matching.ComponentDivergence

/-!
# Good component scales for partial-intertwiner clusters

The scale `|C| / 18` leaves the factor seventeen required by the two-sided
separation theorem.  A component is good when it is large enough and its
completed-label edit budget is less than `h |C| / 72`.  The elementary floor
estimate then supplies the `h m / 2` bound needed for tagged expansion.
-/

namespace GroupApproximation
namespace ExpanderDecomposition

open scoped BigOperators

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}
variable (D : ExpanderDecomposition S T)

/-- Separation scale on a finite component. -/
def componentClusterScale (n : ℕ) (C : D.componentIndex n) : ℕ :=
  C.block.card / 18

theorem componentClusterScale_pos (n : ℕ) (C : D.componentIndex n)
    (hC : 18 ≤ C.block.card) : 0 < D.componentClusterScale n C := by
  unfold componentClusterScale
  omega

theorem seventeen_mul_componentClusterScale_le
    (n : ℕ) (C : D.componentIndex n) :
    17 * D.componentClusterScale n C ≤ C.block.card := by
  unfold componentClusterScale
  omega

theorem card_le_thirtySix_mul_componentClusterScale
    (n : ℕ) (C : D.componentIndex n) (hC : 18 ≤ C.block.card) :
    C.block.card ≤ 36 * D.componentClusterScale n C := by
  unfold componentClusterScale
  omega

/-- Components large enough for the gap theorem and carrying sufficiently
small local graph-edit error. -/
def IsClusterGood (n : ℕ) (C : D.componentIndex n) : Prop :=
  18 ≤ C.block.card ∧
    (D.componentLabelEditBudget n C : ℝ) <
      D.cheeger * C.block.card / 72

theorem clusterGood_taggedExpansion (n : ℕ) (C : D.componentIndex n)
    (hC : D.IsClusterGood n C) :
    FinitePartialBijection.HasTaggedExpansionAtScale
      (fun t : T ↦ D.componentCompletedAction n C t.1)
      (D.cheeger / 4) (D.componentClusterScale n C) := by
  apply D.componentCompletedAction_taggedExpansion
  have hcard := D.card_le_thirtySix_mul_componentClusterScale n C hC.1
  have hcardReal : (C.block.card : ℝ) ≤
      36 * D.componentClusterScale n C := by exact_mod_cast hcard
  have hscaled := mul_le_mul_of_nonneg_left hcardReal D.cheeger_pos.le
  exact hC.2.trans_le (by linarith)

/-- Total vertex mass of components failing the cluster conditions. -/
noncomputable def badClusterComponentMass (n : ℕ) : ℝ :=
  by
    classical
    exact ∑ C : D.componentIndex n,
      if D.IsClusterGood n C then 0 else (C.block.card : ℝ)

/-- Bad component mass is bounded by the bounded-component locus plus a
fixed multiple of the total local edit budget. -/
theorem badClusterComponentMass_le (n : ℕ) :
    D.badClusterComponentMass n ≤
      ((smallBlockVertices (D.blocks n) 17).card : ℝ) +
        (72 / D.cheeger) *
          ∑ C : D.componentIndex n,
            (D.componentLabelEditBudget n C : ℝ) := by
  classical
  have hcoef : 0 ≤ (72 : ℝ) / D.cheeger :=
    (div_pos (by norm_num) D.cheeger_pos).le
  rw [← sum_smallBlock_card (D.blocks n) 17]
  unfold badClusterComponentMass
  calc
    (∑ C : D.componentIndex n,
      if D.IsClusterGood n C then 0 else (C.block.card : ℝ)) ≤
        ∑ C : D.componentIndex n,
          ((if (C.block.card : ℝ) ≤ 17 then (C.block.card : ℝ) else 0) +
            (72 / D.cheeger) * D.componentLabelEditBudget n C) := by
      apply Finset.sum_le_sum
      intro C _
      by_cases hgood : D.IsClusterGood n C
      · rw [if_pos hgood]
        exact add_nonneg (by positivity) (mul_nonneg hcoef (by positivity))
      · rw [if_neg hgood]
        by_cases hsmall : C.block.card ≤ 17
        · rw [if_pos (by exact_mod_cast hsmall)]
          exact le_add_of_nonneg_right (mul_nonneg hcoef (by positivity))
        · rw [if_neg (by exact_mod_cast hsmall), zero_add]
          have hlarge : 18 ≤ C.block.card := by omega
          have hbudget : D.cheeger * (C.block.card : ℝ) / 72 ≤
              D.componentLabelEditBudget n C := by
            have : ¬(D.componentLabelEditBudget n C : ℝ) <
                D.cheeger * C.block.card / 72 := by
              intro h
              exact hgood ⟨hlarge, h⟩
            exact le_of_not_gt this
          have hcheeger : D.cheeger ≠ 0 := D.cheeger_pos.ne'
          calc
            (C.block.card : ℝ) = (72 / D.cheeger) *
                (D.cheeger * C.block.card / 72) := by
              field_simp
            _ ≤ (72 / D.cheeger) * D.componentLabelEditBudget n C :=
              mul_le_mul_of_nonneg_left hbudget hcoef
    _ = (∑ C : D.componentIndex n,
          if (C.block.card : ℝ) ≤ 17 then (C.block.card : ℝ) else 0) +
        (72 / D.cheeger) *
          ∑ C : D.componentIndex n,
            (D.componentLabelEditBudget n C : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Under the internally proved divergence of components, the bad cluster
component mass is negligible. -/
theorem badClusterComponentMass_negligible [Infinite G]
    (hsymm : ∀ g ∈ T, g⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set G) = ⊤) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (D.badClusterComponentMass) := by
  have hsmall := D.smallBlockVertices_negligible hsymm hgen 17
  have hbudget := Negligible.const_mul (72 / D.cheeger)
    D.componentLabelEditBudget_sum_negligible
  have hmajor := Negligible.add hsmall hbudget
  exact Negligible.mono_nonneg (fun _ ↦ by positivity) (fun _ ↦ by
      unfold badClusterComponentMass
      positivity) (fun n ↦ D.badClusterComponentMass_le n) hmajor

end ExpanderDecomposition
end GroupApproximation
