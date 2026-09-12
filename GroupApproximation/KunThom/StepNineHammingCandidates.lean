import GroupApproximation.KunThom.StepNineHammingSums
import GroupApproximation.KunThom.FixedPointNormalizationScaleSums
import GroupApproximation.Matching.PartialClusterCandidates

/-!
# Step 9: the arrow terms of the budget at a vanishing threshold

`BlockEmbedding.sum_stepNineBudget_le` bounds the retained step 9 budget by global
totals.  Two of them concern the arrows themselves: the total defect of the arrows
of `α`, and `|L| · (sourceDefect + k · #defect)` over the arrows of `β`.  In Kun and
Thom (arXiv:2608.06222v3, Lemma 4.2(1)) an allowed arrow has normalized defects at
most `ε_n → 0`, and the candidate threshold `h` of `IsClusterCandidate` plays that
role.  If the arrows are candidates at threshold `h` and at scales of at most a
seventeenth of their blocks, both totals are `O(h |Y|)`.

* `BlockArrows.sum_card_equivarianceDefect_le_of_candidates`: the total defect is
  at most `h / 34 · |Y|`.
* `BlockArrows.sum_arrowTerm_le_of_candidates`: the `β` term is at most
  `(1 + |L| k) · h / 34 · |Y|`, because every missing source point is a defect for
  every label.
* `BlockEmbedding.sum_stepNineBudget_le_of_candidates`: the retained budget is at
  most the bridge, compatibility and conjugation totals plus
  `(2 + |L| k) · h / 34 · |Y|`.
-/

namespace GroupApproximation
namespace BlockPatching

open FinitePartialBijection

universe u

variable {Y : FiniteModel} {I : Type u}

namespace BlockArrows

variable {E : BlockEmbedding Y I}

/-- **Total defect of candidate arrows.**  If the arrow of every block `C` is a
cluster candidate at threshold `h` and at a scale `m C` with `17 * m C ≤ |C|`, the
arrows have at most `h / 34 · |Y|` equivariance failures in total. -/
theorem sum_card_equivarianceDefect_le_of_candidates [Fintype I] {L : Type*} [Fintype L]
    (β : BlockArrows E) (A : BlockAction E L) {h : ℝ} (hh : 0 ≤ h) (m : I → ℕ)
    (hsize : ∀ C, 17 * m C ≤ Fintype.card (E.model C))
    (hcand : ∀ C, (β.arrow C).IsClusterCandidate (A.blockAct C)
      (A.blockAct (β.objEquiv C)) h (m C)) :
    ((∑ C, ((β.arrow C).equivarianceDefect (A.blockAct C)
      (A.blockAct (β.objEquiv C))).card : ℕ) : ℝ) ≤ h / 34 * Fintype.card Y := by
  have hper : ∀ C, (((β.arrow C).equivarianceDefect (A.blockAct C)
      (A.blockAct (β.objEquiv C))).card : ℝ) ≤ h / 34 * Fintype.card (E.model C) := by
    intro C
    have hlt := (hcand C).forwardSmall
    have hm : (17 * m C : ℝ) ≤ Fintype.card (E.model C) := by
      exact_mod_cast hsize C
    have hscaled : h * (17 * m C : ℝ) ≤ h * Fintype.card (E.model C) :=
      mul_le_mul_of_nonneg_left hm hh
    linarith
  rw [Nat.cast_sum]
  exact (Finset.sum_le_sum fun C _ ↦ hper C).trans
    (E.sum_mul_card_model_le (div_nonneg hh (by norm_num)))

/-- **The arrow term of `β` for candidate arrows.**  If the arrow of every block is
a cluster candidate at threshold `h` and at a scale of at most a seventeenth of the
block, then `Σ_C |L| · (sourceDefect + k · #defect)` is at most
`(1 + |L| k) · h / 34 · |Y|`. -/
theorem sum_arrowTerm_le_of_candidates [Fintype I] {L : Type*} [Fintype L]
    (β : BlockArrows E) (A : BlockAction E L) {h : ℝ} (hh : 0 ≤ h) (m : I → ℕ)
    (hsize : ∀ C, 17 * m C ≤ Fintype.card (E.model C))
    (hcand : ∀ C, (β.arrow C).IsClusterCandidate (A.blockAct C)
      (A.blockAct (β.objEquiv C)) h (m C)) (k : ℕ) :
    ((∑ C, Fintype.card L * ((β.arrow C).sourceDefect +
      k * ((β.arrow C).equivarianceDefect (A.blockAct C)
        (A.blockAct (β.objEquiv C))).card) : ℕ) : ℝ) ≤
      ((1 + Fintype.card L * k : ℕ) : ℝ) * (h / 34 * Fintype.card Y) := by
  have hpoint : ∀ C, Fintype.card L * ((β.arrow C).sourceDefect +
      k * ((β.arrow C).equivarianceDefect (A.blockAct C)
        (A.blockAct (β.objEquiv C))).card) ≤
      (1 + Fintype.card L * k) * ((β.arrow C).equivarianceDefect (A.blockAct C)
        (A.blockAct (β.objEquiv C))).card := by
    intro C
    have hsrc := card_mul_sourceDefect_le_card_equivarianceDefect (β.arrow C)
      (A.blockAct C) (A.blockAct (β.objEquiv C))
    have e₁ : Fintype.card L * ((β.arrow C).sourceDefect +
        k * ((β.arrow C).equivarianceDefect (A.blockAct C)
          (A.blockAct (β.objEquiv C))).card) =
        Fintype.card L * (β.arrow C).sourceDefect +
          Fintype.card L * k * ((β.arrow C).equivarianceDefect (A.blockAct C)
            (A.blockAct (β.objEquiv C))).card := by
      ring
    have e₂ : (1 + Fintype.card L * k) * ((β.arrow C).equivarianceDefect (A.blockAct C)
          (A.blockAct (β.objEquiv C))).card =
        ((β.arrow C).equivarianceDefect (A.blockAct C) (A.blockAct (β.objEquiv C))).card +
          Fintype.card L * k * ((β.arrow C).equivarianceDefect (A.blockAct C)
            (A.blockAct (β.objEquiv C))).card := by
      ring
    omega
  have hsum : ∑ C, Fintype.card L * ((β.arrow C).sourceDefect +
      k * ((β.arrow C).equivarianceDefect (A.blockAct C)
        (A.blockAct (β.objEquiv C))).card) ≤
      (1 + Fintype.card L * k) * ∑ C, ((β.arrow C).equivarianceDefect (A.blockAct C)
        (A.blockAct (β.objEquiv C))).card := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun C _ ↦ hpoint C
  have hdef := β.sum_card_equivarianceDefect_le_of_candidates A hh m hsize hcand
  calc ((∑ C, Fintype.card L * ((β.arrow C).sourceDefect +
        k * ((β.arrow C).equivarianceDefect (A.blockAct C)
          (A.blockAct (β.objEquiv C))).card) : ℕ) : ℝ)
      ≤ ((1 + Fintype.card L * k : ℕ) : ℝ) *
          ((∑ C, ((β.arrow C).equivarianceDefect (A.blockAct C)
            (A.blockAct (β.objEquiv C))).card : ℕ) : ℝ) := by
        exact_mod_cast hsum
    _ ≤ ((1 + Fintype.card L * k : ℕ) : ℝ) * (h / 34 * Fintype.card Y) :=
        mul_le_mul_of_nonneg_left hdef (Nat.cast_nonneg _)

end BlockArrows

namespace BlockEmbedding

/-- **The step 9 budget for candidate arrows.**  Let `π` be injective on the
retained objects, and let the arrows of `α` and `β` be cluster candidates at
threshold `h` and at scales of at most a seventeenth of their blocks.  Then the
retained budget is at most the retained bridge terms, twice the total
compatibility failures of the labels and of the words, the total conjugation
failures of `q` and of `q⁻¹`, and `(2 + |L| k) · h / 34 · |Y|`. -/
theorem sum_stepNineBudget_le_of_candidates [Fintype I] {L : Type*} [Fintype L]
    (E : BlockEmbedding Y I) (α β : BlockArrows E) (q : Equiv.Perm Y) (A : BlockAction E L)
    (ws : L → List L) (k : ℕ) (π : I → I) (good : Finset I) (hπ : Set.InjOn π good)
    {h : ℝ} (hh : 0 ≤ h) (mα mβ : I → ℕ)
    (hsizeα : ∀ C, 17 * mα C ≤ Fintype.card (E.model C))
    (hsizeβ : ∀ C, 17 * mβ C ≤ Fintype.card (E.model C))
    (hcandα : ∀ C, (α.arrow C).IsClusterCandidate (A.blockAct C)
      (A.blockAct (α.objEquiv C)) h (mα C))
    (hcandβ : ∀ C, (β.arrow C).IsClusterCandidate (A.blockAct C)
      (A.blockAct (β.objEquiv C)) h (mβ C)) :
    ((∑ i ∈ good, E.stepNineBudget α β q A ws k π i : ℕ) : ℝ) ≤
      ((∑ i ∈ good, Fintype.card L * (E.bridge q⁻¹ (π i) i).targetDefect +
          ∑ i ∈ good, Fintype.card L *
            (E.bridge q⁻¹ (β.objEquiv (π i)) (α.objEquiv i)).sourceDefect +
          2 * ∑ s : L, ∑ C, (A.compatFailure C s).card +
          2 * ∑ s : L, ∑ C, (A.wordCompatFailure C (ws s)).card +
          ∑ s : L, ∑ C, (RelativeFunctorEstimate.conjFailure E q A
            (RelativeFunctorEstimate.wordBlockAction A ws) C s).card +
          ∑ s : L, ∑ C, (RelativeFunctorEstimate.conjFailure E q⁻¹
            (RelativeFunctorEstimate.wordBlockAction A ws) A C s).card : ℕ) : ℝ) +
        ((2 + Fintype.card L * k : ℕ) : ℝ) * (h / 34 * Fintype.card Y) := by
  have h₁ := E.sum_stepNineBudget_le α β q A ws k π good hπ
  have hα := α.sum_card_equivarianceDefect_le_of_candidates A hh mα hsizeα hcandα
  have hβ := β.sum_arrowTerm_le_of_candidates A hh mβ hsizeβ hcandβ k
  have hnat : ∑ i ∈ good, E.stepNineBudget α β q A ws k π i ≤
      (∑ i ∈ good, Fintype.card L * (E.bridge q⁻¹ (π i) i).targetDefect +
          ∑ i ∈ good, Fintype.card L *
            (E.bridge q⁻¹ (β.objEquiv (π i)) (α.objEquiv i)).sourceDefect +
          2 * ∑ s : L, ∑ C, (A.compatFailure C s).card +
          2 * ∑ s : L, ∑ C, (A.wordCompatFailure C (ws s)).card +
          ∑ s : L, ∑ C, (RelativeFunctorEstimate.conjFailure E q A
            (RelativeFunctorEstimate.wordBlockAction A ws) C s).card +
          ∑ s : L, ∑ C, (RelativeFunctorEstimate.conjFailure E q⁻¹
            (RelativeFunctorEstimate.wordBlockAction A ws) A C s).card) +
        ∑ C, ((α.arrow C).equivarianceDefect (A.blockAct C)
          (A.blockAct (α.objEquiv C))).card +
        ∑ C, Fintype.card L * ((β.arrow C).sourceDefect +
          k * ((β.arrow C).equivarianceDefect (A.blockAct C)
            (A.blockAct (β.objEquiv C))).card) := by
    omega
  have hcast : ((∑ i ∈ good, E.stepNineBudget α β q A ws k π i : ℕ) : ℝ) ≤
      ((∑ i ∈ good, Fintype.card L * (E.bridge q⁻¹ (π i) i).targetDefect +
          ∑ i ∈ good, Fintype.card L *
            (E.bridge q⁻¹ (β.objEquiv (π i)) (α.objEquiv i)).sourceDefect +
          2 * ∑ s : L, ∑ C, (A.compatFailure C s).card +
          2 * ∑ s : L, ∑ C, (A.wordCompatFailure C (ws s)).card +
          ∑ s : L, ∑ C, (RelativeFunctorEstimate.conjFailure E q A
            (RelativeFunctorEstimate.wordBlockAction A ws) C s).card +
          ∑ s : L, ∑ C, (RelativeFunctorEstimate.conjFailure E q⁻¹
            (RelativeFunctorEstimate.wordBlockAction A ws) A C s).card : ℕ) : ℝ) +
        ((∑ C, ((α.arrow C).equivarianceDefect (A.blockAct C)
          (A.blockAct (α.objEquiv C))).card : ℕ) : ℝ) +
        ((∑ C, Fintype.card L * ((β.arrow C).sourceDefect +
          k * ((β.arrow C).equivarianceDefect (A.blockAct C)
            (A.blockAct (β.objEquiv C))).card) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hcoef : ((2 + Fintype.card L * k : ℕ) : ℝ) * (h / 34 * Fintype.card Y) =
      h / 34 * Fintype.card Y +
        ((1 + Fintype.card L * k : ℕ) : ℝ) * (h / 34 * Fintype.card Y) := by
    push_cast
    ring
  linarith

end BlockEmbedding

end BlockPatching
end GroupApproximation
