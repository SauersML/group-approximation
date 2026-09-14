import GroupApproximation.KunThom.StepNineHammingCandidates
import GroupApproximation.KunThom.CompressorNormalizationAssemblyFrame
import GroupApproximation.KunThom.BisectionActualDefect
import GroupApproximation.KunThom.CentralizerNormalizationPairImprove

/-!
# Step 9 over a cluster frame: the arrow terms are negligible

The step 9 estimate of Kun and Thom's proof of Theorem 4.1 (arXiv:2608.06222v3,
tex lines 1314--1338) needs the actual equivariance defects of the patched
bisections to be `o(|Y_n|)`.  Over a cluster frame every block arrow of a total
bisection is a cluster candidate at the frame threshold, so these defects are at
most a multiple of the threshold times the model size, and they are negligible once
the threshold vanishes.

* `negligible_mul_card_of_vanishing`: a vanishing nonnegative coefficient times the
  model size is negligible.
* `negligible_sum_card_arrowDefect`: the total defect of the arrows of a sequence of
  total bisections is negligible.
* `negligible_sum_arrowTerm`: so is `Σ_C |L| · (sourceDefect + k · #defect)`, the
  arrow term of `BlockEmbedding.sum_stepNineBudget_le`.
* `negligible_card_compl_domain`: the mass off the glued domain of the patched
  bisections is negligible.
* `hasTaggedExpansionAtScale_frameAction`: the block labels of the frame expand with
  the fixed constant `cheeger / 4` at every scale.  Separation has to use this fixed
  constant rather than the vanishing threshold, or the budget over the constant would
  not vanish.
-/

namespace GroupApproximation
namespace StepNineHammingFrame

open FinitePartialBijection BlockPatching CompressorNormalizationAssembly

/-- A vanishing nonnegative coefficient times the model size is negligible. -/
theorem negligible_mul_card_of_vanishing {Y : ℕ → FiniteModel} {c : ℕ → ℝ} (hc : Vanishing c)
    (hnn : ∀ n, 0 ≤ c n) :
    Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦ c n * Fintype.card (Y n) := by
  refine Vanishing.squeeze
    (a := fun n ↦ c n * (Fintype.card (Y n) : ℝ) / Fintype.card (Y n)) (b := c)
    (fun n ↦ div_nonneg (mul_nonneg (hnn n) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    (fun n ↦ ?_) hc
  show c n * (Fintype.card (Y n) : ℝ) / Fintype.card (Y n) ≤ c n
  by_cases h : (Fintype.card (Y n) : ℝ) = 0
  · rw [h, mul_zero, zero_div]
    exact hnn n
  · rw [mul_div_assoc, div_self h, mul_one]

open Classical in
/-- **The arrow defects over a frame.**  If the threshold of a cluster frame vanishes,
the total equivariance defect of the block arrows of any sequence of total bisections
is negligible. -/
theorem negligible_sum_card_arrowDefect {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R)
    (hthr : Vanishing F.threshold) (b : ∀ n, F.Bis n) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ((∑ X, (((F.arrows n (b n)).arrow X).equivarianceDefect ((F.action n).blockAct X)
        ((F.action n).blockAct ((F.arrows n (b n)).objEquiv X))).card : ℕ) : ℝ) := by
  refine Negligible.mono_nonneg (fun n ↦ Nat.cast_nonneg _) (fun n ↦ Nat.cast_nonneg _)
    (fun n ↦ ?_)
    (negligible_mul_card_of_vanishing (Y := A.model) (c := fun n ↦ F.threshold n / 34)
      ((hthr.const_mul (1 / 34)).congr fun n ↦ by
        show 1 / 34 * F.threshold n = F.threshold n / 34
        ring)
      fun n ↦ div_nonneg (F.threshold_pos n).le (by norm_num))
  exact BlockArrows.sum_card_equivarianceDefect_le_of_candidates (F.arrows n (b n))
    (F.action n) (F.threshold_pos n).le
    (fun X ↦ min ((F.system n).scale X) ((F.system n).scale ((F.arrows n (b n)).objEquiv X)))
    (fun X ↦ (F.system n).size_min_left X _) (fun X ↦ F.arrows_isClusterCandidate n (b n) X)

open Classical in
/-- **The arrow term over a frame.**  If the threshold of a cluster frame vanishes, the
arrow term `Σ_C |L| · (sourceDefect + k · #defect)` of any sequence of total
bisections is negligible. -/
theorem negligible_sum_arrowTerm {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R)
    (hthr : Vanishing F.threshold) (b : ∀ n, F.Bis n) (k : ℕ) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ((∑ X, Fintype.card ↥R.data.generators * (((F.arrows n (b n)).arrow X).sourceDefect +
        k * (((F.arrows n (b n)).arrow X).equivarianceDefect ((F.action n).blockAct X)
          ((F.action n).blockAct ((F.arrows n (b n)).objEquiv X))).card) : ℕ) : ℝ) := by
  refine Negligible.mono_nonneg (fun n ↦ Nat.cast_nonneg _) (fun n ↦ Nat.cast_nonneg _)
    (fun n ↦ ?_)
    (negligible_mul_card_of_vanishing (Y := A.model)
      (c := fun n ↦ ((1 + Fintype.card ↥R.data.generators * k : ℕ) : ℝ) * (F.threshold n / 34))
      ((hthr.const_mul (((1 + Fintype.card ↥R.data.generators * k : ℕ) : ℝ) / 34)).congr
        fun n ↦ by
          show ((1 + Fintype.card ↥R.data.generators * k : ℕ) : ℝ) / 34 * F.threshold n =
            ((1 + Fintype.card ↥R.data.generators * k : ℕ) : ℝ) * (F.threshold n / 34)
          ring)
      fun n ↦ mul_nonneg (Nat.cast_nonneg _) (div_nonneg (F.threshold_pos n).le (by norm_num)))
  exact (BlockArrows.sum_arrowTerm_le_of_candidates (F.arrows n (b n)) (F.action n)
    (F.threshold_pos n).le
    (fun X ↦ min ((F.system n).scale X) ((F.system n).scale ((F.arrows n (b n)).objEquiv X)))
    (fun X ↦ (F.system n).size_min_left X _) (fun X ↦ F.arrows_isClusterCandidate n (b n) X)
    k).trans_eq (by ring)

/-- **The mass off the glued domain over a frame.**  If the threshold of a cluster
frame vanishes, the mass off the glued domain of the patched bisections is
negligible: it lies in no block, or it is a missing source point of a block arrow,
which is a defect for every label. -/
theorem negligible_card_compl_domain {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R)
    (hthr : Vanishing F.threshold) (b : ∀ n, F.Bis n) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ((Finset.univ \ (F.arrows n (b n)).domain).card : ℝ) := by
  refine Negligible.mono_nonneg (fun n ↦ Nat.cast_nonneg _) (fun n ↦ Nat.cast_nonneg _)
    (fun n ↦ ?_) (F.uncovered_negligible.add (negligible_sum_card_arrowDefect F hthr b))
  have hdom := (F.arrows n (b n)).card_compl_domain_le
  have hsrc : ∑ X, ((F.arrows n (b n)).arrow X).sourceDefect ≤
      ∑ X, (((F.arrows n (b n)).arrow X).equivarianceDefect ((F.action n).blockAct X)
        ((F.action n).blockAct ((F.arrows n (b n)).objEquiv X))).card :=
    Finset.sum_le_sum fun X _ ↦ sourceDefect_le_card_equivarianceDefect
      ((F.arrows n (b n)).arrow X) ((F.action n).blockAct X)
      ((F.action n).blockAct ((F.arrows n (b n)).objEquiv X))
  have hnat : (Finset.univ \ (F.arrows n (b n)).domain).card ≤
      (F.embedding n).uncovered.card +
        ∑ X, (((F.arrows n (b n)).arrow X).equivarianceDefect ((F.action n).blockAct X)
          ((F.action n).blockAct ((F.arrows n (b n)).objEquiv X))).card := by
    omega
  exact_mod_cast hnat

/-- **Expansion of the frame labels at a fixed constant.**  The directed Cheeger
bound of the component family gives tagged expansion of every block of the frame with
constant `cheeger / 4`, at every scale. -/
theorem hasTaggedExpansionAtScale_frameAction {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R)
    (n : ℕ) (X : F.Obj n) (m : ℕ) :
    HasTaggedExpansionAtScale ((F.action n).blockAct X) (R.data.family.cheeger / 4) m :=
  CentralizerNormalizationImprove.hasTaggedExpansionAtScale_of_cheeger
    (R.data.family.expands n X.1) (div_pos R.data.family.cheeger_pos (by norm_num))
    (by linarith [R.data.family.cheeger_pos]) m

end StepNineHammingFrame
end GroupApproximation
