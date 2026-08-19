import GroupApproximation.Analysis.FiniteBlockCoronaHilbert

/-!
# "Unitary lifting is not matrix-specific", with nothing added to the print

The manuscript's Questions subsection prints the lifting sentence for arbitrary
unital coordinate algebras:

> If `u` is unitary in `∏_nA_n/⨁_nA_n` for unital `C*`-algebras `A_n`, and
> `(x_n)` is any bounded lift, then `‖x_n^*x_n - 1‖ → 0` and
> `‖x_nx_n^* - 1‖ → 0`.  Thus `x_n` is invertible for all large `n`, and the
> polar correction `u_n = x_n(x_n^*x_n)^{-1/2}` is unitary with
> `‖u_n - x_n‖ → 0`.  No real-rank-zero or semiprojectivity hypothesis is
> needed for this lifting step.

`Analysis/PolarLiftingGeneralCStar` proves this against mathlib's `lp A ∞`, and
that route carries one binder the print does not: `[∀ n, Nontrivial (A n)]`.
The binder is not mathematics -- mathlib builds the *unital* ring structure on
`lp A ∞` only under `NormOneClass` of every block, which for a `C*`-algebra is
exactly nontriviality -- but it is a hypothesis, and a hypothesis in the Lean
statement that is absent from the printed one is a gap whatever its origin.

This file removes it, by stating the sentence where the print states it: on the
lift.  In the quotient `∏_nA_n/⨁_nA_n` the two identities `u^*u = 1` and
`uu^* = 1` say precisely that the two coordinate Gram defects of any lift are
null along the filter -- membership in `⨁_nA_n` *is* the vanishing of the
coordinate norms -- so taking those two vanishing statements as the hypothesis
is the printed hypothesis, read on the printed lift.  With `u` gone from the
statement the product algebra is gone too, and with it every nondegeneracy
requirement on the blocks.

Two further hypotheses of the printed sentence also disappear, because they are
consequences:

* boundedness of the lift (`norm_le_two_of_gram_le`: `‖x_n‖ ≤ 2` wherever the
  first Gram defect is at most `1/2`);
* any restriction on the filter -- `cofinite`, the printed one, is a special
  case of the arbitrary `l` proved here, which is also the `ω`-version.

`printedUnitaryLifting_sequence` is the sentence, clause by clause and in the
printed order.  Nothing is assumed: no nontriviality, no boundedness, no
separability, no real rank zero, no semiprojectivity.
-/

namespace GroupApproximation
namespace FiniteBlockCorona

open Filter
open PolarLiftingGeneralCStar

noncomputable section

/-- **The printed lifting sentence, over arbitrary unital blocks, with no
nondegeneracy hypothesis.**

The two hypotheses are the printed `‖x_n^*x_n - 1‖ → 0` and
`‖x_nx_n^* - 1‖ → 0`, which in the quotient `∏_nA_n/⨁_nA_n` are exactly
`u^*u = 1` and `uu^* = 1` for the class `u` of `(x_n)`.  The three conclusions
are the printed ones, in the printed order:

* `x_n` is invertible for all large `n`;
* the polar correction `u_n = x_n(x_n^*x_n)^{-1/2}` is unitary there;
* `‖u_n - x_n‖ → 0`.

No real rank zero, no semiprojectivity, no finite dimensionality, no
boundedness of the lift, and -- unlike
`PolarLiftingGeneralCStar.printedUnitaryLifting` -- no nontriviality of the
blocks: the product algebra never appears, so mathlib's `NormOneClass`
requirement on `lp A ∞` never arises. -/
theorem printedUnitaryLifting_sequence {A : ℕ → Type*} [∀ n, CStarAlgebra (A n)]
    (l : Filter ℕ) (x : ∀ n, A n)
    (h1 : Tendsto (fun n ↦ ‖star (x n) * x n - 1‖) l (nhds 0))
    (h2 : Tendsto (fun n ↦ ‖x n * star (x n) - 1‖) l (nhds 0)) :
    (∀ᶠ n in l, IsUnit (x n)) ∧
      (∀ᶠ n in l, polarUnitary (x n) ∈ unitary (A n)) ∧
      Tendsto (fun n ↦ ‖polarUnitary (x n) - x n‖) l (nhds 0) := by
  have g1 : ∀ᶠ n in l, ‖star (x n) * x n - 1‖ ≤ 1 / 2 := by
    have hd := (Metric.tendsto_nhds.mp h1) ((1 : ℝ) / 2) (by norm_num)
    filter_upwards [hd] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  have g2 : ∀ᶠ n in l, ‖x n * star (x n) - 1‖ ≤ 1 / 2 := by
    have hd := (Metric.tendsto_nhds.mp h2) ((1 : ℝ) / 2) (by norm_num)
    filter_upwards [hd] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [g1, g2] with n hn1 hn2
    exact isUnit_of_norm_gram_lt (by linarith) (by linarith)
  · filter_upwards [g1, g2] with n hn1 hn2
    exact polarUnitary_mem_unitary hn1 hn2
  · refine squeeze_zero' (g := fun n ↦ 4 * ‖star (x n) * x n - 1‖)
      (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ ?_
    · filter_upwards [g1] with n hn
      have hxn : ‖x n‖ ≤ 2 := norm_le_two_of_gram_le hn
      have hd : ‖polarUnitary (x n) - x n‖
          ≤ 2 * ‖x n‖ * ‖star (x n) * x n - 1‖ := norm_polarUnitary_sub_le hn
      have hprod : 0 ≤ (2 - ‖x n‖) * ‖star (x n) * x n - 1‖ :=
        mul_nonneg (by linarith) (norm_nonneg _)
      show ‖polarUnitary (x n) - x n‖ ≤ 4 * ‖star (x n) * x n - 1‖
      nlinarith [hd]
    · simpa using h1.const_mul (4 : ℝ)

/-- The printed statement at the printed filter.  `cofinite` on `ℕ` is the
filter whose null sequences are the `c₀`-sum `⨁_nA_n`, so this is the sentence
as it stands in the manuscript. -/
theorem printedUnitaryLifting_sequence_cofinite {A : ℕ → Type*}
    [∀ n, CStarAlgebra (A n)] (x : ∀ n, A n)
    (h1 : Tendsto (fun n ↦ ‖star (x n) * x n - 1‖) cofinite (nhds 0))
    (h2 : Tendsto (fun n ↦ ‖x n * star (x n) - 1‖) cofinite (nhds 0)) :
    (∀ᶠ n in cofinite, IsUnit (x n)) ∧
      (∀ᶠ n in cofinite, polarUnitary (x n) ∈ unitary (A n)) ∧
      Tendsto (fun n ↦ ‖polarUnitary (x n) - x n‖) cofinite (nhds 0) :=
  printedUnitaryLifting_sequence cofinite x h1 h2

end

end FiniteBlockCorona
end GroupApproximation
