import GroupApproximation.Analysis.CollapseDiscardCoordinates
import GroupApproximation.Analysis.CollapseLambdaCocycle

/-!
# The printed nonvanishing of `β`, at the join

Proof-ledger row `CO.21`, the paragraph

> Suppose `β(a) = 0` for every `a ∈ S`.  Put `r₁ = 1` and
> `r_i = ∏_{j<i}(1 − q_{a_j})` for `i ≥ 2`.  The products `e_i = r_i q_{a_i}`
> are projections with `e_i = r_i − r_{i+1}`, so they are pairwise orthogonal
> and `∑_i e_i = 1 − r_{m+1} = q`.  Each `d_{a_i}` commutes with `r_i`, so
> `e_i = (d_{a_i} r_i)\,d_{a_i}` and `Λ(e_i) = 0`, whence `Λ(q) = 0` against
> `‖Λ(q)‖ = 1`.  So `β` is not identically zero.

The two halves of that paragraph are already proved separately —
`CollapseLambdaCocycle.lambda_sum_eq_zero` is the telescoping read through
`Λ`, and `RankNormalizedLambda.lambda_mul_mul_eq_zero` is the kernel
stability that makes `Λ(e_i) = 0` follow from `Λ(d_{a_i}) = 0`.  What is
assembled here is the paragraph itself: from the printed shape
`e_i = (d_{a_i} r_i)\,d_{a_i}` and the join `∑_i e_i = q`, the conclusion that
some `Λ(d_{a_i})` is nonzero.

That conclusion is the hypothesis `hne` of
`CollapseCompressionBundle.collapse_contradiction_printed`, so this is the
last of that theorem's hypotheses to be discharged from printed data rather
than assumed.

## Why the rank hypothesis is the eventual one

`‖Λ(q)‖ = 1` is what the contradiction runs against, and it needs the rank of
the projection lift to be positive.  `Analysis/CollapseDiscardCoordinates`
showed that positivity is needed only on a set of `ω` — the printed
"discard the remaining coordinates" being a choice of ultrafilter rather than
a reindexing — so `norm_lambda_projection_eventually` is stated there, and it
is what this file consumes.  Nothing here asks for positivity at every
coordinate.
-/

namespace GroupApproximation
namespace CollapseJoinNonvanishing

open Filter Matrix Topology
open UltraproductModelConstruction
open RankNormalizedHilbertization RankNormalizedLambda KOmegaHilbert
open KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

noncomputable section

variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]

/-! ## `‖Λ(q)‖ = 1` at the eventual rank hypothesis -/

/-- **`‖Λ(q)‖ = 1`, needing the rank positive only `ω`-eventually.**  The
statement of `RankNormalizedLambda.norm_lambda_projection` with the printed
discarding step already discharged. -/
theorem norm_lambda_projection_eventually
    (Q : BoundedMatrixSequence (fun n ↦ Y n)) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite)
    (hproj : ∀ n, IsOrthogonalProjectionMatrix (Q n))
    (hrk : ∀ᶠ n in (ω : Filter ℕ), 0 < (Q n).rank)
    (z : rankIdeal Y (coord Y Q))
    (hz : (z : NormMatrixCStarCorona (fun n ↦ Y n)) = coronaLinear Y Q) :
    ‖lambda Y (coord Y Q) ω hω z‖ = 1 := by
  have hQ : Q ∈ rankControlled Y (coord Y Q) := by
    refine ⟨1, fun n ↦ ?_⟩
    show (Q n).rank ≤ 1 * (Q n).rank
    rw [one_mul]
  rw [lambda_apply Y (coord Y Q) ω hω z ⟨Q, hQ⟩ hz.symm, lambdaBounded_apply]
  exact CollapseDiscardCoordinates.norm_mkK_projection_eventually Y ω
    (coord Y Q) hproj hrk _ rfl

/-! ## The join vanishes if every displacement does -/

/-- **The printed `Λ(e_i) = 0`, then `Λ(q) = 0`.**  The shape
`e_i = (d_{a_i} r_i)\,d_{a_i}` is a left multiple of `d_{a_i}`, so the kernel
stability of `Λ` kills each `e_i`, and the join is their sum. -/
theorem lambda_join_eq_zero_of_generators (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (m : ℕ)
    (e dEl : ℕ → rankIdeal Y P)
    (A : ℕ → NormMatrixCStarCorona (fun n ↦ Y n))
    (he : ∀ i, (e i : NormMatrixCStarCorona (fun n ↦ Y n))
      = A i * (dEl i : NormMatrixCStarCorona (fun n ↦ Y n)) * 1)
    (hzero : ∀ i, lambda Y P ω hω (dEl i) = 0) (qz : rankIdeal Y P)
    (hq : (qz : NormMatrixCStarCorona (fun n ↦ Y n))
      = ∑ i ∈ Finset.range m,
          (e i : NormMatrixCStarCorona (fun n ↦ Y n))) :
    lambda Y P ω hω qz = 0 := by
  refine CollapseLambdaCocycle.lambda_sum_eq_zero Y P ω hω m e qz hq ?_
  intro i
  exact lambda_mul_mul_eq_zero Y P ω hω (dEl i) (hzero i) (A i) 1 (e i) (he i)

/-! ## The printed *"so `β` is not identically zero"* -/

/-- **The nonvanishing of `β`, from the printed join.**

If the join of the displacement supports is the class of a projection lift
whose rank is `ω`-eventually positive, and each summand of the join is a left
multiple of a displacement, then some displacement has nonzero `Λ`.  This is
the hypothesis `hne` of
`CollapseCompressionBundle.collapse_contradiction_printed`, discharged from
the printed data rather than assumed. -/
theorem exists_lambda_ne_zero_of_join
    (Q : BoundedMatrixSequence (fun n ↦ Y n)) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite)
    (hproj : ∀ n, IsOrthogonalProjectionMatrix (Q n))
    (hrk : ∀ᶠ n in (ω : Filter ℕ), 0 < (Q n).rank) (m : ℕ)
    (e dEl : ℕ → rankIdeal Y (coord Y Q))
    (A : ℕ → NormMatrixCStarCorona (fun n ↦ Y n))
    (he : ∀ i, (e i : NormMatrixCStarCorona (fun n ↦ Y n))
      = A i * (dEl i : NormMatrixCStarCorona (fun n ↦ Y n)) * 1)
    (qz : rankIdeal Y (coord Y Q))
    (hqz : (qz : NormMatrixCStarCorona (fun n ↦ Y n)) = coronaLinear Y Q)
    (hq : (qz : NormMatrixCStarCorona (fun n ↦ Y n))
      = ∑ i ∈ Finset.range m,
          (e i : NormMatrixCStarCorona (fun n ↦ Y n))) :
    ∃ i, lambda Y (coord Y Q) ω hω (dEl i) ≠ 0 := by
  by_contra hcon
  have hall : ∀ i, lambda Y (coord Y Q) ω hω (dEl i) = 0 := by
    intro i
    by_contra hi
    exact hcon ⟨i, hi⟩
  have hzero := lambda_join_eq_zero_of_generators Y (coord Y Q) ω hω m e dEl A
    he hall qz hq
  have hnorm := norm_lambda_projection_eventually Y Q ω hω hproj hrk qz hqz
  rw [hzero, norm_zero] at hnorm
  exact zero_ne_one hnorm

end

end CollapseJoinNonvanishing
end GroupApproximation
