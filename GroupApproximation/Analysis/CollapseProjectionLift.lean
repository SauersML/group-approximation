import GroupApproximation.Analysis.NormMatrixCorona
import GroupApproximation.Sofic.FiniteNormalAverageCorner
import GroupApproximation.Sofic.KazhdanCornerCompression

/-!
# The projection lift `Q_n = χ_{[1/2,∞)}(x_n)` of a corona projection

Proof-ledger row `CO.20`, the first clause of the paragraph *The `q`-normalized
Hilbert space* in the proof of `thm:projection-collapse` in
`non_mf_groups_exist.tex` (navigate by the label; that file is under
concurrent edit).

The printed sentence is

> Take a self-adjoint bounded lift `(x_n)` of `q`.  Then `‖x_n² − x_n‖ → 0`,
> so the spectrum of `x_n` clusters at `{0,1}` and continuous functional
> calculus makes `Q_n = χ_{[1/2,∞)}(x_n)` a projection with `‖Q_n − x_n‖ → 0`;
> the sequence `(Q_n)` again lifts `q`.

`Analysis/RankNormalizedLambda` builds `Λ` from such a lift, but takes the
lift as a hypothesis: every statement there quantifies over a bounded sequence
whose coordinates are orthogonal projections.  This file produces one from `q`.

## What each step is

* `abs_indicator_sub_le` is the scalar rounding estimate
  `|1_{λ>1/2} − λ| ≤ 2|λ² − λ|`, **with no bound on `λ`**.  The corpus already
  had it under the hypothesis `|λ| ≤ 1`
  (`FiniteNormalAverageCorner.abs_indicator_sub_le_two_abs_sq_sub_self`); the
  hypothesis is not needed, and dropping it is what lets the estimate apply to
  an arbitrary bounded lift rather than to a contraction.  Above `1/2` the
  factor `2|λ|` already exceeds `1`, and below it `2|λ − 1|` does.
* `norm_spectralAbove_sub_le` is the printed functional calculus in finite
  dimensions: `‖χ_{[1/2,∞)}(H) − H‖ ≤ 2‖H² − H‖` for Hermitian `H`.  In the
  eigenbasis both sides are diagonal, so the matrix estimate is the scalar one
  applied to each eigenvalue, with
  `FiniteNormalAverageCorner.abs_hermitianEigenvalue_sq_sub_self_le` comparing
  the eigenvalue defect to the operator-norm defect.
* `exists_hermitian_lift` is the printed *"take a self-adjoint bounded lift"*:
  symmetrize any bounded lift, which does not move the class because `q` is
  self-adjoint.
* `exists_projection_lift` assembles the three: `‖x_n² − x_n‖ → 0` because the
  class of `x² − x` is `q² − q = 0`, the rounding is a projection of norm at
  most one, hence a bounded sequence, and the estimate makes the difference
  null, so the two classes agree.

## What is still not here

The printed sentence continues *"since `q ≠ 0`, `Q_n ≠ 0` for infinitely many
`n`; discard the remaining coordinates, relabel by `ℕ`, and put
`k_n = rank Q_n ≥ 1`"*.  That relabelling is not performed, and
`∀ n, 0 < rank Q_n` remains a hypothesis of `RankNormalizedLambda`'s
`‖Λ(q)‖ = 1`.  Discarding coordinates changes the index set, hence the
ultrafilter; the honest alternative is to weaken the hypothesis to
`∀ᶠ n in ω, 0 < rank Q_n` and choose `ω` containing the set where `Q_n ≠ 0`,
and neither is done here.
-/

namespace GroupApproximation
namespace CollapseProjectionLift

open Filter Matrix Topology
open KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator ENNReal

noncomputable section

/-! ## Scalar rounding at `1/2` -/

/-- **Scalar rounding at `1/2`, unconditionally.**  The distance from `λ` to
its rounding is at most twice its idempotence defect, with no bound on `λ`:
above `1/2` the factor `2|λ|` already exceeds `1`, and below `1/2` the factor
`2|λ − 1|` does.  The corpus's existing form of this estimate carries the
hypothesis `|λ| ≤ 1`, which the two cases show is unnecessary. -/
theorem abs_indicator_sub_le (l : ℝ) :
    |(if (1 / 2 : ℝ) < l then 1 else 0) - l| ≤ 2 * |l ^ 2 - l| := by
  have hfac : |l ^ 2 - l| = |l| * |l - 1| := by
    rw [← abs_mul]
    congr 1
    ring
  by_cases hhalf : (1 / 2 : ℝ) < l
  · rw [if_pos hhalf, hfac, abs_sub_comm]
    have hl : (1 : ℝ) ≤ 2 * |l| := by
      rw [abs_of_pos (by linarith : (0 : ℝ) < l)]
      linarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * |l| - 1)
      (abs_nonneg (l - 1))]
  · have hle : l ≤ 1 / 2 := le_of_not_gt hhalf
    rw [if_neg hhalf, hfac, zero_sub, abs_neg]
    have hl1 : (1 : ℝ) ≤ 2 * |l - 1| := by
      rw [abs_of_nonpos (by linarith : l - 1 ≤ 0)]
      linarith
    nlinarith [mul_nonneg (abs_nonneg l)
      (by linarith : (0 : ℝ) ≤ 2 * |l - 1| - 1)]

/-! ## The printed functional calculus, in finite dimensions -/

/-- **The printed `‖Q_n − x_n‖ ≤ 2‖x_n² − x_n‖`.**  The spectral cutoff of a
Hermitian matrix at `1/2` is within twice the idempotence defect of the matrix.

In the eigenbasis both the cutoff and the matrix are diagonal, so their
difference is diagonal and its operator norm is the supremum of the entrywise
rounding errors; each of those is the scalar estimate at the corresponding
eigenvalue, whose own idempotence defect is at most the operator-norm defect of
the matrix. -/
theorem norm_spectralAbove_sub_le {Y : FiniteModel}
    (H : Matrix Y Y ℂ) (hH : H.IsHermitian) :
    ‖spectralAbove H hH (1 / 2) - H‖ ≤ 2 * ‖H * H - H‖ := by
  let V : Matrix Y Y ℂ := hH.eigenvectorUnitary
  let P : Matrix Y Y ℂ :=
    Matrix.diagonal (fun i ↦ if (1 / 2 : ℝ) < hH.eigenvalues i then 1 else 0)
  let L : Matrix Y Y ℂ := Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ))
  let R : Matrix Y Y ℂ :=
    Matrix.diagonal (fun i ↦
      (if (1 / 2 : ℝ) < hH.eigenvalues i then (1 : ℂ) else 0) -
        (hH.eigenvalues i : ℂ))
  have hHdiag : H = V * L * Vᴴ := by
    calc
      H = Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) :=
        hH.spectral_theorem
      _ = V * L * Vᴴ := by rfl
  have hPdef : spectralAbove H hH (1 / 2) = V * P * Vᴴ := rfl
  have hcore : P - L = R := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [P, L, R]
    · simp [P, L, R, hij]
  have hrewrite : spectralAbove H hH (1 / 2) - H = V * R * Vᴴ := by
    rw [hPdef, hHdiag]
    calc
      V * P * Vᴴ - V * L * Vᴴ = V * (P - L) * Vᴴ := by noncomm_ring
      _ = V * R * Vᴴ := by rw [hcore]
  have hVstar : Vᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  rw [hrewrite, CStarRing.norm_mul_mem_unitary _ hVstar,
    CStarRing.norm_mem_unitary_mul _ hH.eigenvectorUnitary.2]
  change ‖Matrix.diagonal (fun i ↦
    (if (1 / 2 : ℝ) < hH.eigenvalues i then (1 : ℂ) else 0) -
      (hH.eigenvalues i : ℂ))‖ ≤ 2 * ‖H * H - H‖
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num)
    (norm_nonneg _))).2 fun i ↦ ?_
  have hcast :
      (if (1 / 2 : ℝ) < hH.eigenvalues i then (1 : ℂ) else 0) -
          (hH.eigenvalues i : ℂ) =
        (((if (1 / 2 : ℝ) < hH.eigenvalues i then (1 : ℝ) else 0) -
          hH.eigenvalues i : ℝ) : ℂ) := by
    split <;> norm_num
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  exact (abs_indicator_sub_le _).trans
    (mul_le_mul_of_nonneg_left
      (FiniteNormalAverageCorner.abs_hermitianEigenvalue_sq_sub_self_le H hH i)
      (by norm_num))

/-! ## Lifting a corona projection -/

section Corona

variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]

/-- **The printed *"take a self-adjoint bounded lift `(x_n)` of `q`"*.**
Symmetrizing an arbitrary bounded lift does not move its class, because `q` is
self-adjoint. -/
theorem exists_hermitian_lift (q : NormMatrixCStarCorona (fun n ↦ Y n))
    (hsa : star q = q) :
    ∃ x : BoundedMatrixSequence (fun n ↦ Y n),
      (∀ n, (x n : Matrix (Y n) (Y n) ℂ).IsHermitian) ∧
        normMatrixCStarCoronaMk (fun n ↦ Y n) x = q := by
  obtain ⟨a, ha⟩ := normMatrixCStarCoronaMk_surjective (fun m ↦ Y m) q
  have hstar : star ((2 : ℂ)⁻¹ • (a + star a)) = (2 : ℂ)⁻¹ • (a + star a) := by
    rw [star_smul, star_add, star_star, star_inv₀, star_ofNat, add_comm]
  refine ⟨(2 : ℂ)⁻¹ • (a + star a), fun n ↦ ?_, ?_⟩
  · show ((((2 : ℂ)⁻¹ • (a + star a)) n : Matrix (Y n) (Y n) ℂ))ᴴ
      = (((2 : ℂ)⁻¹ • (a + star a)) n : Matrix (Y n) (Y n) ℂ)
    rw [← Matrix.star_eq_conjTranspose, ← lp.star_apply, hstar]
  · -- The class is computed with ring operations only.  Scalar multiplication
    -- by `ℂ` on the corona reaches `Module ℂ` through both `Algebra.toModule`
    -- and `NormedSpace.toModule`, and the opaque interface does not reduce the
    -- two to a common instance, so the symmetrization is pushed through the
    -- *difference* `x - a`, which is a scalar multiple of the null family
    -- `star a - a` and needs no scalar action downstream.
    have hanti : IsNullMatrixSequence (fun m ↦ Y m) cofinite
        ((star a : BoundedMatrixSequence (fun m ↦ Y m)) - a) := by
      refine (normMatrixCStarCoronaMk_eq_zero_iff (fun m ↦ Y m) _).mp ?_
      rw [map_sub, ← normMatrixCStarCorona_star_mk, ha, hsa, sub_self]
    have hb : ∀ n,
        ‖((((2 : ℂ)⁻¹ • (a + star a)) - a :
            BoundedMatrixSequence (fun m ↦ Y m)) n : Matrix (Y n) (Y n) ℂ)‖
          ≤ ‖(((star a : BoundedMatrixSequence (fun m ↦ Y m)) - a) n
            : Matrix (Y n) (Y n) ℂ)‖ := by
      intro n
      have hAid : (2 : ℂ)⁻¹ • ((a n : Matrix (Y n) (Y n) ℂ) + (a n)ᴴ)
            - (a n : Matrix (Y n) (Y n) ℂ)
          = (2 : ℂ)⁻¹ • (((a n : Matrix (Y n) (Y n) ℂ))ᴴ - a n) := by
        ext i j
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
          Matrix.conjTranspose_apply, smul_eq_mul]
        ring
      have h2 : ‖((2 : ℂ)⁻¹)‖ = (2 : ℝ)⁻¹ := by
        rw [norm_inv]
        norm_num
      show ‖(2 : ℂ)⁻¹ • ((a n : Matrix (Y n) (Y n) ℂ) + (a n)ᴴ)
          - (a n : Matrix (Y n) (Y n) ℂ)‖
        ≤ ‖((a n : Matrix (Y n) (Y n) ℂ))ᴴ - a n‖
      rw [hAid, norm_smul, h2]
      linarith [norm_nonneg (((a n : Matrix (Y n) (Y n) ℂ))ᴴ - a n)]
    have hdiff : IsNullMatrixSequence (fun m ↦ Y m) cofinite
        ((((2 : ℂ)⁻¹ • (a + star a)) - a :
          BoundedMatrixSequence (fun m ↦ Y m))) :=
      squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _)
        (Eventually.of_forall hb) hanti
    have h0 := (normMatrixCStarCoronaMk_eq_zero_iff (fun m ↦ Y m) _).mpr hdiff
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, ha]

/-- **The printed *"`‖Q_n − x_n‖ → 0`, so `(Q_n)` again lifts `q`"*.**  Two
bounded sequences whose coordinate difference is dominated by the idempotence
defect of the second have the same corona class, once that defect vanishes.

Stated separately, and for arbitrary sequences, so that the elaborator meets
the concrete spectral cutoff only through this hypothesis. -/
theorem mk_eq_of_norm_sub_le (x Q : BoundedMatrixSequence (fun n ↦ Y n))
    (hbound : ∀ n, ‖(Q n : Matrix (Y n) (Y n) ℂ) - x n‖
      ≤ 2 * ‖(x n : Matrix (Y n) (Y n) ℂ) * x n - x n‖)
    (hdefect : Tendsto (fun n ↦ ‖(x n : Matrix (Y n) (Y n) ℂ) * x n - x n‖)
      cofinite (nhds 0)) :
    normMatrixCStarCoronaMk (fun n ↦ Y n) Q
      = normMatrixCStarCoronaMk (fun n ↦ Y n) x := by
  have hg : Tendsto (fun n ↦ 2 * ‖(x n : Matrix (Y n) (Y n) ℂ) * x n - x n‖)
      cofinite (nhds 0) := by
    simpa using hdefect.const_mul (2 : ℝ)
  have hnull : IsNullMatrixSequence (fun n ↦ Y n) cofinite (Q - x) :=
    squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _)
      (Eventually.of_forall fun n ↦ hbound n) hg
  have h0 := (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ Y n) _).mpr hnull
  rw [map_sub, sub_eq_zero] at h0
  exact h0

/-- The coordinatewise spectral cutoff of a Hermitian bounded sequence, as a
bounded sequence: the cutoffs are contractions, so the family is in `ℓ∞`. -/
def roundSeq (x : BoundedMatrixSequence (fun n ↦ Y n))
    (hherm : ∀ n, (x n : Matrix (Y n) (Y n) ℂ).IsHermitian) :
    BoundedMatrixSequence (fun n ↦ Y n) :=
  ⟨fun n ↦ spectralAbove (x n : Matrix (Y n) (Y n) ℂ) (hherm n) (1 / 2),
    memℓp_infty ⟨1, by
      rintro _ ⟨n, rfl⟩
      exact norm_spectralAbove_le_one _ (hherm n) _⟩⟩

omit [∀ n, Nonempty (Y n)] in
theorem isOrthogonalProjectionMatrix_roundSeq
    (x : BoundedMatrixSequence (fun n ↦ Y n))
    (hherm : ∀ n, (x n : Matrix (Y n) (Y n) ℂ).IsHermitian) (n : ℕ) :
    IsOrthogonalProjectionMatrix (roundSeq Y x hherm n) :=
  spectralAbove_isOrthogonalProjection _ (hherm n) _

omit [∀ n, Nonempty (Y n)] in
theorem norm_roundSeq_sub_le (x : BoundedMatrixSequence (fun n ↦ Y n))
    (hherm : ∀ n, (x n : Matrix (Y n) (Y n) ℂ).IsHermitian) (n : ℕ) :
    ‖(roundSeq Y x hherm n : Matrix (Y n) (Y n) ℂ) - x n‖
      ≤ 2 * ‖(x n : Matrix (Y n) (Y n) ℂ) * x n - x n‖ :=
  norm_spectralAbove_sub_le _ (hherm n)

omit [∀ n, Nonempty (Y n)] in
/-- The coordinates of the idempotence defect, spelled so that the
`ℓ∞`-algebra operations are rewritten rather than unfolded. -/
theorem coord_mul_sub (x : BoundedMatrixSequence (fun n ↦ Y n)) (n : ℕ) :
    ((x * x - x : BoundedMatrixSequence (fun n ↦ Y n)) n
        : Matrix (Y n) (Y n) ℂ)
      = (x n : Matrix (Y n) (Y n) ℂ) * x n - x n := by
  simp only [lp.coeFn_sub, lp.infty_coeFn_mul, Pi.sub_apply, Pi.mul_apply]

/-- **The printed `‖x_n² − x_n‖ → 0`.**  A bounded lift of an idempotent of
the corona is asymptotically idempotent. -/
theorem tendsto_idempotence_defect (x : BoundedMatrixSequence (fun n ↦ Y n))
    (q : NormMatrixCStarCorona (fun n ↦ Y n))
    (hx : normMatrixCStarCoronaMk (fun n ↦ Y n) x = q) (hidem : q * q = q) :
    Tendsto (fun n ↦ ‖(x n : Matrix (Y n) (Y n) ℂ) * x n - x n‖)
      cofinite (nhds 0) := by
  have hz : normMatrixCStarCoronaMk (fun n ↦ Y n) (x * x - x) = 0 := by
    rw [map_sub, map_mul, hx, hidem, sub_self]
  have hnull : IsNullMatrixSequence (fun n ↦ Y n) cofinite (x * x - x) :=
    (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ Y n) _).mp hz
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ ?_) hnull
  rw [coord_mul_sub]

/-- **The printed projection lift.**  A self-adjoint idempotent of the corona
is the class of a bounded sequence of orthogonal projection matrices.

This is the first clause of `CO.20`, which `Analysis/RankNormalizedLambda`
carries as a hypothesis: `Λ` is built from a projection lift, and here is one.
The rank positivity `k_n ≥ 1` is *not* produced — see the module docstring. -/
theorem exists_projection_lift (q : NormMatrixCStarCorona (fun n ↦ Y n))
    (hsa : star q = q) (hidem : q * q = q) :
    ∃ Q : BoundedMatrixSequence (fun n ↦ Y n),
      (∀ n, IsOrthogonalProjectionMatrix (Q n)) ∧
        normMatrixCStarCoronaMk (fun n ↦ Y n) Q = q := by
  obtain ⟨x, hherm, hx⟩ := exists_hermitian_lift Y q hsa
  refine ⟨roundSeq Y x hherm, isOrthogonalProjectionMatrix_roundSeq Y x hherm,
    ?_⟩
  rw [mk_eq_of_norm_sub_le Y x (roundSeq Y x hherm)
    (norm_roundSeq_sub_le Y x hherm)
    (tendsto_idempotence_defect Y x q hx hidem)]
  exact hx

end Corona

end

end CollapseProjectionLift
end GroupApproximation
