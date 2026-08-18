import GroupApproximation.Analysis.FilterMatrixCStarCorona
import GroupApproximation.Sofic.FiniteNormalAverageCorner

/-!
# Lifting a projection of the matrix corona to coordinate projections

`\label{thm:abstract-nk}`, in the compression paragraph:

> Lift `q` to projections `q_n ∈ M_{d_n}(ℂ)`, nonzero along `ω` and with
> `‖[q_n, V_{g,n}]‖ →_ω 0` for every `g ∈ H̄`.

That sentence has three clauses and this file proves all three, at an arbitrary
filter and for an arbitrary family of finite index types.

## Why the lift exists

A projection of the corona is the class of *some* bounded sequence, and that
sequence can be taken self-adjoint by averaging with its adjoint.  Its
coordinate idempotence defects `a_n a_n − a_n` then vanish along the filter,
because their class is `p² − p = 0`.  Rounding each `a_n` at `1/2` in its own
eigenbasis produces a genuine orthogonal projection `q_n`, and the rounding
error is controlled by *twice* the idempotence defect, dimension-free:

* `abs_indicator_sub_le_two_abs_sq_sub_self` is the scalar inequality
  `|χ_{>1/2}(λ) − λ| ≤ 2|λ² − λ|`, valid for **every** real `λ`.  The
  development already had it under the side condition `|λ| ≤ 1`, which is what
  the finite-subgroup average of `Sofic/FiniteNormalAverageCorner.lean`
  satisfies; a representative of an arbitrary projection satisfies no such
  bound, and the inequality does not need one.
* `norm_spectralAbove_sub_le` reads that off the eigenvalues of an arbitrary
  Hermitian matrix, by conjugating into the eigenbasis where the difference is
  diagonal.

The three clauses are then `exists_projection_lift`,
`mem_of_mk_ne_zero` and `isNullMatrixSequence_commutator_of_commute`.

## What the last clause needs, and what it does not

Asymptotic commutation of representatives is *exactly* exact commutation of
classes, so the printed `‖[q_n, V_{g,n}]‖ →_ω 0` needs the commutation
`π(g) q = q π(g)` **in the corona** and nothing else -- no estimate and no
choice of representative, because the difference of the two products is a single
class and it is zero.  This is why the conjugation identity of
`Analysis/KazhdanProjectionAbsorption.lean` is proved algebraically there rather
than only through the fixed spaces on the Hilbert-space ultraproduct: the
algebraic form is the one this clause consumes.
-/

namespace GroupApproximation
namespace CoronaProjectionLifting

open Filter Matrix
open KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator ENNReal

noncomputable section

universe u

/-! ## Scalar rounding, with no bound on the eigenvalue -/

/-- **Rounding at `1/2` is controlled by twice the idempotence defect**, for
every real number.  No hypothesis: for `λ > 1/2` the factor `2λ` already exceeds
`1`, and for `λ ≤ 1/2` the factor `2(1 − λ)` does. -/
theorem abs_indicator_sub_le_two_abs_sq_sub_self (lambda : ℝ) :
    |(if (1 / 2 : ℝ) < lambda then 1 else 0) - lambda|
      ≤ 2 * |lambda ^ 2 - lambda| := by
  have hfac : |lambda ^ 2 - lambda| = |lambda| * |lambda - 1| := by
    rw [show lambda ^ 2 - lambda = lambda * (lambda - 1) by ring, abs_mul]
  by_cases hhalf : (1 / 2 : ℝ) < lambda
  · rw [if_pos hhalf, hfac, abs_sub_comm]
    have habs : |lambda| = lambda := abs_of_pos (by linarith)
    rw [habs]
    nlinarith [mul_nonneg (abs_nonneg (lambda - 1))
      (show (0 : ℝ) ≤ 2 * lambda - 1 by linarith)]
  · have hle : lambda ≤ 1 / 2 := le_of_not_gt hhalf
    rw [if_neg hhalf, zero_sub, abs_neg, hfac]
    have habs : |lambda - 1| = 1 - lambda := by
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [habs]
    nlinarith [mul_nonneg (abs_nonneg lambda)
      (show (0 : ℝ) ≤ 1 - 2 * lambda by linarith)]

/-! ## Rounding an arbitrary Hermitian matrix -/

/-- **Dimension-free spectral rounding.**  The distance from a Hermitian matrix
to its spectral cutoff at `1/2` is at most twice its idempotence defect.

The estimate is the scalar one read in the eigenbasis: conjugation by the
eigenvector unitary is isometric, and the difference is diagonal there. -/
theorem norm_spectralAbove_sub_le {Z : Type*} [Fintype Z] [DecidableEq Z]
    (H : Matrix Z Z ℂ) (hH : H.IsHermitian) :
    ‖spectralAbove H hH (1 / 2) - H‖ ≤ 2 * ‖H * H - H‖ := by
  classical
  let V : Matrix Z Z ℂ := hH.eigenvectorUnitary
  let P : Matrix Z Z ℂ :=
    Matrix.diagonal (fun i ↦ if (1 / 2 : ℝ) < hH.eigenvalues i then 1 else 0)
  let L : Matrix Z Z ℂ := Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ))
  let Rm : Matrix Z Z ℂ :=
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
  have hcore : P - L = Rm := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [P, L, Rm]
    · simp [P, L, Rm, hij]
  have hrewrite : spectralAbove H hH (1 / 2) - H = V * Rm * Vᴴ := by
    rw [hPdef]
    conv_lhs => rw [hHdiag]
    calc
      V * P * Vᴴ - V * L * Vᴴ = V * (P - L) * Vᴴ := by noncomm_ring
      _ = V * Rm * Vᴴ := by rw [hcore]
  have hVstar : Vᴴ ∈ Matrix.unitaryGroup Z ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  rw [hrewrite, CStarRing.norm_mul_mem_unitary _ hVstar,
    CStarRing.norm_mem_unitary_mul _ hH.eigenvectorUnitary.2]
  show ‖Matrix.diagonal (fun i ↦
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
  exact (abs_indicator_sub_le_two_abs_sq_sub_self _).trans
    (mul_le_mul_of_nonneg_left
      (FiniteNormalAverageCorner.abs_hermitianEigenvalue_sq_sub_self_le H hH i)
      (by norm_num))

/-- An orthogonal projection matrix has norm at most one.  This is what makes a
family of them a bounded sequence. -/
theorem norm_le_one_of_isOrthogonalProjectionMatrix {Z : Type*} [Fintype Z]
    [DecidableEq Z] {P : Matrix Z Z ℂ} (hP : IsOrthogonalProjectionMatrix P) :
    ‖P‖ ≤ 1 := by
  have hstar : star P * P = P := by
    rw [Matrix.star_eq_conjTranspose, hP.1, hP.2]
  have h := CStarRing.norm_star_mul_self (x := P)
  rw [hstar] at h
  nlinarith [norm_nonneg P]

/-! ## The lift -/

section Corona

variable (X : ℕ → Type u) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
  [∀ n, Nonempty (X n)] (l : Filter ℕ)

/-- Every class has a representative.  Stated here rather than at the opaque
boundary because it is the one fact a lifting argument cannot do without. -/
theorem filterMatrixCStarCoronaMk_surjective :
    Function.Surjective (filterMatrixCStarCoronaMk X l) := by
  unfold filterMatrixCStarCoronaMk FilterMatrixCStarCorona
  exact Ideal.Quotient.mk_surjective

/-- **Exact commutation in the corona is asymptotic commutation of
representatives.**

The printed `‖[q_n, V_{g,n}]‖ →_ω 0`.  There is no estimate here and no choice
of representative: the commutator of two representatives is a single class, and
that class is zero exactly when the two classes commute. -/
theorem isNullMatrixSequence_commutator_of_commute
    {a b : BoundedMatrixSequence X}
    (h : filterMatrixCStarCoronaMk X l a * filterMatrixCStarCoronaMk X l b
      = filterMatrixCStarCoronaMk X l b * filterMatrixCStarCoronaMk X l a) :
    IsNullMatrixSequence X l (a * b - b * a) := by
  rw [← filterMatrixCStarCoronaMk_eq_zero_iff, map_sub, map_mul, map_mul, h,
    sub_self]

/-- **The nonvanishing clause.**  If the class is nonzero then the coordinates
are nonzero on a set of the ultrafilter -- the printed "nonzero along `ω`". -/
theorem mem_of_mk_ne_zero (ω : Ultrafilter ℕ) {q : BoundedMatrixSequence X}
    (h : filterMatrixCStarCoronaMk X (ω : Filter ℕ) q ≠ 0) :
    {n | (q : ∀ n, Matrix (X n) (X n) ℂ) n ≠ 0} ∈ (ω : Filter ℕ) := by
  by_contra hmem
  refine h ?_
  rw [filterMatrixCStarCoronaMk_eq_zero_iff]
  have hcompl : {n | (q : ∀ n, Matrix (X n) (X n) ℂ) n ≠ 0}ᶜ ∈ (ω : Filter ℕ) :=
    Ultrafilter.compl_mem_iff_notMem.2 hmem
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [hcompl] with n hn
  have hzero : (q : ∀ n, Matrix (X n) (X n) ℂ) n = 0 := not_not.1 hn
  rw [hzero, norm_zero]

/-- **The lift itself.**

> Lift `q` to projections `q_n ∈ M_{d_n}(ℂ)`

A self-adjoint idempotent of the corona is the class of a sequence of genuine
orthogonal projection matrices.  The witness is the spectral cutoff of a
self-adjoint representative at `1/2`, taken coordinatewise. -/
theorem exists_projection_lift (p : FilterMatrixCStarCorona X l)
    (hsa : IsSelfAdjoint p) (hidem : IsIdempotentElem p) :
    ∃ q : BoundedMatrixSequence X,
      (∀ n, IsOrthogonalProjectionMatrix
          ((q : ∀ n, Matrix (X n) (X n) ℂ) n))
        ∧ filterMatrixCStarCoronaMk X l q = p := by
  classical
  obtain ⟨a₀, ha₀⟩ := filterMatrixCStarCoronaMk_surjective X l p
  set a : BoundedMatrixSequence X := (2 : ℂ)⁻¹ • (a₀ + star a₀) with hadef
  have hstar2 : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    rw [star_inv₀]
    simp
  have hastar : star a = a := by
    rw [hadef, star_smul, star_add, star_star, hstar2, add_comm]
  have hmk : filterMatrixCStarCoronaMk X l a = p := by
    have hq : filterMatrixCStarCoronaQuotient X l a
        = (2 : ℂ)⁻¹ • (p + star p) := by
      rw [hadef, map_smul, map_add, map_star]
      exact congrArg (fun z ↦ (2 : ℂ)⁻¹ • (z + star z)) ha₀
    have hqm : filterMatrixCStarCoronaQuotient X l a
        = filterMatrixCStarCoronaMk X l a := rfl
    rw [hqm] at hq
    rw [hq, hsa.star_eq, ← two_smul ℂ p]
    exact inv_smul_smul₀ (by norm_num : (2 : ℂ) ≠ 0) p
  have hherm : ∀ n, ((a : ∀ n, Matrix (X n) (X n) ℂ) n).IsHermitian := by
    intro n
    exact congrArg (fun b : BoundedMatrixSequence X ↦
      (b : ∀ n, Matrix (X n) (X n) ℂ) n) hastar
  set qf : ∀ n, Matrix (X n) (X n) ℂ := fun n ↦
    spectralAbove ((a : ∀ n, Matrix (X n) (X n) ℂ) n) (hherm n) (1 / 2)
    with hqf
  have hproj : ∀ n, IsOrthogonalProjectionMatrix (qf n) := fun n ↦
    spectralAbove_isOrthogonalProjection _ (hherm n) (1 / 2)
  have hmem : Memℓp qf ∞ :=
    memℓp_infty ⟨1, by
      rintro _ ⟨n, rfl⟩
      exact norm_le_one_of_isOrthogonalProjectionMatrix (hproj n)⟩
  refine ⟨⟨qf, hmem⟩, hproj, ?_⟩
  have hnullb : IsNullMatrixSequence X l (a * a - a) := by
    rw [← filterMatrixCStarCoronaMk_eq_zero_iff, map_sub, map_mul, hmk, hidem,
      sub_self]
  have hnull : IsNullMatrixSequence X l
      ((⟨qf, hmem⟩ : BoundedMatrixSequence X) - a) := by
    have hbound : ∀ n, ‖(((⟨qf, hmem⟩ : BoundedMatrixSequence X) - a :
          BoundedMatrixSequence X) : ∀ n, Matrix (X n) (X n) ℂ) n‖
        ≤ 2 * ‖((a * a - a : BoundedMatrixSequence X) :
            ∀ n, Matrix (X n) (X n) ℂ) n‖ := by
      intro n
      show ‖qf n - (a : ∀ n, Matrix (X n) (X n) ℂ) n‖
        ≤ 2 * ‖((a * a - a : BoundedMatrixSequence X) :
            ∀ n, Matrix (X n) (X n) ℂ) n‖
      exact norm_spectralAbove_sub_le _ (hherm n)
    have h0 : Filter.Tendsto (fun n ↦ ‖((a * a - a : BoundedMatrixSequence X) :
        ∀ n, Matrix (X n) (X n) ℂ) n‖) l (nhds 0) := hnullb
    have hlim : Filter.Tendsto
        (fun n ↦ 2 * ‖((a * a - a : BoundedMatrixSequence X) :
          ∀ n, Matrix (X n) (X n) ℂ) n‖) l (nhds 0) := by
      simpa using h0.const_mul (2 : ℝ)
    exact squeeze_zero (fun n ↦ norm_nonneg _) hbound hlim
  rw [← hmk, filterMatrixCStarCoronaMk_eq_iff]
  exact hnull

end Corona

end

end CoronaProjectionLifting
end GroupApproximation
