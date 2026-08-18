import GroupApproximation.Analysis.RankFrobeniusBound
import GroupApproximation.Sofic.ExactInvolutionLifts
import GroupApproximation.Sofic.HyperlinearScalar

/-!
# The spectral cut that approximately unitizes the Hilbert-Schmidt null ideal

The C-star identity for the quotient of a C-star algebra by a closed two-sided
ideal is not formal: it runs through an approximate unit of the ideal.  For the
`‖·‖₂`-null ideal `J₂ω` of `Analysis/TracialMatrixUltraproduct.lean` the
approximate unit is explicit, and this file proves the two clauses that make it
one, for a single matrix.  Everything here is about one finite matrix; nothing
mentions filters, ideals or quotients.

For `j` a matrix and `t > 0`, the witness is the spectral projection of `jᴴ j`
onto its eigenvalues above `t`,

`cut j t = spectralAbove (jᴴ j) t`,

and the two clauses are

* `norm_mul_one_sub_cut_sq_le`: `‖j (1 - cut j t)‖² ≤ t`, so `j` is moved by at
  most `√t`, which is the approximate-unit clause;
* `hsNormSq_cut_le`: `t · ‖cut j t‖₂² ≤ ‖j‖₂²`, so the cut is *itself* small in
  the Hilbert-Schmidt norm whenever `j` is.  This is what keeps the witness
  inside the ideal, and it is a Chebyshev inequality on the eigenvalue list:
  the normalized Hilbert-Schmidt norm of a projection is its rank over the
  dimension, and every eigenvalue counted by that rank is at least `t`.

The second clause is the one with content.  The first is true of any spectral
cut; the second is what fails for a cut chosen any other way, and it is why
the threshold must be taken on the spectrum rather than, say, on the entries.

## What this does and does not settle

These two clauses are the whole of the "one-element approximate unit" step.
They do **not** by themselves give the C-star identity on the quotient norm:
that additionally needs `‖b + J‖ = lim ‖b - b e‖` along the approximate unit
and then the standard three-line estimate.  Nothing here asserts it.

## Reused rather than rebuilt

The eigenbasis calculus `ExactInvolutionLifts.eigenCalc` — a diagonal matrix
conjugated by the eigenvector unitary — already carries `norm_eigenCalc`
(isometric from the supremum norm on the diagonal), `eigenCalc_sub`,
`eigenCalc_one` and the spectral theorem as `eq_eigenCalc_eigenvalues`.  The
only gap in that calculus was multiplicativity, added here as
`eigenCalc_mul`.  `RankFrobeniusBound.sum_normSq_eq_re_trace` converts the
Frobenius mass to a trace, and `KazhdanCornerMatrices.spectralAbove` is the
cut itself, already known to be an orthogonal projection.
-/

namespace GroupApproximation
namespace HilbertSchmidtApproximateUnit

open Matrix KazhdanCornerMatrices ExactInvolutionLifts
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

/-! ## Multiplicativity of the eigenbasis calculus -/

section Calculus

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- Products pass through the eigenbasis calculus.  This is the one calculus
law `ExactInvolutionLifts` does not already carry. -/
theorem eigenCalc_mul (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (d₁ d₂ : Y → ℂ) :
    eigenCalc H hH d₁ * eigenCalc H hH d₂ =
      eigenCalc H hH (fun i ↦ d₁ i * d₂ i) := by
  have hUU : (hH.eigenvectorUnitary : Matrix Y Y ℂ)ᴴ *
      (hH.eigenvectorUnitary : Matrix Y Y ℂ) = 1 :=
    Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hdiag : Matrix.diagonal (fun i ↦ d₁ i * d₂ i) =
      Matrix.diagonal d₁ * Matrix.diagonal d₂ :=
    (Matrix.diagonal_mul_diagonal d₁ d₂).symm
  rw [eigenCalc, eigenCalc, eigenCalc, hdiag]
  calc (hH.eigenvectorUnitary : Matrix Y Y ℂ) * Matrix.diagonal d₁ *
          (hH.eigenvectorUnitary : Matrix Y Y ℂ)ᴴ *
          ((hH.eigenvectorUnitary : Matrix Y Y ℂ) * Matrix.diagonal d₂ *
            (hH.eigenvectorUnitary : Matrix Y Y ℂ)ᴴ)
      = (hH.eigenvectorUnitary : Matrix Y Y ℂ) * Matrix.diagonal d₁ *
          ((hH.eigenvectorUnitary : Matrix Y Y ℂ)ᴴ *
            (hH.eigenvectorUnitary : Matrix Y Y ℂ)) * Matrix.diagonal d₂ *
          (hH.eigenvectorUnitary : Matrix Y Y ℂ)ᴴ := by noncomm_ring
    _ = (hH.eigenvectorUnitary : Matrix Y Y ℂ) *
          (Matrix.diagonal d₁ * Matrix.diagonal d₂) *
          (hH.eigenvectorUnitary : Matrix Y Y ℂ)ᴴ := by
        rw [hUU]; noncomm_ring

/-- A Hermitian matrix conjugated on both sides by elements of its own
eigenbasis calculus stays in the calculus, with the eigenvalues appearing
pointwise between the two diagonals. -/
theorem eigenCalc_mul_hermitian_mul (H : Matrix Y Y ℂ) (hH : H.IsHermitian)
    (d₁ d₂ : Y → ℂ) :
    eigenCalc H hH d₁ * H * eigenCalc H hH d₂ =
      eigenCalc H hH (fun i ↦ d₁ i * (hH.eigenvalues i : ℂ) * d₂ i) := by
  have hHeq : H = eigenCalc H hH (fun i ↦ (hH.eigenvalues i : ℂ)) :=
    eq_eigenCalc_eigenvalues H hH
  calc eigenCalc H hH d₁ * H * eigenCalc H hH d₂
      = eigenCalc H hH d₁ * eigenCalc H hH (fun i ↦ (hH.eigenvalues i : ℂ)) *
          eigenCalc H hH d₂ := by rw [← hHeq]
    _ = eigenCalc H hH (fun i ↦ d₁ i * (hH.eigenvalues i : ℂ)) *
          eigenCalc H hH d₂ := by rw [eigenCalc_mul]
    _ = eigenCalc H hH (fun i ↦ d₁ i * (hH.eigenvalues i : ℂ) * d₂ i) := by
        rw [eigenCalc_mul]

/-- The spectral cut is the eigenbasis calculus applied to the indicator of
the eigenvalues above the threshold. -/
@[simp] theorem spectralAbove_eq_eigenCalc (H : Matrix Y Y ℂ) (hH : H.IsHermitian)
    (t : ℝ) :
    spectralAbove H hH t =
      eigenCalc H hH (fun i ↦ if t < hH.eigenvalues i then (1 : ℂ) else 0) :=
  rfl

/-- The complementary cut, in the same calculus. -/
theorem one_sub_spectralAbove_eq_eigenCalc (H : Matrix Y Y ℂ)
    (hH : H.IsHermitian) (t : ℝ) :
    1 - spectralAbove H hH t =
      eigenCalc H hH (fun i ↦ if t < hH.eigenvalues i then (0 : ℂ) else 1) := by
  rw [spectralAbove_eq_eigenCalc, ← eigenCalc_one H hH, eigenCalc_sub]
  refine eigenCalc_congr H hH fun i ↦ ?_
  by_cases hi : t < hH.eigenvalues i <;> simp [hi]

end Calculus

/-! ## The cut of a matrix -/

variable (Y : FiniteModel)

/-- `jᴴ j` is Hermitian; its spectrum is what the cut is taken on. -/
theorem isHermitian_conjTranspose_self (j : Matrix Y Y ℂ) :
    (jᴴ * j).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_self j

/-- Its eigenvalues are nonnegative. -/
theorem eigenvalues_conjTranspose_self_nonneg (j : Matrix Y Y ℂ) (i : Y) :
    0 ≤ (isHermitian_conjTranspose_self Y j).eigenvalues i :=
  (Matrix.posSemidef_conjTranspose_mul_self j).eigenvalues_nonneg i

/-- **The witness.**  The spectral projection of `jᴴ j` onto the eigenvalues
strictly above `t`. -/
def cut (j : Matrix Y Y ℂ) (t : ℝ) : Matrix Y Y ℂ :=
  spectralAbove (jᴴ * j) (isHermitian_conjTranspose_self Y j) t

theorem cut_isOrthogonalProjection (j : Matrix Y Y ℂ) (t : ℝ) :
    IsOrthogonalProjectionMatrix (cut Y j t) :=
  spectralAbove_isOrthogonalProjection _ _ t

theorem norm_cut_le_one (j : Matrix Y Y ℂ) (t : ℝ) : ‖cut Y j t‖ ≤ 1 :=
  norm_le_one_of_isOrthogonalProjection (cut_isOrthogonalProjection Y j t)

/-! ## Clause 1: the cut moves `j` by at most `√t` -/

/-- The conjugated middle term of the approximate-unit estimate is the
eigenbasis calculus applied to the eigenvalues truncated at the threshold. -/
theorem one_sub_cut_mul_mul (j : Matrix Y Y ℂ) (t : ℝ) :
    (1 - cut Y j t) * (jᴴ * j) * (1 - cut Y j t) =
      eigenCalc (jᴴ * j) (isHermitian_conjTranspose_self Y j)
        (fun i ↦ if t < (isHermitian_conjTranspose_self Y j).eigenvalues i then 0
          else ((isHermitian_conjTranspose_self Y j).eigenvalues i : ℂ)) := by
  rw [cut, one_sub_spectralAbove_eq_eigenCalc, eigenCalc_mul_hermitian_mul]
  refine eigenCalc_congr _ _ fun i ↦ ?_
  by_cases hi : t < (isHermitian_conjTranspose_self Y j).eigenvalues i <;>
    simp [hi]

/-- **Clause 1.**  `‖j (1 - cut j t)‖² ≤ t`: outside the cut the matrix has
spectrum below the threshold. -/
theorem norm_mul_one_sub_cut_sq_le (j : Matrix Y Y ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖j * (1 - cut Y j t)‖ * ‖j * (1 - cut Y j t)‖ ≤ t := by
  classical
  have hself : (1 - cut Y j t)ᴴ = 1 - cut Y j t :=
    (one_sub_isOrthogonalProjection (cut_isOrthogonalProjection Y j t)).1
  have hexpand : (j * (1 - cut Y j t))ᴴ * (j * (1 - cut Y j t)) =
      (1 - cut Y j t) * (jᴴ * j) * (1 - cut Y j t) := by
    rw [Matrix.conjTranspose_mul, hself]
    noncomm_ring
  have hnorm : ‖j * (1 - cut Y j t)‖ * ‖j * (1 - cut Y j t)‖ =
      ‖(1 - cut Y j t) * (jᴴ * j) * (1 - cut Y j t)‖ := by
    rw [← hexpand, Matrix.l2_opNorm_conjTranspose_mul_self]
  rw [hnorm, one_sub_cut_mul_mul, norm_eigenCalc]
  refine (pi_norm_le_iff_of_nonneg ht).mpr fun i ↦ ?_
  by_cases hi : t < (isHermitian_conjTranspose_self Y j).eigenvalues i
  · simp [hi, ht]
  · have hle : (isHermitian_conjTranspose_self Y j).eigenvalues i ≤ t :=
      not_lt.mp hi
    have hnn := eigenvalues_conjTranspose_self_nonneg Y j i
    rw [if_neg hi, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hle

/-! ## Clause 2: the cut is Hilbert-Schmidt small -/

/-- The trace of the cut counts the eigenvalues above the threshold. -/
theorem trace_cut (j : Matrix Y Y ℂ) (t : ℝ) :
    (cut Y j t).trace =
      ((Finset.univ.filter fun i : Y ↦
        t < (isHermitian_conjTranspose_self Y j).eigenvalues i).card : ℂ) := by
  classical
  have hUU : ((isHermitian_conjTranspose_self Y j).eigenvectorUnitary :
        Matrix Y Y ℂ)ᴴ *
      ((isHermitian_conjTranspose_self Y j).eigenvectorUnitary :
        Matrix Y Y ℂ) = 1 :=
    Unitary.star_mul_self_of_mem
      (isHermitian_conjTranspose_self Y j).eigenvectorUnitary.2
  rw [cut, spectralAbove_eq_eigenCalc, eigenCalc, Matrix.trace_mul_cycle, hUU,
    Matrix.one_mul, Matrix.trace_diagonal, Finset.sum_boole]

/-- The normalized Hilbert-Schmidt norm of the cut is its rank over the
dimension: the cut is a projection, so its Frobenius mass is its trace. -/
theorem hsNormSq_cut (j : Matrix Y Y ℂ) (t : ℝ) :
    hsNormSq Y (cut Y j t) =
      ((Finset.univ.filter fun i : Y ↦
        t < (isHermitian_conjTranspose_self Y j).eigenvalues i).card : ℝ) /
        Fintype.card Y := by
  classical
  have hproj := cut_isOrthogonalProjection Y j t
  have hsq : (cut Y j t)ᴴ * cut Y j t = cut Y j t := by
    rw [hproj.1, hproj.2]
  have hmass : ∑ i : Y, ∑ k : Y, Complex.normSq (cut Y j t i k)
      = ((cut Y j t).trace).re := by
    rw [RankFrobeniusBound.sum_normSq_eq_re_trace, hsq]
  rw [hsNormSq, hmass, trace_cut]
  norm_num

/-- **Chebyshev on the eigenvalue list.**  Each eigenvalue above the threshold
contributes at least the threshold to the total.

No positivity of `t` is needed: below `0` the filter is everything and the
eigenvalues of `jᴴ j` are nonnegative, so the bound is slack rather than
false. -/
theorem threshold_mul_card_le_sum_eigenvalues (j : Matrix Y Y ℂ) (t : ℝ) :
    ((Finset.univ.filter fun i : Y ↦
        t < (isHermitian_conjTranspose_self Y j).eigenvalues i).card : ℝ) * t
      ≤ ∑ i : Y, (isHermitian_conjTranspose_self Y j).eigenvalues i := by
  classical
  have hcard :
      (Finset.univ.filter fun i : Y ↦
          t < (isHermitian_conjTranspose_self Y j).eigenvalues i).card • t
        ≤ ∑ i ∈ Finset.univ.filter (fun i : Y ↦
            t < (isHermitian_conjTranspose_self Y j).eigenvalues i),
            (isHermitian_conjTranspose_self Y j).eigenvalues i := by
    refine Finset.card_nsmul_le_sum _ _ _ fun i hi ↦ ?_
    exact le_of_lt (Finset.mem_filter.mp hi).2
  have hsub :
      ∑ i ∈ Finset.univ.filter (fun i : Y ↦
          t < (isHermitian_conjTranspose_self Y j).eigenvalues i),
          (isHermitian_conjTranspose_self Y j).eigenvalues i
        ≤ ∑ i : Y, (isHermitian_conjTranspose_self Y j).eigenvalues i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun i _ _ ↦ eigenvalues_conjTranspose_self_nonneg Y j i
  rw [nsmul_eq_mul] at hcard
  linarith

/-- The Frobenius mass of `j` is the sum of the eigenvalues of `jᴴ j`. -/
theorem sum_eigenvalues_eq_hsNormSq (j : Matrix Y Y ℂ)
    (hY : 0 < Fintype.card Y) :
    ∑ i : Y, (isHermitian_conjTranspose_self Y j).eigenvalues i
      = hsNormSq Y j * Fintype.card Y := by
  classical
  have hne : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hY.ne'
  have hmass : ∑ i : Y, ∑ k : Y, Complex.normSq (j i k)
      = ∑ i : Y, (isHermitian_conjTranspose_self Y j).eigenvalues i := by
    rw [RankFrobeniusBound.sum_normSq_eq_re_trace,
      (isHermitian_conjTranspose_self Y j).trace_eq_sum_eigenvalues,
      Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Complex.ofReal_re _
  rw [← hmass, hsNormSq]
  field_simp

/-- **Clause 2.**  `t · ‖cut j t‖₂² ≤ ‖j‖₂²`: the cut is Hilbert-Schmidt small
whenever `j` is, uniformly in the dimension.  This is what keeps the witness
inside the `‖·‖₂`-null ideal. -/
theorem hsNormSq_cut_le (j : Matrix Y Y ℂ) (t : ℝ)
    (hY : 0 < Fintype.card Y) :
    t * hsNormSq Y (cut Y j t) ≤ hsNormSq Y j := by
  classical
  have hd : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  have hne : (Fintype.card Y : ℝ) ≠ 0 := hd.ne'
  have hcheb := threshold_mul_card_le_sum_eigenvalues Y j t
  rw [sum_eigenvalues_eq_hsNormSq Y j hY] at hcheb
  refine le_of_mul_le_mul_right ?_ hd
  calc t * hsNormSq Y (cut Y j t) * (Fintype.card Y : ℝ)
      = t * (hsNormSq Y (cut Y j t) * (Fintype.card Y : ℝ)) := by ring
    _ = t * ((Finset.univ.filter fun i : Y ↦
          t < (isHermitian_conjTranspose_self Y j).eigenvalues i).card : ℝ) := by
        rw [hsNormSq_cut]
        field_simp
    _ ≤ hsNormSq Y j * (Fintype.card Y : ℝ) := by linarith

/-! ## The two clauses together -/

/-- **The approximate-unit witness, for one matrix.**  For every threshold
`t > 0` there is an orthogonal projection `e` moving `j` by at most `√t` in
operator norm, whose own normalized Hilbert-Schmidt mass is at most
`‖j‖₂² / t`.

Applied coordinatewise to a sequence lying in the `‖·‖₂`-null ideal, the first
clause is the approximate-unit clause and the second is what keeps the witness
inside the ideal: `t` is fixed before the sequence is varied, so the bound
`t · ‖eₙ‖₂² ≤ ‖jₙ‖₂²` sends `‖eₙ‖₂ → 0` along any filter along which
`‖jₙ‖₂ → 0`. -/
theorem exists_projection_approximate_unit (j : Matrix Y Y ℂ) {t : ℝ}
    (ht : 0 < t) (hY : 0 < Fintype.card Y) :
    ∃ e : Matrix Y Y ℂ, IsOrthogonalProjectionMatrix e ∧ ‖e‖ ≤ 1 ∧
      ‖j - j * e‖ * ‖j - j * e‖ ≤ t ∧
      t * hsNormSq Y e ≤ hsNormSq Y j := by
  refine ⟨cut Y j t, cut_isOrthogonalProjection Y j t, norm_cut_le_one Y j t,
    ?_, hsNormSq_cut_le Y j t hY⟩
  have hsub : j - j * cut Y j t = j * (1 - cut Y j t) := by
    rw [Matrix.mul_sub, Matrix.mul_one]
  rw [hsub]
  exact norm_mul_one_sub_cut_sq_le Y j ht.le

end

end HilbertSchmidtApproximateUnit
end GroupApproximation
