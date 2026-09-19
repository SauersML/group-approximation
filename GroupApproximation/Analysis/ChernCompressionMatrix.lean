import GroupApproximation.Analysis.CuntzPedersenCoronaObstruction
import GroupApproximation.Analysis.OperatorNormCertificate

/-!
# The matrix compression in the projective Chern obstruction

This file contains the finite-dimensional algebra in the Chern-class lemma.
The only geometric statement needed after this file is the common-zero
property for the lower-left bundle sections.  Everything from that common
zero to the operator-norm lower bound is proved here.
-/

namespace GroupApproximation
namespace ChernCompressionMatrix

open CuntzPedersenCoronaObstruction
open scoped Matrix.Norms.L2Operator

noncomputable section

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem diagonal_star_mul_re (Z : Matrix ι ι ℂ) (i : ι) :
    ((star Z * Z) i i).re = ∑ k, Complex.normSq (Z k i) := by
  rw [Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]
  exact Complex.ofReal_re _

private theorem diagonal_mul_star_re (Z : Matrix ι ι ℂ) (i : ι) :
    ((Z * star Z) i i).re = ∑ k, Complex.normSq (Z i k) := by
  rw [Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.star_apply, Complex.star_def, Complex.mul_conj]
  exact Complex.ofReal_re _

/-- If the distinguished column of `Z` vanishes off its diagonal, then the
distinguished diagonal entry of `[Z*,Z]` has nonpositive real part. -/
theorem selfCommutator_diagonal_re_nonpos (Z : Matrix ι ι ℂ) (i₀ : ι)
    (hcol : ∀ k, k ≠ i₀ → Z k i₀ = 0) :
    (selfCommutator Z i₀ i₀).re ≤ 0 := by
  change (((star Z * Z) i₀ i₀) - ((Z * star Z) i₀ i₀)).re ≤ 0
  rw [Complex.sub_re,
    diagonal_star_mul_re, diagonal_mul_star_re]
  have hfirst : (∑ k, Complex.normSq (Z k i₀)) =
      Complex.normSq (Z i₀ i₀) := by
    rw [Finset.sum_eq_single i₀]
    · intro k _ hk
      rw [hcol k hk, Complex.normSq_zero]
    · intro hi
      exact (hi (Finset.mem_univ i₀)).elim
  rw [hfirst]
  have hle : Complex.normSq (Z i₀ i₀) ≤
      ∑ k, Complex.normSq (Z i₀ k) :=
    Finset.single_le_sum (fun k _ ↦ Complex.normSq_nonneg (Z i₀ k))
      (Finset.mem_univ i₀)
  linarith

/-- A finite family with a common lower-left zero has a nonpositive
distinguished compression after summing its self-commutators. -/
theorem sum_selfCommutator_diagonal_re_nonpos {m : ℕ}
    (Z : Fin m → Matrix ι ι ℂ) (i₀ : ι)
    (hcol : ∀ j k, k ≠ i₀ → Z j k i₀ = 0) :
    ((∑ j, selfCommutator (Z j)) i₀ i₀).re ≤ 0 := by
  have heval : (∑ j, selfCommutator (Z j)) i₀ i₀ =
      ∑ j, selfCommutator (Z j) i₀ i₀ := by
    let ev : Matrix ι ι ℂ →+ ℂ :=
      { toFun := fun A ↦ A i₀ i₀
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    change ev (∑ j, selfCommutator (Z j)) =
      ∑ j, ev (selfCommutator (Z j))
    exact map_sum ev (fun j ↦ selfCommutator (Z j)) Finset.univ
  rw [heval, Complex.re_sum]
  exact Finset.sum_nonpos fun j _ ↦
    selfCommutator_diagonal_re_nonpos (Z j) i₀ (hcol j)

/-- The exact compression conclusion: if `h` has distinguished diagonal
entry one and all lower-left corners of the `z_j` vanish at one fibre, then
`h - Σ[z_j*,z_j]` has operator norm at least one. -/
theorem norm_sub_sum_selfCommutator_ge_one {m : ℕ}
    (h : Matrix ι ι ℂ) (Z : Fin m → Matrix ι ι ℂ) (i₀ : ι)
    (hdiag : h i₀ i₀ = 1)
    (hcol : ∀ j k, k ≠ i₀ → Z j k i₀ = 0) :
    1 ≤ ‖h - ∑ j, selfCommutator (Z j)‖ := by
  let W := h - ∑ j, selfCommutator (Z j)
  have hRe : 1 ≤ (W i₀ i₀).re := by
    dsimp only [W]
    change 1 ≤ (h i₀ i₀ - (∑ j, selfCommutator (Z j)) i₀ i₀).re
    rw [Complex.sub_re, hdiag, Complex.one_re]
    have hs := sum_selfCommutator_diagonal_re_nonpos Z i₀ hcol
    linarith
  have hReNorm : (W i₀ i₀).re ≤ ‖W i₀ i₀‖ :=
    Complex.re_le_norm _
  exact hRe.trans (hReNorm.trans
    (OperatorNormCertificate.norm_entry_le_opNorm W i₀ i₀))

end

end ChernCompressionMatrix
end GroupApproximation
