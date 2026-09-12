import GroupApproximation.Sofic.HilbertSchmidtAdjointGap
import GroupApproximation.Sofic.LeavittTraceFloor
import GroupApproximation.Meta.AxiomGuard

/-!
# Hilbert--Schmidt smallness does not bound the operator norm: the printed `D_d`

`non_mf_groups_exist.tex`, opening of the subsection "From Hilbert--Schmidt to
operator norm" (tex lines 596-604 at 73c867c5b):

> Smallness in normalized Hilbert--Schmidt norm does not bound the operator
> norm: for
> `D_d = diag(-1,1,…,1) ∈ U(d)`,  `‖D_d − 1‖₂ = 2/√d → 0`,  `‖D_d − 1‖ = 2`.

The census graded the sentence `structural`; it is a computation with three
printed values, so it is carried here literally: `D_d` is
`HilbertSchmidtAdjointGap.signDiagonal` at the first coordinate of `M_d(ℂ)`, it
is unitary, its normalized Hilbert--Schmidt distance to `1` is exactly
`2/√d`, that quantity tends to `0`, and its operator-norm distance to `1` is
exactly `2`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences

open Filter Matrix HilbertSchmidtAdjointGap
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **The printed `D_d = diag(-1, 1, …, 1)`**, on the literal matrix algebra
`M_d(ℂ)` (`naturalFiniteModel d`, coordinates `Fin d`), flipping the first
coordinate. -/
def printedSignDiagonal (d : ℕ) (hd : 0 < d) :
    Matrix (naturalFiniteModel d) (naturalFiniteModel d) ℂ :=
  signDiagonal (Y := naturalFiniteModel d) (⟨0, hd⟩ : Fin d)

/-- The normalized squared Hilbert--Schmidt norm is invariant under negation. -/
theorem hsNormSq_neg (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    hsNormSq Y (-A) = hsNormSq Y A := by
  simp only [hsNormSq, Matrix.neg_apply, Complex.normSq_neg]

/-- `1 − D_d` is the diagonal matrix with the single entry `2`. -/
theorem one_sub_signDiagonal_eq_diagonal {Y : Type*} [Fintype Y] [DecidableEq Y]
    (i₀ : Y) :
    (1 : Matrix Y Y ℂ) - signDiagonal i₀ = Matrix.diagonal (Pi.single i₀ (2 : ℂ)) := by
  ext i j
  rw [one_sub_signDiagonal_apply, Matrix.diagonal_apply, Pi.single_apply]

/-- **`‖D − 1‖ = 2` in operator norm**, in every dimension. -/
theorem l2_opNorm_signDiagonal_sub_one {Y : Type*} [Fintype Y] [DecidableEq Y]
    (i₀ : Y) :
    ‖signDiagonal i₀ - (1 : Matrix Y Y ℂ)‖ = 2 := by
  rw [norm_sub_rev, one_sub_signDiagonal_eq_diagonal, Matrix.l2_opNorm_diagonal,
    Pi.norm_single]
  norm_num

/-- **`‖D_d − 1‖₂ = 2/√d`.** -/
theorem hsNorm_printedSignDiagonal_sub_one (d : ℕ) (hd : 0 < d) :
    hsNorm (naturalFiniteModel d) (printedSignDiagonal d hd - 1) = 2 / Real.sqrt d := by
  have hneg : printedSignDiagonal d hd - 1
      = -((1 : Matrix (naturalFiniteModel d) (naturalFiniteModel d) ℂ)
          - printedSignDiagonal d hd) := (neg_sub _ _).symm
  have hsq : hsNormSq (naturalFiniteModel d) (printedSignDiagonal d hd - 1)
      = 4 / (d : ℝ) := by
    rw [hneg, hsNormSq_neg, printedSignDiagonal,
      hsNormSq_one_sub_signDiagonal (naturalFiniteModel d) (⟨0, hd⟩ : Fin d),
      card_naturalFiniteModel]
  have hsqrt : (4 : ℝ) / d = (2 / Real.sqrt d) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    norm_num
  rw [hsNorm, hsq, hsqrt, Real.sqrt_sq (div_nonneg zero_le_two (Real.sqrt_nonneg _))]

/-- **The printed sentence, every clause.**  For every `d ≥ 1`, `D_d` is a
unitary of `M_d(ℂ)` with `‖D_d − 1‖₂ = 2/√d` and `‖D_d − 1‖ = 2`, and
`2/√d → 0`. -/
def PrintedHSSmallnessDoesNotBoundOperatorNorm : Prop :=
  (∀ (d : ℕ) (hd : 0 < d),
      printedSignDiagonal d hd ∈ Matrix.unitaryGroup (naturalFiniteModel d) ℂ ∧
      hsNorm (naturalFiniteModel d) (printedSignDiagonal d hd - 1) = 2 / Real.sqrt d ∧
      ‖printedSignDiagonal d hd - 1‖ = 2) ∧
    Tendsto (fun d : ℕ ↦ 2 / Real.sqrt d) atTop (nhds 0)

theorem manuscriptSentence_hsSmallnessDoesNotBoundOperatorNorm :
    PrintedHSSmallnessDoesNotBoundOperatorNorm := by
  refine ⟨fun d hd ↦ ⟨signDiagonal_mem_unitaryGroup _,
    hsNorm_printedSignDiagonal_sub_one d hd, l2_opNorm_signDiagonal_sub_one _⟩, ?_⟩
  exact tendsto_const_nhds.div_atTop
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

end

end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_hsSmallnessDoesNotBoundOperatorNorm
