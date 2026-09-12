import GroupApproximation.Sofic.KazhdanCornerPolar
import GroupApproximation.Sofic.NormTraceGap

/-!
# Two printed estimates of the preliminaries

`notes/NON_MF_PROOF_LEDGER.md` records two small steps of
`non_mf_groups_exist.tex` that the development uses but never states.  Both are
stated here, in closed form, with nothing to the left of the colon.

## The trace bound

The preliminaries list three inequalities "used without comment" on `M_r(ℂ)`:

> `‖x‖₂ ≤ ‖x‖`;  `|tr_r(x)| ≤ ‖x‖`;  and `‖uxv‖₂ = ‖x‖₂` for unitaries `u, v`.

The first and third are `hsDistSq_le_sq_l2_opNorm` and
`hsNormSq_mul_left`/`hsNormSq_mul_right`.  The middle one — the bound on the
*normalized trace* — had no declaration.  It is `norm_normTrace_le_l2_opNorm`
below: each diagonal entry is bounded by the operator norm
(`normSq_entry_le_sq_l2_opNorm`), the trace is the sum of `r` of them, and
dividing by `r` is what the normalization does.

The empty model is not excluded.  There `tr_r` divides by zero, which in Lean
is zero, and the bound holds for the uninteresting reason; no positivity
hypothesis is needed and none is taken.

## The polar-correction estimate

The lifting lemma's proof prints an explicit constant:

> once `‖xₙ*xₙ − 1‖ ≤ 1/2`, polar correction `uₙ = xₙ(xₙ*xₙ)^{-1/2}` is unitary
> with `‖uₙ − xₙ‖ ≤ 2‖xₙ‖‖xₙ*xₙ − 1‖ → 0` by continuous functional calculus.

`Sofic/KazhdanCornerPolar` proves this, but in a form indexed by an auxiliary
tolerance `delta` with `‖xᴴx − 1‖ ≤ delta`, so the printed inequality — the one
with `‖xᴴx − 1‖ itself` in the bound — is not a located statement.
`manuscriptPolarCorrectionEstimate` takes `delta` to be that norm, which is the
sharpest admissible choice, and also records that the corrected matrix is the
printed formula `x(xᴴx)^{-1/2}` rather than merely some unitary nearby.
-/

namespace GroupApproximation
namespace PrintedPreliminaryEstimates

open Matrix
open scoped Matrix.Norms.L2Operator

/-! ## The trace bound `|tr_r x| ≤ ‖x‖` -/

/-- **The normalized trace is bounded by the operator norm.**  This is the
middle inequality of the three the manuscript's preliminaries use without
comment.

Each diagonal entry satisfies `‖x i i‖ ≤ ‖x‖`, so the unnormalized trace is at
most `r · ‖x‖` in absolute value, and the normalized trace divides by `r`. -/
theorem norm_normTrace_le_l2_opNorm (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    ‖normTrace Y A‖ ≤ ‖A‖ := by
  classical
  have hentry : ∀ i : Y, ‖A i i‖ ≤ ‖A‖ := by
    intro i
    have h := normSq_entry_le_sq_l2_opNorm Y A i i
    rw [Complex.normSq_eq_norm_sq] at h
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h
  have htr : ‖Matrix.trace A‖ ≤ ‖A‖ * (Fintype.card Y : ℝ) := by
    have hsum : ‖Matrix.trace A‖ ≤ ∑ _i : Y, ‖A‖ := by
      have hstep : ‖Matrix.trace A‖ ≤ ∑ i : Y, ‖A i i‖ := by
        show ‖∑ i : Y, A i i‖ ≤ ∑ i : Y, ‖A i i‖
        exact norm_sum_le _ _
      exact hstep.trans (Finset.sum_le_sum fun i _ ↦ hentry i)
    have hconst : (∑ _i : Y, ‖A‖) = ‖A‖ * (Fintype.card Y : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    rwa [hconst] at hsum
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with hcard | hcard
  · have hzero : normTrace Y A = 0 := by
      rw [normTrace, hcard]
      simp
    rw [hzero, norm_zero]
    exact norm_nonneg A
  · have hpos : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hcard
    rw [normTrace, norm_div, Complex.norm_natCast, div_le_iff₀ hpos]
    exact htr

/-! ## The polar-correction estimate of the lifting lemma -/

/-- **The printed polar-correction estimate.**  A matrix whose Gram defect is
at most `1/2` is within `2‖x‖‖xᴴx − 1‖` of an exact unitary, and that unitary
is the printed one: `x` times the inverse square root of `xᴴx`.

This is the step of the lifting lemma's proof that supplies the constant, and
it is what makes the correction vanish when the Gram defect does. -/
theorem manuscriptPolarCorrectionEstimate :
    ∀ {Y : Type} [Fintype Y] [DecidableEq Y] (x : Matrix Y Y ℂ),
      ‖xᴴ * x - 1‖ ≤ 1 / 2 →
      ∃ u : Matrix Y Y ℂ,
        u ∈ Matrix.unitaryGroup Y ℂ ∧
          u = x * KazhdanCornerMatrices.cornerGramInvSqrt x
                (KazhdanCornerMatrices.cornerGram_isHermitian x) ∧
          ‖u - x‖ ≤ 2 * ‖x‖ * ‖xᴴ * x - 1‖ := by
  intro Y _ _ x hx
  refine ⟨KazhdanCornerMatrices.polarCorrect x
      (KazhdanCornerMatrices.cornerGram_isHermitian x), ?_, rfl, ?_⟩
  · exact (KazhdanCornerMatrices.polarCorrectUnitary x
      (KazhdanCornerMatrices.cornerGram_isHermitian x) hx le_rfl).property
  · have hbound := KazhdanCornerMatrices.norm_polarCorrect_sub_le_mul x
      (KazhdanCornerMatrices.cornerGram_isHermitian x)
      (norm_nonneg (xᴴ * x - 1)) hx le_rfl
    calc ‖KazhdanCornerMatrices.polarCorrect x
            (KazhdanCornerMatrices.cornerGram_isHermitian x) - x‖
        ≤ ‖x‖ * (2 * ‖xᴴ * x - 1‖) := hbound
      _ = 2 * ‖x‖ * ‖xᴴ * x - 1‖ := by ring

end PrintedPreliminaryEstimates
end GroupApproximation
