import GroupApproximation.Analysis.NormMatrixCorona
import GroupApproximation.Meta.AxiomGuard

/-!
# Radial truncation of a matrix to a prescribed operator-norm radius

Lane `nm-tww-07` (norm-bounded lifting across the trace-kernel quotient).  This is the
coordinatewise cutoff behind the norm-bounded lift.  For `r ≥ 0` and a square complex
matrix `M`, `radialTrunc r M` is `M` when `‖M‖ ≤ r`, and `(r / ‖M‖) • M` otherwise.

* `norm_radialTrunc_le`: `‖radialTrunc r M‖ ≤ r`.
* `norm_radialTrunc_sub_le`: if `‖M‖ ≤ r + δ` with `δ ≥ 0`, the truncation moves `M` by at
  most `δ` in operator norm, and so by at most `δ` in `‖·‖₂`, which is dominated by the
  operator norm.

The radial cutoff needs no spectral calculus, and it applies to every matrix, not only
Hermitian ones.
-/

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The radial truncation of a matrix to operator-norm radius `r`. -/
def radialTrunc (r : ℝ) (M : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  if ‖M‖ ≤ r then M else ((r / ‖M‖ : ℝ) : ℂ) • M

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift.radialTrunc

/-- The radial truncation has operator norm at most the radius. -/
theorem norm_radialTrunc_le {r : ℝ} (hr : 0 ≤ r) (M : Matrix Y Y ℂ) :
    ‖radialTrunc r M‖ ≤ r := by
  unfold radialTrunc
  split_ifs with h
  · exact h
  · have hpos : 0 < ‖M‖ := lt_of_le_of_lt hr (not_le.mp h)
    rw [norm_smul, Complex.norm_of_nonneg (div_nonneg hr (norm_nonneg M)),
      div_mul_cancel₀ r (ne_of_gt hpos)]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift.norm_radialTrunc_le

/-- If `‖M‖ ≤ r + δ`, the radial truncation moves `M` by at most `δ`. -/
theorem norm_radialTrunc_sub_le {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 ≤ δ) (M : Matrix Y Y ℂ)
    (hM : ‖M‖ ≤ r + δ) : ‖radialTrunc r M - M‖ ≤ δ := by
  unfold radialTrunc
  split_ifs with h
  · rw [sub_self, norm_zero]
    exact hδ
  · have hlt : r < ‖M‖ := not_le.mp h
    have hpos : 0 < ‖M‖ := lt_of_le_of_lt hr hlt
    have hq : r / ‖M‖ ≤ 1 := (div_le_one hpos).mpr hlt.le
    have hrw : ((r / ‖M‖ : ℝ) : ℂ) • M - M = -(((1 - r / ‖M‖ : ℝ) : ℂ) • M) := by
      rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, neg_sub]
    rw [hrw, norm_neg, norm_smul, Complex.norm_of_nonneg (sub_nonneg.mpr hq), sub_mul,
      one_mul, div_mul_cancel₀ r (ne_of_gt hpos)]
    linarith

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift.norm_radialTrunc_sub_le

end

end GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift
