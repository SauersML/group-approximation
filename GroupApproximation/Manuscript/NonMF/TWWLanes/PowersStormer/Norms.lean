import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Norm
import GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.Conjugation
import GroupApproximation.Meta.AxiomGuard

/-!
# Powers–Størmer inequality: norm form (lane nm-tww-10, part 3)

Here are the unnormalised norms on `Matrix n n ℂ`:

* `hsNormSq x = ∑ᵢ ∑ⱼ ‖xᵢⱼ‖²`, the squared Hilbert–Schmidt (Frobenius) norm;
* `traceNorm x = ⨆_{u unitary} ‖tr(x u)‖`, the trace norm, defined by duality with the operator
  norm. The supremum is finite because `‖tr(x u)‖ ≤ ∑ᵢ ∑ⱼ ‖xᵢⱼ‖`: the entries of a unitary have
  norm `≤ 1` (`entry_norm_bound_of_unitary`).

For Hermitian `x`, `re tr(x x) = hsNormSq x`. Combining this with the duality form
`exists_selfAdjoint_unitary_powersStormer` gives the endpoint

`powersStormer : hsNormSq (h - k) ≤ traceNorm (h ^ 2 - k ^ 2)` for positive semidefinite `h, k`.

Everything is stated for `Matrix n n ℂ`, with no normalisation by the dimension.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace PowersStormer

open Matrix
open scoped ComplexOrder

noncomputable section

variable {n : Type*} [Fintype n]

/-- The squared (unnormalised) Hilbert–Schmidt norm `∑ᵢ ∑ⱼ ‖xᵢⱼ‖²`. -/
def hsNormSq (x : Matrix n n ℂ) : ℝ :=
  ∑ i, ∑ j, ‖x i j‖ ^ 2

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.hsNormSq

/-- For a Hermitian matrix, `re tr(x x)` is the squared Hilbert–Schmidt norm. -/
theorem re_trace_mul_self_eq_hsNormSq {x : Matrix n n ℂ} (hx : x.IsHermitian) :
    (trace (x * x)).re = hsNormSq x := by
  unfold hsNormSq
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hx.apply j i]
  first
    | rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
    | (simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
        Complex.sq_norm, Complex.normSq_apply]
       ring)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.re_trace_mul_self_eq_hsNormSq

variable [DecidableEq n]

/-- The (unnormalised) trace norm, defined by duality: `‖x‖₁ = ⨆_{u unitary} ‖tr(x u)‖`. -/
def traceNorm (x : Matrix n n ℂ) : ℝ :=
  ⨆ U : Matrix.unitaryGroup n ℂ, ‖trace (x * (U : Matrix n n ℂ))‖

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.traceNorm

/-- The entrywise bound `‖tr(x u)‖ ≤ ∑ᵢ ∑ⱼ ‖xᵢⱼ‖` for a unitary `u`. It makes the supremum in
`traceNorm` finite. -/
theorem norm_trace_mul_unitary_le (x U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    ‖trace (x * U)‖ ≤ ∑ i, ∑ j, ‖x i j‖ := by
  rw [Matrix.trace]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (entry_norm_bound_of_unitary hU j i)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.norm_trace_mul_unitary_le

/-- The set of values whose supremum defines `traceNorm` is bounded above. -/
theorem bddAbove_range_norm_trace_mul_unitary (x : Matrix n n ℂ) :
    BddAbove (Set.range fun U : Matrix.unitaryGroup n ℂ => ‖trace (x * (U : Matrix n n ℂ))‖) := by
  refine ⟨∑ i, ∑ j, ‖x i j‖, ?_⟩
  rintro _ ⟨V, rfl⟩
  exact norm_trace_mul_unitary_le x V V.2

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.bddAbove_range_norm_trace_mul_unitary

/-- Every unitary pairing is bounded by the trace norm. -/
theorem norm_trace_mul_unitary_le_traceNorm (x U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    ‖trace (x * U)‖ ≤ traceNorm x :=
  le_ciSup (bddAbove_range_norm_trace_mul_unitary x) (⟨U, hU⟩ : Matrix.unitaryGroup n ℂ)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.norm_trace_mul_unitary_le_traceNorm

/-- The real part of a unitary pairing is bounded by the trace norm. -/
theorem re_trace_mul_unitary_le_traceNorm (x U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    (trace (x * U)).re ≤ traceNorm x :=
  le_trans (Complex.re_le_norm _) (norm_trace_mul_unitary_le_traceNorm x U hU)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.re_trace_mul_unitary_le_traceNorm

/-- **Powers–Størmer inequality** (unnormalised). For positive semidefinite complex matrices
`h, k`, `‖h - k‖_HS ^ 2 ≤ ‖h ^ 2 - k ^ 2‖_1`. -/
theorem powersStormer (h k : Matrix n n ℂ) (hh : h.PosSemidef) (hk : k.PosSemidef) :
    hsNormSq (h - k) ≤ traceNorm (h ^ 2 - k ^ 2) := by
  obtain ⟨u, hu, -, hineq⟩ := exists_selfAdjoint_unitary_powersStormer hh hk
  rw [← re_trace_mul_self_eq_hsNormSq (hh.isHermitian.sub hk.isHermitian), sq, sq]
  exact le_trans hineq (re_trace_mul_unitary_le_traceNorm _ u hu)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.powersStormer

end

end PowersStormer
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
