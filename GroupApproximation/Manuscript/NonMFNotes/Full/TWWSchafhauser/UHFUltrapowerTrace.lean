import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionUHFModelLift
import GroupApproximation.Analysis.TracialMatrixUltraproduct
import GroupApproximation.Sofic.LeavittTraceFloor

/-!
# The tracial `2`-norm of the universal UHF algebra

Lane `TWWSch3d2Q2` (work order `WO-TWWSch-3d2-Q2`).  Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), through
C. Schafhauser, *A new proof of the Tikuisis--White--Winter theorem*, J. reine
angew. Math. **759** (2020), §4, where the tracial ultrapower `Q^ω` of the
universal UHF algebra is the quotient of `ℓ^∞(ℕ, Q)` by the `ω`-null sequences
for the trace `2`-norm `‖x‖₂² = tr_Q(x* x)`.

The trace of a `UHFModel` is only specified through the conditional expectations:
`tr_Q = tr_{m!} ∘ E_m`.  This file derives the Hilbert--Schmidt estimates that
make the `2`-null sequences an ideal.  Each one is a limit of the matrix
estimate for the block approximants `ι_m (E_m x) → x`, since `tr_Q` is
contractive and hence continuous.

## Main declarations

* `UHFModel.trace_ι`, `UHFModel.continuous_trace`, `UHFModel.trace_mul_comm`;
* `UHFModel.re_trace_star_mul_self_nonneg`;
* `UHFModel.re_trace_star_add_mul_add_le` (`‖u + v‖₂² ≤ 2‖u‖₂² + 2‖v‖₂²`);
* `UHFModel.re_trace_star_mul_mul_le_left`, `UHFModel.re_trace_star_mul_mul_le_right`
  (`‖b a‖₂, ‖a b‖₂ ≤ ‖b‖ ‖a‖₂`);
* `UHFModel.re_trace_star_star_mul_star` (`‖a*‖₂ = ‖a‖₂`);
* `UHFModel.re_trace_star_mul_self_le` (`‖z‖₂² ≤ ‖z‖²`);
* `UHFModel.normSq_trace_le`, `UHFModel.norm_trace_le_sqrt` (`|tr_Q x| ≤ ‖x‖₂`);
* `UHFModel.trace_star`, `UHFModel.ofReal_re_trace_star_mul_self`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Filter Topology
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace UHFModel

variable {Q : Type} [CStarAlgebra Q] (M : UHFModel Q)

/-- The trace of `Q` restricts to the normalized trace on every building block. -/
theorem trace_ι (m : ℕ) (a : Matrix (uhfLevel m) (uhfLevel m) ℂ) :
    M.trace (M.ι m a) = normTrace (uhfLevel m) a := by
  rw [M.trace_eq m, M.expect_ι]

/-- The trace of `Q` is continuous, being contractive. -/
theorem continuous_trace : Continuous M.trace :=
  AddMonoidHomClass.continuous_of_bound M.trace 1 M.norm_trace_le_one_mul

/-- On a building block, `tr_Q(ι(a)* ι(a))` is the normalized Hilbert--Schmidt norm. -/
theorem trace_star_ι_mul_ι (m : ℕ) (a : Matrix (uhfLevel m) (uhfLevel m) ℂ) :
    M.trace (star (M.ι m a) * M.ι m a) = ((hsNormSq (uhfLevel m) a : ℝ) : ℂ) := by
  rw [← map_star (M.ι m) a, ← map_mul (M.ι m), M.trace_ι m, Matrix.star_eq_conjTranspose,
    TracialUltraproduct.ofReal_hsNormSq_conjTranspose_mul]

/-- **The trace of `Q` is tracial**, as a limit of the traciality of `tr_{m!}`. -/
theorem trace_mul_comm (x y : Q) : M.trace (x * y) = M.trace (y * x) := by
  have h1 : Tendsto (fun m : ℕ ↦ M.trace (M.ι m (M.expect m x) * M.ι m (M.expect m y)))
      atTop (𝓝 (M.trace (x * y))) :=
    (M.continuous_trace.tendsto (x * y)).comp
      ((M.tendsto_ι_expect_nhds x).mul (M.tendsto_ι_expect_nhds y))
  have h2 : Tendsto (fun m : ℕ ↦ M.trace (M.ι m (M.expect m y) * M.ι m (M.expect m x)))
      atTop (𝓝 (M.trace (y * x))) :=
    (M.continuous_trace.tendsto (y * x)).comp
      ((M.tendsto_ι_expect_nhds y).mul (M.tendsto_ι_expect_nhds x))
  have h1' : Tendsto (fun m : ℕ ↦ M.trace (M.ι m (M.expect m y) * M.ι m (M.expect m x)))
      atTop (𝓝 (M.trace (x * y))) :=
    Tendsto.congr (fun m ↦ by
      rw [← map_mul (M.ι m), ← map_mul (M.ι m), M.trace_ι m, M.trace_ι m,
        TracialUltraproduct.normTrace_mul_comm]) h1
  exact tendsto_nhds_unique h1' h2

/-- The block approximants of `x* x`, seen through the trace. -/
theorem tendsto_trace_star_ι_mul_ι (x : Q) :
    Tendsto (fun m : ℕ ↦ M.trace (star (M.ι m (M.expect m x)) * M.ι m (M.expect m x)))
      atTop (𝓝 (M.trace (star x * x))) :=
  (M.continuous_trace.tendsto (star x * x)).comp
    ((M.tendsto_ι_expect_nhds x).star.mul (M.tendsto_ι_expect_nhds x))

/-- The real parts of the traces of the block approximants of `x* x`. -/
theorem tendsto_re_trace_star_ι_mul_ι (x : Q) :
    Tendsto (fun m : ℕ ↦ hsNormSq (uhfLevel m) (M.expect m x))
      atTop (𝓝 ((M.trace (star x * x)).re)) :=
  Tendsto.congr (fun m ↦ by
      show (M.trace (star (M.ι m (M.expect m x)) * M.ι m (M.expect m x))).re = _
      rw [M.trace_star_ι_mul_ι m, Complex.ofReal_re])
    ((Complex.continuous_re.tendsto (M.trace (star x * x))).comp
      (M.tendsto_trace_star_ι_mul_ι x))

/-- **Positivity of the trace**: `0 ≤ Re tr_Q(x* x)`. -/
theorem re_trace_star_mul_self_nonneg (x : Q) : 0 ≤ (M.trace (star x * x)).re :=
  ge_of_tendsto' (M.tendsto_re_trace_star_ι_mul_ι x) fun _ ↦ hsNormSq_nonneg _ _

/-- **The squared triangle inequality** `‖u + v‖₂² ≤ 2‖u‖₂² + 2‖v‖₂²`, from the
parallelogram identity and positivity. -/
theorem re_trace_star_add_mul_add_le (u v : Q) :
    (M.trace (star (u + v) * (u + v))).re ≤
      2 * (M.trace (star u * u)).re + 2 * (M.trace (star v * v)).re := by
  have hpar : star (u + v) * (u + v) + star (u - v) * (u - v) =
      star u * u + star u * u + (star v * v + star v * v) := by
    rw [star_add, star_sub, add_mul, mul_add, mul_add, sub_mul, mul_sub, mul_sub]
    abel
  have htr : (M.trace (star (u + v) * (u + v))).re + (M.trace (star (u - v) * (u - v))).re =
      2 * (M.trace (star u * u)).re + 2 * (M.trace (star v * v)).re := by
    rw [← Complex.add_re, ← map_add M.trace, hpar, map_add M.trace, map_add M.trace,
      map_add M.trace, Complex.add_re, Complex.add_re, Complex.add_re]
    ring
  have h0 := M.re_trace_star_mul_self_nonneg (u - v)
  linarith

/-- **Left multiplication** `‖b a‖₂² ≤ ‖b‖² ‖a‖₂²`. -/
theorem re_trace_star_mul_mul_le_left (b a : Q) :
    (M.trace (star (b * a) * (b * a))).re ≤ ‖b‖ ^ 2 * (M.trace (star a * a)).re := by
  have hba : Tendsto (fun m : ℕ ↦ M.ι m (M.expect m b * M.expect m a)) atTop (𝓝 (b * a)) :=
    Tendsto.congr (fun m ↦ (map_mul (M.ι m) (M.expect m b) (M.expect m a)).symm)
      ((M.tendsto_ι_expect_nhds b).mul (M.tendsto_ι_expect_nhds a))
  have h1 : Tendsto (fun m : ℕ ↦ hsNormSq (uhfLevel m) (M.expect m b * M.expect m a))
      atTop (𝓝 ((M.trace (star (b * a) * (b * a))).re)) :=
    Tendsto.congr (fun m ↦ by
        show (M.trace (star (M.ι m (M.expect m b * M.expect m a)) *
          M.ι m (M.expect m b * M.expect m a))).re = _
        rw [M.trace_star_ι_mul_ι m, Complex.ofReal_re])
      ((Complex.continuous_re.tendsto (M.trace (star (b * a) * (b * a)))).comp
        ((M.continuous_trace.tendsto (star (b * a) * (b * a))).comp (hba.star.mul hba)))
  have h2 : Tendsto (fun m : ℕ ↦ ‖b‖ ^ 2 * hsNormSq (uhfLevel m) (M.expect m a))
      atTop (𝓝 (‖b‖ ^ 2 * (M.trace (star a * a)).re)) :=
    (M.tendsto_re_trace_star_ι_mul_ι a).const_mul (‖b‖ ^ 2)
  refine le_of_tendsto_of_tendsto' h1 h2 fun m ↦ ?_
  calc hsNormSq (uhfLevel m) (M.expect m b * M.expect m a)
      ≤ ‖M.expect m b‖ ^ 2 * hsNormSq (uhfLevel m) (M.expect m a) :=
        hsNormSq_mul_le_sq_l2_opNorm_mul (uhfLevel m) (M.expect m b) (M.expect m a)
    _ ≤ ‖b‖ ^ 2 * hsNormSq (uhfLevel m) (M.expect m a) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (M.norm_expect_le m b) 2)
          (hsNormSq_nonneg _ _)

/-- **Invariance under the involution** `‖a*‖₂ = ‖a‖₂`, from traciality. -/
theorem re_trace_star_star_mul_star (a : Q) :
    (M.trace (star (star a) * star a)).re = (M.trace (star a * a)).re := by
  rw [star_star, M.trace_mul_comm]

/-- **Right multiplication** `‖a b‖₂² ≤ ‖b‖² ‖a‖₂²`, from the left estimate for
`(a b)* = b* a*`. -/
theorem re_trace_star_mul_mul_le_right (a b : Q) :
    (M.trace (star (a * b) * (a * b))).re ≤ ‖b‖ ^ 2 * (M.trace (star a * a)).re := by
  calc (M.trace (star (a * b) * (a * b))).re
      = (M.trace (star (star (a * b)) * star (a * b))).re :=
        (M.re_trace_star_star_mul_star (a * b)).symm
    _ = (M.trace (star (star b * star a) * (star b * star a))).re := by rw [star_mul]
    _ ≤ ‖star b‖ ^ 2 * (M.trace (star (star a) * star a)).re :=
        M.re_trace_star_mul_mul_le_left (star b) (star a)
    _ = ‖b‖ ^ 2 * (M.trace (star a * a)).re := by
        rw [norm_star, M.re_trace_star_star_mul_star]

/-- **The trace `2`-norm is dominated by the norm**: `‖z‖₂² ≤ ‖z‖²`. -/
theorem re_trace_star_mul_self_le (z : Q) : (M.trace (star z * z)).re ≤ ‖z‖ ^ 2 := by
  calc (M.trace (star z * z)).re ≤ ‖M.trace (star z * z)‖ := Complex.re_le_norm _
    _ ≤ ‖star z * z‖ := M.norm_trace_le _
    _ = ‖z‖ ^ 2 := by rw [CStarRing.norm_star_mul_self, sq]

/-- **Cauchy--Schwarz for the trace**: `|tr_Q(x)|² ≤ ‖x‖₂²`. -/
theorem normSq_trace_le (x : Q) : Complex.normSq (M.trace x) ≤ (M.trace (star x * x)).re :=
  ge_of_tendsto' (M.tendsto_re_trace_star_ι_mul_ι x) fun m ↦ by
    rw [M.trace_eq m]
    exact normSq_normTrace_le_hsNormSq (uhfLevel m) (M.expect m x)

/-- `|tr_Q(x)| ≤ ‖x‖₂`. -/
theorem norm_trace_le_sqrt (x : Q) : ‖M.trace x‖ ≤ Real.sqrt ((M.trace (star x * x)).re) := by
  have h := Real.sqrt_le_sqrt (M.normSq_trace_le x)
  rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)] at h
  exact h

/-- On a building block the trace commutes with the involution. -/
theorem trace_star_ι (m : ℕ) (a : Matrix (uhfLevel m) (uhfLevel m) ℂ) :
    M.trace (star (M.ι m a)) = star (M.trace (M.ι m a)) := by
  rw [← map_star (M.ι m) a, M.trace_ι m, M.trace_ι m, Matrix.star_eq_conjTranspose]
  exact TracialUltraproduct.normTrace_conjTranspose _ _

/-- **The trace of `Q` is self-adjoint**: `tr_Q(x*) = conj tr_Q(x)`. -/
theorem trace_star (x : Q) : M.trace (star x) = star (M.trace x) := by
  have h1 : Tendsto (fun m : ℕ ↦ M.trace (star (M.ι m (M.expect m x)))) atTop
      (𝓝 (M.trace (star x))) :=
    (M.continuous_trace.tendsto (star x)).comp (M.tendsto_ι_expect_nhds x).star
  have h2 : Tendsto (fun m : ℕ ↦ star (M.trace (M.ι m (M.expect m x)))) atTop
      (𝓝 (star (M.trace x))) :=
    ((M.continuous_trace.tendsto x).comp (M.tendsto_ι_expect_nhds x)).star
  have h1' : Tendsto (fun m : ℕ ↦ star (M.trace (M.ι m (M.expect m x)))) atTop
      (𝓝 (M.trace (star x))) :=
    Tendsto.congr (fun m ↦ M.trace_star_ι m (M.expect m x)) h1
  exact tendsto_nhds_unique h1' h2

/-- **`tr_Q(x* x)` is real.** -/
theorem ofReal_re_trace_star_mul_self (x : Q) :
    (((M.trace (star x * x)).re : ℝ) : ℂ) = M.trace (star x * x) := by
  have h1 : Tendsto (fun m : ℕ ↦ ((hsNormSq (uhfLevel m) (M.expect m x) : ℝ) : ℂ)) atTop
      (𝓝 (((M.trace (star x * x)).re : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (M.tendsto_re_trace_star_ι_mul_ι x)
  have h2 : Tendsto (fun m : ℕ ↦ ((hsNormSq (uhfLevel m) (M.expect m x) : ℝ) : ℂ)) atTop
      (𝓝 (M.trace (star x * x))) :=
    Tendsto.congr (fun m ↦ M.trace_star_ι_mul_ι m (M.expect m x))
      (M.tendsto_trace_star_ι_mul_ι x)
  exact tendsto_nhds_unique h1 h2

end UHFModel

end

end GroupApproximation.Full.TWWSchafhauser
