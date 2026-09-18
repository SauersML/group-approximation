import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.UHFUltrapowerTracial
import GroupApproximation.Sofic.UltrafilterLimit

/-!
# The ultratrace on the tracial ultrapower of the universal UHF algebra

Lane `TWWSch3d2Q2` (work order `WO-TWWSch-3d2-Q2`).  Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), through
C. Schafhauser, *A new proof of the Tikuisis--White--Winter theorem*, J. reine
angew. Math. **759** (2020), §4.  The tracial ultrapower `Q^ω` carries the trace
`tr_ω(x) = lim_ω tr_Q(x_n)`.

The limit exists because `|tr_Q(x_n)| ≤ ‖x‖`.  It depends only on the class of
`x` in `Q^ω`, since `|tr_Q(x_n) - tr_Q(y_n)| ≤ ‖x_n - y_n‖₂` (Cauchy--Schwarz,
`UHFModel.norm_trace_le_sqrt`).  It is tracial, self-adjoint and unital, and it
is faithful: `tr_ω(x* x) = 0` exactly when `x = 0` in `Q^ω`, which is the
definition of the trace-`2`-null ideal.

## Main declarations

* `seqQUltratrace`, `seqQTraceSqLimit`;
* `qUltratrace M ω : QTracialUltrapower M ω →ₗ[ℂ] ℂ`, `qUltratrace_mk`;
* `qUltratrace_mul_comm`, `qUltratrace_star`, `qUltratrace_one`;
* `exists_qUltratrace_star_mul_self_eq` (positivity) and
  `qUltratrace_star_mul_self_eq_zero_iff` (faithfulness).
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Filter Topology GroupApproximation.PolarLiftingGeneralCStar

noncomputable section

/-! ## The ultratrace of a bounded sequence -/

section SeqTrace

variable {Q : Type} [CStarAlgebra Q] (M : UHFModel Q) (ω : Ultrafilter ℕ)

theorem exists_tendsto_trace_seq (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    ∃ L : ℂ, Tendsto (fun n ↦ M.trace (a n)) (ω : Filter ℕ) (𝓝 L) :=
  UltrafilterLimit.exists_tendsto_of_bounded ω (C := ‖a‖)
    fun n ↦ (M.norm_trace_le (a n)).trans (boundedCStarSequence_coord_norm_le _ a n)

/-- **`lim_ω tr_Q(x_n)`**, the ultratrace of a bounded sequence. -/
def seqQUltratrace (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) : ℂ :=
  UltrafilterLimit.ulim ω (fun n ↦ M.trace (a n))

theorem tendsto_seqQUltratrace (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    Tendsto (fun n ↦ M.trace (a n)) (ω : Filter ℕ) (𝓝 (seqQUltratrace M ω a)) :=
  UltrafilterLimit.tendsto_ulim (exists_tendsto_trace_seq M ω a)

theorem seqQUltratrace_zero : seqQUltratrace M ω 0 = 0 := by
  refine UltrafilterLimit.ulim_eq ?_
  refine (tendsto_const_nhds (x := (0 : ℂ))).congr fun n ↦ ?_
  exact (map_zero M.trace).symm

theorem seqQUltratrace_add (a b : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    seqQUltratrace M ω (a + b) = seqQUltratrace M ω a + seqQUltratrace M ω b := by
  refine UltrafilterLimit.ulim_eq ?_
  refine ((tendsto_seqQUltratrace M ω a).add (tendsto_seqQUltratrace M ω b)).congr fun n ↦ ?_
  exact (map_add M.trace (a n) (b n)).symm

theorem seqQUltratrace_smul (c : ℂ) (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    seqQUltratrace M ω (c • a) = c * seqQUltratrace M ω a := by
  refine UltrafilterLimit.ulim_eq ?_
  refine ((tendsto_seqQUltratrace M ω a).const_mul c).congr fun n ↦ ?_
  exact (M.trace.map_smul c (a n)).symm

/-- **Traciality along the sequence.** -/
theorem seqQUltratrace_mul_comm (a b : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    seqQUltratrace M ω (a * b) = seqQUltratrace M ω (b * a) := by
  refine UltrafilterLimit.ulim_eq ?_
  refine (tendsto_seqQUltratrace M ω (b * a)).congr fun n ↦ ?_
  exact M.trace_mul_comm (b n) (a n)

theorem seqQUltratrace_star (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    seqQUltratrace M ω (star a) = star (seqQUltratrace M ω a) := by
  refine UltrafilterLimit.ulim_eq ?_
  refine ((continuous_star.tendsto _).comp (tendsto_seqQUltratrace M ω a)).congr fun n ↦ ?_
  exact (M.trace_star (a n)).symm

/-- **The ultratrace sees only the trace-`2`-class**: `|tr_Q(x_n - y_n)| ≤ ‖x_n - y_n‖₂`. -/
theorem seqQUltratrace_eq_of_isQTraceNull_sub {a b : BoundedCStarSequence (fun _ : ℕ ↦ Q)}
    (h : IsQTraceNull M (ω : Filter ℕ) (a - b)) :
    seqQUltratrace M ω a = seqQUltratrace M ω b := by
  rw [IsQTraceNull] at h
  have hsqrt := h.sqrt
  rw [Real.sqrt_zero] at hsqrt
  have hzero : Tendsto (fun n ↦ M.trace (a n) - M.trace (b n)) (ω : Filter ℕ) (𝓝 0) := by
    refine squeeze_zero_norm (fun n ↦ ?_) hsqrt
    show ‖M.trace (a n) - M.trace (b n)‖ ≤
      Real.sqrt ((M.trace (star (a n - b n) * (a n - b n))).re)
    rw [← map_sub M.trace (a n) (b n)]
    exact M.norm_trace_le_sqrt (a n - b n)
  have hlim := (tendsto_seqQUltratrace M ω a).sub (tendsto_seqQUltratrace M ω b)
  have huniq := tendsto_nhds_unique hlim hzero
  linear_combination huniq

theorem exists_tendsto_re_trace_seq (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    ∃ L : ℝ, Tendsto (fun n ↦ (M.trace (star (a n) * a n)).re) (ω : Filter ℕ) (𝓝 L) :=
  UltrafilterLimit.exists_tendsto_of_bounded ω (C := ‖a‖ ^ 2) fun n ↦ by
    show ‖(M.trace (star (a n) * a n)).re‖ ≤ ‖a‖ ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (M.re_trace_star_mul_self_nonneg (a n))]
    exact (M.re_trace_star_mul_self_le (a n)).trans
      (pow_le_pow_left₀ (norm_nonneg _) (boundedCStarSequence_coord_norm_le _ a n) 2)

/-- **`lim_ω ‖x_n‖₂²`**, the squared trace `2`-norm of a bounded sequence. -/
def seqQTraceSqLimit (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) : ℝ :=
  UltrafilterLimit.ulim ω (fun n ↦ (M.trace (star (a n) * a n)).re)

theorem tendsto_seqQTraceSqLimit (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    Tendsto (fun n ↦ (M.trace (star (a n) * a n)).re) (ω : Filter ℕ)
      (𝓝 (seqQTraceSqLimit M ω a)) :=
  UltrafilterLimit.tendsto_ulim (exists_tendsto_re_trace_seq M ω a)

theorem seqQTraceSqLimit_nonneg (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    0 ≤ seqQTraceSqLimit M ω a :=
  UltrafilterLimit.ulim_nonneg (exists_tendsto_re_trace_seq M ω a)
    fun n ↦ M.re_trace_star_mul_self_nonneg (a n)

theorem seqQTraceSqLimit_eq_zero_iff (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    seqQTraceSqLimit M ω a = 0 ↔ IsQTraceNull M (ω : Filter ℕ) a := by
  rw [IsQTraceNull]
  constructor
  · intro h
    have ht := tendsto_seqQTraceSqLimit M ω a
    rw [h] at ht
    exact ht
  · intro h
    exact UltrafilterLimit.ulim_eq h

/-- `tr_ω(x* x) = lim_ω ‖x_n‖₂²`, a nonnegative real number. -/
theorem seqQUltratrace_star_mul_self (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    seqQUltratrace M ω (star a * a) = (seqQTraceSqLimit M ω a : ℂ) := by
  refine UltrafilterLimit.ulim_eq ?_
  refine ((Complex.continuous_ofReal.tendsto _).comp (tendsto_seqQTraceSqLimit M ω a)).congr
    fun n ↦ ?_
  exact M.ofReal_re_trace_star_mul_self (a n)

/-- The sequence ultratrace as an additive map. -/
def seqQUltratraceHom : BoundedCStarSequence (fun _ : ℕ ↦ Q) →+ ℂ where
  toFun := seqQUltratrace M ω
  map_zero' := seqQUltratrace_zero M ω
  map_add' := seqQUltratrace_add M ω

theorem seqQUltratraceHom_apply (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    seqQUltratraceHom M ω a = seqQUltratrace M ω a :=
  rfl

theorem seqQUltratrace_one [Nontrivial Q] : seqQUltratrace M ω 1 = 1 := by
  refine UltrafilterLimit.ulim_eq ?_
  refine (tendsto_const_nhds (x := (1 : ℂ))).congr fun n ↦ ?_
  exact M.trace_one.symm

end SeqTrace

/-! ## The ultratrace on `Q^ω` -/

section QuotientTrace

variable {Q : Type} [CStarAlgebra Q] [Nontrivial Q] (M : UHFModel Q) (ω : Ultrafilter ℕ)

theorem qTracialNullIdeal_le_seqQUltratrace_ker :
    (qTracialNullIdeal M (ω : Filter ℕ)).toAddSubgroup ≤ (seqQUltratraceHom M ω).ker := by
  intro a ha
  rw [AddMonoidHom.mem_ker, seqQUltratraceHom_apply]
  have hsub : IsQTraceNull M (ω : Filter ℕ) (a - 0) := by
    rw [sub_zero]
    exact ha
  rw [seqQUltratrace_eq_of_isQTraceNull_sub M ω hsub, seqQUltratrace_zero]

/-- The ultratrace on `Q^ω`, as an additive map. -/
def qUltratraceAdd : QTracialUltrapower M ω →+ ℂ :=
  QuotientAddGroup.lift (qTracialNullIdeal M (ω : Filter ℕ)).toAddSubgroup
    (seqQUltratraceHom M ω) (qTracialNullIdeal_le_seqQUltratrace_ker M ω)

theorem qUltratraceAdd_mk (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    qUltratraceAdd M ω (qTracialUltrapowerMk M ω a) = seqQUltratrace M ω a :=
  QuotientAddGroup.lift_mk _ _ _

/-- **The ultratrace `tr_ω` on the tracial ultrapower `Q^ω`** (Schafhauser 2020, §4):
the class of `x` goes to `lim_ω tr_Q(x_n)`. -/
def qUltratrace : QTracialUltrapower M ω →ₗ[ℂ] ℂ where
  toFun := qUltratraceAdd M ω
  map_add' := map_add (qUltratraceAdd M ω)
  map_smul' c x := by
    show qUltratraceAdd M ω (c • x) = c * qUltratraceAdd M ω x
    obtain ⟨a, rfl⟩ := qTracialUltrapowerMk_surjective M ω x
    rw [← map_smul (qTracialUltrapowerMk M ω) c a, qUltratraceAdd_mk, qUltratraceAdd_mk,
      seqQUltratrace_smul]

theorem qUltratrace_mk (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    qUltratrace M ω (qTracialUltrapowerMk M ω a) = seqQUltratrace M ω a :=
  qUltratraceAdd_mk M ω a

/-- The ultratrace is unital. -/
theorem qUltratrace_one : qUltratrace M ω 1 = 1 := by
  rw [← map_one (qTracialUltrapowerMk M ω), qUltratrace_mk, seqQUltratrace_one]

/-- **Traciality**: `tr_ω(x y) = tr_ω(y x)`. -/
theorem qUltratrace_mul_comm (x y : QTracialUltrapower M ω) :
    qUltratrace M ω (x * y) = qUltratrace M ω (y * x) := by
  obtain ⟨a, rfl⟩ := qTracialUltrapowerMk_surjective M ω x
  obtain ⟨b, rfl⟩ := qTracialUltrapowerMk_surjective M ω y
  rw [← map_mul (qTracialUltrapowerMk M ω), ← map_mul (qTracialUltrapowerMk M ω),
    qUltratrace_mk, qUltratrace_mk, seqQUltratrace_mul_comm]

/-- The ultratrace is self-adjoint: `tr_ω(x*) = conj tr_ω(x)`. -/
theorem qUltratrace_star (x : QTracialUltrapower M ω) :
    qUltratrace M ω (star x) = star (qUltratrace M ω x) := by
  obtain ⟨a, rfl⟩ := qTracialUltrapowerMk_surjective M ω x
  rw [← map_star (qTracialUltrapowerMk M ω), qUltratrace_mk, qUltratrace_mk,
    seqQUltratrace_star]

theorem qUltratrace_star_mul_self_mk (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    qUltratrace M ω (star (qTracialUltrapowerMk M ω a) * qTracialUltrapowerMk M ω a) =
      (seqQTraceSqLimit M ω a : ℂ) := by
  rw [← map_star (qTracialUltrapowerMk M ω), ← map_mul (qTracialUltrapowerMk M ω),
    qUltratrace_mk, seqQUltratrace_star_mul_self]

/-- **Positivity**: `tr_ω(x* x)` is a nonnegative real number. -/
theorem exists_qUltratrace_star_mul_self_eq (x : QTracialUltrapower M ω) :
    ∃ t : ℝ, 0 ≤ t ∧ qUltratrace M ω (star x * x) = t := by
  obtain ⟨a, rfl⟩ := qTracialUltrapowerMk_surjective M ω x
  exact ⟨seqQTraceSqLimit M ω a, seqQTraceSqLimit_nonneg M ω a,
    qUltratrace_star_mul_self_mk M ω a⟩

/-- **Faithfulness**: `tr_ω(x* x) = 0` exactly when `x = 0` in `Q^ω`. -/
theorem qUltratrace_star_mul_self_eq_zero_iff (x : QTracialUltrapower M ω) :
    qUltratrace M ω (star x * x) = 0 ↔ x = 0 := by
  obtain ⟨a, rfl⟩ := qTracialUltrapowerMk_surjective M ω x
  rw [qUltratrace_star_mul_self_mk, Complex.ofReal_eq_zero, seqQTraceSqLimit_eq_zero_iff,
    qTracialUltrapowerMk_eq_zero_iff]
  exact Iff.rfl

end QuotientTrace

end

end GroupApproximation.Full.TWWSchafhauser
