import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.UHFUltrapowerTrace
import GroupApproximation.Analysis.CStarProductCorona

/-!
# The norm and tracial ultrapowers of the universal UHF algebra

Lane `TWWSch3d2Q2` (work order `WO-TWWSch-3d2-Q2`).  Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), through
C. Schafhauser, *A new proof of the Tikuisis--White--Winter theorem*, J. reine
angew. Math. **759** (2020), §4.  The trace-kernel extension
`0 → J_ω → Q_ω → Q^ω → 0` of Schafhauser's Proposition 4.3 is built from

* the **norm ultrapower** `Q_ω = ℓ^∞(ℕ, Q) / c_ω(ℕ, Q)`, the quotient by the
  sequences with `‖x_n‖ → 0` along `ω`, and
* the **tracial ultrapower** `Q^ω = ℓ^∞(ℕ, Q) / {x | tr_Q(x_n* x_n) → 0 along ω}`.

The norm ultrapower is the general reduced product `CStarProductCorona` of
`Analysis/CStarProductCorona` at the constant family.  For the tracial ultrapower
this file proves that the trace-`2`-null sequences form a closed star-stable
two-sided ideal, using the Hilbert--Schmidt estimates of `UHFUltrapowerTrace`;
the general closed-ideal quotient theorem then makes the quotient a C⋆-algebra.

## Main declarations

* `QNormCorona Q ω`, `qNormCoronaMk`, `qNormCoronaMk_surjective`,
  `qNormCoronaMk_eq_zero_iff`, `norm_qNormCoronaMk`;
* `IsQTraceNull`, `qTracialNullIdeal`, `isClosed_qTracialNullIdeal`;
* `QTracialUltrapower M ω`, `qTracialUltrapowerMk`, `qTracialUltrapowerMk_surjective`,
  `qTracialUltrapowerMk_eq_zero_iff`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Filter Topology GroupApproximation.PolarLiftingGeneralCStar

noncomputable section

/-! ## The norm ultrapower `Q_ω` -/

/-- **The norm ultrapower `Q_ω`** of a unital C⋆-algebra along an ultrafilter:
`ℓ^∞(ℕ, Q)` modulo the sequences whose norms tend to `0` along `ω`
(Schafhauser 2020, §4). -/
abbrev QNormCorona (Q : Type) [CStarAlgebra Q] [Nontrivial Q] (ω : Ultrafilter ℕ) : Type :=
  CStarProductCorona (fun _ : ℕ ↦ Q) (ω : Filter ℕ)

/-- Audit pin: `Q_ω` is a C⋆-algebra. -/
theorem qNormCorona_hasCStarAlgebra (Q : Type) [CStarAlgebra Q] [Nontrivial Q]
    (ω : Ultrafilter ℕ) : Nonempty (CStarAlgebra (QNormCorona Q ω)) :=
  ⟨inferInstance⟩

/-- The quotient map `ℓ^∞(ℕ, Q) → Q_ω`. -/
def qNormCoronaMk (Q : Type) [CStarAlgebra Q] [Nontrivial Q] (ω : Ultrafilter ℕ) :
    BoundedCStarSequence (fun _ : ℕ ↦ Q) →⋆ₐ[ℂ] QNormCorona Q ω :=
  cStarProductCoronaQuotient (fun _ : ℕ ↦ Q) (ω : Filter ℕ)

theorem qNormCoronaMk_apply (Q : Type) [CStarAlgebra Q] [Nontrivial Q] (ω : Ultrafilter ℕ)
    (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    qNormCoronaMk Q ω a =
      Ideal.Quotient.mk (nullCStarSequenceIdeal (fun _ : ℕ ↦ Q) (ω : Filter ℕ)) a :=
  rfl

theorem qNormCoronaMk_surjective (Q : Type) [CStarAlgebra Q] [Nontrivial Q]
    (ω : Ultrafilter ℕ) : Function.Surjective (qNormCoronaMk Q ω) :=
  cStarProductCoronaQuotient_surjective (fun _ : ℕ ↦ Q) (ω : Filter ℕ)

/-- A bounded sequence vanishes in `Q_ω` exactly when its norms tend to `0` along `ω`. -/
theorem qNormCoronaMk_eq_zero_iff (Q : Type) [CStarAlgebra Q] [Nontrivial Q]
    (ω : Ultrafilter ℕ) (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    qNormCoronaMk Q ω a = 0 ↔ Tendsto (fun n ↦ ‖a n‖) (ω : Filter ℕ) (𝓝 0) :=
  cStarProductCoronaQuotient_eq_zero_iff (fun _ : ℕ ↦ Q) (ω : Filter ℕ) a

/-- The norm of `Q_ω` is the `ω`-limit superior of the coordinate norms. -/
theorem norm_qNormCoronaMk (Q : Type) [CStarAlgebra Q] [Nontrivial Q] (ω : Ultrafilter ℕ)
    (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    ‖qNormCoronaMk Q ω a‖ = Filter.limsup (fun n ↦ ‖a n‖) (ω : Filter ℕ) :=
  norm_cStarProductCorona_quotient_eq_limsup (fun _ : ℕ ↦ Q) (ω : Filter ℕ) a

/-! ## The trace-`2`-null sequences -/

section TraceNull

variable {Q : Type} [CStarAlgebra Q] (M : UHFModel Q) (l : Filter ℕ)

/-- A bounded sequence is **trace-`2`-null along `l`** when `tr_Q(x_n* x_n) → 0`. -/
def IsQTraceNull (x : BoundedCStarSequence (fun _ : ℕ ↦ Q)) : Prop :=
  Tendsto (fun n ↦ (M.trace (star (x n) * x n)).re) l (𝓝 0)

theorem IsQTraceNull.zero : IsQTraceNull M l 0 := by
  rw [IsQTraceNull]
  refine tendsto_const_nhds.congr fun n ↦ ?_
  show (0 : ℝ) = (M.trace (star (0 : Q) * 0)).re
  rw [star_zero, zero_mul, map_zero, Complex.zero_re]

theorem IsQTraceNull.add {x y : BoundedCStarSequence (fun _ : ℕ ↦ Q)}
    (hx : IsQTraceNull M l x) (hy : IsQTraceNull M l y) : IsQTraceNull M l (x + y) := by
  rw [IsQTraceNull] at hx hy ⊢
  refine squeeze_zero (fun n ↦ M.re_trace_star_mul_self_nonneg ((x + y) n))
    (fun n ↦ M.re_trace_star_add_mul_add_le (x n) (y n)) ?_
  have h := (hx.const_mul 2).add (hy.const_mul 2)
  rw [mul_zero, add_zero] at h
  exact h

theorem IsQTraceNull.mul_left (b : BoundedCStarSequence (fun _ : ℕ ↦ Q))
    {a : BoundedCStarSequence (fun _ : ℕ ↦ Q)} (ha : IsQTraceNull M l a) :
    IsQTraceNull M l (b * a) := by
  rw [IsQTraceNull] at ha ⊢
  refine squeeze_zero (fun n ↦ M.re_trace_star_mul_self_nonneg ((b * a) n))
    (fun n ↦ (M.re_trace_star_mul_mul_le_left (b n) (a n)).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (boundedCStarSequence_coord_norm_le _ b n) 2)
        (M.re_trace_star_mul_self_nonneg (a n)))) ?_
  have h := ha.const_mul (‖b‖ ^ 2)
  rw [mul_zero] at h
  exact h

theorem IsQTraceNull.mul_right {a : BoundedCStarSequence (fun _ : ℕ ↦ Q)}
    (ha : IsQTraceNull M l a) (b : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    IsQTraceNull M l (a * b) := by
  rw [IsQTraceNull] at ha ⊢
  refine squeeze_zero (fun n ↦ M.re_trace_star_mul_self_nonneg ((a * b) n))
    (fun n ↦ (M.re_trace_star_mul_mul_le_right (a n) (b n)).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (boundedCStarSequence_coord_norm_le _ b n) 2)
        (M.re_trace_star_mul_self_nonneg (a n)))) ?_
  have h := ha.const_mul (‖b‖ ^ 2)
  rw [mul_zero] at h
  exact h

theorem IsQTraceNull.star {a : BoundedCStarSequence (fun _ : ℕ ↦ Q)}
    (ha : IsQTraceNull M l a) : IsQTraceNull M l (Star.star a) := by
  rw [IsQTraceNull] at ha ⊢
  exact ha.congr fun n ↦ (M.re_trace_star_star_mul_star (a n)).symm

/-! ## The ideal and the tracial ultrapower

From here on the unital ring structure of `ℓ^∞(ℕ, Q)` is used, which mathlib
builds under `NormOneClass Q`, that is, under nontriviality of `Q`. -/

variable [Nontrivial Q]

/-- **The ideal of trace-`2`-null sequences.** -/
def qTracialNullIdeal : Ideal (BoundedCStarSequence (fun _ : ℕ ↦ Q)) where
  carrier := {a | IsQTraceNull M l a}
  zero_mem' := IsQTraceNull.zero M l
  add_mem' := IsQTraceNull.add M l
  smul_mem' := fun b _ ha ↦ IsQTraceNull.mul_left M l b ha

instance qTracialNullIdeal_isTwoSided : (qTracialNullIdeal M l).IsTwoSided where
  mul_mem_of_left := fun b ha ↦ IsQTraceNull.mul_right M l ha b

theorem mem_qTracialNullIdeal_iff (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    a ∈ qTracialNullIdeal M l ↔ IsQTraceNull M l a :=
  Iff.rfl

theorem qTracialNullIdeal_star_mem {a : BoundedCStarSequence (fun _ : ℕ ↦ Q)}
    (ha : a ∈ qTracialNullIdeal M l) : star a ∈ qTracialNullIdeal M l :=
  IsQTraceNull.star M l ha

instance qTracialNullIdeal_isStarStable : CStarTensor.IsStarStable (qTracialNullIdeal M l) where
  star_mem := qTracialNullIdeal_star_mem M l

/-- **The trace-`2`-null ideal is norm closed**, from `‖u + v‖₂² ≤ 2‖u‖₂² + 2‖v‖₂²`
and `‖z‖₂ ≤ ‖z‖`. -/
theorem isClosed_qTracialNullIdeal :
    IsClosed (qTracialNullIdeal M l : Set (BoundedCStarSequence (fun _ : ℕ ↦ Q))) := by
  apply IsSeqClosed.isClosed
  intro s a hs hsa
  change IsQTraceNull M l a
  rw [IsQTraceNull]
  refine TracialUltraproduct.tendsto_zero_of_forall_eventually_lt
    (fun n ↦ M.re_trace_star_mul_self_nonneg (a n)) ?_
  intro ε hε
  have hquarter : (0 : ℝ) < ε / 4 := by linarith
  have hroot : (0 : ℝ) < Real.sqrt (ε / 4) := Real.sqrt_pos.mpr hquarter
  obtain ⟨k, hk⟩ := ((Metric.tendsto_nhds.mp hsa) _ hroot).exists
  have hd : ‖a - s k‖ < Real.sqrt (ε / 4) := by
    rw [← dist_eq_norm, dist_comm]
    exact hk
  have hsq : ‖a - s k‖ ^ 2 < ε / 4 := by
    have hrt : Real.sqrt (ε / 4) ^ 2 = ε / 4 := Real.sq_sqrt hquarter.le
    have hlt : ‖a - s k‖ * ‖a - s k‖ < Real.sqrt (ε / 4) * Real.sqrt (ε / 4) :=
      mul_self_lt_mul_self (norm_nonneg _) hd
    rw [pow_two] at hrt ⊢
    linarith
  have hsk : IsQTraceNull M l (s k) := hs k
  rw [IsQTraceNull] at hsk
  filter_upwards [TracialUltraproduct.eventually_lt_of_tendsto_zero hsk hquarter] with n hn
  have hcoord : ‖a n - s k n‖ ≤ ‖a - s k‖ :=
    boundedCStarSequence_coord_norm_le _ (a - s k) n
  have hrw : (a n - s k n) + s k n = a n := by abel
  have hstep : (M.trace (star (a n) * a n)).re ≤
      2 * (M.trace (star (a n - s k n) * (a n - s k n))).re +
        2 * (M.trace (star (s k n) * s k n)).re := by
    have h := M.re_trace_star_add_mul_add_le (a n - s k n) (s k n)
    rwa [hrw] at h
  have hfirst : (M.trace (star (a n - s k n) * (a n - s k n))).re ≤ ‖a - s k‖ ^ 2 := by
    refine (M.re_trace_star_mul_self_le (a n - s k n)).trans ?_
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self (norm_nonneg (a n - s k n)) hcoord
  linarith

instance qTracialNullIdeal_isClosed :
    IsClosed (qTracialNullIdeal M l : Set (BoundedCStarSequence (fun _ : ℕ ↦ Q))) :=
  isClosed_qTracialNullIdeal M l

end TraceNull

/-- **The tracial ultrapower `Q^ω`** of the universal UHF algebra: `ℓ^∞(ℕ, Q)`
modulo the sequences with `tr_Q(x_n* x_n) → 0` along `ω` (Schafhauser 2020, §4). -/
abbrev QTracialUltrapower {Q : Type} [CStarAlgebra Q] [Nontrivial Q] (M : UHFModel Q)
    (ω : Ultrafilter ℕ) : Type :=
  BoundedCStarSequence (fun _ : ℕ ↦ Q) ⧸ qTracialNullIdeal M (ω : Filter ℕ)

/-- Audit pin: `Q^ω` is a C⋆-algebra. -/
theorem qTracialUltrapower_hasCStarAlgebra {Q : Type} [CStarAlgebra Q] [Nontrivial Q]
    (M : UHFModel Q) (ω : Ultrafilter ℕ) : Nonempty (CStarAlgebra (QTracialUltrapower M ω)) :=
  ⟨inferInstance⟩

/-- The quotient map `ℓ^∞(ℕ, Q) → Q^ω`. -/
def qTracialUltrapowerMk {Q : Type} [CStarAlgebra Q] [Nontrivial Q] (M : UHFModel Q)
    (ω : Ultrafilter ℕ) : BoundedCStarSequence (fun _ : ℕ ↦ Q) →⋆ₐ[ℂ] QTracialUltrapower M ω :=
  CStarTensor.quotientStarMk (qTracialNullIdeal M (ω : Filter ℕ))

theorem qTracialUltrapowerMk_apply {Q : Type} [CStarAlgebra Q] [Nontrivial Q]
    (M : UHFModel Q) (ω : Ultrafilter ℕ) (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    qTracialUltrapowerMk M ω a = Ideal.Quotient.mk (qTracialNullIdeal M (ω : Filter ℕ)) a :=
  rfl

theorem qTracialUltrapowerMk_surjective {Q : Type} [CStarAlgebra Q] [Nontrivial Q]
    (M : UHFModel Q) (ω : Ultrafilter ℕ) : Function.Surjective (qTracialUltrapowerMk M ω) :=
  Ideal.Quotient.mk_surjective

/-- A bounded sequence vanishes in `Q^ω` exactly when it is trace-`2`-null along `ω`. -/
theorem qTracialUltrapowerMk_eq_zero_iff {Q : Type} [CStarAlgebra Q] [Nontrivial Q]
    (M : UHFModel Q) (ω : Ultrafilter ℕ) (a : BoundedCStarSequence (fun _ : ℕ ↦ Q)) :
    qTracialUltrapowerMk M ω a = 0 ↔
      Tendsto (fun n ↦ (M.trace (star (a n) * a n)).re) (ω : Filter ℕ) (𝓝 0) := by
  rw [qTracialUltrapowerMk_apply, Ideal.Quotient.eq_zero_iff_mem]
  rfl

end

end GroupApproximation.Full.TWWSchafhauser
