import GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift.CoronaLifts
import GroupApproximation.Meta.AxiomGuard

/-!
# Kaplansky-type lifting across the trace-kernel quotient

Lane `nm-tww-07`, the endpoint.  Take a sequence of finite models `X` and a free
ultrafilter `ω`.  The canonical ⋆-homomorphism
`π = normMatrixCStarCoronaToTracialMatrixQuotient X ω hω` from the cofinite norm-matrix
corona `∏ M_{k_n} / ⊕ M_{k_n}` onto the tracial quotient `∏_ω M_{k_n} / (‖·‖₂-null)`
satisfies:

1. `π` is surjective;
2. every `x` with `‖x‖ ≤ 1` has a lift `y` with `‖y‖ ≤ 1`;
3. every self-adjoint `x` with `‖x‖ ≤ 1` has a self-adjoint lift `y` with `‖y‖ ≤ 1`;
4. every unitary `x` has a unitary lift.

`TraceKernelSurjectionStatement` is the conjunction, quantified over all `X` and all free
`ω`, and `manuscriptSentence_traceKernelSurjection` proves it with no hypotheses.
-/

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift

open TracialUltraproduct

/-- **Kaplansky-type lifting across the trace-kernel quotient.** -/
def TraceKernelSurjectionStatement : Prop :=
  ∀ (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite),
    Function.Surjective (normMatrixCStarCoronaToTracialMatrixQuotient X ω hω) ∧
    (∀ x : TracialMatrixQuotient X (ω : Filter ℕ), ‖x‖ ≤ 1 →
      ∃ y : NormMatrixCStarCorona (fun n ↦ X n), ‖y‖ ≤ 1 ∧
        normMatrixCStarCoronaToTracialMatrixQuotient X ω hω y = x) ∧
    (∀ x : TracialMatrixQuotient X (ω : Filter ℕ), IsSelfAdjoint x → ‖x‖ ≤ 1 →
      ∃ y : NormMatrixCStarCorona (fun n ↦ X n), IsSelfAdjoint y ∧ ‖y‖ ≤ 1 ∧
        normMatrixCStarCoronaToTracialMatrixQuotient X ω hω y = x) ∧
    (∀ x ∈ unitary (TracialMatrixQuotient X (ω : Filter ℕ)),
      ∃ y ∈ unitary (NormMatrixCStarCorona (fun n ↦ X n)),
        normMatrixCStarCoronaToTracialMatrixQuotient X ω hω y = x)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift.TraceKernelSurjectionStatement

/-- **The trace-kernel quotient map admits Kaplansky-type lifts.** -/
theorem manuscriptSentence_traceKernelSurjection : TraceKernelSurjectionStatement := by
  intro X _ ω hω
  refine ⟨traceKernel_surjective ω hω, fun x hx ↦ ?_, fun x hsa hx ↦ ?_,
    fun x hu ↦ exists_unitary_lift ω hω x hu⟩
  · obtain ⟨y, hy, hπ⟩ := exists_lift_norm_le ω hω x
    exact ⟨y, hy.trans hx, hπ⟩
  · obtain ⟨y, hysa, hy, hπ⟩ := exists_selfAdjoint_lift_norm_le ω hω x hsa
    exact ⟨y, hysa, hy.trans hx, hπ⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift.manuscriptSentence_traceKernelSurjection

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift.manuscriptSentence_traceKernelSurjection

end GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelLift
