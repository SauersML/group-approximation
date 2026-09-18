import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplit
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionTraceTransfer

/-!
# Absorbing extensions with vanishing class: the matrix-level lift

Lane `TWWSchafhauser-3d4`, work order `WO-TWWSchafhauser-3d-4`, specialized for lane 3d1.
C. Schafhauser, *A new proof of the Tikuisis–White–Winter theorem*, J. reine angew. Math. 759
(2020), §5; G. A. Elliott and D. Kucerovsky, Pacific J. Math. 198 (2001).

The abstract theorem `exists_lift_conj_of_isAbsorbingBusby_of_isStablyTrivialBusby` is applied
to the trace-kernel quotient `π = traceKernelQuotient X ω hω : Q_ω → Q^ω`.

* `exists_traceKernelLift_of_isAbsorbingBusby_of_isStablyTrivialBusby`: a unital
  `⋆`-homomorphism `ψ : A → Q_ω` and a unitary `u ∈ Q^ω` with `π ∘ ψ = Ad u ∘ θ`. If `θ`
  induces `τ`, then so does `ψ` through the `ω`-corona.
* `tendsto_normTrace_of_isAbsorbingBusby_of_isStablyTrivialBusby`: for every representative
  sequence `a` of `ψ s`, `tr_{X n}(a n) → τ s` along `ω`.

The trace transport reuses 3d1's `ObstructionTraceTransfer`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Filter

section TraceKernel

variable {A : Type*} [CStarAlgebra A]
variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ)
  (hω : (ω : Filter ℕ) ≤ cofinite)

/-- **The trace-kernel lift from absorption** (Schafhauser 2020, §5). Let `θ : A → Q^ω` absorb
the class `𝒯` and be stably trivial for the trace-kernel quotient. Then there is a unital
`⋆`-homomorphism `ψ : A → Q_ω` and a unitary `u ∈ Q^ω` with `π (ψ a) = u θ(a) u⋆`. If `θ`
induces `τ`, then so does `ψ` through the `ω`-corona. -/
theorem exists_traceKernelLift_of_isAbsorbingBusby_of_isStablyTrivialBusby
    (P : BusbyCuntzPair (TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ)))
    (𝒯 : Set (A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier)))
    (θ : A →⋆ₐ[ℂ] TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ))
    (habs : IsAbsorbingBusby (traceKernelQuotient X ω hω) P 𝒯 θ)
    (hst : IsStablyTrivialBusby (traceKernelQuotient X ω hω) P 𝒯 θ) {τ : A → ℂ}
    (hθτ : ∀ a, TracialUltraproduct.ultratrace X ω (θ a) = τ a) :
    ∃ ψ : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier),
      ∃ u ∈ unitary (TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ)),
        (∀ a, traceKernelQuotient X ω hω (ψ a) = u * θ a * star u) ∧
        ∀ a, TracialUltraproduct.ultratrace X ω
          (filterCoronaToTracialQuotient X (ω : Filter ℕ) (normCoronaToFilterCorona X ω hω (ψ a)))
            = τ a := by
  obtain ⟨ψ, u, hu, h⟩ := exists_lift_conj_of_isAbsorbingBusby_of_isStablyTrivialBusby habs hst
  exact ⟨ψ, u, hu, h, fun a =>
    ultratrace_traceKernelQuotient_conj X ω hω (Unitary.star_mul_self_of_mem hu) (h a) (hθτ a)⟩

/-- **Traces of the lift are limits of matrix traces** (Schafhauser 2020, §5): `τ = lim_ω tr ∘ ψ`
for every representative sequence of `ψ`. -/
theorem tendsto_normTrace_of_isAbsorbingBusby_of_isStablyTrivialBusby
    (P : BusbyCuntzPair (TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ)))
    (𝒯 : Set (A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier)))
    (θ : A →⋆ₐ[ℂ] TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ))
    (habs : IsAbsorbingBusby (traceKernelQuotient X ω hω) P 𝒯 θ)
    (hst : IsStablyTrivialBusby (traceKernelQuotient X ω hω) P 𝒯 θ) {τ : A → ℂ}
    (hθτ : ∀ a, TracialUltraproduct.ultratrace X ω (θ a) = τ a) :
    ∃ ψ : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier),
      ∃ u ∈ unitary (TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ)),
        (∀ a, traceKernelQuotient X ω hω (ψ a) = u * θ a * star u) ∧
        ∀ s (a : TracialUltraproduct.ModelBoundedSequence X),
          filterMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (ω : Filter ℕ) a
              = normCoronaToFilterCorona X ω hω (ψ s) →
            Tendsto (fun n ↦ ‖τ s - normTrace (X n) (a n)‖) (ω : Filter ℕ) (nhds 0) := by
  obtain ⟨ψ, u, hu, h, htr⟩ :=
    exists_traceKernelLift_of_isAbsorbingBusby_of_isStablyTrivialBusby X ω hω P 𝒯 θ habs hst hθτ
  exact ⟨ψ, u, hu, h, fun s a ha => tendsto_norm_sub_normTrace_of_ultratrace_eq X ω a ha (htr s)⟩

end TraceKernel

end GroupApproximation.Full.TWWSchafhauser
