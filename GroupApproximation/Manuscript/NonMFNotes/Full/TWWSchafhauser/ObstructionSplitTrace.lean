import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplitCorona
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionTraceTransfer

/-!
# Absorbing extensions with vanishing class: the matrix-level lift

Lane `TWWSchafhauser-3d4`, work order `WO-TWWSchafhauser-3d-4`, specialized for lane 3d1.
C. Schafhauser, *A new proof of the Tikuisis–White–Winter theorem*, J. reine angew. Math. 759
(2020), §5; G. A. Elliott and D. Kucerovsky, Pacific J. Math. 198 (2001).

The trace-kernel extension `0 → J → Q_ω → Q^ω → 0` (`π = traceKernelQuotient X ω hω`) is presented
by a corona square `π' ∘ ι = κ ∘ π` into a corona `C` of `J`. The Cuntz pair and absorption live
in `C`, not in `Q^ω`: a tracial quotient has no Cuntz pair (3c, `ExtensionFiniteTrace`).
`isTrivialBusby_of_corona` then gives a genuine lift.

* `exists_traceKernelLift_of_corona`: a unital `⋆`-homomorphism `ψ : A → Q_ω` with
  `π ∘ ψ = θ`. If `θ` induces `τ`, then so does `ψ` through the `ω`-corona.
* `tendsto_normTrace_of_corona`: for every representative sequence `a` of `ψ s`,
  `tr_{X n}(a n) → τ s` along `ω`.

The trace transport reuses 3d1's `ObstructionTraceTransfer`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Filter

section TraceKernel

variable {A : Type*} [CStarAlgebra A]
variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ)
  (hω : (ω : Filter ℕ) ≤ cofinite)
variable {M : Type*} [Ring M] [StarRing M] [Algebra ℂ M]
variable {C : Type*} [Ring C] [StarRing C] [Algebra ℂ C]

/-- **The trace-kernel lift from absorption in the corona** (Schafhauser 2020, §5). Present the
trace-kernel extension by a corona square `π' ∘ ι = κ ∘ traceKernelQuotient`. If the Busby map
`κ ∘ θ` is strongly absorbing and strongly stably trivial, then `θ : A → Q^ω` lifts to a unital
`⋆`-homomorphism `ψ : A → Q_ω`. If `θ` induces `τ`, then so does `ψ` through the `ω`-corona. -/
theorem exists_traceKernelLift_of_corona
    {ι : NormMatrixCStarCorona (fun n ↦ (X n).carrier) →⋆ₐ[ℂ] M} {π' : M →⋆ₐ[ℂ] C}
    {κ : TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ) →⋆ₐ[ℂ] C}
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (hcomm : ∀ e, π' (ι e) = κ (traceKernelQuotient X ω hω e))
    (hpull : ∀ m q, π' m = κ q → ∃ e, ι e = m) {P : BusbyCuntzPair C} {𝒯 : Set (A →⋆ₐ[ℂ] M)}
    {θ : A →⋆ₐ[ℂ] TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ)}
    (habs : IsStronglyAbsorbingBusby π' P 𝒯 (κ.comp θ))
    (hst : IsStronglyStablyTrivialBusby π' P 𝒯 (κ.comp θ)) {τ : A → ℂ}
    (hθτ : ∀ a, TracialUltraproduct.ultratrace X ω (θ a) = τ a) :
    ∃ ψ : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier),
      (∀ a, traceKernelQuotient X ω hω (ψ a) = θ a) ∧
        ∀ a, TracialUltraproduct.ultratrace X ω
          (filterCoronaToTracialQuotient X (ω : Filter ℕ) (normCoronaToFilterCorona X ω hω (ψ a)))
            = τ a := by
  obtain ⟨ψ, hψ⟩ := isTrivialBusby_of_corona hι hκ hcomm hpull habs hst
  exact ⟨ψ, hψ, fun a => by
    rw [filterCoronaToTracialQuotient_comp_normCoronaToFilterCorona, hψ a, hθτ a]⟩

/-- **Traces of the lift are limits of matrix traces** (Schafhauser 2020, §5): `τ = lim_ω tr ∘ ψ`
for every representative sequence of `ψ`. -/
theorem tendsto_normTrace_of_corona
    {ι : NormMatrixCStarCorona (fun n ↦ (X n).carrier) →⋆ₐ[ℂ] M} {π' : M →⋆ₐ[ℂ] C}
    {κ : TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ) →⋆ₐ[ℂ] C}
    (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (hcomm : ∀ e, π' (ι e) = κ (traceKernelQuotient X ω hω e))
    (hpull : ∀ m q, π' m = κ q → ∃ e, ι e = m) {P : BusbyCuntzPair C} {𝒯 : Set (A →⋆ₐ[ℂ] M)}
    {θ : A →⋆ₐ[ℂ] TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ)}
    (habs : IsStronglyAbsorbingBusby π' P 𝒯 (κ.comp θ))
    (hst : IsStronglyStablyTrivialBusby π' P 𝒯 (κ.comp θ)) {τ : A → ℂ}
    (hθτ : ∀ a, TracialUltraproduct.ultratrace X ω (θ a) = τ a) :
    ∃ ψ : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier),
      (∀ a, traceKernelQuotient X ω hω (ψ a) = θ a) ∧
        ∀ s (a : TracialUltraproduct.ModelBoundedSequence X),
          filterMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (ω : Filter ℕ) a
              = normCoronaToFilterCorona X ω hω (ψ s) →
            Tendsto (fun n ↦ ‖τ s - normTrace (X n) (a n)‖) (ω : Filter ℕ) (nhds 0) := by
  obtain ⟨ψ, hψ, htr⟩ := exists_traceKernelLift_of_corona X ω hω hι hκ hcomm hpull habs hst hθτ
  exact ⟨ψ, hψ, fun s a ha => tendsto_norm_sub_normTrace_of_ultratrace_eq X ω a ha (htr s)⟩

end TraceKernel

end GroupApproximation.Full.TWWSchafhauser
