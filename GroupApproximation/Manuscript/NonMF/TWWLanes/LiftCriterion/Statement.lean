import GroupApproximation.Manuscript.NonMF.TWWLanes.LiftCriterion.TraceKernel
import GroupApproximation.Analysis.CStarExactness
import GroupApproximation.Meta.AxiomGuard

/-!
# Lifting criterion for nuclear algebras, over the Choi--Effros interface of `nm-tww-08`

Lane `nm-tww-09`, the endpoint in the shape the cartographer asked for:

```text
A separable nuclear,  Φ : A →⋆ₐ ℓ∞(M_{X n}) / c₀(M_{X n}),  trω(π_ω(Φ a)) = τ(a)
      ⟹  τ is a quasidiagonal trace.
```

The only step that uses nuclearity is the existence of unital completely positive
matrix coordinates for `Φ`. That is the Choi--Effros lifting theorem, specialised to the
matrix-sequence corona, and it is lane `nm-tww-08`
(`GroupApproximation/Manuscript/NonMF/TWWLanes/CoronaChoiEffros/`). This lane is written in
parallel with it and nothing from it is on disk yet. Following the author brief, its
interface is recorded here as `CoronaUCPCoordinatesStatement`. The reduction
`isQuasidiagonalTrace_of_traceKernelLift_of_coronaUCPCoordinates` is proved from it.

## Truth check of the interface

Let `A` be separable, unital and nuclear. Let `Φ : A → ℓ∞(M_{kₙ})/c₀(M_{kₙ})` be a
unital `⋆`-homomorphism with all `kₙ ≥ 1`. Choi--Effros (Brown--Ozawa, Thm C.3) gives a
contractive completely positive lift `ψ = (ψₙ)`. Since `ψ(1) − 1 ∈ c₀`, `ψₙ(1)` is
invertible for `n ≥ N`. There the compressions `ψₙ(1)^{-1/2} ψₙ(·) ψₙ(1)^{-1/2}` are
unital completely positive, and they differ from `ψₙ` by a null sequence, uniformly on
the unit ball. For the finitely many `n < N`, take `a ↦ s(a) · 1` for a state `s`. The
coordinates are contractive, so the assembled sequence is bounded. So the interface is
true. It is a special case of a standard theorem and not an open problem.

The proof content of this file is the one-line application. The criterion itself,
`LiftCriterion.isQuasidiagonalTrace_of_traceKernelLift_ucpCoordinates`, is unconditional.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace LiftCriterion

open Filter Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

/-- **Interface of lane `nm-tww-08`** (Choi--Effros lifting into matrix-sequence
coronas). Every unital `⋆`-homomorphism from a separable nuclear C⋆-algebra into the
cofinite norm-matrix corona over nonempty finite models has unital completely positive
matrix coordinates. Their assembled bounded sequence represents the homomorphism.

It is recorded as a proposition and asserted nowhere. See the module docstring for why
it is true. -/
def CoronaUCPCoordinatesStatement : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] [TopologicalSpace.SeparableSpace A],
    CStarExactness.IsNuclearCStarAlgebra A →
    ∀ (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
      (Φ : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n => X n)),
      ∃ (φ : ∀ n : ℕ, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
        (seq : A → BoundedMatrixSequence (fun n => X n)),
        (∀ n : ℕ, φ n 1 = 1) ∧
        (∀ n : ℕ, IsCompletelyPositiveOnMatrices (X n) ⇑(φ n)) ∧
        (∀ (a : A) (n : ℕ), seq a n = φ n a) ∧
        ∀ a : A, normMatrixCStarCoronaMk (fun n => X n) (seq a) = Φ a

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.LiftCriterion.CoronaUCPCoordinatesStatement

/-- **Lifting criterion (nm-tww-09), over the `nm-tww-08` interface.**  Let `A` be a
separable nuclear C⋆-algebra and `Φ : A → ℓ∞(M_{X n})/c₀(M_{X n})` a unital
`⋆`-homomorphism. Assume the image of `Φ` under the trace-kernel quotient into the tracial
matrix ultraproduct `∏_ω M_{X n}` has ultratrace `τ`. Then `τ` is a quasidiagonal trace. -/
theorem isQuasidiagonalTrace_of_traceKernelLift_of_coronaUCPCoordinates
    (hlift : CoronaUCPCoordinatesStatement.{u})
    {A : Type u} [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]
    (hnuc : CStarExactness.IsNuclearCStarAlgebra A) {τ : A → ℂ}
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (Φ : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n => X n))
    (htr : ∀ a : A, TracialUltraproduct.ultratrace X ω
      (TracialUltraproduct.normMatrixCStarCoronaToTracialMatrixQuotient X ω hω (Φ a))
        = τ a) :
    IsQuasidiagonalTrace τ := by
  obtain ⟨φ, seq, hone, hcp, hseq, hΦ⟩ := hlift A hnuc X Φ
  exact isQuasidiagonalTrace_of_traceKernelLift_ucpCoordinates X ω hω Φ htr φ hone hcp
    seq hseq hΦ

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.LiftCriterion.isQuasidiagonalTrace_of_traceKernelLift_of_coronaUCPCoordinates

end

end LiftCriterion
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
