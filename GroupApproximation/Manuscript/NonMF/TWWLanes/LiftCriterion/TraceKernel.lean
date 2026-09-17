import GroupApproximation.Manuscript.NonMF.TWWLanes.LiftCriterion.Coordinates
import GroupApproximation.Analysis.GoldbringHartRoute
import GroupApproximation.Meta.AxiomGuard

/-!
# Lifting criterion through the trace kernel

Lane `nm-tww-09`, the homomorphism form.

The data is a unital `⋆`-homomorphism `Φ : A → ℓ∞(M_{X n}) / c₀(M_{X n})` into the
cofinite norm-matrix corona. The trace clause is stated *without choosing a lift*. The
canonical quotient by the trace kernel,
`TracialUltraproduct.normMatrixCStarCoronaToTracialMatrixQuotient X ω hω`
(`Analysis/GoldbringHartRoute.lean`), takes the corona to the tracial matrix ultraproduct
`∏_ω M_{X n}`. The ultratrace of `Φ a` there is `τ a`:

```text
trω (π_ω (Φ a)) = τ a,     that is,     lim_ω tr_{X n}(x n) = τ a   for every lift x of Φ a.
```

`tendsto_normTrace_of_traceKernelLift` proves the second form from the first, for *every*
lift `x`. So the clause does not depend on the lift. The endpoint
`isQuasidiagonalTrace_of_traceKernelLift_ucpCoordinates` then assumes ucp coordinates
`φₙ` of `Φ` (what Choi--Effros supplies for nuclear `A`, lane `nm-tww-08`). It concludes
that `τ` is quasidiagonal through `LiftCriterion.Coordinates`.

Nothing in this file is conditional.
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

variable {A : Type u} [CStarAlgebra A]

/-- **The trace clause is lift-independent.**  Suppose the ultratrace of the image of
`Φ a` in the tracial matrix ultraproduct is `τ a`. Then the normalized traces of *every*
lift `x` of `Φ a` converge to `τ a` along `ω`. -/
theorem tendsto_normTrace_of_traceKernelLift {τ : A → ℂ}
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (Φ : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n => X n))
    (htr : ∀ a : A, TracialUltraproduct.ultratrace X ω
      (TracialUltraproduct.normMatrixCStarCoronaToTracialMatrixQuotient X ω hω (Φ a))
        = τ a)
    (a : A) (x : BoundedMatrixSequence (fun n => X n))
    (hx : normMatrixCStarCoronaMk (fun n => X n) x = Φ a) :
    Tendsto (fun n => normTrace (X n) (x n)) (ω : Filter ℕ) (nhds (τ a)) := by
  have h := TracialUltraproduct.tendsto_seqUltratrace X ω x
  have e : TracialUltraproduct.seqUltratrace X ω x = τ a := by
    rw [← htr a, ← hx,
      TracialUltraproduct.normMatrixCStarCoronaToTracialMatrixQuotient_mk,
      TracialUltraproduct.ultratrace_mk]
  rwa [e] at h

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.LiftCriterion.tendsto_normTrace_of_traceKernelLift

/-- **Lifting criterion, unconditional coordinate form.**  Let `A` be separable and
`Φ : A → ℓ∞(M_{X n})/c₀(M_{X n})` a unital `⋆`-homomorphism. Assume its image in the
tracial matrix ultraproduct `∏_ω M_{X n}` has ultratrace `τ`. Assume also that `Φ` has
unital completely positive matrix coordinates `φₙ`, with `[(φₙ a)ₙ] = Φ a`. Then `τ` is
a quasidiagonal trace.

The homomorphism property of `Φ` gives exact multiplicativity of the coordinates in the
corona. The trace clause is transported by `tendsto_normTrace_of_traceKernelLift`. -/
theorem isQuasidiagonalTrace_of_traceKernelLift_ucpCoordinates
    [TopologicalSpace.SeparableSpace A] {τ : A → ℂ}
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (Φ : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n => X n))
    (htr : ∀ a : A, TracialUltraproduct.ultratrace X ω
      (TracialUltraproduct.normMatrixCStarCoronaToTracialMatrixQuotient X ω hω (Φ a))
        = τ a)
    (φ : ∀ n : ℕ, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hone : ∀ n : ℕ, φ n 1 = 1)
    (hcp : ∀ n : ℕ, IsCompletelyPositiveOnMatrices (X n) ⇑(φ n))
    (seq : A → BoundedMatrixSequence (fun n => X n))
    (hseq : ∀ (a : A) (n : ℕ), seq a n = φ n a)
    (hlift : ∀ a : A, normMatrixCStarCoronaMk (fun n => X n) (seq a) = Φ a) :
    IsQuasidiagonalTrace τ := by
  refine isQuasidiagonalTrace_of_coronaCoordinates X ω hω φ hone hcp seq hseq ?_ ?_
  · intro a b
    rw [hlift a, hlift b, hlift (a * b), map_mul]
  · intro a
    refine (tendsto_normTrace_of_traceKernelLift X ω hω Φ htr a (seq a)
      (hlift a)).congr ?_
    intro n
    rw [hseq]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.LiftCriterion.isQuasidiagonalTrace_of_traceKernelLift_ucpCoordinates

end

end LiftCriterion
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
