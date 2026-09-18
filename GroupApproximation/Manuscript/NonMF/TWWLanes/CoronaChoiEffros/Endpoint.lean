import GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.Unitalization
import GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.FormBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# Choi--Effros lifting into matrix-sequence coronas (elementary case)

Lane `nm-tww-08`, endpoint. Let `A` be a separable nuclear C-star algebra, let
`X n` be nonempty finite models, and let `Φ : A → ℓ∞(M_{X n}) / c₀(M_{X n})` be a
unital `⋆`-homomorphism. Then there are unital completely positive maps
`φ n : A → M_{X n}` with `[(φ n a)_n] = Φ a`.

## Truth check

The statement is Brown--Ozawa Thm C.3, specialised to the matrix-sequence corona.
Separability is what makes a single diagonal sequence enough.

## Route (all steps unconditional)

1. `ApproximateLift`. CPAP, followed by the corpus CPC lift from finite-dimensional
   C-star algebras into the corona, gives a CPC `ψ` with `q ∘ ψ ≈ Φ` on finite sets.
2. `Assembly`. Contractive coordinates assemble into bounded sequences. The corona image
   is determined on a dense sequence. `diagonalIndex` does the diagonal selection.
3. `DiagonalLift`. A diagonal selection of coordinates, with thresholds from
   `eventually_coord_norm_lt_of_corona_norm_lt`, gives CPC coordinates that represent
   `Φ` exactly.
4. `Unitalization`. The additive unitalization `φ n + ω(·)(1 - φ n 1)` is UCP. It still
   represents `Φ` because `Φ 1 = 1`.
5. `FormBridge`. cp maps into `M_Y` are form-positive.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace CoronaChoiEffros

open GroupApproximation.CStarExactness
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

/-- **Choi--Effros lifting into matrix-sequence coronas (nm-tww-08).** Every unital
`⋆`-homomorphism from a separable nuclear C-star algebra into the cofinite norm-matrix
corona over nonempty finite models has unital completely positive matrix coordinates.
Their assembled bounded sequence represents the homomorphism. -/
theorem exists_ucpCoordinates_of_starHom_normMatrixCorona (A : Type u) [CStarAlgebra A]
    [TopologicalSpace.SeparableSpace A] (hnuc : IsNuclearCStarAlgebra A)
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (Φ : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n => X n)) :
    ∃ (φ : ∀ n : ℕ, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
      (seq : A → BoundedMatrixSequence (fun n => X n)),
      (∀ n : ℕ, φ n 1 = 1) ∧
        (∀ n : ℕ, Quasidiagonal.IsCompletelyPositiveOnMatrices (X n) ⇑(φ n)) ∧
          (∀ (a : A) (n : ℕ), seq a n = φ n a) ∧
            ∀ a : A, normMatrixCStarCoronaMk (fun n => X n) (seq a) = Φ a := by
  obtain ⟨φ, seq, hone, hcp, hseq, hmk⟩ :=
    exists_ucp_coordinates_lift (X := fun n => X n) hnuc Φ
  exact ⟨φ, seq, hone,
    fun n ↦ isCompletelyPositiveOnMatrices_of_isCompletelyPositive (X n) (φ n) (hcp n),
    hseq, hmk⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.exists_ucpCoordinates_of_starHom_normMatrixCorona

end

end CoronaChoiEffros
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
