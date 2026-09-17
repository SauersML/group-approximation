import GroupApproximation.Analysis.QuasidiagonalTraceLocal
import GroupApproximation.Analysis.QuasidiagonalMatricialTrace
import GroupApproximation.Meta.AxiomGuard

/-!
# Averages of characters are local quasidiagonal models

Given characters `χ₁, …, χ_N : A →⋆ₐ ℂ`, the diagonal map
`a ↦ diag(χ₁ a, …, χ_N a) : A → M_N(ℂ)` is a unital `⋆`-homomorphism. So it is completely
positive in the form sense (`Quasidiagonal.isCompletelyPositiveOnMatrices_starAlgHom`), its
multiplicative defect is identically zero, and its normalized trace is the average
`N⁻¹ ∑ᵢ χᵢ a`.

So a functional `τ` that agrees on finite sets, up to `ε`, with averages of characters
satisfies `Quasidiagonal.IsLocallyQuasidiagonalTrace τ`. This is
`isLocallyQuasidiagonalTrace_of_characterAverages`. It is unconditional and needs neither
commutativity nor separability.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace CommutativeQD

open Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- The finite model `Fin N`. -/
abbrev avgModel (N : ℕ) : FiniteModel := ⟨Fin N, inferInstance, inferInstance⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.avgModel

theorem card_avgModel (N : ℕ) : Fintype.card (avgModel N) = N := by
  show Fintype.card (Fin N) = N
  exact Fintype.card_fin N

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.card_avgModel

/-- The diagonal `⋆`-homomorphism `a ↦ diag(χᵢ a)` built from a family of characters. -/
def diagonalStarAlgHom (Y : FiniteModel) (χ : Y → (A →⋆ₐ[ℂ] ℂ)) :
    A →⋆ₐ[ℂ] Matrix Y Y ℂ where
  toFun a := Matrix.diagonal fun i ↦ χ i a
  map_one' := by
    show Matrix.diagonal (fun i ↦ χ i 1) = 1
    have h : (fun i ↦ χ i 1) = fun _ ↦ (1 : ℂ) := funext fun i ↦ map_one (χ i)
    exact (congrArg Matrix.diagonal h).trans Matrix.diagonal_one
  map_mul' a b := by
    show Matrix.diagonal (fun i ↦ χ i (a * b)) =
      Matrix.diagonal (fun i ↦ χ i a) * Matrix.diagonal (fun i ↦ χ i b)
    have h : (fun i ↦ χ i (a * b)) = fun i ↦ χ i a * χ i b :=
      funext fun i ↦ map_mul (χ i) a b
    exact (congrArg Matrix.diagonal h).trans
      (Matrix.diagonal_mul_diagonal (fun i ↦ χ i a) (fun i ↦ χ i b)).symm
  map_zero' := by
    show Matrix.diagonal (fun i ↦ χ i 0) = 0
    have h : (fun i ↦ χ i 0) = fun _ ↦ (0 : ℂ) := funext fun i ↦ map_zero (χ i)
    exact (congrArg Matrix.diagonal h).trans Matrix.diagonal_zero
  map_add' a b := by
    show Matrix.diagonal (fun i ↦ χ i (a + b)) =
      Matrix.diagonal (fun i ↦ χ i a) + Matrix.diagonal (fun i ↦ χ i b)
    have h : (fun i ↦ χ i (a + b)) = fun i ↦ χ i a + χ i b :=
      funext fun i ↦ map_add (χ i) a b
    exact (congrArg Matrix.diagonal h).trans
      (Matrix.diagonal_add (fun i ↦ χ i a) (fun i ↦ χ i b)).symm
  commutes' c := by
    show Matrix.diagonal (fun i ↦ χ i (algebraMap ℂ A c)) = algebraMap ℂ (Matrix Y Y ℂ) c
    rw [Matrix.algebraMap_eq_diagonal]
    have h : (fun i ↦ χ i (algebraMap ℂ A c)) = algebraMap ℂ (Y → ℂ) c :=
      funext fun i ↦ AlgHomClass.commutes (χ i) c
    exact congrArg Matrix.diagonal h
  map_star' a := by
    show Matrix.diagonal (fun i ↦ χ i (star a)) = star (Matrix.diagonal fun i ↦ χ i a)
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    exact congrArg Matrix.diagonal (funext fun i ↦ map_star (χ i) a)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.diagonalStarAlgHom

theorem diagonalStarAlgHom_apply (Y : FiniteModel) (χ : Y → (A →⋆ₐ[ℂ] ℂ)) (a : A) :
    diagonalStarAlgHom Y χ a = Matrix.diagonal fun i ↦ χ i a :=
  rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.diagonalStarAlgHom_apply

/-- The normalized trace of the diagonal model is the average of the characters. -/
theorem normTrace_diagonalStarAlgHom (N : ℕ) (χ : Fin N → (A →⋆ₐ[ℂ] ℂ)) (a : A) :
    normTrace (avgModel N) (diagonalStarAlgHom (avgModel N) χ a) =
      (N : ℂ)⁻¹ * ∑ i, χ i a := by
  have htr : Matrix.trace (Matrix.diagonal fun i : Fin N ↦ χ i a) = ∑ i, χ i a :=
    Matrix.trace_diagonal _
  have hcard : (Fintype.card (avgModel N) : ℂ) = N := by
    rw [card_avgModel]
  show Matrix.trace (Matrix.diagonal fun i : Fin N ↦ χ i a) /
      (Fintype.card (avgModel N) : ℂ) = _
  rw [htr, hcard, div_eq_inv_mul]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.normTrace_diagonalStarAlgHom

/-- **Averages of characters give local quasidiagonal models.** Suppose that for every
finite `F ⊆ A` and `ε > 0` some average of characters agrees with `τ` on `F` up to `ε`.
Then `τ` is locally quasidiagonal. The model is the diagonal `⋆`-homomorphism, which is
unital and completely positive and has zero multiplicative defect. -/
theorem isLocallyQuasidiagonalTrace_of_characterAverages {τ : A → ℂ}
    (h : ∀ (F : Finset A) (ε : ℝ), 0 < ε →
      ∃ (N : ℕ) (χ : Fin N → (A →⋆ₐ[ℂ] ℂ)),
        ∀ a ∈ F, ‖τ a - (N : ℂ)⁻¹ * ∑ i, χ i a‖ ≤ ε) :
    IsLocallyQuasidiagonalTrace τ := by
  intro F ε hε
  obtain ⟨N, χ, hχ⟩ := h F ε hε
  refine ⟨avgModel N,
    (diagonalStarAlgHom (avgModel N) χ : A →ₗ[ℂ] Matrix (avgModel N) (avgModel N) ℂ),
    ?_, ?_, ?_, ?_⟩
  · show diagonalStarAlgHom (avgModel N) χ 1 = 1
    rw [map_one]
  · exact isCompletelyPositiveOnMatrices_starAlgHom (avgModel N)
      (diagonalStarAlgHom (avgModel N) χ)
  · intro x _ y _
    show ‖diagonalStarAlgHom (avgModel N) χ (x * y) -
        diagonalStarAlgHom (avgModel N) χ x * diagonalStarAlgHom (avgModel N) χ y‖ ≤ ε
    rw [map_mul, sub_self, norm_zero]
    exact hε.le
  · intro x hx
    show ‖τ x - normTrace (avgModel N) (diagonalStarAlgHom (avgModel N) χ x)‖ ≤ ε
    rw [normTrace_diagonalStarAlgHom]
    exact hχ x hx

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.isLocallyQuasidiagonalTrace_of_characterAverages

end

end CommutativeQD
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
