import GroupApproximation.Analysis.BlackadarKirchbergFiniteDimensionalArvesonExtension
import GroupApproximation.Analysis.NonUnitalMFSupportCornerEmbedding
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite-dimensional UCP observables on an MF algebra extend to its corona

The Blackadar--Kirchberg upward-map construction first replaces a possibly
nonunital MF representation by its faithful unital support-corner model.  A
finite-dimensional UCP map on the source can then be extended to the entire
matrix corona.  This module packages those two unconditional steps together.

For a repaired nuclear approximation, the map called `observable` below is
the finite-dimensional downward map.  The resulting `extension` is therefore
the exact finite-dimensional CP approximate inverse on the corona side; only
its later localization to finitely many matrix coordinates remains separate.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

open GroupApproximation.CStarExactness

noncomputable section

universe u w

variable {A : Type u} {D : Type w}
  [CStarAlgebra A] [CStarAlgebra D]
  [Nontrivial A] [Nontrivial D]
  [FiniteDimensional ℂ D]

/-- An MF algebra admits a faithful unital matrix-corona representation across
which every finite-dimensional UCP map extends UCP-exactly. -/
theorem exists_unitalMFEmbedding_with_ucp_extension
    (hMF : IsMFAlgebra A)
    (observable : A →ₗ[ℂ] D)
    (hobservableCP : IsCompletelyPositive observable)
    (hobservableOne : observable 1 = 1) :
    ∃ (X : ℕ → FiniteModel) (hX : ∀ n, Nonempty (X n)),
      letI : ∀ n, Nonempty (X n) := hX
      ∃ (embedding : A →⋆ₐ[ℂ]
          NormMatrixCStarCorona (fun n ↦ X n))
        (extension : NormMatrixCStarCorona (fun n ↦ X n) →ₗ[ℂ] D),
        Function.Injective embedding ∧
          IsCompletelyPositive extension ∧
          extension 1 = 1 ∧
          ∀ a : A, extension (embedding a) = observable a := by
  rcases hMF.2 with ⟨Y, hYne, _hYpos, _hYmono, e, he⟩
  letI : ∀ n, Nonempty (Y n) := hYne
  obtain ⟨X, hXne, embedding, hembedding⟩ :=
    NonUnitalMFSupportCornerEmbedding.exists_injective_unital_supportCornerEmbedding
      Y e he
  letI : ∀ n, Nonempty (X n) := hXne
  obtain ⟨extension, hextensionCP, hextensionOne, hextends⟩ :=
    exists_ucp_extension_finiteDimensional embedding hembedding observable
      hobservableCP hobservableOne
  exact ⟨X, hXne, embedding, extension, hembedding, hextensionCP,
    hextensionOne, hextends⟩

/-- Closed universal packaging of the MF-to-corona finite-dimensional UCP
extension theorem. -/
def MFHasFiniteDimensionalUCPExtensions : Prop :=
  ∀ (A : Type u) (D : Type w)
    [CStarAlgebra A] [CStarAlgebra D]
    [Nontrivial A] [Nontrivial D]
    [FiniteDimensional ℂ D],
    IsMFAlgebra A →
      ∀ (observable : A →ₗ[ℂ] D),
        IsCompletelyPositive observable → observable 1 = 1 →
          ∃ (X : ℕ → FiniteModel) (hX : ∀ n, Nonempty (X n)),
            letI : ∀ n, Nonempty (X n) := hX
            ∃ (embedding : A →⋆ₐ[ℂ]
                NormMatrixCStarCorona (fun n ↦ X n))
              (extension :
                NormMatrixCStarCorona (fun n ↦ X n) →ₗ[ℂ] D),
              Function.Injective embedding ∧
                IsCompletelyPositive extension ∧
                extension 1 = 1 ∧
                ∀ a : A, extension (embedding a) = observable a

/-- Every finite-dimensional UCP observable on an MF algebra has a UCP
extension to a faithful unital matrix-corona model. -/
theorem mfHasFiniteDimensionalUCPExtensions :
    MFHasFiniteDimensionalUCPExtensions := by
  intro A D _ _ _ _ _ hMF observable hobservableCP hobservableOne
  exact exists_unitalMFEmbedding_with_ucp_extension hMF observable
    hobservableCP hobservableOne

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms exists_unitalMFEmbedding_with_ucp_extension
#audit_closed_axioms mfHasFiniteDimensionalUCPExtensions
