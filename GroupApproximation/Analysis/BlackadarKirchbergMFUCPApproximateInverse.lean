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
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u w

variable {A : Type u} {D : Type w}
  [CStarAlgebra A] [CStarAlgebra D]
  [Nontrivial A] [Nontrivial D]
  [FiniteDimensional ℂ D]

local instance boundedMatrixSequenceCStarAlgebraForMFUCPInverse
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] :
    CStarAlgebra (BoundedMatrixSequence (fun n ↦ X n)) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := by
    constructor
    intro c x
    apply lp.ext
    funext n
    change star (c • x n) = star c • star (x n)
    rw [star_smul]

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

/-- Numerator form of the preceding theorem.  The corona extension composed
with the quotient map is UCP on the bounded matrix product, kills every
cofinite-null sequence, and recovers the finite-dimensional observable on a
chosen bounded lift of every represented source element.

This is the exact global CP approximate-inverse datum immediately before the
finite-coordinate localization step in the BK construction. -/
theorem exists_numerator_ucp_inverse_of_isMFAlgebra
    (hMF : IsMFAlgebra A)
    (observable : A →ₗ[ℂ] D)
    (hobservableCP : IsCompletelyPositive observable)
    (hobservableOne : observable 1 = 1) :
    ∃ (X : ℕ → FiniteModel) (hX : ∀ n, Nonempty (X n)),
      letI : ∀ n, Nonempty (X n) := hX
      ∃ (embedding : A →⋆ₐ[ℂ]
          NormMatrixCStarCorona (fun n ↦ X n))
        (inverse : BoundedMatrixSequence (fun n ↦ X n) →ₗ[ℂ] D)
        (lift : A → BoundedMatrixSequence (fun n ↦ X n)),
        Function.Injective embedding ∧
          IsCompletelyPositive inverse ∧
          inverse 1 = 1 ∧
          (∀ x, IsNullMatrixSequence (fun n ↦ X n) Filter.cofinite x →
            inverse x = 0) ∧
          ∀ a : A,
            normMatrixCStarCoronaMk (fun n ↦ X n) (lift a) = embedding a ∧
              inverse (lift a) = observable a := by
  obtain ⟨X, hXne, embedding, extension, hembedding, hextensionCP,
      hextensionOne, hextends⟩ :=
    exists_unitalMFEmbedding_with_ucp_extension hMF observable
      hobservableCP hobservableOne
  letI : ∀ n, Nonempty (X n) := hXne
  let quotientStar : BoundedMatrixSequence (fun n ↦ X n) →⋆ₐ[ℂ]
      NormMatrixCStarCorona (fun n ↦ X n) :=
    normMatrixCStarCoronaQuotient (fun n ↦ X n)
  let quotient : BoundedMatrixSequence (fun n ↦ X n) →ₗ[ℂ]
      NormMatrixCStarCorona (fun n ↦ X n) :=
    { toFun := quotientStar
      map_add' := quotientStar.map_add
      map_smul' := fun c x ↦ map_smul quotientStar c x }
  let inverse : BoundedMatrixSequence (fun n ↦ X n) →ₗ[ℂ] D :=
    extension.comp quotient
  let lift : A → BoundedMatrixSequence (fun n ↦ X n) :=
    NonUnitalMFSupportCornerEmbedding.sourceLift X
      embedding.toNonUnitalStarAlgHom
  have hquotientCP : IsCompletelyPositive quotient := by
    intro n M hM
    exact (isCompletelyPositive_of_starAlgHom
      quotientStar.toNonUnitalStarAlgHom) n M hM
  have hquotient_apply (x : BoundedMatrixSequence (fun n ↦ X n)) :
      quotient x = normMatrixCStarCoronaMk (fun n ↦ X n) x := rfl
  refine ⟨X, hXne, embedding, inverse, lift, hembedding,
    hextensionCP.comp hquotientCP, ?_, ?_, ?_⟩
  · dsimp only [inverse, LinearMap.comp_apply]
    rw [hquotient_apply]
    rw [map_one, hextensionOne]
  · intro x hx
    dsimp only [inverse, LinearMap.comp_apply]
    have hzero : normMatrixCStarCoronaMk (fun n ↦ X n) x = 0 :=
      (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) x).mpr hx
    rw [hquotient_apply, hzero, map_zero]
  · intro a
    have hlift : normMatrixCStarCoronaMk (fun n ↦ X n) (lift a) =
        embedding a :=
      NonUnitalMFSupportCornerEmbedding.sourceLift_spec X
        embedding.toNonUnitalStarAlgHom a
    refine ⟨hlift, ?_⟩
    dsimp only [inverse, LinearMap.comp_apply]
    rw [hquotient_apply, hlift]
    exact hextends a

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
#audit_axioms exists_numerator_ucp_inverse_of_isMFAlgebra
#audit_closed_axioms mfHasFiniteDimensionalUCPExtensions
