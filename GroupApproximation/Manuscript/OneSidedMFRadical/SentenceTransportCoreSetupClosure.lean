import GroupApproximation.Analysis.CollapseUltraproductRepresentation
import GroupApproximation.Analysis.KazhdanProjectionOneSidedOrder
import GroupApproximation.Manuscript.OneSidedMFRadical.KazhdanTransport

/-!
# Remaining sentence closure in the transport setup

Exact wrappers for rows 127--132 not already represented by the maximal-C-star,
normalized-almost-representation, or adjoint-corona sentence modules.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

noncomputable section

universe u

/-- **Sentence 127.**  The printed three-line vector computation says that
the inverse of the compressing unitary preserves the invariant subspace. -/
theorem manuscriptSentence127_inverseUnitary_preserves_fixedSpace
    {Gamma : Type*} [Group Gamma] {H : Type*} [Group H]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : H →* (E ≃ₗᵢ[ℝ] E)) (iota : Gamma →* H) (t : H)
    (compresses : ∀ gamma : Gamma, ∃ delta : Gamma,
      t * iota gamma * t⁻¹ = iota delta)
    {x : E}
    (hx : x ∈ KazhdanOrthogonal.invariantSubmodule (rho.comp iota)) :
    (rho t).symm x ∈
      KazhdanOrthogonal.invariantSubmodule (rho.comp iota) :=
  KazhdanProjectionOneSidedOrder.symm_mem_invariantSubmodule_of_compresses
    rho iota t compresses hx

/-- **Sentence 128.**  Hence the inverse-conjugated invariant projection is
dominated by the original invariant projection. -/
theorem manuscriptSentence128_inverseConjugatedProjection_le
    {Gamma : Type*} [Group Gamma] {H : Type*} [Group H]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (rho : H →* (E ≃ₗᵢ[ℝ] E)) (iota : Gamma →* H) (t : H)
    (compresses : ∀ gamma : Gamma, ∃ delta : Gamma,
      t * iota gamma * t⁻¹ = iota delta) :
    star ((rho t : E ≃ₗᵢ[ℝ] E) : E →L[ℝ] E) *
          KazhdanProjection.invariantProjection (rho.comp iota) *
          ((rho t : E ≃ₗᵢ[ℝ] E) : E →L[ℝ] E)
      ≤ KazhdanProjection.invariantProjection (rho.comp iota) :=
  KazhdanProjectionOneSidedOrder.star_mul_invariantProjection_mul_le
    rho iota t compresses

/-- **Sentence 130.**  Both conjugation directions of the printed one-sided
Kazhdan transport theorem. -/
theorem manuscriptSentence130_twoSided_transport :
    OneSidedKazhdanTransport :=
  manuscriptOneSidedKazhdanTransport

/-- **Sentence 131.**  The rank-normalized Hilbert-space ultraproduct exists
as a nonempty complete complex inner-product space. -/
theorem manuscriptSentence131_HilbertSpaceUltraproduct
    (Y : ℕ → FiniteModel) (weight : ℕ → ℝ)
    (omega : Ultrafilter ℕ) (hweight : ∀ n, 0 ≤ weight n) :
    Nonempty (KOmegaHilbert.KOmega Y weight omega hweight) ∧
      CompleteSpace (KOmegaHilbert.KOmega Y weight omega hweight) :=
  ⟨inferInstance, inferInstance⟩

/-- **Sentence 132.**  Coordinatewise unitary conjugation by an exactly
multiplicative family defines an exact unitary representation on that Hilbert
ultraproduct. -/
theorem manuscriptSentence132_conjugationRepresentation
    {H : Type u} [Group H]
    (Y : ℕ → FiniteModel) (weight : ℕ → ℝ)
    (omega : Ultrafilter ℕ) (hweight : ∀ n, 0 ≤ weight n)
    (Theta : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ)) :
    ∃ sigma : H →*
        (KOmegaHilbert.KOmega Y weight omega hweight ≃ₗᵢ[ℂ]
          KOmegaHilbert.KOmega Y weight omega hweight),
      ∀ g : H, sigma g =
        CollapseUltraproductRepresentation.conjIsometryEquiv
          Y weight omega hweight (fun n ↦ Theta g n) := by
  refine ⟨CollapseUltraproductRepresentation.conjRep
    Y weight omega hweight Theta, ?_⟩
  intro g
  rfl

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
