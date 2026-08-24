import GroupApproximation.Sofic.SpectralCompression

/-!
# Closed endpoints for the spectral-compression paper

This file contains the literal, source-closed spectral theorems advertised in
the revised paper.
-/

namespace GroupApproximation
namespace SpectralPaper

universe u

/-- The exact quantitative spectral-compression statement advertised by the
paper, with every ambient object and hypothesis quantified inside the
proposition. -/
def SpectralCompressionTheorem : Prop :=
  ∀ {E' : Type u} [Group E']
    (L : Subgroup E') (_hT : HasKazhdanPropertyT.{u, u} ↥L)
    {s : E'} (_hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (pi : E' →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (v : NormMatrixCStarCorona (fun n ↦ X n))
    (_hv : IsStarNormal v)
    (_hcompressed : ∀ γ ∈ L,
      Commute v
        (((pi (s * γ * s⁻¹) :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n))))
    (_horbit : ∀ γ₁ ∈ L, ∀ γ₂ ∈ L,
      Commute
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₁) v)
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₂) v)),
    ∀ γ ∈ L,
      ‖Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ) v - v‖ ≤
        SpectralComponentDiameter.spectralComponentDiameter v

theorem spectralCompressionTheorem : SpectralCompressionTheorem := by
  intro E' _ L hT s hcomp X _ pi v hv hcompressed horbit
  exact SpectralCompression.corona_spectral_component_motion_supremum
    L hT hcomp X pi v hv hcompressed horbit

/-- The zero-dimensional exact-collapse corollary, again as one source-closed
paper endpoint. -/
def ZeroDimensionalSpectralCollapseTheorem : Prop :=
  ∀ {E' : Type u} [Group E']
    (L : Subgroup E') (_hT : HasKazhdanPropertyT.{u, u} ↥L)
    {s : E'} (_hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (pi : E' →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (v : NormMatrixCStarCorona (fun n ↦ X n))
    (_hv : IsStarNormal v)
    (_hcompressed : ∀ γ ∈ L,
      Commute v
        (((pi (s * γ * s⁻¹) :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n))))
    (_horbit : ∀ γ₁ ∈ L, ∀ γ₂ ∈ L,
      Commute
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₁) v)
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₂) v))
    (_hzero : ∀ z : spectrum ℂ v, connectedComponent z = {z}),
    ∀ γ ∈ L,
      Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ) v = v

theorem zeroDimensionalSpectralCollapseTheorem :
    ZeroDimensionalSpectralCollapseTheorem := by
  intro E' _ L hT s hcomp X _ pi v hv hcompressed horbit hzero
  exact SpectralCompression.corona_zero_dimensional_spectral_collapse
    L hT hcomp X pi v hv hcompressed horbit hzero

end SpectralPaper
end GroupApproximation
