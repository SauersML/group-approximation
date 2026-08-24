import GroupApproximation.Analysis.ClopenSpectralProjection
import GroupApproximation.Sofic.ProjectionCompressionCollapse

/-!
# Spectral collapse under one-sided Kazhdan compression

The projection-collapse theorem applies not only to projections initially
present in a group, but to every clopen spectral projection of a normal
corona element.  This file records that functional-calculus upgrade.  It is
the compression input for the spectral-component motion theorem: property
`(T)` forces every clopen spectral test to be invariant, while the topology
of the spectrum determines how much motion can remain.
-/

namespace GroupApproximation
namespace SpectralCompression

open ClopenSpectralProjection

universe u

variable {E : Type u} [Group E] [Countable E]

/-- Under one-sided Kazhdan compression, every clopen spectral projection of
`v` commutes with the full Kazhdan subgroup.  The hypotheses are stated in
their precise functional-calculus form: `v` and `star v` commute with the
compressed image, and the corresponding conjugation orbits commute
pairwise.  For unitary `v`, the starred hypotheses follow from the unstarred
ones, so the manuscript's unitary statement is an immediate specialization.
-/
theorem corona_clopen_projection_collapse :
    ∀ (L : Subgroup E) (_hT : HasKazhdanPropertyT.{u, u} ↥L)
      {s : E} (_hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
      (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)],
    ∀
    (pi : E →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (v : NormMatrixCStarCorona (fun n ↦ X n))
    (_hv : IsStarNormal v)
    (_hcompressed : ∀ γ ∈ L,
      Commute v
        (((pi (s * γ * s⁻¹) :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n))))
    (_hcompressedStar : ∀ γ ∈ L,
      Commute (star v)
        (((pi (s * γ * s⁻¹) :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n))))
    (_horbit : ∀ γ₁ ∈ L, ∀ γ₂ ∈ L,
      Commute
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₁) v)
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₂) v))
    (_horbitStar : ∀ γ₁ ∈ L, ∀ γ₂ ∈ L,
      Commute
        (star (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₁) v))
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₂) v))
    {U : Set (spectrum ℂ v)} (hU : IsClopen U),
    ∀ γ ∈ L,
      Commute
        (((pi γ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)))
        (projection v U hU) := by
  classical
  intro L hT s hcomp X _ pi v hv hcompressed hcompressedStar horbit horbitStar U hU
  have hpcompressed : ∀ γ ∈ L,
      ((pi (s * γ * s⁻¹) :
          unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) * projection v U hU =
        projection v U hU *
          ((pi (s * γ * s⁻¹) :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) := by
    intro γ hγ
    exact (commute_projection hv (hcompressed γ hγ)
      (hcompressedStar γ hγ) hU).symm.eq
  have hporbit : ∀ γ₁ ∈ L, ∀ γ₂ ∈ L,
      Commute
        (((pi γ₁ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) * projection v U hU *
          star ((pi γ₁ : unitary
            (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)))
        (((pi γ₂ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) * projection v U hU *
          star ((pi γ₂ : unitary
            (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n))) := by
    intro γ₁ hγ₁ γ₂ hγ₂
    change Commute
      (Unitary.conjStarAlgAut ℂ
        (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₁)
        (projection v U hU))
      (Unitary.conjStarAlgAut ℂ
        (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₂)
        (projection v U hU))
    exact commute_conj_projections (pi γ₁) (pi γ₂) hv hU
      (horbit γ₁ hγ₁ γ₂ hγ₂)
      (horbitStar γ₁ hγ₁ γ₂ hγ₂)
      (horbitStar γ₂ hγ₂ γ₁ hγ₁)
  exact ProjectionCompressionCollapse.corona_projection_collapse
    L hT hcomp X pi (projection v U hU)
      (star_projection_eq hU) (projection_mul_self hU)
      hpcompressed hporbit

end SpectralCompression
end GroupApproximation
