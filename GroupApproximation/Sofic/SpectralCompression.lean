import GroupApproximation.Analysis.SpectralComponentMotion
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
open SpectralComponentMotion

universe u

/-- Under one-sided Kazhdan compression, every clopen spectral projection of
`v` commutes with the full Kazhdan subgroup.  The hypotheses are stated in
their precise functional-calculus form: `v` and `star v` commute with the
compressed image, and the corresponding conjugation orbits commute
pairwise.  For unitary `v`, the starred hypotheses follow from the unstarred
ones, so the manuscript's unitary statement is an immediate specialization.
-/
theorem corona_clopen_projection_collapse :
    ∀ {E' : Type u} [Group E'],
    ∀ (L : Subgroup E') (_hT : HasKazhdanPropertyT.{u, u} ↥L)
      {s : E'} (_hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
      (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)],
    ∀
    (pi : E' →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
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
  intro E' _ L hT s hcomp X _ pi v hv hcompressed hcompressedStar horbit horbitStar U hU
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
  have hX : ∀ n, 0 < Fintype.card (X n) := fun n ↦
    Fintype.card_pos_iff.mpr (inferInstance : Nonempty (X n))
  exact ProjectionCompressionCollapse.corona_projection_collapse
    L hT hcomp X hX pi (projection v U hU)
      (star_projection_eq hU) (projection_mul_self hU)
      hpcompressed hporbit

/-- **Spectral compression theorem.**  Under one-sided Kazhdan compression,
the motion of a normal corona element whose conjugates commute is bounded by
any common upper bound for the diameters of the connected components of its
spectrum.  In particular, taking `δ = 0` gives exact collapse whenever all
spectral components are singletons.

The starred commutation assumptions needed by projection collapse are derived
from normality (Fuglede commutation); they are not additional hypotheses. -/
theorem corona_spectral_component_motion
    {E' : Type u} [Group E']
    (L : Subgroup E') (hT : HasKazhdanPropertyT.{u, u} ↥L)
    {s : E'} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (pi : E' →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (v : NormMatrixCStarCorona (fun n ↦ X n))
    (hv : IsStarNormal v)
    (hcompressed : ∀ γ ∈ L,
      Commute v
        (((pi (s * γ * s⁻¹) :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n))))
    (horbit : ∀ γ₁ ∈ L, ∀ γ₂ ∈ L,
      Commute
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₁) v)
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₂) v))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hdiameter : ∀ z : spectrum ℂ v,
      Metric.diam (connectedComponent z) ≤ δ) :
    ∀ γ ∈ L,
      ‖Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ) v - v‖ ≤ δ := by
  classical
  letI : ContinuousFunctionalCalculus ℂ
      (NormMatrixCStarCorona (fun n ↦ X n)) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : IsStarNormal v := hv
  have hcompressedStar : ∀ γ ∈ L,
      Commute (star v)
        (((pi (s * γ * s⁻¹) :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n))) := by
    intro γ hγ
    exact hv.commute_star_left (hcompressed γ hγ)
  have horbitStar : ∀ γ₁ ∈ L, ∀ γ₂ ∈ L,
      Commute
        (star (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₁) v))
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₂) v) := by
    intro γ₁ hγ₁ γ₂ hγ₂
    have hn : IsStarNormal
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₁) v) :=
      IsStarNormal.map
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₁)) v
    exact hn.commute_star_left (horbit γ₁ hγ₁ γ₂ hγ₂)
  intro γ hγ
  let b := Unitary.conjStarAlgAut ℂ
    (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ) v
  have hb : IsStarNormal b :=
    IsStarNormal.map
      (Unitary.conjStarAlgAut ℂ
        (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ)) v
  have hvb : Commute v b := by
    simpa [b] using horbit (1 : E') (L.one_mem) γ hγ
  have hspec : spectrum ℂ b = spectrum ℂ v := by
    exact spectrum_conj_eq (pi γ) v
  have hprojection : ∀ (U : Set (spectrum ℂ v)) (hU : IsClopen U),
      projection v U hU = cfc (spectralIndicator v U hU) b := by
    intro U hU
    have hpcomm := corona_clopen_projection_collapse L hT hcomp X pi v hv
      hcompressed hcompressedStar horbit horbitStar hU γ hγ
    have hfixed : Unitary.conjStarAlgAut ℂ
        (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ)
        (projection v U hU) = projection v U hU := by
      change ((pi γ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) * projection v U hU *
        star ((pi γ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) = projection v U hU
      rw [hpcomm.eq, mul_assoc]
      simp
    dsimp [b]
    exact hfixed.symm.trans (conj_projection_eq_cfc (pi γ) hv hU)
  have hbound := norm_sub_le_of_clopen_projections_eq v b hv hb hvb hspec
    hprojection hδ hdiameter
  simpa [b, norm_sub_rev] using hbound

/-- The quantitative conclusion in its optimal displayed form: the norm motion
is bounded by the supremum of the component diameters. -/
theorem corona_spectral_component_motion_supremum
    {E' : Type u} [Group E']
    (L : Subgroup E') (hT : HasKazhdanPropertyT.{u, u} ↥L)
    {s : E'} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (pi : E' →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (v : NormMatrixCStarCorona (fun n ↦ X n))
    (hv : IsStarNormal v)
    (hcompressed : ∀ γ ∈ L,
      Commute v
        (((pi (s * γ * s⁻¹) :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n))))
    (horbit : ∀ γ₁ ∈ L, ∀ γ₂ ∈ L,
      Commute
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₁) v)
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₂) v)) :
    ∀ γ ∈ L,
      ‖Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ) v - v‖ ≤
        SpectralComponentDiameter.spectralComponentDiameter v :=
  corona_spectral_component_motion L hT hcomp X pi v hv hcompressed horbit
    (SpectralComponentDiameter.spectralComponentDiameter_nonneg v)
    (SpectralComponentDiameter.component_diameter_le_spectralComponentDiameter v)

/-- Zero-dimensional spectrum is the sharp exact-collapse corollary of spectral
component motion. -/
theorem corona_zero_dimensional_spectral_collapse
    {E' : Type u} [Group E']
    (L : Subgroup E') (hT : HasKazhdanPropertyT.{u, u} ↥L)
    {s : E'} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (pi : E' →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (v : NormMatrixCStarCorona (fun n ↦ X n))
    (hv : IsStarNormal v)
    (hcompressed : ∀ γ ∈ L,
      Commute v
        (((pi (s * γ * s⁻¹) :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n))))
    (horbit : ∀ γ₁ ∈ L, ∀ γ₂ ∈ L,
      Commute
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₁) v)
        (Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ₂) v))
    (hzero : ∀ z : spectrum ℂ v, connectedComponent z = {z}) :
    ∀ γ ∈ L,
      Unitary.conjStarAlgAut ℂ
          (NormMatrixCStarCorona (fun n ↦ X n)) (pi γ) v = v := by
  intro γ hγ
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm
  · apply corona_spectral_component_motion L hT hcomp X pi v hv
      hcompressed horbit (δ := 0) (le_refl 0) _ γ hγ
    intro z
    rw [hzero z, Metric.diam_singleton]
  · exact norm_nonneg _

end SpectralCompression
end GroupApproximation

