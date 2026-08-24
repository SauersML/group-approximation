import GroupApproximation.Analysis.SpectralComponentDiameter
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Topology.Algebra.Indicator

/-!
# Clopen spectral projections

Clopen subsets of the spectrum of a normal element define projections by
continuous functional calculus.  This file packages those projections in the
form needed by spectral compression: their values, projection identities,
commutation, unitary-conjugation naturality, and evaluation by characters.
-/

namespace GroupApproximation
namespace ClopenSpectralProjection

open WeakDual

universe u

variable {A : Type u} [CStarAlgebra A]

noncomputable local instance :
    ContinuousFunctionalCalculus ℂ A IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

/-- The characteristic function of a clopen subset of `spectrum ℂ v`, extended
arbitrarily by zero off the spectrum.  Continuous functional calculus only
uses its restriction to the spectrum. -/
noncomputable def spectralIndicator (v : A) (U : Set (spectrum ℂ v))
    (_hU : IsClopen U) : ℂ → ℂ := by
  classical
  exact fun z ↦
    if hz : z ∈ spectrum ℂ v then
      Set.indicator U (fun _ ↦ (1 : ℂ)) ⟨z, hz⟩
    else 0

@[simp]
theorem spectralIndicator_apply_of_mem {v : A} {U : Set (spectrum ℂ v)}
    (hU : IsClopen U) (z : spectrum ℂ v) :
    spectralIndicator v U hU z =
      Set.indicator U (fun _ ↦ (1 : ℂ)) z := by
  simp [spectralIndicator, z.2]

theorem spectralIndicator_continuousOn {v : A} {U : Set (spectrum ℂ v)}
    (hU : IsClopen U) :
    ContinuousOn (spectralIndicator v U hU) (spectrum ℂ v) := by
  rw [continuousOn_iff_continuous_restrict]
  convert hU.continuous_indicator continuous_const using 1
  ext z
  exact spectralIndicator_apply_of_mem hU z

/-- The continuous-functional-calculus projection attached to a clopen
spectral subset. -/
noncomputable def projection (v : A) (U : Set (spectrum ℂ v))
    (hU : IsClopen U) : A :=
  cfc (spectralIndicator v U hU) v

theorem complex_spectrum_eq_singleton (z : ℂ) : spectrum ℂ z = {z} := by
  ext x
  simp [spectrum, resolventSet, sub_eq_zero]

theorem cfc_complex_eq_apply (f : ℂ → ℂ) (z : ℂ) : cfc f z = f z := by
  calc
    cfc f z = cfc (fun _ ↦ f z) z := by
      apply cfc_congr
      intro x hx
      have hxz : x = z := by
        simpa [complex_spectrum_eq_singleton z] using hx
      rw [hxz]
    _ = f z := by simp [cfc_const]

theorem spectralIndicator_star_eq {v : A} {U : Set (spectrum ℂ v)}
    (hU : IsClopen U) :
    (spectrum ℂ v).EqOn
      (fun z ↦ star (spectralIndicator v U hU z))
      (spectralIndicator v U hU) := by
  intro z hz
  by_cases hzin : (⟨z, hz⟩ : spectrum ℂ v) ∈ U
  · have hone : spectralIndicator v U hU z = 1 := by
      rw [spectralIndicator_apply_of_mem hU ⟨z, hz⟩]
      exact Set.indicator_of_mem hzin _
    simp [hone]
  · have hzero : spectralIndicator v U hU z = 0 := by
      rw [spectralIndicator_apply_of_mem hU ⟨z, hz⟩]
      exact Set.indicator_of_notMem hzin _
    simp [hzero]

theorem spectralIndicator_mul_self_eq {v : A} {U : Set (spectrum ℂ v)}
    (hU : IsClopen U) :
    (spectrum ℂ v).EqOn
      (fun z ↦ spectralIndicator v U hU z * spectralIndicator v U hU z)
      (spectralIndicator v U hU) := by
  intro z hz
  by_cases hzin : (⟨z, hz⟩ : spectrum ℂ v) ∈ U
  · have hone : spectralIndicator v U hU z = 1 := by
      rw [spectralIndicator_apply_of_mem hU ⟨z, hz⟩]
      exact Set.indicator_of_mem hzin _
    simp [hone]
  · have hzero : spectralIndicator v U hU z = 0 := by
      rw [spectralIndicator_apply_of_mem hU ⟨z, hz⟩]
      exact Set.indicator_of_notMem hzin _
    simp [hzero]

/-- A clopen spectral projection is self-adjoint. -/
theorem star_projection_eq {v : A} {U : Set (spectrum ℂ v)}
    (hU : IsClopen U) :
    star (projection v U hU) = projection v U hU := by
  rw [projection, ← cfc_star]
  exact cfc_congr (spectralIndicator_star_eq hU)

/-- A clopen spectral projection is idempotent. -/
theorem projection_mul_self {v : A} {U : Set (spectrum ℂ v)}
    (hU : IsClopen U) :
    projection v U hU * projection v U hU = projection v U hU := by
  rw [projection, ← cfc_mul
    (spectralIndicator v U hU) (spectralIndicator v U hU) v
    (spectralIndicator_continuousOn hU)
    (spectralIndicator_continuousOn hU)]
  exact cfc_congr (spectralIndicator_mul_self_eq hU)

/-- An element commuting with a normal element and its adjoint commutes with
all of its clopen spectral projections. -/
theorem commute_projection {v x : A} (hv : IsStarNormal v)
    (h₁ : Commute v x) (h₂ : Commute (star v) x)
    {U : Set (spectrum ℂ v)} (hU : IsClopen U) :
    Commute (projection v U hU) x := by
  rw [projection, cfc_apply _ _ hv (spectralIndicator_continuousOn hU)]
  exact h₁.cfcHom hv h₂ _

/-- Evaluation of a clopen spectral projection by a character is the
characteristic function of the character value. -/
theorem character_apply_projection {v : A} (hv : IsStarNormal v)
    {U : Set (spectrum ℂ v)} (hU : IsClopen U)
    (χ : characterSpace ℂ A) :
    χ (projection v U hU) = spectralIndicator v U hU (χ v) := by
  rw [projection]
  rw [StarAlgHomClass.map_cfc χ (spectralIndicator v U hU) v
    (spectralIndicator_continuousOn hU)]
  exact cfc_complex_eq_apply _ _

/-- Continuous functional calculus is natural under unitary conjugation. -/
theorem conj_projection_eq_cfc (u : unitary A) {v : A}
    (hv : IsStarNormal v) {U : Set (spectrum ℂ v)} (hU : IsClopen U) :
    Unitary.conjStarAlgAut ℂ A u (projection v U hU) =
      cfc (spectralIndicator v U hU)
        (Unitary.conjStarAlgAut ℂ A u v) := by
  letI : IsStarNormal v := hv
  have hcont : Continuous
      (Unitary.conjStarAlgAut ℂ A u).toStarAlgHom := by
    change Continuous (fun x : A ↦ (u : A) * x * star (u : A))
    fun_prop
  rw [projection]
  exact StarAlgHom.map_cfc
    (Unitary.conjStarAlgAut ℂ A u).toStarAlgHom
    (spectralIndicator v U hU) v
    (spectralIndicator_continuousOn hU) hcont

/-- Unitary conjugation preserves the spectrum exactly. -/
theorem spectrum_conj_eq (u : unitary A) (v : A) :
    spectrum ℂ (Unitary.conjStarAlgAut ℂ A u v) = spectrum ℂ v :=
  AlgEquiv.spectrum_eq (Unitary.conjStarAlgAut ℂ A u).toAlgEquiv v

end ClopenSpectralProjection
end GroupApproximation
