import GroupApproximation.Analysis.StateExtension
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# A state concentrated at a spectral point

For a self-adjoint element `m` of a unital C-star algebra and a real
point `μ` of its spectrum, there is a state of the algebra that is
multiplicative on the elemental subalgebra of `m`, sends `m` to `μ`, and
therefore annihilates `(m - μ)²`.

The construction composes the character of the commutative elemental
algebra sitting over the spectral point (Gelfand theory,
`StarAlgebra.elemental.characterSpaceHomeo`) with the positive extension
theorem of `StateExtension`.

This is the spectral brick of the strict-Kazhdan-compression program of
`notes/FORMALIZATION_DIRECTIVES_2026-08-15.md` §1: fed into GNS it
produces a representation in which `m` has the genuine eigenvalue `μ`,
which is what transfers a spectral-gap violation into a concrete
Hilbert-space contradiction.
-/

namespace GroupApproximation
namespace SpectralStateWitness

open StateExtension
open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonnegSpectrumClass ℝ A]

/-- Every character of a closed unital star subalgebra is nonnegative on
ambient positives: its values lie in the ambient spectrum. -/
theorem character_nonneg_on_positives
    (B : StarSubalgebra ℂ A) (hB : IsClosed (B : Set A))
    (χ : WeakDual.characterSpace ℂ B) (b : B) (hb : 0 ≤ (b : A)) :
    ∃ r : ℝ, 0 ≤ r ∧ χ b = r := by
  have hmemB : χ b ∈ spectrum ℂ b := AlgHom.apply_mem_spectrum χ b
  have hmemA : χ b ∈ spectrum ℂ (b : A) := by
    rwa [StarSubalgebra.spectrum_eq (hS := hB) (a := b)] at hmemB
  have hbsa : IsSelfAdjoint (b : A) := .of_nonneg hb
  have hre : χ b = ((χ b).re : ℂ) := hbsa.mem_spectrum_eq_re hmemA
  have hreS : (χ b).re ∈ spectrum ℝ (b : A) := by
    apply spectrum.of_algebraMap_mem (S := ℂ)
    rw [show (algebraMap ℝ ℂ) (χ b).re = ((χ b).re : ℂ) by simp, ← hre]
    exact hmemA
  refine ⟨(χ b).re, ?_, hre⟩
  exact quasispectrum_nonneg_of_nonneg (b : A) hb (χ b).re
    (spectrum_subset_quasispectrum ℝ (b : A) hreS)

/-- **The spectral state**: a state that is `1` at `1` and kills the
square of `m - μ` for a real spectral point `μ` of a self-adjoint `m`. -/
theorem exists_state_annihilating (m : A) (hm : IsSelfAdjoint m) {μ : ℝ}
    (hμ : (μ : ℂ) ∈ spectrum ℂ m) :
    ∃ Φ : A →ₚ[ℂ] ℂ, Φ 1 = 1 ∧
      Φ ((m - algebraMap ℝ A μ) * (m - algebraMap ℝ A μ)) = 0 := by
  haveI : IsStarNormal m := hm.isStarNormal
  set B : StarSubalgebra ℂ A := StarAlgebra.elemental ℂ m with hBdef
  set χ : WeakDual.characterSpace ℂ B :=
    (StarAlgebra.elemental.characterSpaceHomeo (a := m)).symm
      ⟨(μ : ℂ), hμ⟩ with hχdef
  have hχm : χ ⟨m, StarAlgebra.elemental.self_mem ℂ m⟩ = (μ : ℂ) := by
    have h :=
      (StarAlgebra.elemental.characterSpaceHomeo (a := m)).apply_symm_apply
        ⟨(μ : ℂ), hμ⟩
    exact congrArg Subtype.val h
  set φlin : B →ₗ[ℂ] ℂ :=
    { toFun := fun b => χ b
      map_add' := fun x y => map_add χ x y
      map_smul' := fun c x => by rw [map_smul χ]; rfl } with hφdef
  have hφpos : ∀ b : B, 0 ≤ (b : A) → ∃ r : ℝ, 0 ≤ r ∧ φlin b = r :=
    fun b hb => character_nonneg_on_positives B
      (StarAlgebra.elemental.isClosed ℂ m) χ b hb
  obtain ⟨Φ, hΦ⟩ := exists_positiveLinearMap_extension hφpos
  set q : B := ⟨m, StarAlgebra.elemental.self_mem ℂ m⟩
    - algebraMap ℂ B (μ : ℂ) with hqdef
  have hqcoe : ((q * q : B) : A)
      = (m - algebraMap ℝ A μ) * (m - algebraMap ℝ A μ) := by
    have h1 : ((q : B) : A) = m - algebraMap ℝ A μ := by
      show m - algebraMap ℂ A (μ : ℂ) = m - algebraMap ℝ A μ
      rw [show ((μ : ℂ)) = algebraMap ℝ ℂ μ by simp,
        ← IsScalarTower.algebraMap_apply ℝ ℂ A]
    show ((q : B) : A) * ((q : B) : A) = _
    rw [h1]
  have hχq : χ q = 0 := by
    rw [hqdef, map_sub, hχm, AlgHomClass.commutes]
    exact sub_self _
  refine ⟨Φ, ?_, ?_⟩
  · have h1 : Φ ((1 : B) : A) = φlin 1 := hΦ 1
    have h2 : ((1 : B) : A) = (1 : A) := rfl
    rw [h2] at h1
    rw [h1]
    exact map_one χ
  · have h2 : Φ ((q * q : B) : A) = φlin (q * q) := hΦ (q * q)
    rw [← hqcoe, h2]
    show χ (q * q) = 0
    rw [map_mul, hχq, mul_zero]

end

end SpectralStateWitness
end GroupApproximation
