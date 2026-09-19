import GroupApproximation.Analysis.SpectralStateWitness
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The GNS eigenvector of a spectrally concentrated state

For a state `Φ` annihilating `(m - μ)²`, the cyclic vector of the GNS
representation is a genuine unit eigenvector of the represented `m` with
eigenvalue `μ`.  Together with `SpectralStateWitness` this turns a real
spectral point of a self-adjoint element in an abstract unital C-star
algebra into an eigenvector in a concrete Hilbert-space representation.

The module also provides the bridge from unitary elements of the operator
algebra to isometric linear equivalences, so a unitary group
representation composed with the GNS representation yields an isometric
group action ready for the Kazhdan machinery.

Bricks of the strict-Kazhdan-compression program of
`notes/FORMALIZATION_DIRECTIVES_2026-08-15.md` §1.
-/

namespace GroupApproximation
namespace GNSEigenvector

open UniformSpace
open scoped ComplexOrder

noncomputable section

section GNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (Φ : A →ₚ[ℂ] ℂ)

/-- The canonical cyclic vector of the GNS space: the class of `1`. -/
def gnsCyclic : Φ.GNS := ((Φ.toPreGNS 1 : Φ.PreGNS) : Φ.GNS)

theorem norm_gnsCyclic (h1 : Φ 1 = 1) : ‖gnsCyclic Φ‖ = 1 := by
  rw [gnsCyclic, Completion.norm_coe]
  have hsq := Φ.preGNS_norm_sq (Φ.toPreGNS 1)
  rw [Φ.ofPreGNS_toPreGNS, star_one, one_mul, h1] at hsq
  have h2 : ‖(Φ.toPreGNS 1 : Φ.PreGNS)‖ ^ 2 = 1 := by exact_mod_cast hsq
  have h4 : (‖(Φ.toPreGNS 1 : Φ.PreGNS)‖ - 1)
      * (‖(Φ.toPreGNS 1 : Φ.PreGNS)‖ + 1) = 0 := by
    calc (‖(Φ.toPreGNS 1 : Φ.PreGNS)‖ - 1)
          * (‖(Φ.toPreGNS 1 : Φ.PreGNS)‖ + 1)
        = ‖(Φ.toPreGNS 1 : Φ.PreGNS)‖ ^ 2 - 1 := by ring
      _ = 0 := by rw [h2]; ring
  rcases mul_eq_zero.mp h4 with h5 | h5
  · linarith
  · have h6 := norm_nonneg (Φ.toPreGNS 1 : Φ.PreGNS)
    linarith

/-- **The GNS eigenvector**: a state annihilating `(m - μ)²` makes the
cyclic vector an eigenvector of the represented `m` with eigenvalue `μ`. -/
theorem gns_eigenvector (m : A) (hm : IsSelfAdjoint m) (μ : ℝ)
    (hkill : Φ ((m - algebraMap ℝ A μ) * (m - algebraMap ℝ A μ)) = 0) :
    Φ.gnsStarAlgHom m (gnsCyclic Φ) = (μ : ℂ) • gnsCyclic Φ := by
  have halg : algebraMap ℝ A μ = (μ : ℂ) • (1 : A) := by
    rw [Algebra.algebraMap_eq_smul_one, ← algebraMap_smul ℂ μ (1 : A)]
    congr 1
  have h0 : Φ.gnsStarAlgHom m (gnsCyclic Φ)
      = ((Φ.leftMulMapPreGNS m (Φ.toPreGNS 1) : Φ.PreGNS) : Φ.GNS) :=
    Φ.gnsNonUnitalStarAlgHom_apply_coe
  have h1 : (Φ.leftMulMapPreGNS m (Φ.toPreGNS 1) : Φ.PreGNS)
      = Φ.toPreGNS m := by
    rw [Φ.leftMulMapPreGNS_apply, Φ.ofPreGNS_toPreGNS, mul_one]
  have h2 : (μ : ℂ) • gnsCyclic Φ
      = ((Φ.toPreGNS (algebraMap ℝ A μ) : Φ.PreGNS) : Φ.GNS) := by
    rw [gnsCyclic, ← Completion.coe_smul, ← map_smul, halg]
  rw [h0, h1, h2]
  have hsaμ : star (algebraMap ℝ A μ) = algebraMap ℝ A μ := by
    rw [Algebra.algebraMap_eq_smul_one, star_smul, star_trivial, star_one]
  have hsa : star (m - algebraMap ℝ A μ) = m - algebraMap ℝ A μ := by
    rw [star_sub, hm.star_eq, hsaμ]
  have hd : ‖(Φ.toPreGNS m - Φ.toPreGNS (algebraMap ℝ A μ) : Φ.PreGNS)‖ ^ 2
      = 0 := by
    have hsq := Φ.preGNS_norm_sq
      (Φ.toPreGNS m - Φ.toPreGNS (algebraMap ℝ A μ))
    rw [← map_sub, Φ.ofPreGNS_toPreGNS, hsa, hkill] at hsq
    exact_mod_cast hsq
  have hnorm0 :
      ‖((Φ.toPreGNS m - Φ.toPreGNS (algebraMap ℝ A μ) : Φ.PreGNS) :
        Φ.GNS)‖ = 0 := by
    rw [Completion.norm_coe]
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hd
  have hcoe0 :
      ((Φ.toPreGNS m - Φ.toPreGNS (algebraMap ℝ A μ) : Φ.PreGNS) : Φ.GNS)
        = 0 :=
    norm_eq_zero.mp hnorm0
  rw [Completion.coe_sub] at hcoe0
  exact sub_eq_zero.mp hcoe0

end GNS

section UnitaryIsometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A unitary operator on a Hilbert space, as an isometric linear
equivalence. -/
def unitaryToIsometryEquiv (u : unitary (H →L[ℂ] H)) : H ≃ₗᵢ[ℂ] H where
  toLinearEquiv :=
    { toFun := ⇑(u : H →L[ℂ] H)
      map_add' := map_add (u : H →L[ℂ] H)
      map_smul' := map_smul (u : H →L[ℂ] H)
      invFun := ⇑((star u : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
      left_inv := fun x =>
        congrArg (fun T : H →L[ℂ] H => T x) u.property.1
      right_inv := fun x =>
        congrArg (fun T : H →L[ℂ] H => T x) u.property.2 }
  norm_map' := fun x =>
    ContinuousLinearMap.norm_map_of_mem_unitary u.property x

@[simp] theorem unitaryToIsometryEquiv_apply (u : unitary (H →L[ℂ] H)) (x : H) :
    unitaryToIsometryEquiv u x = (u : H →L[ℂ] H) x :=
  rfl

/-- Unitaries act as isometric equivalences, as a monoid homomorphism. -/
def unitaryIsometryHom : unitary (H →L[ℂ] H) →* (H ≃ₗᵢ[ℂ] H) where
  toFun := unitaryToIsometryEquiv
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    rfl
  map_mul' := fun u v => by
    apply LinearIsometryEquiv.ext
    intro x
    rfl

end UnitaryIsometry

end

end GNSEigenvector
end GroupApproximation
