import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Complex.Order
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.Topology.ContinuousMap.StarOrdered
import GroupApproximation.Meta.AxiomGuard

/-!
# Transporting a state to the character space

Let `A` be a commutative unital C⋆-algebra and `τ : A → ℂ` a linear functional with
`τ(x⋆x) ≥ 0`. Gelfand duality `A ≃⋆ₐ C(Χ, ℂ)`, with `Χ = characterSpace ℂ A`, transports
`τ` to `f ↦ τ(Γ⁻¹ f)` on `C(Χ, ℂ)`.

* It is positive. A pointwise nonnegative `f` equals `q⋆q` for `q = √(re f)`, so
  `Γ⁻¹ f = (Γ⁻¹ q)⋆ (Γ⁻¹ q)`.
* It is continuous. Positive maps between C⋆-algebras are bounded
  (`PositiveLinearMap.exists_norm_apply_le`).

No continuity of `τ` is assumed. That matters for the consumers, whose
`TracialState`/`FaithfulTracialState` carry only a linear map.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace CommutativeQD

open WeakDual
open scoped ComplexOrder

noncomputable section

universe u

variable {A : Type u} [CommCStarAlgebra A]

/-- The functional `f ↦ τ(Γ⁻¹ f)` on continuous functions on the character space. -/
def transportedFunctional (τ : A →ₗ[ℂ] ℂ) : C(characterSpace ℂ A, ℂ) →ₗ[ℂ] ℂ where
  toFun f := τ ((gelfandStarTransform A).symm f)
  map_add' f g := by
    show τ ((gelfandStarTransform A).symm (f + g)) =
      τ ((gelfandStarTransform A).symm f) + τ ((gelfandStarTransform A).symm g)
    rw [map_add, map_add]
  map_smul' c f := by
    show τ ((gelfandStarTransform A).symm (c • f)) = c • τ ((gelfandStarTransform A).symm f)
    rw [map_smul, map_smul]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.transportedFunctional

theorem transportedFunctional_apply (τ : A →ₗ[ℂ] ℂ) (f : C(characterSpace ℂ A, ℂ)) :
    transportedFunctional τ f = τ ((gelfandStarTransform A).symm f) :=
  rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.transportedFunctional_apply

/-- **Positivity survives the inverse Gelfand transform.** A pointwise nonnegative
function is `q⋆q` for its continuous square root `q`. -/
theorem transportedFunctional_nonneg (τ : A →ₗ[ℂ] ℂ)
    (hpos : ∀ x : A, 0 ≤ τ (star x * x))
    (f : C(characterSpace ℂ A, ℂ)) (hf : 0 ≤ f) :
    0 ≤ transportedFunctional τ f := by
  let q : C(characterSpace ℂ A, ℂ) :=
    { toFun := fun χ ↦ (Real.sqrt (f χ).re : ℂ)
      continuous_toFun := Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp (Complex.continuous_re.comp f.continuous_toFun)) }
  have hfq : f = star q * q := by
    ext χ
    have hχ : 0 ≤ f χ := ContinuousMap.le_def.mp hf χ
    obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hχ
    have hsqrt : Real.sqrt (f χ).re * Real.sqrt (f χ).re = (f χ).re :=
      Real.mul_self_sqrt hre
    have hstar : star (Real.sqrt (f χ).re : ℂ) = (Real.sqrt (f χ).re : ℂ) := by
      rw [Complex.star_def]
      exact Complex.conj_ofReal _
    change f χ = star (Real.sqrt (f χ).re : ℂ) * (Real.sqrt (f χ).re : ℂ)
    rw [hstar, ← Complex.ofReal_mul, hsqrt]
    refine Complex.ext (Complex.ofReal_re _).symm ?_
    rw [Complex.ofReal_im]
    exact him.symm
  show 0 ≤ τ ((gelfandStarTransform A).symm f)
  rw [hfq, map_mul, map_star]
  exact hpos _

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.transportedFunctional_nonneg

/-- **Automatic continuity.** The transported functional is positive between
C⋆-algebras, hence bounded. -/
theorem transportedFunctional_exists_bound (τ : A →ₗ[ℂ] ℂ)
    (hpos : ∀ x : A, 0 ≤ τ (star x * x)) :
    ∃ C : ℝ, ∀ f : C(characterSpace ℂ A, ℂ),
      ‖transportedFunctional τ f‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ := PositiveLinearMap.exists_norm_apply_le
    (PositiveLinearMap.mk₀ (transportedFunctional τ) (transportedFunctional_nonneg τ hpos))
  exact ⟨C, hC⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.transportedFunctional_exists_bound

/-- The transported functional as a continuous linear functional. -/
def transportedCLM (τ : A →ₗ[ℂ] ℂ) (hpos : ∀ x : A, 0 ≤ τ (star x * x)) :
    C(characterSpace ℂ A, ℂ) →L[ℂ] ℂ :=
  (transportedFunctional τ).mkContinuousOfExistsBound
    (transportedFunctional_exists_bound τ hpos)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.transportedCLM

theorem transportedCLM_apply (τ : A →ₗ[ℂ] ℂ) (hpos : ∀ x : A, 0 ≤ τ (star x * x))
    (f : C(characterSpace ℂ A, ℂ)) :
    transportedCLM τ hpos f = τ ((gelfandStarTransform A).symm f) :=
  rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.transportedCLM_apply

/-- The transported continuous functional is positive. -/
theorem transportedCLM_nonneg (τ : A →ₗ[ℂ] ℂ) (hpos : ∀ x : A, 0 ≤ τ (star x * x))
    (f : C(characterSpace ℂ A, ℂ)) (hf : 0 ≤ f) :
    0 ≤ transportedCLM τ hpos f :=
  transportedFunctional_nonneg τ hpos f hf

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.transportedCLM_nonneg

/-- The transported continuous functional is unital. -/
theorem transportedCLM_one (τ : A →ₗ[ℂ] ℂ) (hpos : ∀ x : A, 0 ≤ τ (star x * x))
    (hone : τ 1 = 1) :
    transportedCLM τ hpos 1 = 1 := by
  show τ ((gelfandStarTransform A).symm 1) = 1
  rw [map_one, hone]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.transportedCLM_one

/-- The transported functional reads `τ` back on Gelfand transforms. -/
theorem transportedCLM_gelfand (τ : A →ₗ[ℂ] ℂ) (hpos : ∀ x : A, 0 ≤ τ (star x * x))
    (a : A) :
    transportedCLM τ hpos (gelfandStarTransform A a) = τ a := by
  show τ ((gelfandStarTransform A).symm (gelfandStarTransform A a)) = τ a
  rw [StarAlgEquiv.symm_apply_apply]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.transportedCLM_gelfand

end

end CommutativeQD
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
