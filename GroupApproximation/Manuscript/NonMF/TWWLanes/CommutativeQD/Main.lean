import GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.Statement
import GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.DiagonalModel
import GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.Positivity
import GroupApproximation.Analysis.ShulmanTraceClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# Tracial states on separable commutative C⋆-algebras are quasidiagonal

Lane `nm-tww-02`: *every tracial state on a separable unital commutative C⋆-algebra is
quasidiagonal*, over the interface `PointEvaluationAverageStatement` of lane `nm-tww-01`.

## Route

1. Put `Γ : A ≃⋆ₐ C(Χ, ℂ)` for Gelfand duality, with `Χ = characterSpace ℂ A`. Transport
   `τ` to the positive, unital, automatically continuous functional `τ ∘ Γ⁻¹`
   (`Positivity.lean`).
2. Apply `nm-tww-01` to it on the finite set `Γ(F)`. This gives points `x₁, …, x_N ∈ Χ`
   with `‖τ a − N⁻¹ ∑ᵢ xᵢ(a)‖ ≤ ε` for `a ∈ F`, because `Γ a (xᵢ) = xᵢ(a)`.
3. The diagonal `⋆`-homomorphism `a ↦ diag(xᵢ(a))` is a unital completely positive local
   model with zero multiplicative defect (`DiagonalModel.lean`). So `τ` is locally
   quasidiagonal, and by separability it is quasidiagonal
   (`Quasidiagonal.isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace`).

Traciality is not used, since it is automatic in a commutative algebra. Only
`τ 1 = 1` and `τ(x⋆x) ≥ 0` enter. Continuity of `τ` is not assumed.

## Endpoints

* `isQuasidiagonalTrace_of_commCStarAlgebra_of_pointEvaluationAverage`: for a
  `CommCStarAlgebra` and a linear `τ`.
* `isQuasidiagonalTrace_of_commutative_of_pointEvaluationAverage`: for a `CStarAlgebra`
  with `hcomm : ∀ a b, a * b = b * a`. A local commutative instance is built from `hcomm`.
* `isQuasidiagonalTrace_of_commutative_isTracialState_of_pointEvaluationAverage`: the lane
  shape, with `τ : A → ℂ` and `hτ : IsTracialState τ`.
* The corollaries `..._tracialState_...` and `..._faithfulTracialState_...` are for the
  bundled structures that `nm-tww-05` uses.

## Remaining gap

This is only `PointEvaluationAverageStatement`, the interface of lane `nm-tww-01`, which
is recorded in `Statement.lean` together with its truth check. It is strictly smaller in
proof content than the target. It concerns a single positive functional on `C(X)` and
says nothing about matrices, complete positivity, Gelfand duality or separability.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace CommutativeQD

open WeakDual Quasidiagonal
open scoped ComplexOrder

universe u

/-- **Lane `nm-tww-02`, commutative-instance form.** Let `A` be a separable commutative
unital C⋆-algebra and `τ` a unital linear functional with `τ(x⋆x) ≥ 0`. Then `τ` is a
quasidiagonal trace, given the point-evaluation interface of `nm-tww-01`. -/
theorem isQuasidiagonalTrace_of_commCStarAlgebra_of_pointEvaluationAverage
    (hPE : PointEvaluationAverageStatement.{u}) {A : Type u} [CommCStarAlgebra A]
    (hsep : TopologicalSpace.SeparableSpace A) (τ : A →ₗ[ℂ] ℂ) (hone : τ 1 = 1)
    (hpos : ∀ x : A, 0 ≤ τ (star x * x)) :
    IsQuasidiagonalTrace (fun a : A ↦ τ a) := by
  classical
  apply isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace hsep
  apply isLocallyQuasidiagonalTrace_of_characterAverages
  intro F ε hε
  obtain ⟨N, x, hx⟩ := hPE (characterSpace ℂ A) (transportedCLM τ hpos)
    (transportedCLM_nonneg τ hpos) (transportedCLM_one τ hpos hone)
    (F.image (gelfandStarTransform A)) ε hε
  refine ⟨N, fun i ↦ StarAlgHomClass.toStarAlgHom (x i), fun a ha ↦ ?_⟩
  have h := hx (gelfandStarTransform A a) (Finset.mem_image_of_mem _ ha)
  have hsum : (N : ℂ)⁻¹ * ∑ i, (gelfandStarTransform A a) (x i) =
      (N : ℂ)⁻¹ * ∑ i, (StarAlgHomClass.toStarAlgHom (x i) : A →⋆ₐ[ℂ] ℂ) a :=
    rfl
  rw [transportedCLM_gelfand, hsum] at h
  exact h

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.isQuasidiagonalTrace_of_commCStarAlgebra_of_pointEvaluationAverage

/-- **Lane `nm-tww-02`, commutation-hypothesis form.** This is the same statement for a
`CStarAlgebra` whose multiplication commutes. A commutative instance is assembled locally
from `hcomm`. It agrees with the ambient `CStarAlgebra` structure by structure eta. -/
theorem isQuasidiagonalTrace_of_commutative_of_pointEvaluationAverage
    (hPE : PointEvaluationAverageStatement.{u}) {A : Type u} [CStarAlgebra A]
    [TopologicalSpace.SeparableSpace A] (hcomm : ∀ a b : A, a * b = b * a)
    (τ : A →ₗ[ℂ] ℂ) (hone : τ 1 = 1) (hpos : ∀ x : A, 0 ≤ τ (star x * x)) :
    IsQuasidiagonalTrace (fun a : A ↦ τ a) := by
  letI : CommCStarAlgebra A :=
    { (inferInstance : CStarAlgebra A) with mul_comm := hcomm }
  exact isQuasidiagonalTrace_of_commCStarAlgebra_of_pointEvaluationAverage hPE
    (inferInstance : TopologicalSpace.SeparableSpace A) τ hone hpos

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.isQuasidiagonalTrace_of_commutative_of_pointEvaluationAverage

/-- A continuous-functional form, matching the lane's suggested signature. -/
theorem isQuasidiagonalTrace_of_commutative_clm_of_pointEvaluationAverage
    (hPE : PointEvaluationAverageStatement.{u}) {A : Type u} [CStarAlgebra A]
    [TopologicalSpace.SeparableSpace A] (hcomm : ∀ a b : A, a * b = b * a)
    (τ : A →L[ℂ] ℂ) (hone : τ 1 = 1) (hpos : ∀ x : A, 0 ≤ τ (star x * x)) :
    IsQuasidiagonalTrace (fun a : A ↦ τ a) :=
  isQuasidiagonalTrace_of_commutative_of_pointEvaluationAverage hPE hcomm
    (τ : A →ₗ[ℂ] ℂ) hone hpos

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.isQuasidiagonalTrace_of_commutative_clm_of_pointEvaluationAverage

/-- **Every tracial state on a separable unital commutative C⋆-algebra is
quasidiagonal**, for a bundled `TracialState`. -/
theorem isQuasidiagonalTrace_of_commutative_tracialState_of_pointEvaluationAverage
    (hPE : PointEvaluationAverageStatement.{u}) {A : Type u} [CStarAlgebra A]
    [TopologicalSpace.SeparableSpace A] (hcomm : ∀ a b : A, a * b = b * a)
    (τ : TracialState A) :
    IsQuasidiagonalTrace (fun a : A ↦ τ a) :=
  isQuasidiagonalTrace_of_commutative_of_pointEvaluationAverage hPE hcomm
    τ.toLinearMap τ.map_one τ.map_star_mul_self_nonneg

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.isQuasidiagonalTrace_of_commutative_tracialState_of_pointEvaluationAverage

/-- The same for a bundled `FaithfulTracialState`. Faithfulness is not used. -/
theorem isQuasidiagonalTrace_of_commutative_faithfulTracialState_of_pointEvaluationAverage
    (hPE : PointEvaluationAverageStatement.{u}) {A : Type u} [CStarAlgebra A]
    [TopologicalSpace.SeparableSpace A] (hcomm : ∀ a b : A, a * b = b * a)
    (τ : FaithfulTracialState A) :
    IsQuasidiagonalTrace (fun a : A ↦ τ a) :=
  isQuasidiagonalTrace_of_commutative_of_pointEvaluationAverage hPE hcomm
    τ.toLinearMap τ.map_one τ.map_star_mul_self_nonneg

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.isQuasidiagonalTrace_of_commutative_faithfulTracialState_of_pointEvaluationAverage

/-- **Lane shape.** A function `τ : A → ℂ` that is a tracial state (`IsTracialState`) on a
separable unital commutative C⋆-algebra is a quasidiagonal trace. -/
theorem isQuasidiagonalTrace_of_commutative_isTracialState_of_pointEvaluationAverage
    (hPE : PointEvaluationAverageStatement.{u}) {A : Type u} [CStarAlgebra A]
    [TopologicalSpace.SeparableSpace A] (hcomm : ∀ a b : A, a * b = b * a)
    {τ : A → ℂ} (hτ : IsTracialState τ) :
    IsQuasidiagonalTrace τ := by
  obtain ⟨σ, hσ⟩ := hτ
  have heq : (fun a : A ↦ σ a) = τ := funext hσ
  rw [← heq]
  exact isQuasidiagonalTrace_of_commutative_tracialState_of_pointEvaluationAverage hPE
    hcomm σ

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.isQuasidiagonalTrace_of_commutative_isTracialState_of_pointEvaluationAverage

end CommutativeQD
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
