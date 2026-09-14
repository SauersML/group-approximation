import GroupApproximation.Algebra.FiniteResidual
import GroupApproximation.Algebra.MalcevLinear
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite-dimensional orthogonal representations and residual finiteness

A finitely generated group is residually finite as soon as every nontrivial
element acts nontrivially in some finite-dimensional orthogonal representation.
The image of the group in the general linear group of that representation is a
finitely generated linear group, hence residually finite by Mal'cev's theorem
(`MalcevLinear.residuallyFinite_of_fg`).  The finite residual maps into the
finite residual of the image, which is trivial.

This is the last step of Kirchberg's Theorem 1.1.
-/

namespace GroupApproximation
namespace OrthogonalRepresentationResiduallyFinite

open Matrix

universe u v

/-- Mathlib's residual finiteness gives the repository predicate. -/
theorem isResiduallyFinite_of_groupResiduallyFinite {H : Type v} [Group H]
    [Group.ResiduallyFinite H] : IsResiduallyFinite H := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  exact Group.residuallyFinite_iff_forall_finiteIndex.mp ‹_› x
    (fun L hL ↦ mem_finiteResidual_iff.mp hx L hL)

section Matrix

variable {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Linear isometry equivalences as linear equivalences, multiplicatively. -/
def toLinearEquivHom : (W ≃ₗᵢ[ℝ] W) →* (W ≃ₗ[ℝ] W) where
  toFun e := e.toLinearEquiv
  map_one' := LinearEquiv.ext fun _ ↦ rfl
  map_mul' _ _ := LinearEquiv.ext fun _ ↦ rfl

/-- The matrix of a linear isometry equivalence in a basis. -/
noncomputable def matrixHom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ W) : (W ≃ₗᵢ[ℝ] W) →* GeneralLinearGroup ι ℝ :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom).comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ W).symm.toMonoidHom.comp
      toLinearEquivHom)

theorem matrixHom_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ W) : Function.Injective (matrixHom b) := by
  intro e e' h
  have h1 := congrArg (fun u : GeneralLinearGroup ι ℝ ↦ (u : Matrix ι ι ℝ)) h
  have h2 : ((LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ W).symm e.toLinearEquiv :
        Module.End ℝ W) =
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ W).symm e'.toLinearEquiv :
        Module.End ℝ W) :=
    (LinearMap.toMatrixAlgEquiv b).injective h1
  have h3 := Units.ext h2
  exact LinearIsometryEquiv.toLinearEquiv_injective
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ W).symm.injective h3)

theorem matrixHom_ne_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ W) {e : W ≃ₗᵢ[ℝ] W} (he : e ≠ 1) : matrixHom b e ≠ 1 :=
  fun h ↦ he (matrixHom_injective b (h.trans (map_one _).symm))

end Matrix

/-- **Separating finite-dimensional orthogonal representations give residual
finiteness.** -/
theorem isResiduallyFinite_of_forall_ne_one {G : Type u} [Group G] [hfg : Group.FG G]
    (hsep : ∀ x : G, x ≠ 1 → ∃ (W : Type v) (_ : NormedAddCommGroup W)
      (_ : InnerProductSpace ℝ W) (_ : FiniteDimensional ℝ W)
      (ρ : G →* (W ≃ₗᵢ[ℝ] W)), ρ x ≠ 1) :
    IsResiduallyFinite G := by
  classical
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨W, i1, i2, i3, ρ, hρ⟩ := hsep x hx1
  let b := Module.finBasis ℝ W
  let ψ : G →* GeneralLinearGroup (Fin (Module.finrank ℝ W)) ℝ := (matrixHom b).comp ρ
  have hrange : ψ.range.FG := by
    obtain ⟨S, hS⟩ : (⊤ : Subgroup G).FG := hfg.out
    refine ⟨S.image ψ, ?_⟩
    rw [MonoidHom.range_eq_map, ← hS, Finset.coe_image, MonoidHom.map_closure]
  haveI : Group.ResiduallyFinite ψ.range := MalcevLinear.residuallyFinite_of_fg ψ.range hrange
  have hRF : IsResiduallyFinite ψ.range := isResiduallyFinite_of_groupResiduallyFinite
  have hmap : ψ.rangeRestrict x ∈ finiteResidual ψ.range :=
    map_finiteResidual_le ψ.rangeRestrict ⟨x, hx, rfl⟩
  rw [hRF, Subgroup.mem_bot] at hmap
  have hψ : ψ x = 1 := by
    have := congrArg Subtype.val hmap
    simpa using this
  exact matrixHom_ne_one b hρ hψ

end OrthogonalRepresentationResiduallyFinite
end GroupApproximation
