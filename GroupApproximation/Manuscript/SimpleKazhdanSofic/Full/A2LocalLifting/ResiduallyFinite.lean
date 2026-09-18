import GroupApproximation.Algebra.FiniteResidual
import GroupApproximation.Algebra.MalcevLinear
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import GroupApproximation.Meta.AxiomGuard

/-!
# Separating orthogonal representations give residual finiteness (table row A2)

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.54–59 (table row A2): Ozawa's remark that
the full C⋆-algebra of an infinite simple hyperlinear Kazhdan group has no local lifting property
runs through Kirchberg's factorization theorem, whose last step is residual finiteness.

A finitely generated group is residually finite as soon as every nontrivial element acts
nontrivially in some finite-dimensional orthogonal representation.  The image in the general
linear group of that representation is a finitely generated linear group, hence residually finite
by Mal'cev's theorem (`MalcevLinear.residuallyFinite_of_fg`), and the finite residual maps into
the finite residual of the image, which is trivial.

This is a fork, into lane `A2LocalLifting`, of the never-wired module
`Algebra/OrthogonalRepresentationResiduallyFinite.lean` (left untouched).

Kirchberg, *Discrete groups with Kazhdan's property T and factorization property are residually
finite*, Math. Ann. **299** (1994), Theorem 1.1, last step.
-/

namespace GroupApproximation
namespace Full
namespace A2LocalLifting

universe u v

/-- Mathlib's residual finiteness gives the repository predicate `IsResiduallyFinite`. -/
theorem isResiduallyFinite_of_groupResiduallyFinite {H : Type v} [Group H]
    [hH : Group.ResiduallyFinite H] : IsResiduallyFinite H :=
  (isResiduallyFinite_iff (G := H)).mpr (Group.residuallyFinite_iff_exists_finiteIndex.mp hH)

section Matrix

variable {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Linear isometry equivalences as linear equivalences, multiplicatively. -/
def toLinearEquivHom : (W ≃ₗᵢ[ℝ] W) →* (W ≃ₗ[ℝ] W) where
  toFun e := e.toLinearEquiv
  map_one' := LinearEquiv.ext fun _ ↦ rfl
  map_mul' _ _ := LinearEquiv.ext fun _ ↦ rfl

/-- The matrix of a linear isometry equivalence in a basis. -/
noncomputable def matrixHom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ W) : (W ≃ₗᵢ[ℝ] W) →* Matrix.GeneralLinearGroup ι ℝ :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom).comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ W).symm.toMonoidHom.comp
      toLinearEquivHom)

/-- The underlying matrix of `matrixHom b e` is the matrix of `e` in the basis `b`. -/
theorem matrixHom_apply_val {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ W) (e : W ≃ₗᵢ[ℝ] W) :
    ((matrixHom b e : Matrix.GeneralLinearGroup ι ℝ) : Matrix ι ι ℝ) =
      LinearMap.toMatrix b b (e.toLinearEquiv : W →ₗ[ℝ] W) :=
  rfl

theorem matrixHom_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ W) : Function.Injective (matrixHom b) := by
  intro e e' h
  have h1 : LinearMap.toMatrix b b (e.toLinearEquiv : W →ₗ[ℝ] W) =
      LinearMap.toMatrix b b (e'.toLinearEquiv : W →ₗ[ℝ] W) := by
    rw [← matrixHom_apply_val, ← matrixHom_apply_val, h]
  have h2 : (e.toLinearEquiv : W →ₗ[ℝ] W) = (e'.toLinearEquiv : W →ₗ[ℝ] W) :=
    (LinearMap.toMatrix b b).injective h1
  exact LinearIsometryEquiv.toLinearEquiv_injective (LinearEquiv.toLinearMap_injective h2)

theorem matrixHom_ne_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ W) {e : W ≃ₗᵢ[ℝ] W} (he : e ≠ 1) : matrixHom b e ≠ 1 :=
  fun h ↦ he (matrixHom_injective b (h.trans (map_one (matrixHom b)).symm))

end Matrix

/-- **Separating finite-dimensional orthogonal representations give residual finiteness**
(Kirchberg 1994, Theorem 1.1, last step; the residually-finite ingredient of row A2, tex l.54–59).
A finitely generated group in which every nontrivial element acts nontrivially in some
finite-dimensional orthogonal representation is residually finite. -/
theorem isResiduallyFinite_of_forall_ne_one {G : Type u} [Group G] [hfg : Group.FG G]
    (hsep : ∀ x : G, x ≠ 1 → ∃ (W : Type v) (_ : NormedAddCommGroup W)
      (_ : InnerProductSpace ℝ W) (_ : FiniteDimensional ℝ W)
      (ρ : G →* (W ≃ₗᵢ[ℝ] W)), ρ x ≠ 1) :
    IsResiduallyFinite G := by
  classical
  show finiteResidual G = ⊥
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨W, i1, i2, i3, ρ, hρ⟩ := hsep x hx1
  let b := Module.finBasis ℝ W
  let ψ : G →* Matrix.GeneralLinearGroup (Fin (Module.finrank ℝ W)) ℝ := (matrixHom b).comp ρ
  have hrange : ψ.range.FG := by
    obtain ⟨S, hS⟩ : (⊤ : Subgroup G).FG := hfg.out
    refine ⟨S.image ψ, ?_⟩
    rw [MonoidHom.range_eq_map, ← hS, Finset.coe_image, MonoidHom.map_closure]
  haveI : Group.ResiduallyFinite ψ.range :=
    MalcevLinear.residuallyFinite_of_fg ψ.range hrange
  have hRF : finiteResidual ψ.range = ⊥ := isResiduallyFinite_of_groupResiduallyFinite
  have hmap : ψ.rangeRestrict x ∈ finiteResidual ψ.range :=
    map_finiteResidual_le ψ.rangeRestrict (Subgroup.mem_map_of_mem ψ.rangeRestrict hx)
  rw [hRF, Subgroup.mem_bot] at hmap
  have hψ : matrixHom b (ρ x) = 1 := congrArg Subtype.val hmap
  exact matrixHom_ne_one b hρ hψ

end A2LocalLifting
end Full
end GroupApproximation

open GroupApproximation.Full.A2LocalLifting

#audit_axioms isResiduallyFinite_of_forall_ne_one
