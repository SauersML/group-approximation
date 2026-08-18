import GroupApproximation.Analysis.CStarStinespringRep

/-!
# The Stinespring dilation identity

## What this module proves

The last piece of the dilation: the intertwiner `V : H → K` sending `x`
to the class of `1 ⊗ x`, and the identity

  `⟪V x, π(c) (V y)⟫ = ⟪x, φ(c) y⟫`,   i.e.   `V* ∘ π(c) ∘ V = φ(c)`.

At the level of the free model the identity is almost definitional:
`π(c)` carries `1 ⊗ y` to `c ⊗ y`, and the form pairs `1 ⊗ x` with
`c ⊗ y` to `⟪x, φ(star 1 * c) y⟫ = ⟪x, φ(c) y⟫`.  The only analysis is
the boundedness of `V`, which is the operator norm of `φ(1)`.

* `stinespringV` -- the intertwiner, with `‖V x‖ ≤ √‖φ(1)‖ ‖x‖`;
* `inner_stinespringV_repOp` -- the identity in inner-product form;
* `stinespring_dilation` -- the identity in operator form.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `RE.05`
remains **MISSING**.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace
open UniformSpace

universe u w

variable {A : Type u} [CStarAlgebra A]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (φ : A →ₗ[ℂ] (H →L[ℂ] H)) (hφ : IsCompletelyPositive φ)

/-- The vector `1 ⊗ x` of the pre-space, as a linear map in `x`. -/
noncomputable def stinespringSingleOne : H →ₗ[ℂ] StinespringPre φ hφ where
  toFun x := toStinespringPre φ hφ (Finsupp.single 1 x)
  map_add' x y := by
    show toStinespringPre φ hφ (Finsupp.single 1 (x + y)) = _
    rw [Finsupp.single_add, map_add]
  map_smul' r x := by
    show toStinespringPre φ hφ (Finsupp.single 1 (r • x)) = _
    rw [Finsupp.smul_single, map_smul]
    rfl

theorem norm_stinespringSingleOne_le (x : H) :
    ‖stinespringSingleOne φ hφ x‖ ≤ Real.sqrt ‖φ 1‖ * ‖x‖ := by
  rw [stinespringPre_norm_def]
  have h1 : stinespringSesq φ
      (ofStinespringPre φ hφ (stinespringSingleOne φ hφ x))
      (ofStinespringPre φ hφ (stinespringSingleOne φ hφ x))
      = ⟪x, φ 1 x⟫_ℂ := by
    show stinespringSesq φ (Finsupp.single 1 x) (Finsupp.single 1 x)
      = ⟪x, φ 1 x⟫_ℂ
    rw [stinespringSesq_single, star_one, one_mul]
  rw [h1]
  have h2 : (⟪x, φ 1 x⟫_ℂ).re ≤ ‖φ 1‖ * ‖x‖ ^ 2 := by
    refine (Complex.re_le_norm _).trans ?_
    refine (norm_inner_le_norm _ _).trans ?_
    have h3 : ‖(φ 1) x‖ ≤ ‖φ 1‖ * ‖x‖ := (φ 1).le_opNorm x
    calc ‖x‖ * ‖(φ 1) x‖ ≤ ‖x‖ * (‖φ 1‖ * ‖x‖) := by
          gcongr
      _ = ‖φ 1‖ * ‖x‖ ^ 2 := by ring
  calc Real.sqrt (⟪x, φ 1 x⟫_ℂ).re
      ≤ Real.sqrt (‖φ 1‖ * ‖x‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt ‖φ 1‖ * ‖x‖ := by
        rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg x)]

/-- **The Stinespring intertwiner** `V : H → K`, `x ↦ [1 ⊗ x]`. -/
noncomputable def stinespringV : H →L[ℂ] StinespringSpace φ hφ :=
  (UniformSpace.Completion.toComplL).comp
    (LinearMap.mkContinuous (stinespringSingleOne φ hφ)
      (Real.sqrt ‖φ 1‖) (norm_stinespringSingleOne_le φ hφ))

theorem stinespringV_apply (x : H) :
    stinespringV φ hφ x
      = ((stinespringSingleOne φ hφ x : StinespringPre φ hφ) :
          StinespringSpace φ hφ) := rfl

/-- **The dilation identity, inner form**:
`⟪V x, π(c) (V y)⟫ = ⟪x, φ(c) y⟫`. -/
theorem inner_stinespringV_repOp (c : A) (x y : H) :
    ⟪stinespringV φ hφ x,
        stinespringRepOp φ hφ c (stinespringV φ hφ y)⟫_ℂ
      = ⟪x, φ c y⟫_ℂ := by
  rw [stinespringV_apply, stinespringV_apply, stinespringRepOp_coe,
    Completion.inner_coe]
  have hact : stinespringActCLM φ hφ c (stinespringSingleOne φ hφ y)
      = toStinespringPre φ hφ (Finsupp.single c y) := by
    show toStinespringPre φ hφ
        (stinespringActFree c (Finsupp.single 1 y)) = _
    rw [stinespringActFree_single, mul_one]
  rw [hact]
  show stinespringSesq φ (Finsupp.single 1 x) (Finsupp.single c y)
    = ⟪x, φ c y⟫_ℂ
  rw [stinespringSesq_single, star_one, one_mul]

/-- **The Stinespring dilation identity, operator form**:
`V* ∘ π(c) ∘ V = φ(c)`. -/
theorem stinespring_dilation (c : A) :
    (ContinuousLinearMap.adjoint (stinespringV φ hφ)).comp
        ((stinespringRepOp φ hφ c).comp (stinespringV φ hφ))
      = φ c := by
  refine ContinuousLinearMap.ext fun y => ?_
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  exact inner_stinespringV_repOp φ hφ c x y

end CStarExactness
end GroupApproximation
