import GroupApproximation.Analysis.CStarTensorProductSeminorm
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Star.TensorProduct

/-!
# The spatial (minimal) C⋆-norm on an algebraic tensor product

## What this file constructs

Given ⋆-representations `π` of a complex ⋆-algebra `A` on an inner product
space `H` and `ρ` of `B` on `K`, this file builds the **product
representation** of the algebraic tensor product `A ⊗[ℂ] B` on `H ⊗[ℂ] K`,
sending `a ⊗ₜ b` to `S ↦ π a ⊗ ρ b`, and shows that it is again a
⋆-representation by adjointable operators.  Combining with
`StarRep.isCStarSeminorm` from `CStarTensorProductSeminorm.lean`, the
**spatial seminorm**

  `‖x‖_{π,ρ} = ‖(π ⊗ ρ)(x)‖`

is a C⋆-seminorm on `A ⊗[ℂ] B`, and a C⋆-norm when the product representation
is faithful.  It is also proved to be a **cross norm** on elementary tensors:
`‖a ⊗ₜ b‖_{π,ρ} = ‖π a‖ * ‖ρ b‖`, via the equality `‖S ⊗ T‖ = ‖S‖ * ‖T‖`
(`norm_mapL`), which Mathlib states only as an inequality.

No completeness of `H` or `K` is used, so nothing here needs a Hilbert-space
tensor product: the operator algebra lives on the *algebraic* tensor product,
which by `Mathlib/Analysis/InnerProductSpace/TensorProduct.lean` is an inner
product space in its own right.  See `CStarTensorProduct.lean` for the full
roadmap and for what this does *not* achieve --- namely independence of the
norm from the chosen pair of representations, which is Takesaki's theorem and
is what would make `⊗_min` canonical.

## What Mathlib supplies, and what it does not

The pinned revision does have, in
`Mathlib/Analysis/InnerProductSpace/TensorProduct.lean`, the inner product
space structure on `E ⊗[𝕜] F` with `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`, the
continuous map `TensorProduct.mapL`, and `norm_mapL_le : ‖mapL f g‖ ≤ ‖f‖ ‖g‖`;
and in `Mathlib/Algebra/Star/TensorProduct.lean` and
`Mathlib/RingTheory/TensorProduct/Basic.lean` the full ⋆-ring structure on
`A ⊗[R] B` with `star (a ⊗ₜ b) = star a ⊗ₜ star b`.  It does **not** have: the
adjoint of `mapL f g`, the reverse inequality `‖S‖ ‖T‖ ≤ ‖mapL S T‖`, any
C⋆-norm on a tensor product, or the minimal tensor product itself.  The first
three are supplied here.

## Contents

* `isAdjoint_mapL` --- `mapL S' T'` is an adjoint of `mapL S T`.
* `norm_mapL` --- `‖mapL S T‖ = ‖S‖ * ‖T‖`.
* `rTensorAlgHom`, `lTensorAlgHom` --- amplification as algebra maps.
* `spatialHom`, `spatialRep` --- the product representation.
* `spatialNorm`, `spatialNorm_isCStarSeminorm`, `spatialNorm_tmul`,
  `spatialNorm_isCStarNorm_of_injective`.

## Manuscript status

Infrastructure; certifies no manuscript step.  The exactness and nuclearity
rows remain **MISSING**.
-/

namespace GroupApproximation
namespace CStarTensor

open scoped InnerProductSpace TensorProduct

universe u v w x

variable {A : Type u} {B : Type v} [Ring A] [StarRing A] [Algebra ℂ A]
  [StarModule ℂ A] [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
variable {H : Type w} {K : Type x} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-! ## Adjoints of tensor products of operators -/

/-- **The adjoint of a tensor product of operators is the tensor product of
the adjoints.**  Checked on elementary tensors, where it is exactly
`⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫ ⟪b, d⟫`, and extended by additivity in each
variable. -/
theorem isAdjoint_mapL {S S' : H →L[ℂ] H} {T T' : K →L[ℂ] K}
    (hS : IsAdjoint S S') (hT : IsAdjoint T T') :
    IsAdjoint (TensorProduct.mapL S T) (TensorProduct.mapL S' T') := by
  have key : ∀ (a : H) (b : K) (v : H ⊗[ℂ] K),
      ⟪TensorProduct.mapL S T (a ⊗ₜ[ℂ] b), v⟫_ℂ
        = ⟪(a ⊗ₜ[ℂ] b : H ⊗[ℂ] K), TensorProduct.mapL S' T' v⟫_ℂ := by
    intro a b v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
        rw [TensorProduct.mapL_tmul, TensorProduct.mapL_tmul,
          TensorProduct.inner_tmul, TensorProduct.inner_tmul, hS a c, hT b d]
    | add v₁ v₂ h₁ h₂ =>
        rw [map_add, inner_add_right, inner_add_right, h₁, h₂]
  intro u v
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => exact key a b v
  | add u₁ u₂ h₁ h₂ =>
      rw [map_add, inner_add_left, inner_add_left, h₁, h₂]

/-! ## The norm of a tensor product of operators

Mathlib proves `‖mapL S T‖ ≤ ‖S‖ * ‖T‖`.  The reverse inequality is what makes
the spatial norm a *cross* norm, and it is proved here by cancelling the two
factors one at a time. -/

/-- If `‖S ξ‖ * d ≤ c * ‖ξ‖` for every `ξ`, then `‖S‖ * d ≤ c`.  The point is
the degenerate case `d = 0`, where no cancellation is available. -/
private theorem opNorm_mul_le_of_forall {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (S : E →L[ℂ] F)
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (h : ∀ ξ : E, ‖S ξ‖ * d ≤ c * ‖ξ‖) :
    ‖S‖ * d ≤ c := by
  rcases eq_or_lt_of_le hd with hz | hpos
  · rw [← hz, mul_zero]
    exact hc
  · have hbound : ∀ ξ : E, ‖S ξ‖ ≤ (c / d) * ‖ξ‖ := by
      intro ξ
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
      exact h ξ
    have hSle : ‖S‖ ≤ c / d :=
      S.opNorm_le_bound (div_nonneg hc (le_of_lt hpos)) hbound
    rwa [le_div_iff₀ hpos] at hSle

/-- **The operator norm is multiplicative on tensor products of operators**,
`‖S ⊗ T‖ = ‖S‖ * ‖T‖`.  Mathlib supplies only `≤`; the reverse inequality is
the cross-norm property of the spatial tensor norm. -/
theorem norm_mapL (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    ‖TensorProduct.mapL S T‖ = ‖S‖ * ‖T‖ := by
  refine le_antisymm (TensorProduct.norm_mapL_le S T) ?_
  have hCnn : (0 : ℝ) ≤ ‖TensorProduct.mapL S T‖ := norm_nonneg _
  have hpt : ∀ (ξ : H) (η : K),
      ‖S ξ‖ * ‖T η‖ ≤ ‖TensorProduct.mapL S T‖ * (‖ξ‖ * ‖η‖) := by
    intro ξ η
    have h2 := (TensorProduct.mapL S T).le_opNorm (ξ ⊗ₜ[ℂ] η)
    simp only [TensorProduct.mapL_tmul, TensorProduct.norm_tmul] at h2
    exact h2
  have step1 : ∀ η : K, ‖S‖ * ‖T η‖ ≤ ‖TensorProduct.mapL S T‖ * ‖η‖ := by
    intro η
    refine opNorm_mul_le_of_forall S (mul_nonneg hCnn (norm_nonneg η))
      (norm_nonneg (T η)) ?_
    intro ξ
    calc ‖S ξ‖ * ‖T η‖
        ≤ ‖TensorProduct.mapL S T‖ * (‖ξ‖ * ‖η‖) := hpt ξ η
      _ = ‖TensorProduct.mapL S T‖ * ‖η‖ * ‖ξ‖ := by ring
  have step2 : ‖T‖ * ‖S‖ ≤ ‖TensorProduct.mapL S T‖ := by
    refine opNorm_mul_le_of_forall T hCnn (norm_nonneg S) ?_
    intro η
    calc ‖T η‖ * ‖S‖ = ‖S‖ * ‖T η‖ := mul_comm _ _
      _ ≤ ‖TensorProduct.mapL S T‖ * ‖η‖ := step1 η
  calc ‖S‖ * ‖T‖ = ‖T‖ * ‖S‖ := mul_comm _ _
    _ ≤ ‖TensorProduct.mapL S T‖ := step2

/-! ## Amplification as algebra homomorphisms -/

variable (K) in
/-- Amplification `S ↦ S ⊗ 1` as a `ℂ`-linear map. -/
noncomputable def rTensorₗ :
    (H →L[ℂ] H) →ₗ[ℂ] ((H ⊗[ℂ] K) →L[ℂ] (H ⊗[ℂ] K)) where
  toFun S := S.rTensor K
  map_add' S S' := by simp
  map_smul' c S := by simp

variable (H) in
/-- Amplification `T ↦ 1 ⊗ T` as a `ℂ`-linear map. -/
noncomputable def lTensorₗ :
    (K →L[ℂ] K) →ₗ[ℂ] ((H ⊗[ℂ] K) →L[ℂ] (H ⊗[ℂ] K)) where
  toFun T := T.lTensor H
  map_add' T T' := by simp
  map_smul' c T := by simp

variable (K) in
/-- Amplification `S ↦ S ⊗ 1` as a homomorphism of `ℂ`-algebras. -/
noncomputable def rTensorAlgHom :
    (H →L[ℂ] H) →ₐ[ℂ] ((H ⊗[ℂ] K) →L[ℂ] (H ⊗[ℂ] K)) :=
  AlgHom.ofLinearMap (rTensorₗ K)
    (by
      show (1 : H →L[ℂ] H).rTensor K = 1
      simp)
    (fun S S' => by
      show (S * S').rTensor K = S.rTensor K * S'.rTensor K
      rw [ContinuousLinearMap.rTensor_mul])

variable (H) in
/-- Amplification `T ↦ 1 ⊗ T` as a homomorphism of `ℂ`-algebras. -/
noncomputable def lTensorAlgHom :
    (K →L[ℂ] K) →ₐ[ℂ] ((H ⊗[ℂ] K) →L[ℂ] (H ⊗[ℂ] K)) :=
  AlgHom.ofLinearMap (lTensorₗ H)
    (by
      show (1 : K →L[ℂ] K).lTensor H = 1
      simp)
    (fun T T' => by
      show (T * T').lTensor H = T.lTensor H * T'.lTensor H
      rw [ContinuousLinearMap.lTensor_mul])

@[simp] theorem rTensorAlgHom_apply (S : H →L[ℂ] H) :
    rTensorAlgHom K S = S.rTensor K := rfl

@[simp] theorem lTensorAlgHom_apply (T : K →L[ℂ] K) :
    lTensorAlgHom H T = T.lTensor H := rfl

/-- The two amplifications commute: `(S ⊗ 1)(1 ⊗ T) = (1 ⊗ T)(S ⊗ 1)`, both
being `S ⊗ T`. -/
theorem commute_rTensor_lTensor (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    Commute (S.rTensor K) (T.lTensor H) := by
  show S.rTensor K * T.lTensor H = T.lTensor H * S.rTensor K
  refine ContinuousLinearMap.ext fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
      show (S.rTensor K) ((T.lTensor H) (u ⊗ₜ[ℂ] v))
        = (T.lTensor H) ((S.rTensor K) (u ⊗ₜ[ℂ] v))
      rw [ContinuousLinearMap.lTensor_tmul, ContinuousLinearMap.rTensor_tmul,
        ContinuousLinearMap.rTensor_tmul, ContinuousLinearMap.lTensor_tmul]
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]

/-! ## The product representation and the spatial norm -/

/-- The **product representation** `π ⊗ ρ` of `A ⊗[ℂ] B` on `H ⊗[ℂ] K`, as an
algebra homomorphism.  It exists because the two amplifications commute. -/
noncomputable def spatialHom (π : StarRep A H) (ρ : StarRep B K) :
    (A ⊗[ℂ] B) →ₐ[ℂ] ((H ⊗[ℂ] K) →L[ℂ] (H ⊗[ℂ] K)) :=
  Algebra.TensorProduct.lift
    ((rTensorAlgHom K).comp π.hom)
    ((lTensorAlgHom H).comp ρ.hom)
    (fun a b => commute_rTensor_lTensor (π.hom a) (ρ.hom b))

@[simp] theorem spatialHom_tmul (π : StarRep A H) (ρ : StarRep B K)
    (a : A) (b : B) :
    spatialHom π ρ (a ⊗ₜ[ℂ] b) = TensorProduct.mapL (π.hom a) (ρ.hom b) := rfl

/-- **The product representation is a ⋆-representation.**  Adjointability is
checked on elementary tensors by `isAdjoint_mapL` and extended by additivity;
`star` on the algebraic tensor product is Mathlib's, with
`star (a ⊗ₜ b) = star a ⊗ₜ star b`. -/
noncomputable def spatialRep (π : StarRep A H) (ρ : StarRep B K) :
    StarRep (A ⊗[ℂ] B) (H ⊗[ℂ] K) where
  hom := spatialHom π ρ
  isAdjoint_star := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
        simp only [star_zero, map_zero]
        exact isAdjoint_zero
    | tmul a b =>
        rw [TensorProduct.star_tmul, spatialHom_tmul, spatialHom_tmul]
        exact isAdjoint_mapL (π.isAdjoint_star a) (ρ.isAdjoint_star b)
    | add x y hx hy =>
        simp only [star_add, map_add]
        exact hx.add hy

/-- The **spatial seminorm** attached to a pair of ⋆-representations. -/
noncomputable def spatialNorm (π : StarRep A H) (ρ : StarRep B K) :
    (A ⊗[ℂ] B) → ℝ :=
  (spatialRep π ρ).seminorm

@[simp] theorem spatialNorm_apply (π : StarRep A H) (ρ : StarRep B K)
    (x : A ⊗[ℂ] B) : spatialNorm π ρ x = ‖spatialHom π ρ x‖ := rfl

/-- **The spatial seminorm is a C⋆-seminorm.**  This is the whole point of the
construction, and it follows with no further analysis from
`StarRep.isCStarSeminorm`, which needs no completeness. -/
theorem spatialNorm_isCStarSeminorm (π : StarRep A H) (ρ : StarRep B K) :
    IsCStarSeminorm (spatialNorm π ρ) :=
  (spatialRep π ρ).isCStarSeminorm

/-- **The spatial seminorm is a cross norm on elementary tensors**:
`‖a ⊗ₜ b‖ = ‖π a‖ * ‖ρ b‖`.

When `π` and `ρ` are faithful representations of C⋆-algebras on Hilbert
spaces, injective ⋆-homomorphisms of C⋆-algebras are isometric, so the right
side is `‖a‖ * ‖b‖`; that upgrade is not available at this level of
generality, where the target `H →L[ℂ] H` need not be a C⋆-algebra because `H`
need not be complete. -/
theorem spatialNorm_tmul (π : StarRep A H) (ρ : StarRep B K) (a : A) (b : B) :
    spatialNorm π ρ (a ⊗ₜ[ℂ] b) = ‖π.hom a‖ * ‖ρ.hom b‖ := by
  show ‖spatialHom π ρ (a ⊗ₜ[ℂ] b)‖ = ‖π.hom a‖ * ‖ρ.hom b‖
  rw [spatialHom_tmul]
  exact norm_mapL (π.hom a) (ρ.hom b)

/-- **A faithful product representation makes the spatial seminorm a
C⋆-norm.**

This is as far as the spatial construction goes without Takesaki's theorem:
the norm is completely constructed and all its C⋆-axioms are proved, but it is
attached to the chosen pair `(π, ρ)`.  Independence of that choice --- which
is what makes `⊗_min` canonical, and what is needed before `A ⊗_min B` can be
written --- is *not* proved here or anywhere in this development. -/
theorem spatialNorm_isCStarNorm_of_injective (π : StarRep A H) (ρ : StarRep B K)
    (h : Function.Injective (spatialHom π ρ)) :
    IsCStarNorm (spatialNorm π ρ) :=
  (spatialRep π ρ).isCStarNorm_of_injective h

end CStarTensor
end GroupApproximation
