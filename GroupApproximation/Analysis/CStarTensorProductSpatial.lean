import GroupApproximation.Analysis.CStarTensorProductSeminorm
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Star.TensorProduct
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis

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
C⋆-norm on a tensor product, or the minimal tensor product itself.

The first two are supplied here outright.  The third is supplied **only as a
C⋆-seminorm**: `spatialNorm_isCStarSeminorm` is unconditional, but
`spatialNorm_isCStarNorm_of_injective` assumes `Function.Injective (spatialHom
π ρ)`, and **nothing in this repository discharges that hypothesis** --- see
the analysis at the end of this docstring.  The fourth is not supplied at all.

## Contents

* `isAdjoint_mapL` --- `mapL S' T'` is an adjoint of `mapL S T`.
* `norm_mapL` --- `‖mapL S T‖ = ‖S‖ * ‖T‖`.
* `rTensorAlgHom`, `lTensorAlgHom` --- amplification as algebra maps.
* `spatialHom`, `spatialRep` --- the product representation.
* `spatialNorm`, `spatialNorm_isCStarSeminorm`, `spatialNorm_tmul`,
  `spatialNorm_isCStarNorm_of_injective`.

## The hypothesis that used to be undischarged --- now discharged

`spatialNorm_isCStarNorm_of_injective` assumes `Function.Injective (spatialHom
π ρ)`.  That hypothesis is **now proved**, as `spatialHom_injective`, from the
natural condition that each factor be faithfully represented; the unconditional
consequence is `spatialNorm_isCStarNorm`.  Previously nothing in this
repository established it and non-degeneracy was known only on **elementary**
tensors (`CStarTensorProductConcrete.spatialNorm_tmul_ne_zero`), so the lane
delivered a C⋆-seminorm unconditionally and a C⋆-norm only conditionally.

The rest of this section is kept because the *reason* it was cheap is worth
recording, and because the roadmap in `CStarTensorProduct.lean` still budgets
it wrongly.

**The roadmap's Stage A overestimates this step.**  It says full faithfulness
"requires states on a C⋆-algebra and the fact that they separate points
(Mathlib has `GelfandNaimarkSegal`)", and budgets ~800 lines.  That is the cost
of the *analytic* slice maps --- the ones that must be shown continuous for the
minimal norm, which is what Takesaki's theorem needs.  **Mere injectivity of
`spatialHom π ρ` on the algebraic tensor product needs no states, no GNS and no
continuity**: the vector functionals already separate points.

**The argument.**  Suppose `π.hom` and `ρ.hom` are injective and
`spatialHom π ρ x = 0`.

1. *The vector functionals separate points.*  For `a ≠ 0`, injectivity gives
   `π.hom a ≠ 0`, so `π.hom a ξ ≠ 0` for some `ξ`; taking `ξ' = π.hom a ξ`
   makes `⟪π.hom a ξ, ξ'⟫ = ‖π.hom a ξ‖² ≠ 0`.  Likewise for `ρ`.
2. *Matrix coefficients of the product representation factor.*  For fixed
   `ξ, ξ', η, η'` let `Φ : A ⊗[ℂ] B →ₗ[ℂ] ℂ` be `TensorProduct.lift` of the
   bilinear map `(a, b) ↦ ⟪π.hom a ξ, ξ'⟫ * ⟪ρ.hom b η, η'⟫`.  Then
   `⟪spatialHom π ρ x (ξ ⊗ₜ η), ξ' ⊗ₜ η'⟫ = Φ x`, by
   `TensorProduct.induction_on` on `x` using `TensorProduct.inner_tmul` and
   `TensorProduct.mapL_tmul`.  Hence `Φ x = 0` for all four vectors.
3. *Kill the first slice.*  Because the `ρ`-vector functionals separate the
   points of `B`, vanishing for every `η, η'` forces the slice
   `sliceRight (vecFunctional π ξ ξ') x` to be `0`, for every `ξ, ξ'`.
4. *Collapse.*  Apply a basis coordinate of `B` and move it across
   `coord_sliceRight`; the `π`-vector functionals then kill `coordSlice c j x`,
   so that is `0` for every `j`, and
   `eq_zero_of_forall_coordSlice_eq_zero` gives `x = 0`.

**The one linear-algebra fact.**  Step 4's last move is the only step that is
not bookkeeping, and Mathlib supplies both halves of it:
`Module.Basis.tensorProduct` makes `b i ⊗ₜ c j` a basis of `A ⊗[ℂ] B`, and
`Module.Basis.forall_coord_eq_zero_iff` (`LinearAlgebra/Basis/Defs.lean:670`) says a
vector all of whose coordinates vanish is zero.  What has to be checked is only
that the `(i, j)` coordinate functional of that basis *is* the composite of the
two slices (`tensorProduct_coord_apply`), an identity on elementary tensors
extended by additivity.

An earlier draft of this analysis routed the same step through
`TensorProduct.finsuppRight` and a transport along `c.repr`.  That works too,
but it is strictly more plumbing --- it drags in the `R S M N ι` scalar-tower
signature of `finsuppRight` --- and the `Module.Basis.tensorProduct` route above needs
no transport at all.

**Verdict: it was closable at this Mathlib pin, and it is now closed.**  Every
ingredient was present: `Module.Basis.ofVectorSpace`
(`LinearAlgebra/Basis/VectorSpace.lean:150`), `Module.Basis.tensorProduct` and
`Module.Basis.tensorProduct_repr_tmul_apply`
(`LinearAlgebra/TensorProduct/Basis.lean:38,55`),
`Module.Basis.forall_coord_eq_zero_iff`, `TensorProduct.lid`/`rid`, and
`TensorProduct.inner_tmul`
(`Analysis/InnerProductSpace/TensorProduct.lean:69`).  **No literature input
and no analysis** --- in particular no states, no GNS, and no continuity.

**What it would still not give.**  Independence of the norm from `(π, ρ)` is
untouched by the above: that is Takesaki's theorem.  (It has since been
proved downstream: for faithful pairs on complete Hilbert spaces the spatial
norm equals the canonical minimal norm,
`CStarTakesakiIdentification.spatialNorm_eq_minTensorNorm`; this file's own
content remains exactly the fixed-pair construction.)  On its own this
repair upgrades the lane from "a conditional C⋆-norm attached to a chosen
pair" to "a C⋆-norm attached to a chosen pair", and **does not** make
C⋆-exactness statable.  See `CStarExactness.lean`.

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
  -- `opNorm_nonneg`, not `norm_nonneg`: `H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K` carries two
  -- `Norm` instances (`SeminormedAddGroup.toNorm` and
  -- `ContinuousLinearMap.hasOpNorm`) and Lean will not unify them, so the
  -- lemma has to be the one stated at the operator norm.
  have hCnn : (0 : ℝ) ≤ ‖TensorProduct.mapL S T‖ :=
    (TensorProduct.mapL S T).opNorm_nonneg
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
    refine opNorm_mul_le_of_forall T hCnn S.opNorm_nonneg ?_
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

omit [StarModule ℂ A] [StarModule ℂ B] in
/-- The product representation on an elementary tensor is the tensor product of
the two operators.  (`spatialHom` itself needs no `StarModule`; the ⋆-structure
enters only in `spatialRep` below, hence the `omit`.) -/
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

/-! ## Non-degeneracy: the product representation is faithful

Everything in this section is algebra.  No completeness, no states, no GNS, no
continuity of slice maps: the vector functionals `a ↦ ⟪ξ', π a ξ⟫` already
separate the points of `A` as soon as `π.hom` is injective, and separation plus
a Hamel basis on one factor is enough.  See the analysis in the module
docstring for why this is much cheaper than the roadmap's Stage A. -/

section Injectivity

/-! ### Vector functionals

These need a ⋆-representation, hence `StarRing`, but no `StarModule`; they are
given their own minimal variable block rather than inheriting the file's, so
that no unused section variable is auto-included. -/

section VecFunctional

variable {M : Type u} [Ring M] [StarRing M] [Algebra ℂ M]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The **vector functional** `a ↦ ⟪ξ', π a ξ⟫` of a ⋆-representation.

The inner product is taken with the representation's value in the *second*
argument, because Mathlib's `inner` is conjugate-linear in the first: written
the other way round this would be conjugate-linear in `a` and would not be a
`ℂ`-linear functional at all. -/
noncomputable def vecFunctional (π : StarRep M E) (ξ ξ' : E) : M →ₗ[ℂ] ℂ where
  toFun a := ⟪ξ', π.hom a ξ⟫_ℂ
  map_add' a b := by
    simp only [map_add, add_apply, inner_add_right]
  map_smul' r a := by
    simp only [map_smul, smul_apply, inner_smul_right,
      RingHom.id_apply, smul_eq_mul]

@[simp] theorem vecFunctional_apply (π : StarRep M E) (ξ ξ' : E) (a : M) :
    vecFunctional π ξ ξ' a = ⟪ξ', π.hom a ξ⟫_ℂ := rfl

/-- **The vector functionals of a faithful ⋆-representation separate points.**
If they all vanish at `a` then `π a` kills every vector, so `π a = 0` and
injectivity gives `a = 0`.  The witness is `ξ' = π a ξ`, where the pairing is
`‖π a ξ‖²`. -/
theorem eq_zero_of_forall_vecFunctional_eq_zero (π : StarRep M E)
    (hπ : Function.Injective π.hom) {a : M}
    (h : ∀ ξ ξ' : E, vecFunctional π ξ ξ' a = 0) : a = 0 := by
  have hz : π.hom a = 0 := by
    refine ContinuousLinearMap.ext fun ξ => ?_
    show π.hom a ξ = 0
    exact inner_self_eq_zero.mp (h ξ (π.hom a ξ))
  have hzz : π.hom a = π.hom 0 := by rw [hz, map_zero]
  exact hπ hzz

end VecFunctional

/-! ### Slices

Pure linear algebra: no ⋆-structure and no topology anywhere below, so these
are stated for bare `ℂ`-vector spaces.  They specialise to `A` and `B` because
`Ring` plus `Algebra ℂ` supplies `AddCommGroup` and `Module ℂ`. -/

section Slices

variable {V : Type u} {W : Type v} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- Slicing `V ⊗ W` in the **first** variable along a linear functional,
landing in `W`. -/
noncomputable def sliceRight (φ : V →ₗ[ℂ] ℂ) : (V ⊗[ℂ] W) →ₗ[ℂ] W :=
  (TensorProduct.lid ℂ W).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id

@[simp] theorem sliceRight_tmul (φ : V →ₗ[ℂ] ℂ) (a : V) (b : W) :
    sliceRight φ (a ⊗ₜ[ℂ] b) = φ a • b := by
  simp only [sliceRight, LinearMap.coe_comp, Function.comp_apply,
    TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul]

/-- Slicing `V ⊗ W` in the **second** variable along a basis coordinate,
landing in `V`. -/
noncomputable def coordSlice {κ : Type*} (c : Module.Basis κ ℂ W) (j : κ) :
    (V ⊗[ℂ] W) →ₗ[ℂ] V :=
  (TensorProduct.rid ℂ V).toLinearMap ∘ₗ LinearMap.lTensor V (c.coord j)

@[simp] theorem coordSlice_tmul {κ : Type*} (c : Module.Basis κ ℂ W) (j : κ)
    (a : V) (b : W) : coordSlice c j (a ⊗ₜ[ℂ] b) = c.repr b j • a := by
  simp only [coordSlice, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
    Module.Basis.coord_apply]

/-- The two slices commute: taking a basis coordinate of a first-variable slice
is the same as applying the functional to the corresponding second-variable
slice.  Both sides are `φ a * c.repr b j` on `a ⊗ₜ b`. -/
theorem coord_sliceRight {κ : Type*} (c : Module.Basis κ ℂ W) (j : κ)
    (φ : V →ₗ[ℂ] ℂ) (y : V ⊗[ℂ] W) :
    c.coord j (sliceRight φ y) = φ (coordSlice c j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      simp only [sliceRight_tmul, coordSlice_tmul, map_smul, Module.Basis.coord_apply,
        smul_eq_mul]
      exact mul_comm _ _
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-! ### The one linear-algebra fact this turns on

Pure linear algebra over a field, and the only step of the faithfulness proof
that is not bookkeeping.  It is short because Mathlib supplies both halves:
`Module.Basis.tensorProduct` makes `b i ⊗ₜ c j` a basis of `V ⊗[ℂ] W`, and
`Module.Basis.forall_coord_eq_zero_iff` says a vector with all coordinates zero is
zero.  All that has to be checked is that the `(i, j)` coordinate functional of
that basis *is* the composite of the two slices, which is an identity on
elementary tensors extended by additivity. -/

/-- **The `(i, j)` coordinate of the tensor-product basis is the composite of
the two slices.**  On `a ⊗ₜ β` both sides are `c.repr β j * b.repr a i`; the
general case is additivity. -/
theorem tensorProduct_coord_apply {ι κ : Type*} (b : Module.Basis ι ℂ V)
    (c : Module.Basis κ ℂ W) (i : ι) (j : κ) (y : V ⊗[ℂ] W) :
    (b.tensorProduct c).coord (i, j) y = b.coord i (coordSlice c j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a β =>
      rw [Module.Basis.coord_apply, Module.Basis.tensorProduct_repr_tmul_apply, coordSlice_tmul,
        map_smul, Module.Basis.coord_apply]
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- **Coordinate slices along a basis of the right factor detect zero.**  If
`c` is a basis of `W` and every slice `coordSlice c j` kills `x`, then `x = 0`.

No topology and no analysis: the basis of `V` is an arbitrary Hamel basis,
supplied by `Module.Basis.ofVectorSpace`. -/
theorem eq_zero_of_forall_coordSlice_eq_zero {κ : Type*} (c : Module.Basis κ ℂ W)
    {x : V ⊗[ℂ] W} (h : ∀ j : κ, coordSlice c j x = 0) : x = 0 := by
  classical
  refine ((Module.Basis.ofVectorSpace ℂ V).tensorProduct c).forall_coord_eq_zero_iff.mp ?_
  rintro ⟨i, j⟩
  rw [tensorProduct_coord_apply (Module.Basis.ofVectorSpace ℂ V) c i j x, h j, map_zero]

end Slices

/-! ### Matrix coefficients of the product representation

From here on the full variable block is needed: these statements mention
`spatialHom`, and through `spatialRep` the ⋆-structure really is in play. -/

section Faithful

-- No local `variable` block: these statements mention `spatialHom`, so they
-- want exactly the file-level variables declared at the top of this file.
-- Re-declaring them here would shadow rather than reuse them.

omit [StarModule ℂ A] [StarModule ℂ B] in
/-- **The matrix coefficients of `π ⊗ ρ` factor through the slices.**  Pairing
`(π ⊗ ρ)(x)(ξ ⊗ η)` against `ξ' ⊗ η'` gives the `ρ`-vector functional applied
to the `π`-slice of `x`.  On `a ⊗ₜ b` this is exactly
`⟪ξ' ⊗ η', π a ξ ⊗ ρ b η⟫ = ⟪ξ', π a ξ⟫ ⟪η', ρ b η⟫`.

(`spatialHom` needs no `StarModule`; only `spatialRep` does, so those two
section variables are omitted here as they are on `spatialHom_tmul`.) -/
theorem inner_spatialHom_apply (π : StarRep A H) (ρ : StarRep B K)
    (ξ ξ' : H) (η η' : K) (x : A ⊗[ℂ] B) :
    ⟪(ξ' ⊗ₜ[ℂ] η' : H ⊗[ℂ] K), spatialHom π ρ x (ξ ⊗ₜ[ℂ] η)⟫_ℂ
      = vecFunctional ρ η η' (sliceRight (vecFunctional π ξ ξ') x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      rw [spatialHom_tmul, TensorProduct.mapL_tmul, TensorProduct.inner_tmul,
        sliceRight_tmul]
      -- `smul_apply` and `inner_smul_right` are deliberately absent: the
      -- linter reports them as never firing, so `map_smul` is already
      -- reaching the normal form on its own.  Needing a fact and needing a
      -- `simp only` entry for it are different things.
      simp only [vecFunctional_apply, map_smul, smul_eq_mul]
  | add x y hx hy =>
      rw [map_add, add_apply, inner_add_right, hx, hy,
        map_add, map_add]

/-! ### Faithfulness -/

omit [StarModule ℂ A] [StarModule ℂ B] in
/-- **The product representation of a pair of faithful ⋆-representations is
faithful.**

This discharges the hypothesis of `spatialNorm_isCStarNorm_of_injective`, which
until now had to be assumed, and it replaces it by the natural condition that
each factor be faithfully represented.

The argument, in four steps.  Suppose `spatialHom π ρ x = 0`.

1. Every matrix coefficient vanishes, so by `inner_spatialHom_apply` the
   `ρ`-vector functionals all kill `sliceRight (vecFunctional π ξ ξ') x`.
2. Those functionals separate the points of `B`
   (`eq_zero_of_forall_vecFunctional_eq_zero`), so that slice is `0`, for
   every `ξ, ξ'`.
3. Apply a basis coordinate and move it across `coord_sliceRight`: every
   `π`-vector functional kills `coordSlice c j x`, so that is `0` too, for
   every `j`.
4. `eq_zero_of_forall_coordSlice_eq_zero` turns the vanishing of all
   coordinate slices into `x = 0`. -/
theorem spatialHom_injective (π : StarRep A H) (ρ : StarRep B K)
    (hπ : Function.Injective π.hom) (hρ : Function.Injective ρ.hom) :
    Function.Injective (spatialHom π ρ) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx
  set c := Module.Basis.ofVectorSpace ℂ B
  -- Steps 1 and 2: every first-variable slice vanishes.
  have hslice : ∀ ξ ξ' : H, sliceRight (vecFunctional π ξ ξ') x = 0 := by
    intro ξ ξ'
    refine eq_zero_of_forall_vecFunctional_eq_zero ρ hρ ?_
    intro η η'
    rw [← inner_spatialHom_apply π ρ ξ ξ' η η' x, hx]
    simp
  -- Step 3: every second-variable coordinate slice vanishes.
  have hcoord : ∀ j, coordSlice c j x = 0 := by
    intro j
    refine eq_zero_of_forall_vecFunctional_eq_zero π hπ ?_
    intro ξ ξ'
    rw [← coord_sliceRight c j (vecFunctional π ξ ξ') x, hslice ξ ξ']
    simp
  -- Step 4.
  exact eq_zero_of_forall_coordSlice_eq_zero c hcoord

/-- **The spatial seminorm of a pair of faithful ⋆-representations is a
C⋆-norm**, unconditionally.

This is `spatialNorm_isCStarNorm_of_injective` with its hypothesis discharged
by `spatialHom_injective`.

**What this does and does not buy.**  It converts the lane's *conditional*
C⋆-norm into an unconditional one **for a fixed pair `(π, ρ)`**.  It says
nothing whatever about canonicity: the norm still depends on the chosen pair,
independence of that choice is Takesaki's theorem, and until that is proved the
norm must not be written `‖·‖_min`.  In particular this is **not** progress on
the manuscript's exactness row, which needs `⊗_min` and a noncommutative
C⋆-quotient before it is even statable.  See `CStarExactness.lean`. -/
theorem spatialNorm_isCStarNorm (π : StarRep A H) (ρ : StarRep B K)
    (hπ : Function.Injective π.hom) (hρ : Function.Injective ρ.hom) :
    IsCStarNorm (spatialNorm π ρ) :=
  spatialNorm_isCStarNorm_of_injective π ρ (spatialHom_injective π ρ hπ hρ)

end Faithful

end Injectivity

end CStarTensor
end GroupApproximation
