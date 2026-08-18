import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Adjointable operators on a pre-Hilbert space, and the C⋆-identity

## Why this file exists

This is the first layer of the missing foundation for the *minimal (spatial)
tensor product* of C⋆-algebras, which `non_mf_groups_exist.tex` needs twice:
once for the exactness of a reduced group C⋆-algebra (`The algebra is also
exact, by the block normal form of`, beneath `\ref{thm:reduced}`) and
once for the failure of nuclearity (`is not nuclear \cite{Lance}`).  Neither statement is currently
*expressible* in Mathlib: at the pinned revision there is no C⋆-tensor product
of any kind, and no completed Hilbert-space tensor product either.

The spatial norm of `x ∈ A ⊙ B` is the operator norm of the image of `x` under
a product representation on `H ⊗ K`.  The standard textbook route completes
`H ⊗ K` to a Hilbert space first.  **That completion is not needed**, and this
file is the reason: an operator algebra acting on an *incomplete* inner product
space already satisfies the C⋆-identity, because the identity
`‖T‖² = ‖T⋆T‖` is proved from Cauchy--Schwarz and the definition of the
operator norm alone, with no appeal to completeness, to the existence of
adjoints, or to the Riesz representation theorem.

Consequently the whole spatial construction can be carried out on the
*algebraic* tensor product `H ⊗[ℂ] K` equipped with its inner product, and
only the very last step (passing to a C⋆-algebra rather than a C⋆-normed
⋆-algebra) needs a completion.  See `CStarTensorProduct.lean` for the roadmap
in which this file is step 0.

## What is proved here

For `V` a complex inner product space --- explicitly **not** assumed complete
--- and `T S : V →L[ℂ] V`, write `IsAdjoint T S` for the relation
`⟪T x, y⟫ = ⟪x, S y⟫`.  Then:

* `IsAdjoint.symm` --- the relation is symmetric;
* `IsAdjoint.unique` --- an operator has at most one adjoint;
* `IsAdjoint.norm_eq` --- `‖S‖ = ‖T‖`, the adjoint is isometric;
* `IsAdjoint.norm_sq_le_norm_comp` --- `‖T‖² ≤ ‖S ∘ T‖`;
* `IsAdjoint.norm_comp_self` --- **the C⋆-identity** `‖S ∘ T‖ = ‖T‖ * ‖T‖`;
* closure of the adjointable operators under `0`, `1`, `+`, `-`, `•` and `∘`,
  with the adjoint computed in each case.

Nothing here assumes `CompleteSpace V`; Mathlib's `ContinuousLinearMap.adjoint`
does, which is exactly why the relation is respelled unbundled.

## Manuscript status

This file certifies no manuscript step by itself.  It is infrastructure for the
`⊗_min` construction that the exactness and nuclearity rows of the manuscript
would need; those rows remain **MISSING**, as the manuscript itself states.
-/

namespace GroupApproximation
namespace CStarTensor

open scoped InnerProductSpace

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ## The adjoint relation -/

/-- `IsAdjoint T S` says that the bounded operator `S` is an adjoint of the
bounded operator `T` on the inner product space `V`:  `⟪T x, y⟫ = ⟪x, S y⟫` for
all `x y`.

`V` is **not** assumed complete, so `S` cannot be produced from `T` by the
Riesz representation theorem; adjointability is a genuine restriction and is
carried as data.  On a complete space this is `S = ContinuousLinearMap.adjoint
T` and the relation always holds for a unique `S`. -/
def IsAdjoint (T S : V →L[ℂ] V) : Prop :=
  ∀ x y : V, ⟪T x, y⟫_ℂ = ⟪x, S y⟫_ℂ

/-- Multiplication of continuous endomorphisms is composition. -/
@[simp] theorem mul_eq_comp (S T : V →L[ℂ] V) : S * T = S.comp T := rfl

namespace IsAdjoint

/-- The adjoint relation is symmetric: if `S` is an adjoint of `T` then `T` is
an adjoint of `S`.  This is conjugate symmetry of the inner product. -/
theorem symm {T S : V →L[ℂ] V} (h : IsAdjoint T S) : IsAdjoint S T := by
  intro x y
  calc ⟪S x, y⟫_ℂ = (starRingEnd ℂ) ⟪y, S x⟫_ℂ := (inner_conj_symm (S x) y).symm
    _ = (starRingEnd ℂ) ⟪T y, x⟫_ℂ := by rw [h y x]
    _ = ⟪x, T y⟫_ℂ := inner_conj_symm x (T y)

/-- An operator has at most one adjoint.  This is nondegeneracy of the inner
product and needs no completeness. -/
theorem unique {T S₁ S₂ : V →L[ℂ] V} (h₁ : IsAdjoint T S₁) (h₂ : IsAdjoint T S₂) :
    S₁ = S₂ := by
  ext y
  have hzero : ∀ x : V, ⟪x, S₁ y - S₂ y⟫_ℂ = 0 := by
    intro x
    rw [inner_sub_right, ← h₁ x y, ← h₂ x y, sub_self]
  have hself : ⟪S₁ y - S₂ y, S₁ y - S₂ y⟫_ℂ = 0 := hzero (S₁ y - S₂ y)
  have : S₁ y - S₂ y = 0 := inner_self_eq_zero.mp hself
  exact sub_eq_zero.mp this

end IsAdjoint

/-! ## Two elementary auxiliary facts

Both are separated out so that the operator-theoretic proofs below are pure
calculations. -/

/-- The norm of the inner product of a vector with itself is the square of its
norm. -/
private theorem norm_inner_self (v : V) : ‖⟪v, v⟫_ℂ‖ = ‖v‖ ^ 2 := by
  rw [← inner_self_re_eq_norm]
  exact inner_self_eq_norm_sq v

/-- A quadratic bound on all vectors bounds the square of the operator norm. -/
private theorem opNorm_sq_le_of_forall {T : V →L[ℂ] V} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : V, ‖T x‖ ^ 2 ≤ c * ‖x‖ ^ 2) : ‖T‖ ^ 2 ≤ c := by
  have hb : ∀ x : V, ‖T x‖ ≤ Real.sqrt c * ‖x‖ := by
    intro x
    have hnn : 0 ≤ Real.sqrt c * ‖x‖ :=
      mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg x)
    have hsq : ‖T x‖ ^ 2 ≤ (Real.sqrt c * ‖x‖) ^ 2 := by
      have hexp : (Real.sqrt c * ‖x‖) ^ 2 = c * ‖x‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hc]
      rw [hexp]
      exact h x
    have hroot := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg (T x)), Real.sqrt_sq hnn] at hroot
  have hle : ‖T‖ ≤ Real.sqrt c := T.opNorm_le_bound (Real.sqrt_nonneg c) hb
  have hmul := mul_self_le_mul_self (norm_nonneg T) hle
  have hsq : ‖T‖ ^ 2 ≤ Real.sqrt c ^ 2 := by
    rw [pow_two, pow_two]
    exact hmul
  rwa [Real.sq_sqrt hc] at hsq

/-- Composition is submultiplicative for the operator norm.  Proved from
`opNorm_le_bound` rather than quoted, so that the file depends on as little of
the operator-norm API as possible. -/
theorem norm_comp_le_mul (S T : V →L[ℂ] V) : ‖S.comp T‖ ≤ ‖S‖ * ‖T‖ := by
  refine (S.comp T).opNorm_le_bound (mul_nonneg (norm_nonneg S) (norm_nonneg T))
    fun x ↦ ?_
  calc ‖(S.comp T) x‖ = ‖S (T x)‖ := by rw [ContinuousLinearMap.comp_apply]
    _ ≤ ‖S‖ * ‖T x‖ := S.le_opNorm (T x)
    _ ≤ ‖S‖ * (‖T‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg S)
    _ = ‖S‖ * ‖T‖ * ‖x‖ := by ring

namespace IsAdjoint

/-! ## Norm identities -/

/-- The adjoint is a contraction, hence (with `symm`) an isometry. -/
theorem norm_le {T S : V →L[ℂ] V} (h : IsAdjoint T S) : ‖S‖ ≤ ‖T‖ := by
  refine S.opNorm_le_bound (norm_nonneg T) fun y ↦ ?_
  have hy : ⟪S y, S y⟫_ℂ = ⟪y, T (S y)⟫_ℂ := h.symm y (S y)
  have hquad : ‖S y‖ * ‖S y‖ ≤ ‖T‖ * ‖y‖ * ‖S y‖ := by
    have hstep : ‖S y‖ ^ 2 ≤ ‖T‖ * ‖y‖ * ‖S y‖ := by
      calc ‖S y‖ ^ 2 = ‖⟪S y, S y⟫_ℂ‖ := (norm_inner_self (S y)).symm
        _ = ‖⟪y, T (S y)⟫_ℂ‖ := by rw [hy]
        _ ≤ ‖y‖ * ‖T (S y)‖ := norm_inner_le_norm _ _
        _ ≤ ‖y‖ * (‖T‖ * ‖S y‖) :=
            mul_le_mul_of_nonneg_left (T.le_opNorm (S y)) (norm_nonneg y)
        _ = ‖T‖ * ‖y‖ * ‖S y‖ := by ring
    rwa [pow_two] at hstep
  rcases eq_or_lt_of_le (norm_nonneg (S y)) with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg (norm_nonneg T) (norm_nonneg y)
  · exact le_of_mul_le_mul_right hquad hpos

/-- **The adjoint is isometric.** -/
theorem norm_eq {T S : V →L[ℂ] V} (h : IsAdjoint T S) : ‖S‖ = ‖T‖ :=
  le_antisymm h.norm_le h.symm.norm_le

/-- Half of the C⋆-identity: `‖T‖² ≤ ‖T⋆T‖`.  This is the direction that
carries the content, and it is pure Cauchy--Schwarz. -/
theorem norm_sq_le_norm_comp {T S : V →L[ℂ] V} (h : IsAdjoint T S) :
    ‖T‖ ^ 2 ≤ ‖S.comp T‖ := by
  refine opNorm_sq_le_of_forall (norm_nonneg (S.comp T)) fun x ↦ ?_
  have hx : ⟪T x, T x⟫_ℂ = ⟪x, S (T x)⟫_ℂ := h x (T x)
  have hcomp : (S.comp T) x = S (T x) := ContinuousLinearMap.comp_apply S T x
  calc ‖T x‖ ^ 2 = ‖⟪T x, T x⟫_ℂ‖ := (norm_inner_self (T x)).symm
    _ = ‖⟪x, S (T x)⟫_ℂ‖ := by rw [hx]
    _ ≤ ‖x‖ * ‖S (T x)‖ := norm_inner_le_norm _ _
    _ = ‖x‖ * ‖(S.comp T) x‖ := by rw [hcomp]
    _ ≤ ‖x‖ * (‖S.comp T‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left ((S.comp T).le_opNorm x) (norm_nonneg x)
    _ = ‖S.comp T‖ * ‖x‖ ^ 2 := by ring

/-- **The C⋆-identity on a pre-Hilbert space.**  If `S` is an adjoint of `T`
then `‖S ∘ T‖ = ‖T‖ * ‖T‖`.

No completeness of `V` is used anywhere in the proof: the two inequalities come
from Cauchy--Schwarz and from submultiplicativity of the operator norm together
with the isometry of the adjoint. -/
theorem norm_comp_self {T S : V →L[ℂ] V} (h : IsAdjoint T S) :
    ‖S.comp T‖ = ‖T‖ * ‖T‖ := by
  refine le_antisymm ?_ ?_
  · calc ‖S.comp T‖ ≤ ‖S‖ * ‖T‖ := norm_comp_le_mul S T
      _ = ‖T‖ * ‖T‖ := by rw [h.norm_eq]
  · have hsq := h.norm_sq_le_norm_comp
    rwa [pow_two] at hsq

/-- The C⋆-identity written with the ring multiplication of `V →L[ℂ] V`. -/
theorem norm_mul_self {T S : V →L[ℂ] V} (h : IsAdjoint T S) :
    ‖S * T‖ = ‖T‖ * ‖T‖ := by
  rw [mul_eq_comp]
  exact h.norm_comp_self

end IsAdjoint

/-! ## The adjointable operators are closed under the ⋆-algebra operations

Each lemma both witnesses closure and computes the adjoint. -/

/-- The zero operator is its own adjoint. -/
theorem isAdjoint_zero : IsAdjoint (0 : V →L[ℂ] V) 0 := by
  intro x y
  simp

/-- The identity operator is its own adjoint. -/
@[simp] theorem isAdjoint_id : IsAdjoint (ContinuousLinearMap.id ℂ V)
    (ContinuousLinearMap.id ℂ V) := by
  intro x y
  rfl

/-- The unit of the algebra `V →L[ℂ] V` is its own adjoint. -/
theorem isAdjoint_one : IsAdjoint (1 : V →L[ℂ] V) 1 :=
  isAdjoint_id

/-- Adjoints add. -/
theorem IsAdjoint.add {T₁ S₁ T₂ S₂ : V →L[ℂ] V} (h₁ : IsAdjoint T₁ S₁)
    (h₂ : IsAdjoint T₂ S₂) : IsAdjoint (T₁ + T₂) (S₁ + S₂) := by
  intro x y
  have hx : (T₁ + T₂) x = T₁ x + T₂ x := rfl
  have hy : (S₁ + S₂) y = S₁ y + S₂ y := rfl
  rw [hx, hy, inner_add_left, inner_add_right, h₁ x y, h₂ x y]

/-- Adjoints negate. -/
theorem IsAdjoint.neg {T S : V →L[ℂ] V} (h : IsAdjoint T S) :
    IsAdjoint (-T) (-S) := by
  intro x y
  have hx : (-T) x = -(T x) := rfl
  have hy : (-S) y = -(S y) := rfl
  rw [hx, hy, inner_neg_left, inner_neg_right, h x y]

/-- Adjoints subtract. -/
theorem IsAdjoint.sub {T₁ S₁ T₂ S₂ : V →L[ℂ] V} (h₁ : IsAdjoint T₁ S₁)
    (h₂ : IsAdjoint T₂ S₂) : IsAdjoint (T₁ - T₂) (S₁ - S₂) := by
  have hsubT : T₁ - T₂ = T₁ + (-T₂) := by rw [sub_eq_add_neg]
  have hsubS : S₁ - S₂ = S₁ + (-S₂) := by rw [sub_eq_add_neg]
  rw [hsubT, hsubS]
  exact h₁.add h₂.neg

/-- Scalars pass to the adjoint conjugated: the adjoint of `c • T` is
`conj c • S`. -/
theorem IsAdjoint.smul {T S : V →L[ℂ] V} (h : IsAdjoint T S) (c : ℂ) :
    IsAdjoint (c • T) ((starRingEnd ℂ c) • S) := by
  intro x y
  have hx : (c • T) x = c • T x := rfl
  have hy : ((starRingEnd ℂ c) • S) y = (starRingEnd ℂ c) • S y := rfl
  rw [hx, hy, inner_smul_left, inner_smul_right, h x y]

/-- Adjoints of a composite compose in the opposite order. -/
theorem IsAdjoint.comp {T₁ S₁ T₂ S₂ : V →L[ℂ] V} (h₁ : IsAdjoint T₁ S₁)
    (h₂ : IsAdjoint T₂ S₂) : IsAdjoint (T₁.comp T₂) (S₂.comp S₁) := by
  intro x y
  have hx : (T₁.comp T₂) x = T₁ (T₂ x) := ContinuousLinearMap.comp_apply T₁ T₂ x
  have hy : (S₂.comp S₁) y = S₂ (S₁ y) := ContinuousLinearMap.comp_apply S₂ S₁ y
  rw [hx, hy, h₁ (T₂ x) y, h₂ x (S₁ y)]

/-- Adjoints of a product multiply in the opposite order. -/
theorem IsAdjoint.mul {T₁ S₁ T₂ S₂ : V →L[ℂ] V} (h₁ : IsAdjoint T₁ S₁)
    (h₂ : IsAdjoint T₂ S₂) : IsAdjoint (T₁ * T₂) (S₂ * S₁) := by
  rw [mul_eq_comp, mul_eq_comp]
  exact h₁.comp h₂

/-- The scalar operators are adjointable, with conjugated adjoint. -/
theorem isAdjoint_algebraMap (c : ℂ) :
    IsAdjoint (algebraMap ℂ (V →L[ℂ] V) c)
      (algebraMap ℂ (V →L[ℂ] V) (starRingEnd ℂ c)) := by
  have hc : algebraMap ℂ (V →L[ℂ] V) c = c • (1 : V →L[ℂ] V) :=
    Algebra.algebraMap_eq_smul_one c
  have hc' : algebraMap ℂ (V →L[ℂ] V) (starRingEnd ℂ c)
      = (starRingEnd ℂ c) • (1 : V →L[ℂ] V) :=
    Algebra.algebraMap_eq_smul_one _
  rw [hc, hc']
  exact isAdjoint_one.smul c

end CStarTensor
end GroupApproximation
