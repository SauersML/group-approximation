import GroupApproximation.Analysis.CStarModuleDirectSum
import GroupApproximation.Analysis.CStarCompactOperators

/-!
# Operators on a direct sum

The inclusions and projections of `E ⊞ F`, the diagonal operator
`S ⊞ T`, and the fact that a direct sum of compact operators is compact.
This is what makes the direct sum of two Kasparov modules a Kasparov module,
which is the addition of `KK(A,B)`.

## What is proved

* `norm_prod_le`, `norm_fst_le`, `norm_snd_le` --- the two-sided comparison
  between the norm of a pair and the norms of its entries.  The direct sum
  norm is *not* the sum and *not* the max --- it is `‖⟨x,x⟩+⟨y,y⟩‖^{1/2}` ---
  and these are the only two facts about it anything needs;
* `inl`, `inr` --- the inclusions, adjointable with the projections as
  adjoints, so `fst` and `snd` are *defined* as `inl⋆` and `inr⋆` and their
  boundedness is `IsBoundedBy.adjoint` rather than a second computation;
* `prodMap S T = S ⊞ T`, with `IsBoundedBy`, `IsFiniteRank` and `IsCompactOp`
  all inherited from the two summands.

## Why everything here is pointwise

`IsFiniteRank`, `IsBoundedBy` and `IsCompactOp` are all statements about
`T.toFun`, never about `T` as a structure.  So `S ⊞ T` can be shown compact
without ever proving the operator identity
`S ⊞ T = ι₁S p₁ + ι₂T p₂` --- which would need an extensionality principle for
`Adjointable`, hence proof irrelevance on its adjoint-relation field.  The
pointwise route is shorter and needs nothing.
-/

namespace GroupApproximation
namespace HilbertModule

open OrderZero

universe v w w'

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B]
variable {E : CStarModule.{v, w} B} {F : CStarModule.{v, w'} B}

/-! ## The norm of a pair -/

theorem norm_prod_le (p : E.carrier × F.carrier) :
    (prod E F).norm p ≤ E.norm p.1 + F.norm p.2 := by
  have hsq : (prod E F).norm p ^ 2 ≤ (E.norm p.1 + F.norm p.2) ^ 2 := by
    have h1 : (prod E F).norm p ^ 2 = ‖E.inner p.1 p.1 + F.inner p.2 p.2‖ :=
      (prod E F).norm_sq p
    have h2 : ‖E.inner p.1 p.1 + F.inner p.2 p.2‖
        ≤ ‖E.inner p.1 p.1‖ + ‖F.inner p.2 p.2‖ := norm_add_le _ _
    have h3 : ‖E.inner p.1 p.1‖ + ‖F.inner p.2 p.2‖
        ≤ (E.norm p.1 + F.norm p.2) ^ 2 := by
      rw [← E.norm_sq p.1, ← F.norm_sq p.2]
      nlinarith [E.norm_nonneg p.1, F.norm_nonneg p.2]
    rw [h1]
    exact le_trans h2 h3
  refine (pow_le_pow_iff_left₀ ((prod E F).norm_nonneg p) ?_
    (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact add_nonneg (E.norm_nonneg p.1) (F.norm_nonneg p.2)

theorem norm_fst_le (p : E.carrier × F.carrier) :
    E.norm p.1 ≤ (prod E F).norm p := by
  rw [CStarModule.norm_def, CStarModule.norm_def]
  refine Real.sqrt_le_sqrt ?_
  refine OrderZero.norm_le_norm_of_nonneg_of_le (E.inner_self_nonneg p.1) ?_
  show E.inner p.1 p.1 ≤ E.inner p.1 p.1 + F.inner p.2 p.2
  exact le_add_of_nonneg_right (F.inner_self_nonneg p.2)

theorem norm_snd_le (p : E.carrier × F.carrier) :
    F.norm p.2 ≤ (prod E F).norm p := by
  rw [CStarModule.norm_def, CStarModule.norm_def]
  refine Real.sqrt_le_sqrt ?_
  refine OrderZero.norm_le_norm_of_nonneg_of_le (F.inner_self_nonneg p.2) ?_
  show F.inner p.2 p.2 ≤ E.inner p.1 p.1 + F.inner p.2 p.2
  exact le_add_of_nonneg_left (E.inner_self_nonneg p.1)

namespace Adjointable

/-! ## Inclusions and projections -/

/-- The inclusion of the first summand, adjointable with the first projection
as its adjoint. -/
def inl (E : CStarModule.{v, w} B) (F : CStarModule.{v, w'} B) :
    Adjointable E (prod E F) where
  toFun x := (x, 0)
  adj p := p.1
  inner_adj x p := by
    show E.inner x p.1 + F.inner 0 p.2 = E.inner x p.1
    rw [F.inner_zero_left, add_zero]

/-- The inclusion of the second summand. -/
def inr (E : CStarModule.{v, w} B) (F : CStarModule.{v, w'} B) :
    Adjointable F (prod E F) where
  toFun y := (0, y)
  adj p := p.2
  inner_adj y p := by
    show E.inner 0 p.1 + F.inner y p.2 = F.inner y p.2
    rw [E.inner_zero_left, zero_add]

/-- The first projection: the adjoint of the first inclusion, not a second
construction. -/
def fstProj (E : CStarModule.{v, w} B) (F : CStarModule.{v, w'} B) :
    Adjointable (prod E F) E := Adjointable.adjoint (inl E F)

/-- The second projection. -/
def sndProj (E : CStarModule.{v, w} B) (F : CStarModule.{v, w'} B) :
    Adjointable (prod E F) F := Adjointable.adjoint (inr E F)

@[simp] theorem fstProj_toFun (p : E.carrier × F.carrier) :
    (fstProj E F).toFun p = p.1 := rfl

@[simp] theorem sndProj_toFun (p : E.carrier × F.carrier) :
    (sndProj E F).toFun p = p.2 := rfl

/-- The inclusion is isometric: `⟨(x,0),(x,0)⟩ = ⟨x,x⟩`. -/
theorem norm_inl (x : E.carrier) : (prod E F).norm (x, 0) = E.norm x := by
  rw [CStarModule.norm_def, CStarModule.norm_def]
  congr 1
  show ‖E.inner x x + F.inner 0 0‖ = ‖E.inner x x‖
  rw [F.inner_zero_left, add_zero]

theorem norm_inr (y : F.carrier) : (prod E F).norm (0, y) = F.norm y := by
  rw [CStarModule.norm_def, CStarModule.norm_def]
  congr 1
  show ‖E.inner 0 0 + F.inner y y‖ = ‖F.inner y y‖
  rw [E.inner_zero_left, zero_add]

theorem isBoundedBy_inl : (inl E F).IsBoundedBy 1 := by
  intro x
  show (prod E F).norm (x, 0) ≤ 1 * E.norm x
  rw [norm_inl, one_mul]

theorem isBoundedBy_inr : (inr E F).IsBoundedBy 1 := by
  intro y
  show (prod E F).norm (0, y) ≤ 1 * F.norm y
  rw [norm_inr, one_mul]

theorem isBounded_inl : (inl E F).IsBounded := ⟨1, zero_le_one, isBoundedBy_inl⟩

theorem isBounded_inr : (inr E F).IsBounded := ⟨1, zero_le_one, isBoundedBy_inr⟩

theorem isBounded_fstProj : (fstProj E F).IsBounded :=
  isBounded_inl.adjoint

theorem isBounded_sndProj : (sndProj E F).IsBounded :=
  isBounded_inr.adjoint

/-! ## The diagonal operator -/

/-- **`S ⊞ T`**, acting entrywise on a direct sum. -/
def prodMap (S : Adjointable E E) (T : Adjointable F F) :
    Adjointable (prod E F) (prod E F) where
  toFun p := (S.toFun p.1, T.toFun p.2)
  adj p := (S.adj p.1, T.adj p.2)
  inner_adj p q := by
    show E.inner (S.toFun p.1) q.1 + F.inner (T.toFun p.2) q.2
        = E.inner p.1 (S.adj q.1) + F.inner p.2 (T.adj q.2)
    rw [S.inner_adj, T.inner_adj]

@[simp] theorem prodMap_toFun (S : Adjointable E E) (T : Adjointable F F)
    (p : E.carrier × F.carrier) :
    (prodMap S T).toFun p = (S.toFun p.1, T.toFun p.2) := rfl

theorem IsBoundedBy.prodMap {S : Adjointable E E} {T : Adjointable F F}
    {C D : ℝ} (hS : S.IsBoundedBy C) (hT : T.IsBoundedBy D) (hC : 0 ≤ C)
    (hD : 0 ≤ D) : (Adjointable.prodMap S T).IsBoundedBy (C + D) := by
  intro p
  show (prod E F).norm (S.toFun p.1, T.toFun p.2) ≤ (C + D) * (prod E F).norm p
  calc (prod E F).norm (S.toFun p.1, T.toFun p.2)
      ≤ E.norm (S.toFun p.1) + F.norm (T.toFun p.2) := norm_prod_le _
    _ ≤ C * E.norm p.1 + D * F.norm p.2 := add_le_add (hS p.1) (hT p.2)
    _ ≤ C * (prod E F).norm p + D * (prod E F).norm p :=
        add_le_add (mul_le_mul_of_nonneg_left (norm_fst_le p) hC)
          (mul_le_mul_of_nonneg_left (norm_snd_le p) hD)
    _ = (C + D) * (prod E F).norm p := by ring

theorem IsBounded.prodMap {S : Adjointable E E} {T : Adjointable F F}
    (hS : S.IsBounded) (hT : T.IsBounded) :
    (Adjointable.prodMap S T).IsBounded := by
  obtain ⟨C, hC, hSb⟩ := hS
  obtain ⟨D, hD, hTb⟩ := hT
  exact ⟨C + D, add_nonneg hC hD, hSb.prodMap hTb hC hD⟩

/-! ## `S ⊞ T` is functorial, and definitionally so

Composition, difference, identity and adjoint all commute with `⊞` *by
construction*: the product's algebraic operations are defined coordinatewise
and Lean's structure eta makes `(p.1, p.2) = p` definitional, so each of the
four statements below is `rfl`.  They are stated because the direct-sum
Kasparov module needs them by name, not because they need proof. -/

@[simp] theorem prodMap_comp (S S' : Adjointable E E) (T T' : Adjointable F F)
    (p : E.carrier × F.carrier) :
    ((Adjointable.prodMap S T).comp (Adjointable.prodMap S' T')).toFun p
      = (Adjointable.prodMap (S.comp S') (T.comp T')).toFun p := rfl

@[simp] theorem prodMap_sub (S S' : Adjointable E E) (T T' : Adjointable F F)
    (p : E.carrier × F.carrier) :
    ((Adjointable.prodMap S T).sub (Adjointable.prodMap S' T')).toFun p
      = (Adjointable.prodMap (S.sub S') (T.sub T')).toFun p := rfl

@[simp] theorem prodMap_id (p : E.carrier × F.carrier) :
    (Adjointable.id (prod E F)).toFun p
      = (Adjointable.prodMap (Adjointable.id E) (Adjointable.id F)).toFun p :=
  rfl

@[simp] theorem prodMap_adjoint (S : Adjointable E E) (T : Adjointable F F)
    (p : E.carrier × F.carrier) :
    (Adjointable.adjoint (Adjointable.prodMap S T)).toFun p
      = (Adjointable.prodMap (Adjointable.adjoint S)
          (Adjointable.adjoint T)).toFun p := rfl

/-- `S ⊞ T` is, pointwise, `ι₁ S p₁ + ι₂ T p₂`.  Stated pointwise, which is
all that `IsCompactOp.congr` needs. -/
theorem prodMap_apply (S : Adjointable E E) (T : Adjointable F F)
    (p : E.carrier × F.carrier) :
    (Adjointable.prodMap S T).toFun p
      = (((inl E F).comp (S.comp (fstProj E F))).add
          ((inr E F).comp (T.comp (sndProj E F)))).toFun p := by
  show (S.toFun p.1, T.toFun p.2)
      = (S.toFun p.1, (0 : F.carrier)) + ((0 : E.carrier), T.toFun p.2)
  rw [Prod.mk_add_mk, add_zero, zero_add]

/-- **A direct sum of finite-rank operators has finite rank.**  Through the
same decomposition: `ι₁Sp₁` and `ι₂Tp₂` are finite rank because the
finite-rank operators are an ideal, and their sum is finite rank. -/
theorem IsFiniteRank.prodMap {S : Adjointable E E} {T : Adjointable F F}
    (hS : S.IsFiniteRank) (hT : T.IsFiniteRank) :
    (Adjointable.prodMap S T).IsFiniteRank :=
  IsFiniteRank.congr (fun p => (prodMap_apply S T p).symm)
    (((hS.comp_right (fstProj E F)).comp_left (inl E F)).add
      ((hT.comp_right (sndProj E F)).comp_left (inr E F)))

/-- **A direct sum of compact operators is compact.**

This is the statement that makes the direct sum of two Kasparov modules a
Kasparov module, hence the addition of `KK(A,B)`.  It is proved from the ideal
property alone: `ι₁Sp₁` is compact because `S` is and `ι₁`, `p₁` are bounded,
and `𝓚(E ⊞ F)` is closed under sums. -/
theorem IsCompactOp.prodMap {S : Adjointable E E} {T : Adjointable F F}
    (hS : S.IsCompactOp) (hT : T.IsCompactOp) :
    (Adjointable.prodMap S T).IsCompactOp :=
  IsCompactOp.congr (fun p => (prodMap_apply S T p).symm)
    (((hS.comp_right isBounded_fstProj).comp_left isBounded_inl).add
      ((hT.comp_right isBounded_sndProj).comp_left isBounded_inr))

end Adjointable

end HilbertModule
end GroupApproximation
