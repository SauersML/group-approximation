import GroupApproximation.Analysis.CStarAdjointable

/-!
# Finite-rank operators on a Hilbert C⋆-module

A Kasparov `A`-`B`-bimodule is a representation `π : A → 𝓛(E)` together with an
operator `F ∈ 𝓛(E)` for which `(F² − 1)π(a)`, `(F − F⋆)π(a)` and `[F, π(a)]`
are **compact**.  The compact operators `𝓚(E)` are the closed linear span of
the rank-one operators `θ_{x,y}`, so the theory needs two things: the algebra
of finite sums of rank-ones, and a norm in which to close it.

**This file builds the first, in full and unconditionally.**  The second needs
Cauchy--Schwarz for `B`-valued inner products, hence the order theory of `B`,
and is not here; what is here is exactly the algebra that closure is applied
to.

## What is proved

`IsFiniteRank T` says `T` is a finite sum of rank-one operators, indexed by an
arbitrary finite type.  Then:

* `isFiniteRank_rankOne` --- rank-one operators have finite rank;
* `IsFiniteRank.comp_left`, `IsFiniteRank.comp_right` --- **the finite-rank
  operators are a two-sided ideal**: `S ∘ T` and `T ∘ S` have finite rank
  whenever `T` does, for *any* adjointable `S`.  The two proofs are the two
  halves of the adjoint relation: on the left one pushes `S` through the
  action (`map_act`), on the right one moves it across the inner product
  (`inner_adj'`), turning `θ_{x,y} ∘ S` into `θ_{x, S⋆y}`;
* `IsFiniteRank.add` --- closed under sums;
* `IsFiniteRank.adjoint` --- **closed under adjoints**, by uniqueness of the
  adjoint together with the two `Finset`-additivity lemmas for the inner
  product.

So the finite-rank operators form a `⋆`-closed two-sided ideal in `𝓛(E)`.
That is the statement `𝓚(E)` inherits by closure, and it is the last purely
algebraic ingredient of the Fredholm picture.

Two auxiliary results, both proved here and both used above, are of general
use: `Adjointable.map_sum` (an adjointable map commutes with finite sums ---
it is additive by `map_add`, which was itself a theorem, not an assumption)
and `CStarModule.inner_sum_left`/`inner_sum_right`.
-/

namespace GroupApproximation
namespace HilbertModule

universe v w w' w''

variable {B : Type v} [NonUnitalCStarAlgebra B]

/-! ## Finite additivity of the inner product -/

namespace CStarModule

variable (E : CStarModule.{v, w} B)

theorem inner_sum_right {ι : Type*} (s : Finset ι) (x : E.carrier)
    (f : ι → E.carrier) :
    E.inner x (∑ i ∈ s, f i) = ∑ i ∈ s, E.inner x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, E.inner_zero_right]
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, E.inner_add_right, ih, Finset.sum_insert ha]

theorem inner_sum_left {ι : Type*} (s : Finset ι) (f : ι → E.carrier)
    (x : E.carrier) :
    E.inner (∑ i ∈ s, f i) x = ∑ i ∈ s, E.inner (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, E.inner_zero_left]
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, E.inner_add_left, ih, Finset.sum_insert ha]

end CStarModule

namespace Adjointable

variable {E : CStarModule.{v, w} B} {F : CStarModule.{v, w'} B}
variable {G : CStarModule.{v, w''} B}

/-- An adjointable map commutes with finite sums.  Additivity is
`Adjointable.map_add`, which is itself a theorem rather than an assumption. -/
theorem map_sum (T : Adjointable E F) {ι : Type*} (s : Finset ι)
    (f : ι → E.carrier) :
    T.toFun (∑ i ∈ s, f i) = ∑ i ∈ s, T.toFun (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, T.map_zero]
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, T.map_add, ih, Finset.sum_insert ha]

/-! ## Finite rank -/

/-- **`T` has finite rank**: it is a finite sum of rank-one operators.

The index type is an arbitrary finite type rather than `Fin n`, which is what
makes the closure under sums a one-line argument over `ι ⊕ κ` instead of an
exercise in `Fin` arithmetic. -/
def IsFiniteRank (T : Adjointable E F) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (x : ι → F.carrier) (y : ι → E.carrier),
    ∀ z : E.carrier, T.toFun z = ∑ i, F.act (x i) (E.inner (y i) z)

theorem isFiniteRank_rankOne (x : F.carrier) (y : E.carrier) :
    IsFiniteRank (rankOne x y) := by
  refine ⟨Fin 1, inferInstance, fun _ => x, fun _ => y, ?_⟩
  intro z
  simp

/-- **Left ideal property**: composing a finite-rank operator with any
adjointable operator on the left keeps the rank finite, because
`S ∘ θ_{x,y} = θ_{S x, y}`. -/
theorem IsFiniteRank.comp_left {T : Adjointable E F} (h : IsFiniteRank T)
    (S : Adjointable F G) : IsFiniteRank (S.comp T) := by
  obtain ⟨ι, hι, x, y, hT⟩ := h
  refine ⟨ι, hι, fun i => S.toFun (x i), y, ?_⟩
  intro z
  rw [comp_toFun, hT z, S.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [S.map_act]

/-- **Right ideal property**: composing on the right keeps the rank finite,
because `θ_{x,y} ∘ S = θ_{x, S⋆ y}`.  This is where the adjoint of `S` is
used, and it is why the ideal is two-sided only for *adjointable* `S`. -/
theorem IsFiniteRank.comp_right {T : Adjointable E F} (h : IsFiniteRank T)
    (S : Adjointable G E) : IsFiniteRank (T.comp S) := by
  obtain ⟨ι, hι, x, y, hT⟩ := h
  refine ⟨ι, hι, x, fun i => S.adj (y i), ?_⟩
  intro z
  rw [comp_toFun, hT (S.toFun z)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [S.inner_adj' z (y i)]

/-- The finite-rank operators are closed under sums. -/
theorem IsFiniteRank.add {T S : Adjointable E F} (hT : IsFiniteRank T)
    (hS : IsFiniteRank S) : IsFiniteRank (T.add S) := by
  obtain ⟨ι, hι, x, y, hTeq⟩ := hT
  obtain ⟨κ, hκ, u, v, hSeq⟩ := hS
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim x u, Sum.elim y v, ?_⟩
  intro z
  have hsum :
      (∑ i : ι ⊕ κ, F.act (Sum.elim x u i) (E.inner (Sum.elim y v i) z))
        = (∑ a : ι, F.act (x a) (E.inner (y a) z))
          + ∑ b : κ, F.act (u b) (E.inner (v b) z) :=
    Fintype.sum_sum_type _
  rw [add_toFun, hTeq z, hSeq z, hsum]

/-- **The finite-rank operators are closed under adjoints**, the adjoint of
`θ_{x,y}` being `θ_{y,x}`.

The proof is uniqueness of the adjoint: the candidate `∑ θ_{yᵢ,xᵢ}` is checked
against the adjoint relation, which reduces termwise to conjugate symmetry of
the inner product. -/
theorem IsFiniteRank.adjoint {T : Adjointable E F} (h : IsFiniteRank T) :
    IsFiniteRank (Adjointable.adjoint T) := by
  obtain ⟨ι, hι, x, y, hT⟩ := h
  refine ⟨ι, hι, y, x, ?_⟩
  intro w
  show T.adj w = ∑ i, E.act (y i) (F.inner (x i) w)
  refine (adj_unique T (fun w => ∑ i, E.act (y i) (F.inner (x i) w)) ?_ w).symm
  intro z w'
  rw [hT z, F.inner_sum_left, E.inner_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [F.inner_act_left, E.inner_act_right, E.inner_star]

end Adjointable

end HilbertModule
end GroupApproximation
