import GroupApproximation.Analysis.CStarHilbertModule

/-!
# Adjointable operators, and the multiplier algebra

The operators of Hilbert C⋆-module theory are the **adjointable** ones: a map
`T : E → F` for which there is `T⋆ : F → E` with `⟨T x, y⟩ = ⟨x, T⋆ y⟩`.  They
are the morphisms Kasparov modules are built from, and the adjointable
operators on `B` regarded as a module over itself are the **multiplier
algebra** `M(B)` --- the algebra `Analysis.KirchbergRordamOrderZeroLift` has to
gesture at with an ambient algebra, because it did not exist here.

## What is proved, and why it is not assumed

Adjointability is a strong condition, and the striking classical fact is how
much it forces.  **None of additivity, `ℂ`-linearity or `B`-linearity is part
of the definition below** --- `toFun` is a bare function --- and all three are
theorems:

* `Adjointable.map_add`, `Adjointable.map_zero`, `Adjointable.map_smul`;
* `Adjointable.map_act` --- `T (x·b) = (T x)·b`.

Each is the same one-line argument: test against an arbitrary vector, move
everything through the adjoint, and use that the inner product separates
points (`CStarModule.eq_of_inner_eq`).  Boundedness is the one property that
does *not* come for free this way --- it needs the closed graph theorem or the
Banach--Steinhaus argument --- and nothing below uses it.

Also proved: the adjoint is unique (`Adjointable.adj_unique`), adjointable
operators are closed under composition, addition and adjoint, and the adjoint
of an adjointable operator is adjointable with the original as its adjoint ---
so `Adjointable` on a fixed module is a `⋆`-algebra, which is what `M(B)` is.

## The multiplier algebra

`Multiplier B := Adjointable (selfModule B) (selfModule B)`, and
`ofElem : B → Multiplier B` embeds `B` by left multiplication, with adjoint
left multiplication by `b⋆`.  `ofElem_mul` proves the embedding is
multiplicative.

This is where the supporting `⋆`-homomorphism of the Winter--Zacharias
factorization lives, and where the Kasparov bimodules of `KK(A,B)` are
assembled.  It does not by itself construct `KK`: that still needs the
compact operators on a Hilbert module, Kasparov's stabilization theorem, and
the product.  It removes one of the three obstructions
`Analysis.KKTheoryKasparov` lists.
-/

namespace GroupApproximation
namespace HilbertModule

universe v w w' w''

variable {B : Type v} [NonUnitalCStarAlgebra B]

/-- **An adjointable operator** between Hilbert C⋆-modules: a map together
with a map in the other direction satisfying the adjoint relation.

`toFun` is a bare function: linearity is a *theorem*, not part of the
definition. -/
structure Adjointable (E : CStarModule.{v, w} B) (F : CStarModule.{v, w'} B) where
  /-- The underlying map. -/
  toFun : E.carrier → F.carrier
  /-- The adjoint map. -/
  adj : F.carrier → E.carrier
  /-- The adjoint relation. -/
  inner_adj : ∀ (x : E.carrier) (y : F.carrier),
    F.inner (toFun x) y = E.inner x (adj y)

namespace Adjointable

variable {E : CStarModule.{v, w} B} {F : CStarModule.{v, w'} B}
variable {G : CStarModule.{v, w''} B}

/-- The adjoint relation with the operator in the second slot, obtained from
the first by conjugate symmetry.  Every proof below goes through this
form. -/
theorem inner_adj' (T : Adjointable E F) (x : E.carrier) (y : F.carrier) :
    F.inner y (T.toFun x) = E.inner (T.adj y) x := by
  have h := T.inner_adj x y
  have h2 := congrArg star h
  rwa [F.inner_star, E.inner_star] at h2

/-! ## Linearity is automatic -/

/-- **An adjointable map is additive.**  Additivity was not assumed. -/
theorem map_add (T : Adjointable E F) (x y : E.carrier) :
    T.toFun (x + y) = T.toFun x + T.toFun y := by
  refine F.eq_of_inner_eq fun z => ?_
  rw [T.inner_adj' (x + y) z, E.inner_add_right, ← T.inner_adj' x z,
    ← T.inner_adj' y z, ← F.inner_add_right]

/-- An adjointable map preserves `0`. -/
theorem map_zero (T : Adjointable E F) : T.toFun 0 = 0 := by
  have h : T.toFun 0 = T.toFun 0 + T.toFun 0 := by
    rw [← T.map_add, add_zero]
  exact self_eq_add_left.mp h

/-- **An adjointable map is `ℂ`-linear.** -/
theorem map_smul (T : Adjointable E F) (c : ℂ) (x : E.carrier) :
    T.toFun (c • x) = c • T.toFun x := by
  refine F.eq_of_inner_eq fun z => ?_
  rw [T.inner_adj' (c • x) z, E.inner_smul_right, ← T.inner_adj' x z,
    ← F.inner_smul_right]

/-- **An adjointable map is `B`-linear.**  This is the clause that makes
adjointable operators the right morphisms for Hilbert modules, and it is a
consequence of the adjoint relation rather than an assumption. -/
theorem map_act (T : Adjointable E F) (x : E.carrier) (b : B) :
    T.toFun (E.act x b) = F.act (T.toFun x) b := by
  refine F.eq_of_inner_eq fun z => ?_
  rw [T.inner_adj' (E.act x b) z, E.inner_act_right, ← T.inner_adj' x z,
    ← F.inner_act_right]

/-! ## Uniqueness of the adjoint -/

/-- **The adjoint is unique.**  Any map satisfying the adjoint relation is the
adjoint, so `Adjointable` carries no more data than its underlying map. -/
theorem adj_unique (T : Adjointable E F) (S : F.carrier → E.carrier)
    (hS : ∀ (x : E.carrier) (y : F.carrier),
      F.inner (T.toFun x) y = E.inner x (S y)) (y : F.carrier) :
    S y = T.adj y := by
  refine E.eq_of_inner_eq fun z => ?_
  rw [← hS z y, T.inner_adj z y]

/-! ## The `⋆`-algebra structure -/

/-- The identity operator. -/
def id (E : CStarModule.{v, w} B) : Adjointable E E where
  toFun x := x
  adj y := y
  inner_adj _ _ := rfl

/-- Composition of adjointable operators. -/
def comp (S : Adjointable F G) (T : Adjointable E F) : Adjointable E G where
  toFun x := S.toFun (T.toFun x)
  adj z := T.adj (S.adj z)
  inner_adj x z := by rw [S.inner_adj, T.inner_adj]

@[simp] theorem comp_toFun (S : Adjointable F G) (T : Adjointable E F)
    (x : E.carrier) : (S.comp T).toFun x = S.toFun (T.toFun x) := rfl

/-- **The adjoint of an adjointable operator is adjointable**, with the
original operator as its adjoint. -/
def adjoint (T : Adjointable E F) : Adjointable F E where
  toFun := T.adj
  adj := T.toFun
  inner_adj y x := (T.inner_adj' x y).symm

@[simp] theorem adjoint_toFun (T : Adjointable E F) (y : F.carrier) :
    (adjoint T).toFun y = T.adj y := rfl

/-- The adjoint is an involution. -/
theorem adjoint_adjoint (T : Adjointable E F) :
    (adjoint (adjoint T)).toFun = T.toFun := rfl

/-- Sum of adjointable operators. -/
def add (T S : Adjointable E F) : Adjointable E F where
  toFun x := T.toFun x + S.toFun x
  adj y := T.adj y + S.adj y
  inner_adj x y := by
    rw [F.inner_add_left, T.inner_adj, S.inner_adj, ← E.inner_add_right]

@[simp] theorem add_toFun (T S : Adjointable E F) (x : E.carrier) :
    (T.add S).toFun x = T.toFun x + S.toFun x := rfl

/-- The zero operator. -/
def zero (E : CStarModule.{v, w} B) (F : CStarModule.{v, w'} B) :
    Adjointable E F where
  toFun _ := 0
  adj _ := 0
  inner_adj x y := by
    rw [F.inner_zero_left, E.inner_zero_right]

/-- Two adjointable operators with the same underlying map have the same
adjoint, by `adj_unique`; so equality of operators may be tested on
`toFun`. -/
theorem adj_eq_of_toFun_eq (T S : Adjointable E F)
    (h : ∀ x, T.toFun x = S.toFun x) (y : F.carrier) : T.adj y = S.adj y := by
  refine adj_unique S T.adj ?_ y
  intro x z
  rw [← h x, T.inner_adj]

/-! ## Rank-one operators

The building blocks of the compact operators on a Hilbert module, and the
reason the theory has a Fredholm theory at all: a Kasparov module asks for
`(F² - 1)π(a)`, `(F - F⋆)π(a)` and `[F, π(a)]` to be *compact*, and compact
means "in the closed span of the operators below". -/

/-- **The rank-one operator** `θ_{x,y} : z ↦ x · ⟨y, z⟩`, adjointable with
adjoint `θ_{y,x}`.

The verification is two applications of the module axioms and one of
conjugate symmetry, and it is the only place where the inner product is used
in both variables at once. -/
def rankOne (x : F.carrier) (y : E.carrier) : Adjointable E F where
  toFun z := F.act x (E.inner y z)
  adj w := E.act y (F.inner x w)
  inner_adj z w := by
    rw [F.inner_act_left, E.inner_act_right, E.inner_star]

@[simp] theorem rankOne_toFun (x : F.carrier) (y : E.carrier)
    (z : E.carrier) : (rankOne x y).toFun z = F.act x (E.inner y z) := rfl

/-- The adjoint of a rank-one operator is the rank-one operator with the
vectors exchanged. -/
theorem adjoint_rankOne (x : F.carrier) (y : E.carrier) (w : F.carrier) :
    (adjoint (rankOne x y)).toFun w = (rankOne y x).toFun w := rfl

end Adjointable

/-! ## The multiplier algebra -/

/-- **The multiplier algebra** `M(B)`: the adjointable operators on `B`
regarded as a Hilbert module over itself.

For unital `B` this is `B` again; for non-unital `B` it is the largest
C⋆-algebra containing `B` as an essential ideal, and it is where the
supporting `⋆`-homomorphism of a Winter--Zacharias factorization lives. -/
abbrev Multiplier (B : Type v) [NonUnitalCStarAlgebra B] : Type v :=
  Adjointable (selfModule B) (selfModule B)

/-- **The canonical embedding `B → M(B)`**, by left multiplication.  Its
adjoint is left multiplication by `b⋆`. -/
def ofElem (b : B) : Multiplier B where
  toFun x := b * x
  adj x := star b * x
  inner_adj x y := by
    show star (b * x) * y = star x * (star b * y)
    rw [star_mul, mul_assoc]

@[simp] theorem ofElem_toFun (b x : B) : (ofElem b).toFun x = b * x := rfl

/-- The embedding is multiplicative. -/
theorem ofElem_mul (b c : B) (x : B) :
    (ofElem (b * c)).toFun x = ((ofElem b).comp (ofElem c)).toFun x := by
  show b * c * x = b * (c * x)
  rw [mul_assoc]

/-- The embedding is additive. -/
theorem ofElem_add (b c : B) (x : B) :
    (ofElem (b + c)).toFun x = ((ofElem b).add (ofElem c)).toFun x := by
  show (b + c) * x = b * x + c * x
  rw [add_mul]

/-- The embedding carries the adjoint of `B` to the adjoint of `M(B)`. -/
theorem ofElem_star (b x : B) :
    (ofElem (star b)).toFun x = (Adjointable.adjoint (ofElem b)).toFun x := rfl

/-- **The embedding is injective**, which is the statement that `B` sits
inside `M(B)`.  It is definiteness of the inner product again: an operator
that is left multiplication by `b` and vanishes identically has `b⋆b = 0`. -/
theorem ofElem_injective_of_eq {b c : B}
    (h : ∀ x : B, (ofElem b).toFun x = (ofElem c).toFun x) : b = c := by
  have hbc : ∀ x : B, (b - c) * x = 0 := by
    intro x
    have hx : b * x = c * x := h x
    rw [sub_mul, hx, sub_self]
  have h0 : star (star (b - c)) * star (b - c) = 0 := by
    rw [star_star]
    exact hbc (star (b - c))
  have h1 : star (b - c) = 0 :=
    (selfModule B).inner_self_eq_zero (star (b - c)) h0
  have h2 := congrArg star h1
  rw [star_star, star_zero] at h2
  exact sub_eq_zero.mp h2

end HilbertModule
end GroupApproximation
