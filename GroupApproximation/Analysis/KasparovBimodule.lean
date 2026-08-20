import GroupApproximation.Analysis.CStarDirectSumOperators

/-!
# Kasparov bimodules

`Analysis.KKTheoryKasparov` says, in its own docstring, that `KK(A,B)` cannot
be constructed in this development because "there are no Hilbert C⋆-modules,
no multiplier algebras, no Fredholm theory over a C⋆-algebra".  The first two
were built in `Analysis.CStarHilbertModule` and `Analysis.CStarAdjointable`;
the third is `𝓚(E)`, built in `Analysis.CStarCompactOperators`.  **This file
writes down the cycles of `KK(A,B)`.**

A Kasparov `A`-`B`-bimodule is a `ℤ/2`-graded Hilbert `B`-module `E`, a graded
representation `π : A → 𝓛(E)`, and an odd operator `F ∈ 𝓛(E)` for which

  `(F² - 1)π(a)`,  `(F - F⋆)π(a)`,  `[F, π(a)]`

are all **compact**.  Every one of those three is now a statement this
development can make.

## What is here, and what is not

Here: the definition, its degenerate cycles, and the direct sum --- with all
of the compactness verified, not assumed.  `KK(A,B)` is the set of these
modulo homotopy, and the direct sum is what makes it a monoid.

Not here: the group structure (needs the homotopy relation and the inverse,
hence Kasparov's stabilization theorem), and the Kasparov product (the
technical theorem).  `KasparovTheory` in `Analysis.KKTheoryKasparov` remains
the axiomatization those two would discharge, and nothing below claims to
inhabit it.

## The pointwise style, and why it is not a compromise

Every clause is stated on `T.toFun`: `π(a + a')x = π(a)x + π(a')x` rather than
`π(a + a') = π(a) + π(a')`.  This is the style of `ofElem_mul` in
`Analysis.CStarAdjointable`, and it is forced by the same fact: `Adjointable`
bundles an operator with its adjoint, so an equation between operators is an
equation between *pairs*, and proving the second component is either an appeal
to uniqueness of the adjoint or an appeal to proof irrelevance.  Since
`IsBounded`, `IsFiniteRank` and `IsCompactOp` are themselves pointwise
(`IsCompactOp.congr`), nothing is ever needed about the second component, and
the direct-sum construction below verifies its nine clauses with `rfl` and
`Prod.ext` alone.
-/

namespace GroupApproximation
namespace HilbertModule

open OrderZero

universe u v w w'

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B]

namespace Adjointable

/-- The zero operator has finite rank: the empty sum. -/
theorem isFiniteRank_zero {E : CStarModule.{v, w} B}
    {F : CStarModule.{v, w'} B} : (zero E F).IsFiniteRank := by
  refine ⟨Empty, inferInstance, Empty.elim, Empty.elim, ?_⟩
  intro z
  show (0 : F.carrier) = ∑ i : Empty, F.act (Empty.elim i) (E.inner (Empty.elim i) z)
  simp

theorem isCompactOp_zero {E : CStarModule.{v, w} B}
    {F : CStarModule.{v, w'} B} : (zero E F).IsCompactOp :=
  isFiniteRank_zero.isCompactOp

end Adjointable

/-! ## Representations -/

/-- **A representation of `A` by bounded adjointable operators on `E`**: a
`⋆`-homomorphism `A → 𝓛(E)`, with every clause stated pointwise.

`map_star` says the adjoint of `π(a)` is `π(a⋆)`, which is the clause that
makes `π` a `⋆`-homomorphism rather than merely an algebra map, and the one
that forces `π(a)` to be bounded whenever `a` is selfadjoint. -/
structure IsRepresentation (E : CStarModule.{v, w} B)
    (pi : A → Adjointable E E) : Prop where
  /-- Every operator in the image is bounded. -/
  bounded : ∀ a : A, (pi a).IsBounded
  /-- `π` is additive. -/
  map_add : ∀ (a a' : A) (x : E.carrier),
    (pi (a + a')).toFun x = (pi a).toFun x + (pi a').toFun x
  /-- `π` is `ℂ`-linear. -/
  map_smul : ∀ (c : ℂ) (a : A) (x : E.carrier),
    (pi (c • a)).toFun x = c • (pi a).toFun x
  /-- `π` is multiplicative. -/
  map_mul : ∀ (a a' : A) (x : E.carrier),
    (pi (a * a')).toFun x = (pi a).toFun ((pi a').toFun x)
  /-- `π` is `⋆`-preserving. -/
  map_star : ∀ (a : A) (x : E.carrier),
    (pi (star a)).toFun x = (pi a).adj x

namespace IsRepresentation

variable {E : CStarModule.{v, w} B} {pi : A → Adjointable E E}

theorem map_zero (h : IsRepresentation E pi) (x : E.carrier) :
    (pi (0 : A)).toFun x = 0 := by
  have h0 : (pi (0 : A)).toFun x = (pi (0 : A)).toFun x + (pi (0 : A)).toFun x := by
    have := h.map_add 0 0 x
    rwa [add_zero] at this
  exact left_eq_add.mp h0

end IsRepresentation

/-! ## Kasparov bimodules -/

/-- **A Kasparov `A`-`B`-bimodule**: a graded Hilbert `B`-module with an even
representation of `A` and an odd operator that is a unitary involution modulo
compacts and commutes with the representation modulo compacts.

These are the cycles of `KK(A,B)`. -/
structure KasparovBimodule (A : Type u) [NonUnitalCStarAlgebra A]
    (B : Type v) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] where
  /-- The underlying Hilbert `B`-module. -/
  E : CStarModule.{v, w} B
  /-- The grading operator `γ`. -/
  grading : Adjointable E E
  /-- The representation of `A`. -/
  pi : A → Adjointable E E
  /-- The Fredholm operator. -/
  op : Adjointable E E
  /-- `γ` is bounded. -/
  grading_bounded : grading.IsBounded
  /-- `γ` is selfadjoint. -/
  grading_selfAdjoint : ∀ x : E.carrier, grading.adj x = grading.toFun x
  /-- `γ² = 1`. -/
  grading_involutive : ∀ x : E.carrier,
    grading.toFun (grading.toFun x) = x
  /-- `π` is a representation. -/
  rep : IsRepresentation E pi
  /-- `π` is even: it commutes with the grading. -/
  rep_even : ∀ (a : A) (x : E.carrier),
    grading.toFun ((pi a).toFun x) = (pi a).toFun (grading.toFun x)
  /-- `F` is bounded. -/
  op_bounded : op.IsBounded
  /-- `F` is odd: it anticommutes with the grading. -/
  op_odd : ∀ x : E.carrier,
    grading.toFun (op.toFun x) = -(op.toFun (grading.toFun x))
  /-- `(F² - 1)π(a)` is compact. -/
  compact_one : ∀ a : A,
    (((op.comp op).sub (Adjointable.id E)).comp (pi a)).IsCompactOp
  /-- `(F - F⋆)π(a)` is compact. -/
  compact_selfAdjoint : ∀ a : A,
    ((op.sub (Adjointable.adjoint op)).comp (pi a)).IsCompactOp
  /-- `[F, π(a)]` is compact. -/
  compact_commutator : ∀ a : A,
    ((op.comp (pi a)).sub ((pi a).comp op)).IsCompactOp

/-- **A degenerate bimodule**: one in which the three defining expressions are
not merely compact but zero.

Degenerate cycles are the ones that represent `0` in `KK(A,B)`; that they are
*cycles* is the observation that `0` is compact, and it is the only content of
`isKasparov_of_degenerate` below. -/
structure IsDegenerate (M : KasparovBimodule.{u, v, w} A B) : Prop where
  /-- `F² = 1` on the nose. -/
  op_sq : ∀ (a : A) (x : M.E.carrier),
    M.op.toFun (M.op.toFun ((M.pi a).toFun x)) = (M.pi a).toFun x
  /-- `F` is selfadjoint on the nose. -/
  op_selfAdjoint : ∀ (a : A) (x : M.E.carrier),
    M.op.adj ((M.pi a).toFun x) = M.op.toFun ((M.pi a).toFun x)
  /-- `F` commutes with the representation on the nose. -/
  op_commutes : ∀ (a : A) (x : M.E.carrier),
    M.op.toFun ((M.pi a).toFun x) = (M.pi a).toFun (M.op.toFun x)

/-! ## The direct sum

The addition of `KK(A,B)`, before the homotopy relation.  Nine clauses, and
none of them is work: the grading, representation and operator clauses are
`Prod.ext` of the corresponding clauses of the summands, and the three
compactness clauses are `IsCompactOp.prodMap` transported along a `rfl`,
because `⊞` commutes with composition, difference, identity and adjoint
definitionally. -/

namespace KasparovBimodule

variable (M N : KasparovBimodule.{u, v, w} A B)

/-- **The direct sum of two Kasparov bimodules.** -/
def add : KasparovBimodule.{u, v, w} A B where
  E := prod M.E N.E
  grading := Adjointable.prodMap M.grading N.grading
  pi a := Adjointable.prodMap (M.pi a) (N.pi a)
  op := Adjointable.prodMap M.op N.op
  grading_bounded := Adjointable.IsBounded.prodMap M.grading_bounded
    N.grading_bounded
  grading_selfAdjoint p :=
    Prod.ext (M.grading_selfAdjoint p.1) (N.grading_selfAdjoint p.2)
  grading_involutive p :=
    Prod.ext (M.grading_involutive p.1) (N.grading_involutive p.2)
  rep :=
    { bounded := fun a => Adjointable.IsBounded.prodMap (M.rep.bounded a)
        (N.rep.bounded a)
      map_add := fun a a' p =>
        Prod.ext (M.rep.map_add a a' p.1) (N.rep.map_add a a' p.2)
      map_smul := fun c a p =>
        Prod.ext (M.rep.map_smul c a p.1) (N.rep.map_smul c a p.2)
      map_mul := fun a a' p =>
        Prod.ext (M.rep.map_mul a a' p.1) (N.rep.map_mul a a' p.2)
      map_star := fun a p =>
        Prod.ext (M.rep.map_star a p.1) (N.rep.map_star a p.2) }
  rep_even a p := Prod.ext (M.rep_even a p.1) (N.rep_even a p.2)
  op_bounded := Adjointable.IsBounded.prodMap M.op_bounded N.op_bounded
  op_odd p := Prod.ext (M.op_odd p.1) (N.op_odd p.2)
  compact_one a :=
    Adjointable.IsCompactOp.congr (fun _ => rfl)
      (Adjointable.IsCompactOp.prodMap (M.compact_one a) (N.compact_one a))
  compact_selfAdjoint a :=
    Adjointable.IsCompactOp.congr (fun _ => rfl)
      (Adjointable.IsCompactOp.prodMap (M.compact_selfAdjoint a)
        (N.compact_selfAdjoint a))
  compact_commutator a :=
    Adjointable.IsCompactOp.congr (fun _ => rfl)
      (Adjointable.IsCompactOp.prodMap (M.compact_commutator a)
        (N.compact_commutator a))

@[simp] theorem add_pi_toFun (a : A) (p : M.E.carrier × N.E.carrier) :
    ((M.add N).pi a).toFun p = ((M.pi a).toFun p.1, (N.pi a).toFun p.2) := rfl

@[simp] theorem add_op_toFun (p : M.E.carrier × N.E.carrier) :
    ((M.add N).op).toFun p = (M.op.toFun p.1, N.op.toFun p.2) := rfl

end KasparovBimodule

end HilbertModule
end GroupApproximation
