import GroupApproximation.Analysis.NormMatrixCorona

/-!
# The norm-matrix corona at an arbitrary filter, behind an opaque boundary

`Analysis/NormMatrixCorona.lean` builds every parent structure of the bundled
C⋆-algebra class on `FilterMatrixCoronaAlgebra X l` at an arbitrary filter, and
then assembles them **only at `cofinite`**, behind the opaque synonym
`NormMatrixCStarCorona`.  Its own header says why the opacity is there: the
quotient is a noncommutative ideal quotient, and downstream typeclass search
unfolds it repeatedly.

At a free ultrafilter the same six instances are available and nothing assembled
them, so the ω side had no such synonym.  The cost is not hypothetical.  Asking
for `Semiring (FilterMatrixCoronaAlgebra (Idx Y) ↑ω)` in a file that also
imports the vector-ultraproduct tower exhausts the default `synthInstance`
budget outright, which is what
`Analysis/OmegaCoronaKazhdanProjection.lean`'s header records — and raising the
budget is not available, because `scripts/check.py` counts budget bumps as
findings and a peer lane spent 2026-08-18 removing every one of them.

This file is the general fix rather than the ω-shaped one: `l` stays a variable,
so `cofinite` and a free `ω` are the same construction, and the `NeBot`
hypothesis appears only on the two instances that genuinely need it.

## What is here

* `FilterMatrixCStarCorona` — the corona as an opaque type synonym, with all
  eight structures transported and the bundled `CStarAlgebra` assembled;
* `filterMatrixCStarCoronaMk` — the quotient map, as a ⋆-algebra homomorphism;
* `filterMatrixCStarCoronaLift` — the universal property.  A ⋆-homomorphism out
  of the bounded sequences that kills the `l`-null ones factors through the
  corona.  This is what lets a consumer define a map **out of** the opaque type
  without unfolding it, which is the whole point of the boundary.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  It is used by
`Analysis/VectorOmegaCoronaAction.lean`, which is where `NK.06`'s remaining
clause is answered.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u v

variable (X : ℕ → Type u) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
  [∀ n, Nonempty (X n)] (l : Filter ℕ)

/-- **The norm-matrix corona at the filter `l`, opaque.**  Same elements as
`FilterMatrixCoronaAlgebra X l`, with its structures transported explicitly so
that typeclass search stops at the boundary instead of unfolding the ideal
quotient.  At `l = cofinite` this is `NormMatrixCStarCorona`; at a free
ultrafilter it is the manuscript's `∏_ω M_{d_n}`. -/
def FilterMatrixCStarCorona := FilterMatrixCoronaAlgebra X l

noncomputable instance filterMatrixCStarCoronaNormedRing :
    NormedRing (FilterMatrixCStarCorona X l) := by
  unfold FilterMatrixCStarCorona
  exact filterMatrixCoronaAlgebraNormedRing X l

noncomputable instance filterMatrixCStarCoronaCompleteSpace :
    CompleteSpace (FilterMatrixCStarCorona X l) := by
  unfold FilterMatrixCStarCorona
  exact filterMatrixCoronaAlgebraCompleteSpace X l

noncomputable instance filterMatrixCStarCoronaStarRing :
    StarRing (FilterMatrixCStarCorona X l) := by
  unfold FilterMatrixCStarCorona
  exact filterMatrixCoronaAlgebraStarRing X l

noncomputable instance filterMatrixCStarCoronaNormedStarGroup :
    NormedStarGroup (FilterMatrixCStarCorona X l) := by
  unfold FilterMatrixCStarCorona
  exact filterMatrixCoronaAlgebraNormedStarGroup X l

noncomputable instance filterMatrixCStarCoronaAlgebra :
    Algebra ℂ (FilterMatrixCStarCorona X l) := by
  unfold FilterMatrixCStarCorona
  exact Ideal.Quotient.algebra ℂ

noncomputable instance filterMatrixCStarCoronaNormedAlgebra :
    NormedAlgebra ℂ (FilterMatrixCStarCorona X l) := by
  unfold FilterMatrixCStarCorona
  exact filterMatrixCoronaAlgebraNormedAlgebra X l

noncomputable instance filterMatrixCStarCoronaStarModule :
    StarModule ℂ (FilterMatrixCStarCorona X l) := by
  unfold FilterMatrixCStarCorona
  exact filterMatrixCoronaAlgebraStarModule X l

noncomputable instance filterMatrixCStarCoronaCStarRing [l.NeBot] :
    CStarRing (FilterMatrixCStarCorona X l) := by
  unfold FilterMatrixCStarCorona
  exact filterMatrixCoronaAlgebraCStarRing X l

/-- **The corona at any `NeBot` filter is a bundled unital complex
C⋆-algebra.**  Six field assignments, every one of them an instance above. -/
noncomputable instance filterMatrixCStarCoronaCStarAlgebra [l.NeBot] :
    CStarAlgebra (FilterMatrixCStarCorona X l) where
  toNormedRing := filterMatrixCStarCoronaNormedRing X l
  toStarRing := filterMatrixCStarCoronaStarRing X l
  toCompleteSpace := filterMatrixCStarCoronaCompleteSpace X l
  toCStarRing := filterMatrixCStarCoronaCStarRing X l
  toNormedAlgebra := filterMatrixCStarCoronaNormedAlgebra X l
  toStarModule := filterMatrixCStarCoronaStarModule X l

/-- The quotient map into the opaque corona, as a ring homomorphism. -/
noncomputable def filterMatrixCStarCoronaMk :
    BoundedMatrixSequence X →+* FilterMatrixCStarCorona X l := by
  unfold FilterMatrixCStarCorona
  exact filterMatrixCoronaMk X l

@[simp] theorem filterMatrixCStarCorona_star_mk (a : BoundedMatrixSequence X) :
    star (filterMatrixCStarCoronaMk X l a) =
      filterMatrixCStarCoronaMk X l (star a) := by
  unfold filterMatrixCStarCoronaMk FilterMatrixCStarCorona
  exact filterMatrixCorona_star_mk X l a

/-- The quotient map as a complex ⋆-algebra homomorphism. -/
noncomputable def filterMatrixCStarCoronaQuotient :
    BoundedMatrixSequence X →⋆ₐ[ℂ] FilterMatrixCStarCorona X l where
  toFun := filterMatrixCStarCoronaMk X l
  map_one' := map_one (filterMatrixCStarCoronaMk X l)
  map_mul' := map_mul (filterMatrixCStarCoronaMk X l)
  map_zero' := map_zero (filterMatrixCStarCoronaMk X l)
  map_add' := map_add (filterMatrixCStarCoronaMk X l)
  commutes' z := by
    unfold filterMatrixCStarCoronaMk FilterMatrixCStarCorona
    exact Ideal.Quotient.mk_algebraMap ℂ (nullMatrixSequenceIdeal X l) z
  map_star' a := (filterMatrixCStarCorona_star_mk X l a).symm

/-- **The universal property, at the transparent quotient.**

Stated here rather than directly at the opaque type because the anonymous
constructor re-synthesizes its expected type's instances: inside a goal already
rewritten by `unfold`, `Algebra ℂ (FilterMatrixCoronaAlgebra X l)` is asked for
against a goal whose instance argument still names the opaque type, and the
search fails.  At the top level the same instance is found immediately.  So the
map is built where it is cheap and transported afterwards. -/
noncomputable def filterMatrixCoronaStarLift {B : Type v} [Ring B] [StarRing B]
    [Algebra ℂ B] (f : BoundedMatrixSequence X →⋆ₐ[ℂ] B)
    (hf : ∀ a : BoundedMatrixSequence X, IsNullMatrixSequence X l a → f a = 0) :
    FilterMatrixCoronaAlgebra X l →⋆ₐ[ℂ] B :=
  -- The ring homomorphism is named rather than inlined.  Left anonymous, the
  -- `map_one'`/`map_mul'` fields are elaborated as `map_one _`, and resolving
  -- the morphism class against `ℓ∞(M_{d_n}) ⧸ null →+* B` exhausts the
  -- `synthInstance` budget.  Through the named `g` they are projections.
  let g : FilterMatrixCoronaAlgebra X l →+* B :=
    Ideal.Quotient.lift (nullMatrixSequenceIdeal X l) f.toAlgHom.toRingHom
      (fun a ha ↦ hf a ha)
  { toFun := g
    map_one' := g.map_one
    map_mul' := g.map_mul
    map_zero' := g.map_zero
    map_add' := g.map_add
    commutes' := fun r ↦ by
      show g (algebraMap ℂ (FilterMatrixCoronaAlgebra X l) r) = algebraMap ℂ B r
      rw [← Ideal.Quotient.mk_algebraMap ℂ (nullMatrixSequenceIdeal X l) r]
      exact f.commutes r
    map_star' := fun x ↦ by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      show g (star (Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a)) =
        star (g (Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a))
      rw [filterMatrixCorona_star_mk]
      exact map_star f a }

@[simp] theorem filterMatrixCoronaStarLift_mk {B : Type v} [Ring B] [StarRing B]
    [Algebra ℂ B] (f : BoundedMatrixSequence X →⋆ₐ[ℂ] B)
    (hf : ∀ a : BoundedMatrixSequence X, IsNullMatrixSequence X l a → f a = 0)
    (a : BoundedMatrixSequence X) :
    filterMatrixCoronaStarLift X l f hf
      (Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a) = f a := rfl

/-- **The universal property of the corona.**

A ⋆-homomorphism out of the bounded sequences that kills the sequences null
along `l` factors through the corona, still as a ⋆-homomorphism.

This is what a consumer uses instead of unfolding `FilterMatrixCStarCorona`.
Unfolding would put the ideal quotient back in front of typeclass search, which
is exactly what the opaque boundary exists to prevent. -/
noncomputable def filterMatrixCStarCoronaLift {B : Type v} [Ring B] [StarRing B]
    [Algebra ℂ B] (f : BoundedMatrixSequence X →⋆ₐ[ℂ] B)
    (hf : ∀ a : BoundedMatrixSequence X, IsNullMatrixSequence X l a → f a = 0) :
    FilterMatrixCStarCorona X l →⋆ₐ[ℂ] B := by
  unfold FilterMatrixCStarCorona
  exact filterMatrixCoronaStarLift X l f hf

@[simp] theorem filterMatrixCStarCoronaLift_mk {B : Type v} [Ring B] [StarRing B]
    [Algebra ℂ B] (f : BoundedMatrixSequence X →⋆ₐ[ℂ] B)
    (hf : ∀ a : BoundedMatrixSequence X, IsNullMatrixSequence X l a → f a = 0)
    (a : BoundedMatrixSequence X) :
    filterMatrixCStarCoronaLift X l f hf (filterMatrixCStarCoronaMk X l a) =
      f a := rfl

end GroupApproximation
