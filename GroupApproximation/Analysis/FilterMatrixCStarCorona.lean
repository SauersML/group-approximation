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

/-- The real scalars sit under the complex ones.  This is the ONE structure that
does not transport by itself: `Algebra ℝ` is found on the opaque type through
`NormedAlgebra.complexToReal`, but the tower relating it to the complex action is
not, and `StarAlgHom.map_cfc` needs it because the calculus is taken over `ℝ`
while the algebra is over `ℂ`. -/
private theorem coronaIsScalarTowerReal :
    IsScalarTower ℝ ℂ (FilterMatrixCoronaAlgebra X l) := inferInstance

instance filterMatrixCStarCoronaIsScalarTowerReal :
    IsScalarTower ℝ ℂ (FilterMatrixCStarCorona X l) := coronaIsScalarTowerReal X l

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

/-! ## The lift is contractive, hence continuous

`StarAlgHom.map_cfc` -- the naturality that lets the functional calculus be
computed on either side of a ⋆-homomorphism -- takes `Continuous ⇑φ` as a
hypothesis.  For a ⋆-homomorphism between C⋆-algebras that is automatic
mathematically, but it is not a `fun_prop` fact about a map built by a lift, so
it is proved here once, from the only estimate the quotient norm supplies. -/

section Bound

variable {B : Type v} [NormedRing B] [StarRing B] [NormedAlgebra ℂ B]

/-- **A contractive ⋆-homomorphism descends to a contractive one.**

The quotient norm is an infimum over representatives, so the bound transfers by
choosing a representative within `ε` of it. -/
theorem norm_filterMatrixCoronaStarLift_le
    (f : BoundedMatrixSequence X →⋆ₐ[ℂ] B)
    (hf : ∀ a : BoundedMatrixSequence X, IsNullMatrixSequence X l a → f a = 0)
    (hb : ∀ a : BoundedMatrixSequence X, ‖f a‖ ≤ ‖a‖)
    (x : FilterMatrixCoronaAlgebra X l) :
    ‖filterMatrixCoronaStarLift X l f hf x‖ ≤ ‖x‖ := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨a, ha, hlt⟩ := Submodule.Quotient.norm_mk_lt x hε
  have hmk : (Submodule.Quotient.mk a : FilterMatrixCoronaAlgebra X l)
      = Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a := rfl
  rw [hmk] at ha
  calc ‖filterMatrixCoronaStarLift X l f hf x‖
      = ‖f a‖ := by rw [← ha, filterMatrixCoronaStarLift_mk]
    _ ≤ ‖a‖ := hb a
    _ ≤ ‖x‖ + ε := hlt.le

/-- The same bound at the opaque corona.  The two types are definitionally
equal and their norms are the transported ones, so this is the lemma above. -/
theorem norm_filterMatrixCStarCoronaLift_le
    (f : BoundedMatrixSequence X →⋆ₐ[ℂ] B)
    (hf : ∀ a : BoundedMatrixSequence X, IsNullMatrixSequence X l a → f a = 0)
    (hb : ∀ a : BoundedMatrixSequence X, ‖f a‖ ≤ ‖a‖)
    (x : FilterMatrixCStarCorona X l) :
    ‖filterMatrixCStarCoronaLift X l f hf x‖ ≤ ‖x‖ :=
  norm_filterMatrixCoronaStarLift_le X l f hf hb x

/-- **The lift of a contractive ⋆-homomorphism is continuous.**  This is the
hypothesis `StarAlgHom.map_cfc` asks for. -/
theorem continuous_filterMatrixCStarCoronaLift
    (f : BoundedMatrixSequence X →⋆ₐ[ℂ] B)
    (hf : ∀ a : BoundedMatrixSequence X, IsNullMatrixSequence X l a → f a = 0)
    (hb : ∀ a : BoundedMatrixSequence X, ‖f a‖ ≤ ‖a‖) :
    Continuous (filterMatrixCStarCoronaLift X l f hf) :=
  AddMonoidHomClass.continuous_of_bound (filterMatrixCStarCoronaLift X l f hf) 1
    (fun x ↦ by simpa using norm_filterMatrixCStarCoronaLift_le X l f hf hb x)

end Bound

/-! ## Classes of unitary sequences

`Analysis/NormMatrixCoronaUnitary.lean` sends a coordinatewise-unitary sequence
to a unitary of the corona, at `cofinite` and for a family that is
**strictly** multiplicative.  The manuscript's family is neither: it lives at a
free `ω` and is only `ω`-multiplicative.  The unitarity half generalizes
verbatim, and is separated out here; multiplicativity is a different argument
and belongs with the family that supplies it. -/

section Unitary

/-- The class of a sequence is zero exactly when the sequence is `l`-null. -/
theorem filterMatrixCStarCoronaMk_eq_zero_iff (a : BoundedMatrixSequence X) :
    filterMatrixCStarCoronaMk X l a = 0 ↔ IsNullMatrixSequence X l a := by
  unfold filterMatrixCStarCoronaMk FilterMatrixCStarCorona
  exact filterMatrixCoronaMk_eq_zero_iff X l a

/-- **A sequence that is unitary on the nose has a unitary class.**

The hypotheses are the exact identities, not approximate ones: for a
coordinatewise-unitary family they hold at every stage, so nothing is lost by
asking for them, and the quotient does the rest. -/
theorem filterMatrixCStarCoronaMk_mem_unitary (a : BoundedMatrixSequence X)
    (h₁ : star a * a = 1) (h₂ : a * star a = 1) :
    filterMatrixCStarCoronaMk X l a ∈
      unitary (FilterMatrixCStarCorona X l) := by
  constructor
  · rw [filterMatrixCStarCorona_star_mk, ← map_mul, h₁, map_one]
  · rw [filterMatrixCStarCorona_star_mk, ← map_mul, h₂, map_one]

/-- Two sequences have the same class exactly when they differ by an `l`-null
one.  This is what turns `ω`-multiplicativity of a family into genuine
multiplicativity of its classes. -/
theorem filterMatrixCStarCoronaMk_eq_iff (a b : BoundedMatrixSequence X) :
    filterMatrixCStarCoronaMk X l a = filterMatrixCStarCoronaMk X l b ↔
      IsNullMatrixSequence X l (a - b) := by
  rw [← filterMatrixCStarCoronaMk_eq_zero_iff, map_sub, sub_eq_zero]

end Unitary

end GroupApproximation
