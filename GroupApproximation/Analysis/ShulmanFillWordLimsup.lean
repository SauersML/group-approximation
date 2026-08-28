import GroupApproximation.Analysis.ShulmanFillConjugatePair
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCoronaNormSeparation

/-!
# The limsup bridge for the conjugated pair

`ShulmanFillConjugatePair` reduces Theorem 16 to
`ConjugateWordNormingStatement`, whose conclusion is an inequality between the
amalgam norm of a word `y` and the norm of its evaluation at
`conjugateRepresentation iA iB l r hlr u hu`.  That evaluation lands in a norm
matrix corona, and the corona norm of a class is the `limsup` of the coordinate
norms of any bounded representative
(`Manuscript.OneSidedMFRadical.norm_normMatrixCStarCoronaMk_eq_limsup`).  This
module is the passage between the two: it turns the corona-level statement
into a statement about finite-dimensional matrices, which is where the
remaining analytic estimate has to be done.

The bridge splits cleanly in two, and only the first half needs the corona:

* `norm_eval_conjugateRepresentation_eq_limsup` — for **any** bounded
  representative `a` of the evaluation, the norm of the evaluation is
  `limsup ‖a n‖`.  Proved.  With `exists_boundedRepresentative` (surjectivity
  of the quotient) this already gives the limsup form at every element of the
  amalgam, not only at words.
* `CoordinatewiseWordRepresentativeStatement` — the representative may be
  taken to be the *same word* in the discrete models: if `L` and `R` are
  coordinatewise lifts of `l` and of `u r u*`, then every word in the two
  factor images lifts to the corresponding word in `L` and `R`.  Not proved
  here; see below.

Composing them is `norm_eval_conjugateRepresentation_word`, which is the
statement `ShulmanFillConjugatePair`'s docstring asks for.

## What the word clause needs, and why it is not proved here

`CoordinatewiseWordRepresentativeStatement` is purely algebraic — no norms, no
limits, no properties of `L` and `R` beyond lifting `l` and `u r u*`
pointwise.  It says that the image of

  `T = StarAlgebra.adjoin ℂ (Set.range L ∪ Set.range R) ≤ BoundedMatrixSequence Z`

under the quotient `*`-homomorphism contains

  `StarAlgebra.adjoin ℂ (Set.range l ∪ Set.range (fun b ↦ u * r b * u*))`,

which holds because the quotient map is a `*`-homomorphism carrying the
generators of the second set onto images of generators of the first.  Two
one-step routes: `StarAlgebra.adjoin_le` into the image star subalgebra
`T.map (normMatrixCStarCoronaQuotient Z)`, whose membership is
`StarSubalgebra.mem_map`; or `StarAlgebra.adjoin_induction` on `y`, carrying
the representative through `algebraMap`, `add`, `mul` and `star` by the
matching `map_*` lemma of the quotient.  Both are short, and neither was
written here because this module was authored with builds suspended and the
argument order of `StarSubalgebra.map` and the binder shape of
`StarAlgebra.adjoin_induction` are exactly the two things a blind author gets
wrong.  Stating it as a `Prop` keeps the composition below honest.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated.
-/

namespace GroupApproximation
namespace ShulmanFill

-- the operator norm on each `Matrix (Z n) (Z n) ℂ`, and with it the ring and
-- norm structure of `BoundedMatrixSequence`, live in this scope
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {C A₁ A₂ : Type} [CStarAlgebra C] [CStarAlgebra A₁] [CStarAlgebra A₂]
  (iA : C →⋆ₐ[ℂ] A₁) (iB : C →⋆ₐ[ℂ] A₂)
  [Nonempty (CStarAmalgamRepresentation iA iB)]
  (Z : ℕ → FiniteModel) [∀ n, Nonempty (Z n)]
  (l : A₁ →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n))
  (r : A₂ →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n))
  (hlr : l.comp iA = r.comp iB)
  (u : unitary (NormMatrixCStarCorona (fun n ↦ Z n)))
  (hu : ∀ c : C,
    (u : NormMatrixCStarCorona (fun n ↦ Z n)) * l (iA c) =
      l (iA c) * (u : NormMatrixCStarCorona (fun n ↦ Z n)))

/-- The `ℓ∞` product of the models' matrix algebras is a `ℂ`-star module.  This
is Mathlib's own `lp` instance, registered here at the model-indexed family:
`StarAlgebra.adjoin ℂ` below asks for it twice, and rediscovering it from the
`lp` instance graph each time overruns the instance-search budget.  The proof is
Mathlib's, transported through `lp.ext`. -/
noncomputable instance boundedMatrixSequenceStarModule :
    StarModule ℂ (BoundedMatrixSequence (fun n ↦ Z n)) where
  star_smul _ _ :=
    lp.ext (star_smul (R := ℂ) (A := ∀ n, Matrix (Z n) (Z n) ℂ) _ _)

/-! ## The evaluation of the conjugated pair, on generators -/

@[simp] theorem eval_conjugateRepresentation_left (a : A₁) :
    universalCStarAmalgamEval iA iB
        (conjugateRepresentation iA iB l r hlr u hu)
        (universalCStarAmalgamLeft iA iB a) = l a := rfl

@[simp] theorem eval_conjugateRepresentation_right (b : A₂) :
    universalCStarAmalgamEval iA iB
        (conjugateRepresentation iA iB l r hlr u hu)
        (universalCStarAmalgamRight iA iB b) =
      (u : NormMatrixCStarCorona (fun n ↦ Z n)) * r b *
        star (u : NormMatrixCStarCorona (fun n ↦ Z n)) := rfl

/-! ## The corona norm is a limsup of coordinate norms -/

/-- Every value of the conjugated evaluation has a bounded matrix-sequence
representative: the quotient onto the corona is surjective. -/
theorem exists_boundedRepresentative (y : UniversalCStarAmalgam iA iB) :
    ∃ a : BoundedMatrixSequence (fun n ↦ Z n),
      normMatrixCStarCoronaMk (fun n ↦ Z n) a =
        universalCStarAmalgamEval iA iB
          (conjugateRepresentation iA iB l r hlr u hu) y :=
  normMatrixCStarCoronaMk_surjective (fun n ↦ Z n) _

/-- **The bridge, at any representative.**  The norm of the conjugated
evaluation is the `limsup` of the coordinate norms of any bounded sequence
representing it.  This is the only place the corona is used; everything after
it is a statement about finite matrices. -/
theorem norm_eval_conjugateRepresentation_eq_limsup
    (y : UniversalCStarAmalgam iA iB)
    (a : BoundedMatrixSequence (fun n ↦ Z n))
    (ha : normMatrixCStarCoronaMk (fun n ↦ Z n) a =
      universalCStarAmalgamEval iA iB
        (conjugateRepresentation iA iB l r hlr u hu) y) :
    ‖universalCStarAmalgamEval iA iB
        (conjugateRepresentation iA iB l r hlr u hu) y‖ =
      Filter.limsup (fun n ↦ ‖a n‖) Filter.cofinite := by
  rw [← ha]
  exact Manuscript.OneSidedMFRadical.norm_normMatrixCStarCoronaMk_eq_limsup
    (fun n ↦ Z n) a

/-- The limsup form at every element of the amalgam, with the representative
existentially quantified. -/
theorem exists_limsup_eq_norm_eval_conjugateRepresentation
    (y : UniversalCStarAmalgam iA iB) :
    ∃ a : BoundedMatrixSequence (fun n ↦ Z n),
      normMatrixCStarCoronaMk (fun n ↦ Z n) a =
          universalCStarAmalgamEval iA iB
            (conjugateRepresentation iA iB l r hlr u hu) y ∧
        ‖universalCStarAmalgamEval iA iB
            (conjugateRepresentation iA iB l r hlr u hu) y‖ =
          Filter.limsup (fun n ↦ ‖a n‖) Filter.cofinite := by
  obtain ⟨a, ha⟩ := exists_boundedRepresentative iA iB Z l r hlr u hu y
  exact ⟨a, ha,
    norm_eval_conjugateRepresentation_eq_limsup iA iB Z l r hlr u hu y a ha⟩

/-! ## The word clause -/

/-- **Words lift to words.**  If `L` and `R` lift `l` and `u r u*`
coordinatewise, every word in the two factor images of the amalgam is
represented by a word in `L` and `R`.  Purely algebraic: it is the statement
that the quotient `*`-homomorphism carries the star subalgebra generated by
the ranges of `L` and `R` onto the star subalgebra generated by the ranges of
`l` and `u r u*`. -/
def CoordinatewiseWordRepresentativeStatement : Prop :=
  ∀ (L : A₁ → BoundedMatrixSequence (fun n ↦ Z n))
    (R : A₂ → BoundedMatrixSequence (fun n ↦ Z n)),
    (∀ a : A₁, normMatrixCStarCoronaMk (fun n ↦ Z n) (L a) = l a) →
    (∀ b : A₂, normMatrixCStarCoronaMk (fun n ↦ Z n) (R b) =
      (u : NormMatrixCStarCorona (fun n ↦ Z n)) * r b *
        star (u : NormMatrixCStarCorona (fun n ↦ Z n))) →
      ∀ y ∈ adjoinSet iA iB,
        ∃ s ∈ StarAlgebra.adjoin ℂ (Set.range L ∪ Set.range R),
          normMatrixCStarCoronaMk (fun n ↦ Z n) s =
            universalCStarAmalgamEval iA iB
              (conjugateRepresentation iA iB l r hlr u hu) y

/-- **`norm_eval_conjugateRepresentation_word`.**  For a word `y` of the
amalgam, the norm of its evaluation at the conjugated pair is the `limsup` of
the coordinate norms of the corresponding word in the discrete models
`(L_n, u_n r_n u_n^*)`.  This is the form in which the remaining estimate is
an estimate about finite matrices. -/
theorem norm_eval_conjugateRepresentation_word
    (hword : CoordinatewiseWordRepresentativeStatement iA iB Z l r hlr u hu)
    (L : A₁ → BoundedMatrixSequence (fun n ↦ Z n))
    (R : A₂ → BoundedMatrixSequence (fun n ↦ Z n))
    (hL : ∀ a : A₁, normMatrixCStarCoronaMk (fun n ↦ Z n) (L a) = l a)
    (hR : ∀ b : A₂, normMatrixCStarCoronaMk (fun n ↦ Z n) (R b) =
      (u : NormMatrixCStarCorona (fun n ↦ Z n)) * r b *
        star (u : NormMatrixCStarCorona (fun n ↦ Z n)))
    (y : UniversalCStarAmalgam iA iB) (hy : y ∈ adjoinSet iA iB) :
    ∃ s ∈ StarAlgebra.adjoin ℂ (Set.range L ∪ Set.range R),
      ‖universalCStarAmalgamEval iA iB
          (conjugateRepresentation iA iB l r hlr u hu) y‖ =
        Filter.limsup (fun n ↦ ‖s n‖) Filter.cofinite := by
  obtain ⟨s, hsmem, hs⟩ := hword L R hL hR y hy
  exact ⟨s, hsmem,
    norm_eval_conjugateRepresentation_eq_limsup iA iB Z l r hlr u hu y s hs⟩

end

end ShulmanFill
end GroupApproximation
