import GroupApproximation.Analysis.NormMatrixCoronaUnitary
import GroupApproximation.Analysis.ShulmanFillConjugatePair

/-!
# From asymptotically commuting unitaries to a unitary of the commutant

`ShulmanFill.ConjugateWordNormingStatement` asks for a unitary of the corona
that commutes with the image of the amalgamated algebra.  The construction
produces no such unitary directly: it produces finite-dimensional unitaries
`u_n` whose commutators against the models die.  This module is the passage
between the two — exactly commuting in the corona is *asymptotically*
commuting in the models, because the corona kills null sequences.

`coronaUnitary_commutes_of_tendsto_commutator` is that passage for one
element, and `commutes_with_range_of_tendsto_commutator` is the form the
conjugation step consumes: it produces the hypothesis `hu` of
`ShulmanFill.conjugateRepresentation` from a family of representatives whose
commutators against `u_n` are null.

## What is still missing, precisely

Write `γ_n = l_n ∘ ι_A` for the finite-dimensional model of the amalgamated
part and `y` for a word of the amalgam.  After all the reductions in the
`ShulmanFill` chain, the one statement that remains is finite dimensional:

> `exists_diagonal_unitaries_attaining_word_norm`: for a word `y` and `ε > 0`
> there are unitaries `u_n ∈ U(k_n)` with `‖[u_n, γ_n c]‖ → 0` for every `c`
> and `‖y‖ - ε ≤ limsup_n ‖y(l_n, u_n r_n u_n^*)‖`.

Only the second clause is open.  The first clause is discharged by this
module, and the *reverse* inequality is free: every compatible pair evaluates
the amalgam contractively (`norm_universalCStarAmalgamEval_le` below), so the
limsup never exceeds `‖y‖`.  The whole analytic content of Shulman's Theorem
16 is therefore the single inequality `‖y‖ - ε ≤ limsup_n …`.

## Correction: that inequality is not how the paper proceeds

An earlier version of this docstring described the missing step as an
estimate of Haagerup--Thorbjørnsen type — random matrices, asymptotic
freeness, generic position.  Reading the paper shows that is wrong.  Shulman
proves Theorem 16 (arXiv:2603.13564v2, p. 10) by putting
`D = C*(φ_A(A), φ_B(B))`, quoting `A *_C B ⊂ D *_C D` from Enders--Shulman
(arXiv:2403.12224, Th. 4.11, her Theorem 13) and applying the symmetric
Theorem 10 to `D`, whose conjugating unitary is the explicit **flip**
`((0,1),(1,0))` — it commutes with the amalgamated part exactly, because the
two factor representations agree on `C`.  No random matrix appears anywhere
in the argument.  The corrected account, with page references, is in
`Analysis/ShulmanFillCommutantExact`.

The statement below is therefore not the paper's route.  It remains a
sufficient condition — a norming family does make the amalgam MF, by
`isMFAlgebra_of_norming_representations` — but formalizing Shulman means
Theorem 4 (her lifting characterization of MF), Lemma 7, Lemma 9 and the
cited Theorem 13, not a genericity estimate.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter
-- the operator norm on each `Matrix (X n) (X n) ℂ`, and with it the ring and
-- norm structure of `BoundedMatrixSequence`, live in this scope
open scoped Matrix.Norms.L2Operator

noncomputable section

variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]

/-! ## The commutator of a unitary sequence with a bounded sequence -/

/-- Coordinates of the commutator of a unitary sequence with a bounded
sequence. -/
theorem commutatorSeq_apply (u : ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (a : BoundedMatrixSequence (fun n ↦ X n)) (n : ℕ) :
    (unitarySequenceBounded X u * a - a * unitarySequenceBounded X u) n =
      (u n : Matrix (X n) (X n) ℂ) * a n -
        a n * (u n : Matrix (X n) (X n) ℂ) := by
  simp only [lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_mul, Pi.mul_apply,
    unitarySequenceBounded_apply]

/-- **Asymptotically commuting becomes commuting.**  If the commutators of a
unitary sequence with the coordinates of a bounded sequence vanish along
`cofinite`, the corona class of the unitary sequence commutes with the corona
class of the bounded sequence. -/
theorem coronaUnitary_commutes_of_tendsto_commutator
    (u : ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (a : BoundedMatrixSequence (fun n ↦ X n))
    (h : Tendsto (fun n ↦ ‖(u n : Matrix (X n) (X n) ℂ) * a n -
      a n * (u n : Matrix (X n) (X n) ℂ)‖) cofinite (nhds 0)) :
    ((unitarySequenceToCorona X u : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) *
        normMatrixCStarCoronaMk (fun n ↦ X n) a =
      normMatrixCStarCoronaMk (fun n ↦ X n) a *
        ((unitarySequenceToCorona X u :
          unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) := by
  have hcoe : ((unitarySequenceToCorona X u :
        unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n))
      = normMatrixCStarCoronaMk (fun n ↦ X n) (unitarySequenceBounded X u) := rfl
  have hnull : IsNullMatrixSequence (fun n ↦ X n) cofinite
      (unitarySequenceBounded X u * a - a * unitarySequenceBounded X u) := by
    show Tendsto (fun n ↦ ‖(unitarySequenceBounded X u * a -
      a * unitarySequenceBounded X u) n‖) cofinite (nhds 0)
    have hfun : ∀ n, ‖(u n : Matrix (X n) (X n) ℂ) * a n -
        a n * (u n : Matrix (X n) (X n) ℂ)‖ =
          ‖(unitarySequenceBounded X u * a -
            a * unitarySequenceBounded X u) n‖ := by
      intro n
      rw [commutatorSeq_apply]
    exact Filter.Tendsto.congr hfun h
  rw [hcoe, ← sub_eq_zero, ← map_mul, ← map_mul, ← map_sub,
    normMatrixCStarCoronaMk_eq_zero_iff]
  exact hnull

/-- **The hypothesis of `conjugateRepresentation`, from asymptotic data.**
Representatives of the images of the amalgamated algebra whose commutators
against a unitary sequence are null give a corona unitary commuting with those
images. -/
theorem commutes_with_range_of_tendsto_commutator
    {C A : Type} [CStarAlgebra C] [CStarAlgebra A]
    (u : ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (iA : C →⋆ₐ[ℂ] A) (l : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (a : C → BoundedMatrixSequence (fun n ↦ X n))
    (ha : ∀ c, normMatrixCStarCoronaMk (fun n ↦ X n) (a c) = l (iA c))
    (h : ∀ c, Tendsto (fun n ↦ ‖(u n : Matrix (X n) (X n) ℂ) * (a c) n -
      (a c) n * (u n : Matrix (X n) (X n) ℂ)‖) cofinite (nhds 0)) :
    ∀ c : C,
      ((unitarySequenceToCorona X u :
          unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) * l (iA c) =
        l (iA c) *
          ((unitarySequenceToCorona X u :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
              NormMatrixCStarCorona (fun n ↦ X n)) := by
  intro c
  rw [← ha c]
  exact coronaUnitary_commutes_of_tendsto_commutator X u (a c) (h c)

/-- The compatible representation built from a compatible corona pair and a
sequence of asymptotically commuting unitaries. -/
def conjugateRepresentationOfAsymptoticCommutator
    {C A B : Type} [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
    (u : ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    (l : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (r : B →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (hlr : l.comp iA = r.comp iB)
    (a : C → BoundedMatrixSequence (fun n ↦ X n))
    (ha : ∀ c, normMatrixCStarCoronaMk (fun n ↦ X n) (a c) = l (iA c))
    (h : ∀ c, Tendsto (fun n ↦ ‖(u n : Matrix (X n) (X n) ℂ) * (a c) n -
      (a c) n * (u n : Matrix (X n) (X n) ℂ)‖) cofinite (nhds 0)) :
    CStarAmalgamRepresentation iA iB :=
  conjugateRepresentation iA iB l r hlr (unitarySequenceToCorona X u)
    (commutes_with_range_of_tendsto_commutator X u iA l a ha h)

/-! ## The free half of the missing estimate -/

/-- Every evaluation coordinate is contractive, so no compatible pair can
overshoot the amalgam norm.  Only the lower bound is missing from
`exists_diagonal_unitaries_attaining_word_norm`. -/
theorem norm_universalCStarAmalgamEval_le
    {C A B : Type} [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    (R : CStarAmalgamRepresentation iA iB) (y : UniversalCStarAmalgam iA iB) :
    ‖universalCStarAmalgamEval iA iB R y‖ ≤ ‖y‖ :=
  NonUnitalStarAlgHom.norm_apply_le (universalCStarAmalgamEval iA iB R) y

end

end ShulmanFill
end GroupApproximation
