import GroupApproximation.Higman.EvalRaw
import GroupApproximation.Algebra.TorsionFreeRadicalTower

/-!
# (B2) reduced: the torsion-free quotient of a recursive presentation

`Higman.Program`'s split of Chiodo Proposition 3.8 has a second half, **(B2)**:
the universal torsion-free quotient of a recursively presented group is
recursively presented.  This file does the algebra of it and leaves exactly one
recursive-enumerability statement.

A `Higman.RecursivePresentation` is three fields.  Two of them transfer with no
work at all:

* the generating family of `A^tf` is the image of the generating family of `A`
  (`quotientGen`), and it spans because the projection is onto
  (`spans_quotientGen`);
* a raw word dies in `A^tf` exactly when its value in `A` lies in the
  torsion-free radical (`evalRaw_quotientGen_eq_one_iff`), and by Chiodo's
  Proposition 3.3 --- `Algebra.TorsionFreeRadicalTower` --- exactly when it
  lies in some finite stage of the tower
  (`evalRaw_quotientGen_eq_one_iff_tower`).

So (B2) is exactly the statement that

    { w | ∃ i, evalRaw gen w ∈ torsionTower A i }

is recursively enumerable, and `recursivePresentationQuotient` takes that as
its only hypothesis.  This is Chiodo's Lemmas 3.5--3.7, and it is where the
real content of Proposition 3.8 lives: the stages have to be enumerated
*uniformly*, each stage being a normal closure of an r.e. set of "becomes
torsion modulo the previous stage" witnesses.  None of that is here.

Note what the reduction buys.  The `∃ i` is an *unbounded* search over a
`Primcodable` type, and membership in `torsionTower A i` is, stage by stage, a
normal-closure membership --- again an existential over raw data (conjugators
and exponents).  So the shape is again "one unbounded search with a decidable
matrix", the same shape `WordProblemRE.rePred_exists_eq_true` consumes, and the
same shape `Higman.BlockSearch` put (B1) into.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.Chiodo

variable {A : Type} [Group A]

/-! ## 1.  The generating family of the quotient -/

/-- The generating family of `A^tf`: the images of a generating family of
`A`. -/
def quotientGen (gen : ℕ → A) : ℕ → TorsionFreeQuotient A :=
  fun n ↦ toTorsionFreeQuotient A (gen n)

theorem evalRaw_quotientGen (gen : ℕ → A) (w : RawWord) :
    evalRaw (quotientGen gen) w = toTorsionFreeQuotient A (evalRaw gen w) :=
  (map_evalRaw (toTorsionFreeQuotient A) gen w).symm

/-- **It spans**, because the projection is onto. -/
theorem spans_quotientGen {gen : ℕ → A}
    (hspan : Subgroup.closure (Set.range gen) = ⊤) :
    Subgroup.closure (Set.range (quotientGen gen)) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro q
  obtain ⟨g, rfl⟩ := toTorsionFreeQuotient_surjective q
  obtain ⟨w, rfl⟩ :=
    (mem_closure_iff_exists_evalRaw gen g).1
      (by rw [hspan]; exact Subgroup.mem_top g)
  rw [← evalRaw_quotientGen gen w]
  exact evalRaw_mem_closure _ w

/-! ## 2.  The word problem of the quotient -/

/-- A raw word dies in `A^tf` exactly when its value lies in the torsion-free
radical. -/
theorem evalRaw_quotientGen_eq_one_iff (gen : ℕ → A) (w : RawWord) :
    evalRaw (quotientGen gen) w = 1 ↔ evalRaw gen w ∈ torsionFreeRadical A := by
  rw [evalRaw_quotientGen]
  exact toTorsionFreeQuotient_eq_one_iff

/-- **The form (B2) has to make effective.**  By Chiodo's Proposition 3.3 the
radical is the union of the tower, so membership is witnessed at a finite
stage. -/
theorem evalRaw_quotientGen_eq_one_iff_tower (gen : ℕ → A) (w : RawWord) :
    evalRaw (quotientGen gen) w = 1 ↔
      ∃ i : ℕ, evalRaw gen w ∈ torsionTower A i := by
  rw [evalRaw_quotientGen_eq_one_iff, torsionFreeRadical_eq_torsionOmega,
    mem_torsionOmega_iff]

/-! ## 3.  (B2), modulo one recursive-enumerability statement -/

/-- **(B2) reduced to one statement.**  A recursive presentation of `A` gives a
recursive presentation of `A^tf` as soon as tower membership of the word values
is recursively enumerable.

The hypothesis is Chiodo's Lemmas 3.5--3.7 in the vocabulary of this
development, and it is the only thing left of Proposition 3.8. -/
def recursivePresentationQuotient (P : RecursivePresentation A)
    (hre : REPred fun w : RawWord ↦ ∃ i : ℕ, evalRaw P.gen w ∈ torsionTower A i) :
    RecursivePresentation (TorsionFreeQuotient A) where
  gen := quotientGen P.gen
  spans := spans_quotientGen P.spans
  re := hre.of_eq fun w => (evalRaw_quotientGen_eq_one_iff_tower P.gen w).symm

end Higman
end GroupApproximation
