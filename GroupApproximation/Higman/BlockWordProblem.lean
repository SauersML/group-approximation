import GroupApproximation.Higman.BlockDecomposition
import GroupApproximation.Computability.WordProblemRE

/-!
# The per-block condition is the coded word problem

`Higman.BlockDecomposition` reduces the remaining field of a
`Higman.RecursivePresentation Higman.PCDirectSum` --- recursive enumerability
of `{w | evalRaw pcGen w = 1}` --- to a conjunction, over the finitely many
codes occurring as blocks of `w`, of statements of the form

    evalRaw (fun k ↦ PresentedGroup.of (letterOf c k)) v = 1 ,

`v` being the block-`c` subword re-indexed by that code's letters.  This file
identifies that statement with `AdianRabinWordProblem.WordProblem c v`, the
repository's coded word problem, which is recursively enumerable
(`Computability.WordProblemRE.rePred_wordProblemPred`).

The identification is two steps and no computability.  First, in a free
group, `evalRaw` of a family of generators is the `FreeGroup.mk` of the
letter list (`evalRaw_freeGroup`); this is where `FreeGroup.mul_mk`,
`FreeGroup.one_eq_mk` and `FreeGroup.inv_mk` do the work.  Second,
`PresentedGroup.of` is `PresentedGroup.mk` of `FreeGroup.of`, so the presented
value is the image of the free value (`Higman.map_evalRaw`), and
`PresentationCodes.wordOf` is by definition the `FreeGroup.mk` in question.

## What is left of (B1) after this file

Exactly one thing: that a conjunction, over a list computed from the input, of
instances of `wordProblemPred` is recursively enumerable.  Mathlib's `REPred`
API is thin --- `of_eq`, `Partrec.dom_re`, `to_re`,
`computable_iff_re_compl_re` and nothing else --- so the route is not to close
`REPred` under conjunction but to merge certificates:
`AdianRabinWordProblem.wordProblemPred_iff` presents each conjunct as one
existential over the `Primcodable` type `RawCertificate` with a decidable
matrix, so the whole conjunction is a single existential over a *list* of
certificates, which is the shape `WordProblemRE.rePred_exists_eq_true`
consumes.  That step is not taken here.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.PresentationCodes
open GroupApproximation.AdianRabinWordProblem

/-! ## 1.  `evalRaw` in a free group -/

/-- **A raw word evaluated at free generators is the free group element it
spells.** -/
theorem evalRaw_freeGroup {α : Type} (f : ℕ → α) (u : RawWord) :
    evalRaw (fun k ↦ FreeGroup.of (f k)) u
      = FreeGroup.mk (u.map fun p ↦ (f p.1, p.2)) := by
  induction u with
  | nil => simp [FreeGroup.one_eq_mk]
  | cons p u ih =>
      obtain ⟨k, b⟩ := p
      have hletter :
          (if b then FreeGroup.of (f k) else (FreeGroup.of (f k))⁻¹)
            = FreeGroup.mk [(f k, b)] := by
        cases b with
        | false => simp [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]
        | true => simp [FreeGroup.of]
      simp [ih, hletter, FreeGroup.mul_mk]

/-! ## 2.  ... and in a coded group -/

/-- The value of a raw word at the generators of a coded group is the class of
the free-group word the code spells. -/
theorem evalRaw_letterOf (c : PresentationCode) (u : RawWord) :
    evalRaw (fun k ↦ (PresentedGroup.of (letterOf c k) : Carrier c)) u
      = PresentedGroup.mk (relatorSet c) (wordOf c u) := by
  have hfam : (fun k ↦ (PresentedGroup.of (letterOf c k) : Carrier c))
      = fun k ↦ PresentedGroup.mk (relatorSet c) (FreeGroup.of (letterOf c k)) :=
    rfl
  rw [hfam, ← map_evalRaw, evalRaw_freeGroup]
  rfl

/-- **The per-block condition is the coded word problem.** -/
theorem evalRaw_letterOf_eq_one_iff (c : PresentationCode) (u : RawWord) :
    evalRaw (fun k ↦ (PresentedGroup.of (letterOf c k) : Carrier c)) u = 1
      ↔ WordProblem c u := by
  rw [evalRaw_letterOf]
  exact Iff.rfl

/-! ## 3.  (B1)'s remaining field, as a finite conjunction of word problems -/

/-- **The reduction (B1) is now down to.**  A raw word is trivial in the
Primcodable-indexed absorber's direct sum exactly when, for each of the
finitely many codes occurring as a block of `w`, the corresponding re-indexed
subword solves that code's word problem.

Every ingredient of the right-hand side is computed from `w` by a `List.map`
and a `List.filter`, and each conjunct is recursively enumerable
(`Computability.WordProblemRE.rePred_wordProblemPred`).  What is not proved
here is that the conjunction is. -/
theorem evalRaw_pcGen_eq_one_iff_wordProblem (w : RawWord) :
    evalRaw pcGen w = 1 ↔
      ∀ c ∈ blockList w, wordProblemPred (c, blockWord w c) := by
  rw [evalRaw_pcGen_eq_one_iff_reindexed]
  refine forall_congr' fun c => imp_congr_right fun _ => ?_
  exact evalRaw_letterOf_eq_one_iff c _

end Higman
end GroupApproximation
