import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Freely trivial iff a deletion sequence reaches the empty word

`Computability.AdianRabinWordProblem` reduces r.e.-ness of the word problem to
one obligation, and names the mathematics inside it: the equivalence

> freely trivial iff some deletion sequence reaches `[]`

That equivalence is proved here, and it is smaller than the docstring's estimate
suggests, because Mathlib's `FreeGroup.Red` *is* the reflexive-transitive
closure of the deletion step.  So "some deletion sequence reaches `[]`" is
literally `FreeGroup.Red L []`, and the content is only the passage from
equality in the group to reducibility of the representative word.

`FreeGroup.Red.exact` gives `mk L₁ = mk L₂ ↔ Join Red L₁ L₂`, i.e. a common
reduct.  Against the empty word the common reduct collapses: `Red [] M` forces
`M = []` (`Red.nil_iff`), so the join degenerates to `Red L []` and no
confluence argument is needed at this point.

## Why this is the useful direction for `D2`

The remaining obligation there is a *computability* one, and the recommended
route stays on raw words precisely to avoid needing `Primcodable (FreeGroup α)`
— which Mathlib does not have, at this revision, in any form.  This lemma is
what licenses that route: it lets a certificate talk about deletion steps on
`List (α × Bool)`, where `List.take`, `List.drop`, `List.append` and decidable
equality are all within reach of Mathlib's `Primrec` list API, instead of about
elements of a free group, which are not encodable at all.
-/

namespace GroupApproximation
namespace Computability

open FreeGroup

variable {α : Type*}

/-- **Freely trivial iff reducible to the empty word.**  The right-hand side is
`Red`, which unfolds to a finite sequence of deletions of adjacent inverse
pairs, so this is the equivalence the certificate search needs. -/
theorem mk_eq_one_iff_red_nil {L : List (α × Bool)} :
    FreeGroup.mk L = 1 ↔ FreeGroup.Red L [] := by
  rw [FreeGroup.one_eq_mk, FreeGroup.Red.exact]
  constructor
  · rintro ⟨M, hLM, hnilM⟩
    rwa [FreeGroup.Red.nil_iff.mp hnilM] at hLM
  · intro h
    exact ⟨[], h, FreeGroup.Red.refl⟩

/-- The same statement for a word given as `FreeGroup.mk`, in the direction the
certificate produces it. -/
theorem red_nil_of_mk_eq_one {L : List (α × Bool)} (h : FreeGroup.mk L = 1) :
    FreeGroup.Red L [] :=
  mk_eq_one_iff_red_nil.mp h

/-- And the converse, which is the soundness half: a deletion sequence to `[]`
witnesses triviality, whatever else the certificate contains. -/
theorem mk_eq_one_of_red_nil {L : List (α × Bool)} (h : FreeGroup.Red L []) :
    FreeGroup.mk L = 1 :=
  mk_eq_one_iff_red_nil.mpr h

end Computability
end GroupApproximation
