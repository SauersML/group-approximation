import Mathlib.GroupTheory.FreeGroup.Reduce
import GroupApproximation.Meta.AxiomGuard

/-!
# Initial segments of reduced words in a free group

Powers' combinatorial condition for a free group of rank at least two is proved
by looking at the first letters of reduced words.  This module supplies two
tools that argument runs on:

* `toWord_mul_of_isReduced` — when the concatenation of two reduced words is
  itself reduced, it *is* the reduced word of the product: no cancellation.
  Its hypothesis is discharged by `isReduced_append`, which is
  `List.isChain_append` read through the definition of `FreeGroup.IsReduced`,
  namely `L.IsChain fun a b ↦ a.1 = b.1 → a.2 = b.2`.
* `initialRun_replicate_append` — the initial run of a letter `p` in
  `replicate k p ++ L` has length exactly `k` when `L` does not begin with `p`.

The second is what makes the translates `bⁱ D` of Powers' construction pairwise
disjoint: distinct exponents give distinct initial-run lengths, so the
translates cannot meet.

## What this module is not

It does not prove Powers' property, and it does not pretend to be close to it.
The step it does not touch is the one needing a cancellation *count*:
conjugating a finite set by a long enough power of one generator makes every
element of the set begin and end with that generator.  See `RESIDUAL.md` of the
`o-cstar-reg` lane for the construction in full.

## Manuscript status

Infrastructure toward `ReducedGroupCStarTrace.PowersProperty` for free groups;
certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace FreeGroupWord

open FreeGroup

universe u

variable {X : Type u}

/-! ## Concatenation without cancellation -/

/-- **The junction criterion.**  A concatenation of two reduced words is reduced
exactly when no letter at the junction cancels. -/
theorem isReduced_append {L₁ L₂ : List (X × Bool)} (h₁ : IsReduced L₁)
    (h₂ : IsReduced L₂)
    (hj : ∀ x ∈ L₁.getLast?, ∀ y ∈ L₂.head?, x.1 = y.1 → x.2 = y.2) :
    IsReduced (L₁ ++ L₂) :=
  List.isChain_append.mpr ⟨h₁, h₂, hj⟩

/-- **No cancellation means concatenation.**  If the concatenation of the
reduced words of `u` and `v` is reduced then it is the reduced word of `u * v`. -/
theorem toWord_mul_of_isReduced [DecidableEq X] {u v : FreeGroup X}
    (h : IsReduced (u.toWord ++ v.toWord)) :
    (u * v).toWord = u.toWord ++ v.toWord := by
  rw [toWord_mul, h.reduce_eq]

/-! ## The initial run of a fixed letter -/

/-- The length of the initial block of letters equal to `p`. -/
def initialRun [DecidableEq X] (p : X × Bool) (L : List (X × Bool)) : ℕ :=
  (L.takeWhile (fun q ↦ decide (q = p))).length

@[simp] theorem initialRun_nil [DecidableEq X] (p : X × Bool) :
    initialRun p ([] : List (X × Bool)) = 0 := rfl

theorem initialRun_cons_of_eq [DecidableEq X] {p q : X × Bool} (h : q = p)
    (L : List (X × Bool)) :
    initialRun p (q :: L) = initialRun p L + 1 := by
  rw [initialRun, List.takeWhile_cons_of_pos (by simpa using h), List.length_cons,
    initialRun]

theorem initialRun_cons_of_ne [DecidableEq X] {p q : X × Bool} (h : q ≠ p)
    (L : List (X × Bool)) : initialRun p (q :: L) = 0 := by
  rw [initialRun, List.takeWhile_cons_of_neg (by simpa using h), List.length_nil]

/-- **The initial run of `replicate k p ++ L` is exactly `k`** when `L` does not
itself begin with `p`. -/
theorem initialRun_replicate_append [DecidableEq X] (p : X × Bool) (k : ℕ)
    {L : List (X × Bool)} (hL : ∀ y ∈ L.head?, y ≠ p) :
    initialRun p (List.replicate k p ++ L) = k := by
  induction k with
  | zero =>
      rw [List.replicate_zero, List.nil_append]
      cases hcase : L with
      | nil => simp
      | cons y t =>
          refine initialRun_cons_of_ne ?_ t
          refine hL y ?_
          rw [hcase]
          simp
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, initialRun_cons_of_eq rfl, ih]

end FreeGroupWord
end GroupApproximation

open GroupApproximation.FreeGroupWord

#audit_axioms isReduced_append
#audit_axioms toWord_mul_of_isReduced
#audit_axioms initialRun_replicate_append
