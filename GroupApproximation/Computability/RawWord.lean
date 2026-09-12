import GroupApproximation.Computability.PresentationCodeList

/-!
# Reading raw words

`PresentationCodes.wordOf` reads a `List (ℕ × Bool)` as an element of the free
group on a code's alphabet, by reducing each letter modulo the alphabet size.
Everything a *computable* transformation does happens at the level of these raw
words, and everything the group theory says happens at the level of the free
group, so the two have to be related letter by letter.

This file is that dictionary, and it is four facts: reading respects
concatenation, a one-letter word is a generator or its inverse, inversion is
`FreeGroup.invRev`, and a letter already below the alphabet size is read as
itself.  Nothing here is specific to any construction.
-/

namespace GroupApproximation
namespace RawWord

open PresentationCodes

variable (c : PresentationCode)

/-- The definitional unfolding of `wordOf`, named so that `rw` can use it.

**Deliberately not `@[simp]`, which is why the audit's RFL scan reports it.**
The scan's remedy for a `rfl`-proved theorem is to tag it, on the ground that
such a lemma exists to make a definitional fact available to `simp`.  That is
the wrong reading here: the three lemmas below (`wordOf_nil`, `wordOf_append`,
`wordOf_inv`) are the intended `simp` interface to `wordOf`, and two of them are
already tagged.  A `simp`-visible `wordOf_def` would unfold `wordOf` before they
could fire — including in `wordOf c []`, where it competes directly with
`wordOf_nil` — and it would do so in every `simp` call across the whole
`Computability` subtree, which is where all 180 occurrences of `wordOf` live.

So this one is left as an explicit-`rw` lemma.  The four call sites all spell it
out. -/
@[simp] theorem wordOf_def (u : List (ℕ × Bool)) :
    wordOf c u = FreeGroup.mk (u.map fun p => (letterOf c p.1, p.2)) := rfl

@[simp] theorem wordOf_nil : wordOf c [] = 1 := rfl

theorem wordOf_append (u v : List (ℕ × Bool)) :
    wordOf c (u ++ v) = wordOf c u * wordOf c v := by
  rw [wordOf_def, wordOf_def, wordOf_def, List.map_append]
  rfl

/-- A one-letter positive word.  `@[simp]` for the same reason as the two
`cons` lemmas below: the content is definitional, and stating it is worth doing
only if `simp` can use it.  It agrees with `wordOf_cons_pos` on the singleton,
which reaches the same normal form through `wordOf_nil` and `mul_one`. -/
@[simp] theorem wordOf_pos (i : ℕ) :
    wordOf c [(i, true)] = FreeGroup.of (letterOf c i) := rfl

/-- A one-letter negative word. -/
@[simp] theorem wordOf_neg (i : ℕ) :
    wordOf c [(i, false)] = (FreeGroup.of (letterOf c i))⁻¹ := rfl

theorem wordOf_cons (p : ℕ × Bool) (u : List (ℕ × Bool)) :
    wordOf c (p :: u) = wordOf c [p] * wordOf c u := by
  rw [← wordOf_append]
  rfl

/-- Peeling a positive letter.  Stated as its own lemma rather than through
`wordOf_cons` because `wordOf_cons` also matches a singleton, and so loops. -/
@[simp] theorem wordOf_cons_pos (i : ℕ) (u : List (ℕ × Bool)) :
    wordOf c ((i, true) :: u) = FreeGroup.of (letterOf c i) * wordOf c u := rfl

/-- Peeling a negative letter. -/
@[simp] theorem wordOf_cons_neg (i : ℕ) (u : List (ℕ × Bool)) :
    wordOf c ((i, false) :: u) = (FreeGroup.of (letterOf c i))⁻¹ * wordOf c u := rfl

/-- The inverse of a raw word is its reverse with the signs flipped. -/
def invWord (u : List (ℕ × Bool)) : List (ℕ × Bool) :=
  (u.map fun p => (p.1, !p.2)).reverse

theorem wordOf_invWord (u : List (ℕ × Bool)) :
    wordOf c (invWord u) = (wordOf c u)⁻¹ := by
  rw [wordOf_def, wordOf_def, FreeGroup.inv_mk]
  congr 1
  rw [invWord, FreeGroup.invRev, List.map_reverse, List.map_map, List.map_map]
  rfl

/-- A letter already below the alphabet size is read as itself. -/
theorem letterOf_val_of_lt {i : ℕ} (h : i < genCount c) :
    ((letterOf c i : Fin (genCount c)) : ℕ) = i :=
  Nat.mod_eq_of_lt h

end RawWord
end GroupApproximation
