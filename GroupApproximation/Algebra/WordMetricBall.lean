import GroupApproximation.Algebra.WordMetric
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Finite balls and the exponential growth bound for a finite generating set

`Algebra/WordMetric.lean` develops `wordNorm` and `wordDist` for an arbitrary
alphabet `S : Set G`.  Deliberately so: `S` there may be infinite and need not
contain `1`.  This file supplies the one thing that generality leaves out and
that every *quantitative* coarse-geometric argument begins from:

> for a **finite** symmetric generating set, balls are finite, and their
> cardinality grows at most exponentially in the radius.

This is item **G1.1** of the prerequisite list in
`Analysis/ExactnessPermanence.lean` ("Finite balls: `{g | wordNorm S g ≤ n}` is
finite for finite `S`").

## Why the bound is stated the way it is

The consumer is Guentner--Kaminker's estimate (14) --- see
`Analysis/CoarseCompression.lean` --- which needs exactly

```
    card { t : d(s,t) = n }  ≤  Λ ^ n     for a constant Λ independent of s, n.
```

Guentner and Kaminker write this with `Λ = card S`, using that a geodesic word
for an element of the sphere of radius `n` is a word of length exactly `n`.
Here the constant is `Λ = card T + 1`, which is what the induction below
produces without a separate "exactly `n`" bookkeeping step: a word of length at
most `n + 1` is either a word of length at most `n` or a letter followed by one.
The extra `+1` is invisible to every use --- all that is ever needed is that the
bound is *some* geometric function of the radius, since the Gaussian factor
`exp(-κ n^{1+ε})` beats every geometric series.

Nothing here needs the alphabet to generate for the *counting*; generation
enters only when the count is transferred from words to `wordNorm`, because
`wordNorm` takes the junk value `0` on elements that no word spells.

## Statements

* `exists_finset_isWord` --- the elements spelled by `T`-words of length at most
  `n` lie in a finite set of cardinality at most `(card T + 1) ^ n`;
* `exists_ball_finset` --- the same for the ball `{g | wordNorm T g ≤ n}`, under
  `IsSymmetricGeneratingSet`;
* `card_le_pow_of_wordDist_le` --- the form the analytic estimate uses: any
  finite set of points at word distance at most `n` from a common point `s` has
  cardinality at most `(card T + 1) ^ n`, uniformly in `s`.
-/

namespace GroupApproximation
namespace WordMetric

universe u

variable {G : Type u} [Group G]

/-! ## Words of bounded length -/

/-- **Words of bounded length spell finitely many elements.**  The elements of
`G` spelled by a `T`-word of length at most `n` all lie in one finite set, of
cardinality at most `(card T + 1) ^ n`.

The induction is the obvious one: a word of length at most `n + 1` is either
empty or a letter of `T` followed by a word of length at most `n`, so the set
grows by at most the pointwise product `T * B` at each step, and
`card (T * B) ≤ card T * card B`. -/
theorem exists_finset_isWord (T : Finset G) (n : ℕ) :
    ∃ B : Finset G, B.card ≤ (T.card + 1) ^ n ∧
      ∀ (l : List G) (g : G), IsWord (↑T : Set G) l g → l.length ≤ n → g ∈ B := by
  classical
  induction n with
  | zero =>
    refine ⟨{1}, by simp, ?_⟩
    intro l g hl hlen
    have hl0 : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst hl0
    have hg : g = 1 := by simpa using hl.prod_eq.symm
    simp [hg]
  | succ n ih =>
    obtain ⟨B, hcard, hmem⟩ := ih
    refine ⟨B ∪ T * B, ?_, ?_⟩
    · calc (B ∪ T * B).card ≤ B.card + (T * B).card := Finset.card_union_le _ _
        _ ≤ B.card + T.card * B.card := Nat.add_le_add_left Finset.card_mul_le _
        _ = (T.card + 1) * B.card := by ring
        _ ≤ (T.card + 1) * (T.card + 1) ^ n := Nat.mul_le_mul (le_refl _) hcard
        _ = (T.card + 1) ^ (n + 1) := by ring
    · intro l g hl hlen
      cases l with
      | nil =>
        have h1B : (1 : G) ∈ B := hmem [] 1 (isWord_nil _) (by simp)
        have hg : g = 1 := by simpa using hl.prod_eq.symm
        rw [hg]
        exact Finset.mem_union_left _ h1B
      | cons a l' =>
        have ha : a ∈ T := by
          have h := hl.letters a (List.mem_cons_self ..)
          simpa using h
        have hl' : IsWord (↑T : Set G) l' l'.prod :=
          ⟨fun x hx ↦ hl.letters x (List.mem_cons_of_mem a hx), rfl⟩
        have hlen' : l'.length ≤ n := by
          rw [List.length_cons] at hlen
          omega
        have hmem' : l'.prod ∈ B := hmem l' l'.prod hl' hlen'
        have hg : g = a * l'.prod := by
          rw [← hl.prod_eq]
          exact List.prod_cons
        rw [hg]
        exact Finset.mem_union_right _ (Finset.mul_mem_mul ha hmem')

/-! ## Balls -/

/-- **Balls are finite, with an exponential cardinality bound.**  Generation is
what lets the bound be read off `wordNorm`: without it `wordNorm` is `0` on
every element no word spells, and the "ball" is all of `G`. -/
theorem exists_ball_finset {T : Finset G}
    (hT : IsSymmetricGeneratingSet (↑T : Set G)) (n : ℕ) :
    ∃ B : Finset G, B.card ≤ (T.card + 1) ^ n ∧
      ∀ g : G, wordNorm (↑T : Set G) g ≤ n → g ∈ B := by
  obtain ⟨B, hcard, hmem⟩ := exists_finset_isWord T n
  refine ⟨B, hcard, ?_⟩
  intro g hg
  obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq hT g
  refine hmem l g hl ?_
  rw [hlen]
  exact hg

/-- **The uniform sphere bound**, in the form the Gaussian estimate consumes:
a finite set of points within word distance `n` of a common base point `s` has
at most `(card T + 1) ^ n` elements, with a bound independent of `s`.

Left invariance of the word metric is the whole content: translating by `s⁻¹`
carries the set into the ball at the identity. -/
theorem card_le_pow_of_wordDist_le {T : Finset G}
    (hT : IsSymmetricGeneratingSet (↑T : Set G)) (n : ℕ) (s : G) (F : Finset G)
    (hF : ∀ t ∈ F, wordDist (↑T : Set G) s t ≤ n) :
    F.card ≤ (T.card + 1) ^ n := by
  classical
  obtain ⟨B, hcard, hmem⟩ := exists_ball_finset hT n
  have hmaps : ∀ t ∈ F, s⁻¹ * t ∈ B := by
    intro t ht
    have h := hF t ht
    unfold wordDist at h
    exact hmem _ h
  have hinj : Set.InjOn (fun t ↦ s⁻¹ * t) (F : Set G) := by
    intro x _ y _ h
    simpa using h
  exact le_trans (Finset.card_le_card_of_injOn _ hmaps hinj) hcard

/-- The growth constant is at least one, so it can be used as the ratio of a
geometric series without a positivity side condition. -/
theorem one_le_growth (T : Finset G) : (1 : ℝ) ≤ (T.card : ℝ) + 1 := by
  have : (0 : ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
  linarith

end WordMetric
end GroupApproximation
