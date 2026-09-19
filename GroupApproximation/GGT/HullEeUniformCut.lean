import GroupApproximation.GGT.HullEeAdjoinSet

/-!
# Every closed word is an `N`-gon with every edge a side

The isolated-component estimate is indexed by a side count, and returns a radius
depending on it.  Hull's Lemma `ee` applies it once per element of a relative
ball, and those elements are spelled by words of *different* lengths --- so if
each word were made a polygon with its own side count, each would come back with
its own radius, and there would be no single finite set of permitted letters to
enlarge the base by.

The fix is that the side count does not have to be the word's length.  It has to
be a number at least the word's length, and it may be the same number for all of
them.  This module builds the polygon at a **uniform** side count `N`, for every
closed admissible word of length at most `N`.

## Why an over-long side count is legal

`IsQuasiGeodesicPolygon` asks its cut function only to be monotone, to start at
`0`, and to finish at the word's length.  It does **not** ask it to be strictly
increasing.  So `c s = min s |u|` is a legal cut for any `N ≥ |u|`: it walks up
one letter at a time until it reaches the end of the word and then stands still,
and the sides beyond that point are empty.

An empty side is vacuously quasi-geodesic, and so is a single-edge side, which is
the whole reason `b ≥ 1` is the right instantiation: the per-side obligation is
`(j − i)/μ − b ≤ d`, and on a side of length at most one the left-hand side is at
most `1 − b ≤ 0`, while a distance is never negative.  Nothing about the geometry
is used --- the hypothesis is discharged by arithmetic, which is what makes the
uniform side count free.

## What this costs

The radius grows with `N` rather than with the individual word, so the constant
is worse than a per-word one would be.  That is exactly the trade Lemma `ee` can
afford: as recorded in `GGT/HullLemmaEe.lean`, the only thing ever read off the
bound is that the resulting set is *finite*, and a larger finite radius is as
good as a smaller one.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section UniformCut

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A closed admissible word of length at most `N` is an `N`-gon whose sides
are its edges.**

The cut is `c s = min s |u|`: one letter per side until the word runs out, then
empty sides.  The per-side obligation is discharged by arithmetic alone, since
`b ≥ 1` dominates a side of length at most one.

Stated with `b : ℕ` and the cast, which is the shape
`OsinComponents.exists_isolatedComponentBound_nGon` and
`sumBound_of_fourPointHyperbolic` consume. -/
theorem isQuasiGeodesicPolygon_everyEdge (D : RelGenSet G Λ) {N : ℕ} (b : ℕ)
    (hb : 1 ≤ b) (v : G) {u : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ u, D.IsLetter a) (hclosed : RelLetter.listVal u = 1)
    (hlen : u.length ≤ N) :
    IsQuasiGeodesicPolygon D 1 (b : ℝ) N v u := by
  refine ⟨hlet, hclosed, fun s => min s u.length, ?_, ?_, ?_, ?_⟩
  · simp
  · exact min_eq_right hlen
  · intro s
    exact min_le_min (Nat.le_succ s) (le_refl _)
  · intro s _ i j hi hij hj
    -- the cut was supplied as a lambda, so the bounds arrive unreduced; without
    -- this `omega` reads `(fun s => min s u.length) s` and `min s u.length` as
    -- two unrelated atoms and cannot connect the hypotheses
    dsimp only at hi hj
    have hle : j - i ≤ 1 := by omega
    have hji : ((j - i : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hle
    have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have hnn : (0 : ℝ)
        ≤ ((wordDist D.alphabet.carrier (vertex v u i) (vertex v u j) : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    have hone : ((j - i : ℕ) : ℝ) / 1 = ((j - i : ℕ) : ℝ) := by ring
    rw [hone]
    linarith

/-- **The cycle of a short word is such a polygon.**

The word Lemma `ee` starts from has length at most `n`, so its closure has length
at most `n + 1`, and `N = n + 1` serves every element of the ball at once.  This
is the instance the estimate is applied at. -/
theorem isQuasiGeodesicPolygon_cycle (D : RelGenSet G Λ) (b : ℕ) (hb : 1 ≤ b)
    (v : G) {u : List (RelLetter G Λ)} {n : ℕ}
    (hlet : ∀ a ∈ cycleWord u (RelLetter.listVal u)⁻¹, D.IsLetter a)
    (hlen : u.length ≤ n) :
    IsQuasiGeodesicPolygon D 1 (b : ℝ) (n + 1) v
      (cycleWord u (RelLetter.listVal u)⁻¹) := by
  refine isQuasiGeodesicPolygon_everyEdge D b hb v hlet
    (listVal_cycleWord_inv u) ?_
  rw [length_cycleWord]
  omega

end UniformCut

end OsinComponents
end GGT
end GroupApproximation
