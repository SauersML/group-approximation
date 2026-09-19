import GroupApproximation.GGT.GuessingGeodesicsSegment

/-!
# Bowditch's bootstrap: the bound feeds back into itself

The subdivision bound grows with the scale.  Bowditch removes the growth by an
argument that does not improve the bound directly but relates it to *itself at a
larger scale*, after which one instantiation of a growth comparison collapses
the whole family to a constant.  This module is that relation:

    Bnd D n b  →  Bnd D (2b + 4K + 2) b'  →  Bnd D n (3K + b')

Read as a recursion on `pathBound`, it says that the least bound at scale `n` is
within `3K` of the least bound at scale `2 · pathBound n + 4K + 2`, which is the
self-application the closure of `GGT/GuessingGeodesicsGrowth.lean` is aimed at.

## The cut

Let `w` be a vertex of the path from `x` to `y`, let `a` be its distance from
`x`, and let `t = b + 2K + 1`.  Cut the geodesic at `l₀ = a - t` and at
`l₁ = min N (a + t)`, writing `x' = c l₀` and `y' = c l₁`.  Two applications of
`GuessingData.thin` --- first at `x'`, then at `y'` on the surviving branch ---
put `w` within `K` of the path to `x'`, or within `2K` of the path from `x'` to
`y'`, or within `2K` of the path from `y'` to `y`.

The middle case is the conclusion: `x'` and `y'` are at most `2t` apart, which is
the enlarged scale, so the path between them is `b'`-close to the geodesic
segment it spans.

The two outer cases are excluded --- or, where the cut clamps, conclude
directly.  Excluded because a point of the path to `x'` is `b`-close to the
geodesic before `l₀`, hence at least `t` from `w`, and `t` exceeds `K + b`; the
mirror at the far end exceeds `2K + b`, which is why `t` carries `2K` and not
`K`.  Where the clamp bites --- `a < t` at the near end, `N < a + t` at the far
one --- there is nothing to exclude, and `dist_le_of_path_self` reads off
`d(w, x) ≤ 2K` or `d(w, y) ≤ 3K` instead.  That is the whole reason the constant
is `3K + b'` rather than `2K + b'`.

## Why `a` is bounded at all

The cut indexes the geodesic at `a - t`, which is only meaningful if `a ≤ N + t`,
and the path carries no such bound: it may wander arbitrarily far from `x`.  What
bounds it is the hypothesis already in hand — `Bnd D n b` applied to `w` itself
puts `w` within `b` of some geodesic vertex, so `a ≤ N + b`.  That is the first
step of the proof, before any cut is named.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.WordMetric

universe u

variable {G : Type u} [Group G]

/-- **Bowditch's bootstrap step.**

A bound at scale `n`, together with a bound at the enlarged scale
`2b + 4K + 2`, gives a better-shaped bound at scale `n`.  See the module header
for the cut and the three cases. -/
theorem bnd_bootstrap {S : Set G} (hS : IsSymmetricGeneratingSet S) {K : ℕ}
    {D : GuessingData S K} {n b b' : ℕ} (hb : Bnd D n b)
    (hb' : Bnd D (2 * b + 4 * K + 2) b') :
    Bnd D n (3 * K + b') := by
  intro x y hxy c hc0 hcN hchain i hi
  -- name the length, then read everything in the chain's coordinates
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = wordDist S x y := ⟨_, rfl⟩
  rw [← hN] at hxy hcN hchain ⊢
  subst hc0
  subst hcN
  -- the path vertex is within `N + b` of the basepoint
  have hself : wordDist S (D.path (c 0) (c N) i) (D.path (c 0) (c N) i) ≤ 0 := by
    have h := wordDist_self S (D.path (c 0) (c N) i)
    omega
  have hbase := wordDist_le_of_near_prefix hS hb hchain (le_refl N) hxy hi hself
  -- the cut
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = b + 2 * K + 1 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = wordDist S (c 0) (D.path (c 0) (c N) i) :=
    ⟨_, rfl⟩
  obtain ⟨l₀, hl₀⟩ : ∃ l : ℕ, l = a - t := ⟨_, rfl⟩
  obtain ⟨l₁, hl₁⟩ : ∃ l : ℕ, l = min N (a + t) := ⟨_, rfl⟩
  have hl₀N : l₀ ≤ N := by omega
  have hl₁N : l₁ ≤ N := by omega
  have hl01 : l₀ ≤ l₁ := by omega
  -- the first application of `thin`, at `c l₀`
  obtain ⟨j, hj⟩ := D.thin (c 0) (c N) (c l₀) i hi
  rcases hj with ⟨hjle, hjd⟩ | ⟨hjle, hjd⟩
  · -- near the path to `x'`
    rcases Nat.lt_or_ge a t with hlt | hge
    · -- the cut clamps: `x' = x`, and the path to it has diameter `K`
      have hz : l₀ = 0 := by omega
      rw [hz] at hjle hjd
      have hnear := dist_le_of_path_self hS hjle hjd
      exact ⟨0, Nat.zero_le N, by omega⟩
    · -- excluded: `w` is at least `t` from the geodesic before `l₀`
      exfalso
      have hpre :=
        wordDist_le_of_near_prefix hS hb hchain hl₀N (by omega) hjle hjd
      omega
  · -- the second application of `thin`, at `c l₁`
    obtain ⟨j', hj'⟩ := D.thin (c l₀) (c N) (c l₁) j hjle
    have hstep : ∀ z : G, wordDist S (D.path (c l₀) (c N) j) z ≤ K →
        wordDist S (D.path (c 0) (c N) i) z ≤ 2 * K := by
      intro z hz
      have htri := wordDist_triangle hS (D.path (c 0) (c N) i)
        (D.path (c l₀) (c N) j) z
      omega
    rcases hj' with ⟨hj'le, hj'd⟩ | ⟨hj'le, hj'd⟩
    · -- the conclusion: the middle segment spans at most the enlarged scale
      obtain ⟨k, hk₀, hk₁, hkd⟩ :=
        bnd_apply_segment hb' hchain hl01 hl₁N (by omega) hj'le
      refine ⟨k, by omega, ?_⟩
      have h2K := hstep (D.path (c l₀) (c l₁) j') hj'd
      have htri := wordDist_triangle hS (D.path (c 0) (c N) i)
        (D.path (c l₀) (c l₁) j') (c k)
      omega
    · -- near the path from `y'`
      have h2K := hstep (D.path (c l₁) (c N) j') hj'd
      rcases Nat.lt_or_ge N (a + t) with hlt | hge
      · -- the cut clamps at the far end: `y' = y`
        have hz : l₁ = N := by omega
        rw [hz] at hj'le h2K
        have hfar := dist_le_of_path_self hS hj'le h2K
        exact ⟨N, le_refl N, by omega⟩
      · -- excluded: `w` is at least `t` from the geodesic after `l₁`
        exfalso
        have hsuf :=
          le_wordDist_of_near_suffix hS hb hchain hl₁N (by omega) hj'le h2K
        omega

/-- **The bootstrap, on the bound function.**

`pathBound` at a scale is within `3K` of `pathBound` at the scale its own value
determines.  This is the self-application the closure argument instantiates. -/
theorem pathBound_le_bootstrap {S : Set G} (hS : IsSymmetricGeneratingSet S)
    {K : ℕ} (D : GuessingData S K) (n : ℕ) :
    pathBound D n ≤ 3 * K + pathBound D (2 * pathBound D n + 4 * K + 2) :=
  pathBound_le
    (bnd_bootstrap hS (bnd_pathBound hS D n) (bnd_pathBound hS D _))

end OsinEnlargement
end GGT
end GroupApproximation
