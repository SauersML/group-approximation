import GroupApproximation.GGT.GuessingGeodesicsBound

/-!
# Reading the bound on a segment of a geodesic, and the two degenerate ends

Bowditch's bootstrap cuts a geodesic `c` of length `N` at two indices `l₀ ≤ l₁`
and applies the bound at the current scale to the two outer pieces and at a
larger scale to the middle one.  This module is the four lemmas that cut costs:
one that reads `Bnd` on an arbitrary segment, two that turn a segment reading
into an inequality about the distance from the basepoint, and one that handles
the degenerate ends.

## Why the ends are degenerate at all

The cut positions are `l₀ = a - t` and `l₁ = min N (a + t)` with `a` the distance
from the basepoint to the path vertex under consideration.  Truncated
subtraction in `ℕ` *is* Bowditch's `max(0, ·)`, so no clamping has to be written
--- but when the clamp bites, `c l₀` is the basepoint itself and the outer piece
is the path from a point to itself.  There is then no "far from the outer piece"
estimate to contradict, and the argument does not need one: a path from `x` to
`x` has diameter at most `K` by `GuessingData.short`, so anything close to it is
close to `x`, which lies on the geodesic.  `dist_le_of_path_self` is that
observation, and it serves both ends.

Writing the two ends as standalone lemmas keeps the case split out of the body
of the bootstrap, where it would otherwise interleave with the three-way
disjunction and double the proof.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.WordMetric

universe u

variable {G : Type u} [Group G]

/-! ## The degenerate end -/

/-- **A path from a point to itself is within `K` of that point**, so anything
`m`-close to such a path is `(m + K)`-close to the point.

This is what both clamped ends of the cut reduce to: `GuessingData.short` at
`x = y`, whose hypothesis `wordDist S x x ≤ 1` is free. -/
theorem dist_le_of_path_self {S : Set G} (hS : IsSymmetricGeneratingSet S)
    {K : ℕ} {D : GuessingData S K} {w x : G} {j m : ℕ} (hj : j ≤ D.len x x)
    (h : wordDist S w (D.path x x j) ≤ m) :
    wordDist S w x ≤ m + K := by
  have hxx : wordDist S x x ≤ 1 := by
    rw [wordDist_self]
    omega
  have hshort := D.short x x hxx j hj 0 (Nat.zero_le _)
  rw [D.start] at hshort
  have htri := wordDist_triangle hS w (D.path x x j) x
  omega

/-! ## Reading the bound on a segment -/

/-- **A bound at scale `m` applies to any segment of a geodesic chain of index
width at most `m`.**

The segment is the shifted chain `i ↦ c (l₀ + i)`, which
`IsGeodesicChain.shift` and `.mono` make a geodesic chain of the right length,
and whose endpoints are `c l₀` and `c l₁` because the chain realises index
differences as distances. -/
theorem bnd_apply_segment {S : Set G} {K : ℕ} {D : GuessingData S K} {m b : ℕ}
    (hb : Bnd D m b) {c : ℕ → G} {N : ℕ} (hchain : IsGeodesicChain S c N)
    {l₀ l₁ : ℕ} (h01 : l₀ ≤ l₁) (h1N : l₁ ≤ N) (hseg : l₁ - l₀ ≤ m) {j : ℕ}
    (hj : j ≤ D.len (c l₀) (c l₁)) :
    ∃ k : ℕ, l₀ ≤ k ∧ k ≤ l₁ ∧
      wordDist S (D.path (c l₀) (c l₁) j) (c k) ≤ b := by
  have hd : wordDist S (c l₀) (c l₁) = l₁ - l₀ := hchain l₀ l₁ h01 h1N
  have hshift : IsGeodesicChain S (fun i => c (l₀ + i))
      (wordDist S (c l₀) (c l₁)) := by
    rw [hd]
    exact (hchain.shift (le_trans h01 h1N)).mono (by omega)
  have h0 : (fun i => c (l₀ + i)) 0 = c l₀ := by
    show c (l₀ + 0) = c l₀
    rw [Nat.add_zero]
  have hfin : (fun i => c (l₀ + i)) (wordDist S (c l₀) (c l₁)) = c l₁ := by
    show c (l₀ + wordDist S (c l₀) (c l₁)) = c l₁
    rw [hd]
    congr 1
    omega
  obtain ⟨k, hk, hkd⟩ :=
    hb (c l₀) (c l₁) (by omega) (fun i => c (l₀ + i)) h0 hfin hshift j hj
  exact ⟨l₀ + k, by omega, by omega, hkd⟩

/-! ## The two outer estimates -/

/-- **Close to the initial segment means close to the basepoint.**

If `w` is `r`-close to a vertex of the path joining the two ends of `c 0 … c l`,
then `w` is at distance at most `l + r + b` from `c 0`: the vertex is `b`-close
to some `c k` with `k ≤ l`, and `c k` is at distance exactly `k` from `c 0`. -/
theorem wordDist_le_of_near_prefix {S : Set G} (hS : IsSymmetricGeneratingSet S)
    {K : ℕ} {D : GuessingData S K} {m b : ℕ} (hb : Bnd D m b) {c : ℕ → G}
    {N : ℕ} (hchain : IsGeodesicChain S c N) {l : ℕ} (hl : l ≤ N)
    (hlm : l ≤ m) {w : G} {j : ℕ} (hj : j ≤ D.len (c 0) (c l)) {r : ℕ}
    (h : wordDist S w (D.path (c 0) (c l) j) ≤ r) :
    wordDist S (c 0) w ≤ l + r + b := by
  obtain ⟨k, -, hkl, hkd⟩ :=
    bnd_apply_segment hb hchain (Nat.zero_le l) hl (by omega) hj
  have hck : wordDist S (c 0) (c k) = k := by
    have hstep := hchain 0 k (Nat.zero_le k) (le_trans hkl hl)
    omega
  have htri := wordDist_triangle hS (c 0) (c k) w
  have htri' := wordDist_triangle hS (c k) (D.path (c 0) (c l) j) w
  have hcomm := wordDist_comm hS (c k) (D.path (c 0) (c l) j)
  have hcomm' := wordDist_comm hS (D.path (c 0) (c l) j) w
  omega

/-- **Close to the final segment means far from the basepoint.**

The mirror estimate: if `w` is `r`-close to a vertex of the path joining
`c l … c N`, then `l ≤ d(c 0, w) + r + b`, because the vertex is `b`-close to
some `c k` with `l ≤ k`. -/
theorem le_wordDist_of_near_suffix {S : Set G} (hS : IsSymmetricGeneratingSet S)
    {K : ℕ} {D : GuessingData S K} {m b : ℕ} (hb : Bnd D m b) {c : ℕ → G}
    {N : ℕ} (hchain : IsGeodesicChain S c N) {l : ℕ} (hl : l ≤ N)
    (hlm : N - l ≤ m) {w : G} {j : ℕ} (hj : j ≤ D.len (c l) (c N)) {r : ℕ}
    (h : wordDist S w (D.path (c l) (c N) j) ≤ r) :
    l ≤ wordDist S (c 0) w + r + b := by
  obtain ⟨k, hlk, hkN, hkd⟩ :=
    bnd_apply_segment hb hchain hl le_rfl (by omega) hj
  have hck : wordDist S (c 0) (c k) = k := by
    have hstep := hchain 0 k (Nat.zero_le k) hkN
    omega
  have htri := wordDist_triangle hS (c 0) w (c k)
  have htri' := wordDist_triangle hS w (D.path (c l) (c N) j) (c k)
  omega

end OsinEnlargement
end GGT
end GroupApproximation
