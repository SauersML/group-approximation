import GroupApproximation.GGT.GeodesicChainExists

/-!
# The subdivision half of Bowditch's criterion

`GGT/OsinLemma55GuessingGeodesics.lean` declares `GuessingGeodesics` --- a
family of paths, one for each pair of points, with two coarse conditions, forces
the four-point condition --- and derives Osin's Lemma 5.5 from it.  This module
begins the proof of the criterion itself.

`GuessingData` bundles the five clauses of that `Prop`, and
`exists_chain_index_close` proves the first half of the argument: every vertex of
the path joining two points of a geodesic chain is close to a vertex of the
chain, at a constant growing with the *number of halvings* the interval allows.

## No logarithm

The informal statement is "triangles are thin at scale `K log(perimeter)`", and
the temptation is to write `Nat.log2` into it.  Nothing is gained: the induction
consumes `b - a ≤ 2 ^ t` and produces `(t + 1) * K`, and every consumer knows a
`t` for its own perimeter.  Carrying the exponent as a parameter keeps the
statement free of a logarithm it would only have to rewrite away.

The arithmetic gotcha is that `omega` does not know powers.  The halving step
needs `2 ^ (t + 1) = 2 ^ t * 2` supplied first, after which `2 ^ t` is an atom
and `omega` handles the midpoint bounds.

## Why the connectivity clause exists

`GuessingData.step` --- consecutive vertices at distance at most one --- is used
**nowhere in this module**, and that is worth stating rather than hiding, since a
clause that is never used invites deletion.  Deleting it makes the criterion
FALSE.

Take `G = ℤ²` with the standard generators, `len x y = 1`, `path x y 0 = x` and
`path x y 1 = y`.  Then `short` holds at `K = 1`, and `thin` holds at `K = 0`:
for `i ≤ 1` the vertex is `x` or `y`, and `x = path x z 0` while
`y = path z y 1`.  But `ℤ²` satisfies no four-point condition at any constant.
Only `step` fails, `d(path x y 0, path x y 1) = d(x,y)` being unbounded.

So the criterion's content is exactly what `step` adds, and the two halves of
its proof divide along that line: subdivision and the final assembly run on
`short` and `thin` alone, and connectivity is spent in the step between them ---
the one that removes the dependence on `t`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.WordMetric

universe u

variable {G : Type u} [Group G]

/-! ## The data -/

/-- **The hypotheses of Bowditch's criterion, bundled.**

A path for each ordered pair, from the first point to the second, with
consecutive vertices one step apart, of bounded diameter when its endpoints are
adjacent, and with the triangle condition.  These are the five clauses of
`GuessingGeodesics` in `GGT/OsinLemma55GuessingGeodesics.lean`, in the same
order; that `Prop` is not restated here, so that nothing downstream of it
moves. -/
structure GuessingData (S : Set G) (K : ℕ) where
  /-- The length of the path from `x` to `y`. -/
  len : G → G → ℕ
  /-- Its vertices. -/
  path : G → G → ℕ → G
  /-- It starts at `x`. -/
  start : ∀ x y : G, path x y 0 = x
  /-- It ends at `y`. -/
  finish : ∀ x y : G, path x y (len x y) = y
  /-- **Connectivity.**  Used only in the step that removes the dependence on
  the number of halvings; see the module header for the `ℤ²` configuration that
  satisfies everything else and is not hyperbolic. -/
  step : ∀ (x y : G) (i : ℕ), i < len x y →
    wordDist S (path x y i) (path x y (i + 1)) ≤ 1
  /-- The path of an adjacent pair has diameter at most `K`. -/
  short : ∀ x y : G, wordDist S x y ≤ 1 → ∀ i ≤ len x y, ∀ j ≤ len x y,
    wordDist S (path x y i) (path x y j) ≤ K
  /-- Every vertex of `path x y` is `K`-close to a vertex of `path x z` or of
  `path z y`. -/
  thin : ∀ x y z : G, ∀ i ≤ len x y, ∃ j : ℕ,
    (j ≤ len x z ∧ wordDist S (path x y i) (path x z j) ≤ K) ∨
    (j ≤ len z y ∧ wordDist S (path x y i) (path z y j) ≤ K)

/-! ## The subdivision bound -/

/-- **Dyadic subdivision.**  If two vertices of a geodesic chain are at most
`2 ^ t` indices apart, every vertex of the path joining them is within
`(t + 1) * K` of a chain vertex lying between them.

Induction on `t`.  At `t = 0` the two chain vertices are adjacent, so `short`
applies and the chain vertex is the path's own starting point.  At `t + 1` the
midpoint splits the index interval into two of size at most `2 ^ t`; `thin`
moves the vertex within `K` of a vertex of one of the two halves' paths, and the
inductive hypothesis moves that one within `(t + 1) * K` of a chain vertex in
the corresponding index range.  The constant is exact: `K` per halving, plus `K`
for the base.

`GuessingData.step` is not used. -/
theorem exists_chain_index_close {S : Set G} (hS : IsSymmetricGeneratingSet S)
    {K : ℕ} (D : GuessingData S K) {c : ℕ → G} {n : ℕ}
    (hc : IsGeodesicChain S c n) :
    ∀ t a b : ℕ, a ≤ b → b ≤ n → b - a ≤ 2 ^ t →
      ∀ i ≤ D.len (c a) (c b), ∃ k : ℕ, a ≤ k ∧ k ≤ b ∧
        wordDist S (D.path (c a) (c b) i) (c k) ≤ (t + 1) * K := by
  intro t
  induction t with
  | zero =>
      intro a b hab hbn hdiff i hi
      rw [pow_zero] at hdiff
      refine ⟨a, le_rfl, hab, ?_⟩
      have hd : wordDist S (c a) (c b) ≤ 1 := by
        rw [hc a b hab hbn]
        omega
      have h := D.short (c a) (c b) hd i hi 0 (Nat.zero_le _)
      rw [D.start] at h
      calc wordDist S (D.path (c a) (c b) i) (c a) ≤ K := h
        _ = (0 + 1) * K := by ring
  | succ t ih =>
      intro a b hab hbn hdiff i hi
      have hpow : 2 ^ (t + 1) = 2 ^ t * 2 := pow_succ 2 t
      obtain ⟨m, ham, hmb, hma, hbm⟩ :
          ∃ m : ℕ, a ≤ m ∧ m ≤ b ∧ m - a ≤ 2 ^ t ∧ b - m ≤ 2 ^ t :=
        ⟨(a + b) / 2, by omega, by omega, by omega, by omega⟩
      obtain ⟨j, ⟨hjle, hjd⟩ | ⟨hjle, hjd⟩⟩ :=
        D.thin (c a) (c b) (c m) i hi
      · obtain ⟨k, hka, hkm, hkd⟩ :=
          ih a m ham (le_trans hmb hbn) hma j hjle
        refine ⟨k, hka, le_trans hkm hmb, ?_⟩
        calc wordDist S (D.path (c a) (c b) i) (c k)
            ≤ wordDist S (D.path (c a) (c b) i) (D.path (c a) (c m) j)
              + wordDist S (D.path (c a) (c m) j) (c k) :=
              wordDist_triangle hS _ _ _
          _ ≤ K + (t + 1) * K := Nat.add_le_add hjd hkd
          _ = (t + 1 + 1) * K := by ring
      · obtain ⟨k, hkm, hkb, hkd⟩ := ih m b hmb hbn hbm j hjle
        refine ⟨k, le_trans ham hkm, hkb, ?_⟩
        calc wordDist S (D.path (c a) (c b) i) (c k)
            ≤ wordDist S (D.path (c a) (c b) i) (D.path (c m) (c b) j)
              + wordDist S (D.path (c m) (c b) j) (c k) :=
              wordDist_triangle hS _ _ _
          _ ≤ K + (t + 1) * K := Nat.add_le_add hjd hkd
          _ = (t + 1 + 1) * K := by ring

/-! ## What it says about an arbitrary pair -/

/-- **Every vertex of a path is close to a point between its endpoints**, at a
constant growing with the number of halvings.

This is the subdivision bound read at the two endpoints of a chain supplied by
`exists_isGeodesicChain`, with `IsGeodesicChain.isBetween` turning the chain
vertex into a between-point.  It is one of the two Hausdorff directions the
criterion needs; the other --- every between-point close to the path --- is the
one that needs `GuessingData.step`, and is not proved here.

Removing the `t` is the remaining work.  As it stands the constant is uniform on
each ball, which is not enough for hyperbolicity. -/
theorem exists_isBetween_close {S : Set G} (hS : IsSymmetricGeneratingSet S)
    {K : ℕ} (D : GuessingData S K) {x y : G} {t : ℕ}
    (ht : wordDist S x y ≤ 2 ^ t) (i : ℕ) (hi : i ≤ D.len x y) :
    ∃ q : G, Hyperbolic.IsBetween S x q y ∧
      wordDist S (D.path x y i) q ≤ (t + 1) * K := by
  obtain ⟨c, hc0, hcn, hchain⟩ := exists_isGeodesicChain hS x y
  have hi' : i ≤ D.len (c 0) (c (wordDist S x y)) := by
    rw [hc0, hcn]
    exact hi
  obtain ⟨k, -, hkn, hkd⟩ := exists_chain_index_close hS D hchain t 0
    (wordDist S x y) (Nat.zero_le _) le_rfl (by simpa using ht) i hi'
  have hbet := hchain.isBetween hkn
  rw [hc0, hcn] at hbet hkd
  exact ⟨c k, hbet, hkd⟩

end OsinEnlargement
end GGT
end GroupApproximation
