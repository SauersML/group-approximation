import GroupApproximation.GGT.HyperbolicTreeAction

/-!
# The tree shift lemma

`GGT/HyperbolicTreeAction.lean` reduces acylindricity of a tree action to two
inputs: trivial pointwise stabilisers of long segments, which a Bass--Serre
construction supplies algebraically, and `HasSegmentShift`, which is geometry.
This module proves the geometry, so `SegmentShiftStatement` stops being a named
hypothesis and `isAcylindrical_treeSpace_of_adj` becomes unconditional.

## The obstruction, and the invariant that replaces a fixed point

An automorphism moving both ends of a long segment only a little need fix
nothing at all: a translation of the line moves every vertex by one, and every
segment stabiliser is trivial.  So the count cannot run on a fixed point.  What
`g` does preserve is its *displacement along the segment*, and the whole content
of this module is that this displacement is an integer read off a single
distance:

```
    Φ g  :=  d(x,y) − d(x, g·y).
```

`|Φ g| ≤ n` is the triangle inequality.  The theorem is that `Φ` determines
`g` on the middle of the segment: `between_smul_of_middle` shows `g·m` is again
between `x` and `y`, at distance `d(x,m) − Φ g` from `x`, and
`between_unique` says a point between `x` and `y` is determined by its distance
to `x`.  So two elements with the same `Φ` agree on the whole middle segment,
and the fibres of `Φ` are cosets of its pointwise stabiliser.

## Everything comes from the tripod

`between_tripod` is the one geometric input, and it is immediate from the sharp
four-point inequality of `GGT/HyperbolicTreeMetric.lean`.  If `m` is between `x`
and `y` then `(x|y)_m = 0`, so for any `z` the four-point condition at basepoint
`m` gives `min ((x|z)_m, (z|y)_m) ≤ 0`; both are nonnegative, so **one of them
vanishes exactly**.  In words: every point of a tree hangs off a geodesic on one
side of any of its points, never on both.  `δ = 0` rather than `δ = 1` is what
makes this an exact alternative instead of an estimate, which is why removing
the rounding slack in `graphDist_fourPoint_zero` was worth doing.

Each of the three steps below is that alternative applied once, with the
excluded branch ruled out by a collar condition:

* `between_unique` --- the branch `z` on the far side forces `d(m,m') = 0`.
* `between_smul_of_middle` --- the branch through `g·x` would force
  `d(x,m) ≤ n`, and the branch through `g·y` would force `d(m,y) ≤ n`; both are
  excluded for `m` strictly inside the `n`-collars.
* `exists_middle_pair` --- the two ends of the middle segment, produced at
  depths `n+1` and `d(x,y) − (n+1)` on the geodesic.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.TreeGraphGeometry

universe u v

/-! ## Distance zero -/

/-- In a tree, vanishing distance is equality.  The geodesic has length zero, so
both of its endpoints are indexed vertices at an index bounded by zero, hence at
the same index. -/
theorem eq_of_dist_eq_zero {V : Type v} {H : SimpleGraph V} (hH : H.IsTree)
    {p q : V} (h : H.dist p q = 0) : p = q := by
  have hlen : (geodesic H hH p q).length = 0 := by
    rw [geodesic_length]
    exact h
  obtain ⟨i, hi, hile⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
      (geodesic H hH p q).end_mem_support
  obtain ⟨j, hj, hjle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
      (geodesic H hH p q).start_mem_support
  have hij : i = j := by omega
  rw [hij] at hi
  exact hj.symm.trans hi

/-! ## The tripod alternative -/

/-- **The tripod alternative.**  If `m` lies between `x` and `y`, then every
vertex `z` lies on one of the two sides: either `m` is between `x` and `z`, or
`m` is between `z` and `y`.

This is the sharp four-point inequality applied at basepoint `m`: betweenness
makes `(x|y)_m = 0`, so `min ((x|z)_m, (z|y)_m) ≤ 0`, and Gromov products are
nonnegative, so one of the two is exactly zero. -/
theorem between_tripod {V : Type v} {H : SimpleGraph V} (hH : H.IsTree)
    {x y m : V} (hm : H.dist x m + H.dist m y = H.dist x y) (z : V) :
    H.dist x m + H.dist m z = H.dist x z ∨
      H.dist z m + H.dist m y = H.dist z y := by
  have key := graphDist_fourPoint_zero H hH m x z y
  have c1 : H.dist y m = H.dist m y := SimpleGraph.dist_comm
  have c2 : H.dist z m = H.dist m z := SimpleGraph.dist_comm
  have t1 := hH.connected.dist_triangle (u := x) (v := m) (w := z)
  have t2 := hH.connected.dist_triangle (u := z) (v := m) (w := y)
  omega

/-- **A point between two others is determined by its distance to one of
them.**  Both branches of the tripod alternative force the two candidates to be
at distance zero. -/
theorem between_unique {V : Type v} {H : SimpleGraph V} (hH : H.IsTree)
    {x y m m' : V} (hm : H.dist x m + H.dist m y = H.dist x y)
    (hm' : H.dist x m' + H.dist m' y = H.dist x y)
    (heq : H.dist x m = H.dist x m') : m = m' := by
  refine eq_of_dist_eq_zero hH ?_
  have c : H.dist m' m = H.dist m m' := SimpleGraph.dist_comm
  rcases between_tripod hH hm m' with h | h
  · omega
  · omega

/-! ## The image of a middle vertex is again a middle vertex -/

/-- **The shift.**  Let `g` move `x` and `y` by at most `n`, and let `m` lie
between them, strictly outside both `n`-collars.  Then `g · m` again lies
between `x` and `y`, and its distance to `x` is `d(x,m)` corrected by the single
number `d(x, g·y) - d(x,y)`.

Two applications of the tripod alternative.  First at `g·m`, which lies between
`g·x` and `g·y`, against `z = x`: the branch through `g·x` would give
`d(g·x, g·m) + d(g·m, x) = d(g·x, x) ≤ n`, and the left summand is `d(x,m) > n`.
So `g·m` lies between `x` and `g·y`.  Then at `g·m` again against `z = y`: the
branch through `g·y` would give `d(y, g·m) + d(g·m, g·y) = d(y, g·y) ≤ n`, and
the second summand is `d(m,y) > n`.  So `g·m` lies between `x` and `y`. -/
theorem between_smul_of_middle {G : Type u} [Group G] {V : Type v}
    {H : SimpleGraph V} [MulAction G V] (hH : H.IsTree)
    (hiso : ∀ (a : G) (p q : V), H.dist (a • p) (a • q) = H.dist p q) (g : G)
    {x y m : V} {n : ℕ} (hgx : H.dist x (g • x) ≤ n)
    (hgy : H.dist y (g • y) ≤ n)
    (hm : H.dist x m + H.dist m y = H.dist x y) (hi1 : n < H.dist x m)
    (hi2 : n < H.dist m y) :
    H.dist x (g • m) + H.dist (g • m) y = H.dist x y ∧
      H.dist x (g • m) + H.dist m y = H.dist x (g • y) := by
  have e1 : H.dist (g • x) (g • m) = H.dist x m := hiso g x m
  have e2 : H.dist (g • m) (g • y) = H.dist m y := hiso g m y
  have e3 : H.dist (g • x) (g • y) = H.dist x y := hiso g x y
  have hb : H.dist (g • x) (g • m) + H.dist (g • m) (g • y)
      = H.dist (g • x) (g • y) := by
    rw [e1, e2, e3]
    exact hm
  have step1 : H.dist x (g • m) + H.dist (g • m) (g • y)
      = H.dist x (g • y) := by
    rcases between_tripod hH hb x with h | h
    · exfalso
      have c : H.dist (g • x) x = H.dist x (g • x) := SimpleGraph.dist_comm
      omega
    · exact h
  refine ⟨?_, ?_⟩
  · rcases between_tripod hH step1 y with h | h
    · exact h
    · exfalso
      omega
  · rw [← e2]
    exact step1

/-- **Two elements with the same shift agree on a middle vertex.**  Both images
lie between `x` and `y` at the same distance from `x`, so `between_unique`
identifies them. -/
theorem smul_eq_smul_of_dist_eq {G : Type u} [Group G] {V : Type v}
    {H : SimpleGraph V} [MulAction G V] (hH : H.IsTree)
    (hiso : ∀ (a : G) (p q : V), H.dist (a • p) (a • q) = H.dist p q) (g h : G)
    {x y m : V} {n : ℕ} (hgx : H.dist x (g • x) ≤ n)
    (hgy : H.dist y (g • y) ≤ n) (hhx : H.dist x (h • x) ≤ n)
    (hhy : H.dist y (h • y) ≤ n)
    (hm : H.dist x m + H.dist m y = H.dist x y) (hi1 : n < H.dist x m)
    (hi2 : n < H.dist m y)
    (heq : H.dist x (g • y) = H.dist x (h • y)) : g • m = h • m := by
  obtain ⟨hg1, hg2⟩ :=
    between_smul_of_middle hH hiso g hgx hgy hm hi1 hi2
  obtain ⟨hh1, hh2⟩ :=
    between_smul_of_middle hH hiso h hhx hhy hm hi1 hi2
  have hd : H.dist x (g • m) = H.dist x (h • m) := by omega
  exact between_unique hH hg1 hh1 hd

/-! ## The middle of a long segment -/

/-- **The two ends of the middle segment.**  At depths `n+1` and
`d(x,y) - (n+1)` along the geodesic they lie strictly inside both `n`-collars,
and they are at distance at least `L` apart.

The distance between them is the tripod alternative once more: the branch that
puts the deeper vertex between `x` and the shallower one would force
`d(x,y) ≤ 2n + 2`, which the hypothesis excludes unless `L = 0`, and then there
is nothing to prove. -/
theorem exists_middle_pair {V : Type v} {H : SimpleGraph V} (hH : H.IsTree)
    (L n : ℕ) (x y : V) (hxy : L + 2 * n + 2 ≤ H.dist x y) :
    ∃ u w : V, L ≤ H.dist u w ∧
      (H.dist x u + H.dist u y = H.dist x y ∧ n < H.dist x u ∧
        n < H.dist u y) ∧
      (H.dist x w + H.dist w y = H.dist x y ∧ n < H.dist x w ∧
        n < H.dist w y) := by
  have hu1 : H.dist x ((geodesic H hH x y).getVert (n + 1)) = n + 1 :=
    dist_getVert_geodesic H hH (by omega)
  have hw1 : H.dist x ((geodesic H hH x y).getVert (H.dist x y - (n + 1)))
      = H.dist x y - (n + 1) := dist_getVert_geodesic H hH (by omega)
  have hu2 : H.dist x ((geodesic H hH x y).getVert (n + 1))
      + H.dist ((geodesic H hH x y).getVert (n + 1)) y = H.dist x y :=
    dist_add_dist_eq_of_mem_geodesic H hH
      (SimpleGraph.Walk.getVert_mem_support _ _)
  have hw2 : H.dist x ((geodesic H hH x y).getVert (H.dist x y - (n + 1)))
      + H.dist ((geodesic H hH x y).getVert (H.dist x y - (n + 1))) y
      = H.dist x y :=
    dist_add_dist_eq_of_mem_geodesic H hH
      (SimpleGraph.Walk.getVert_mem_support _ _)
  refine ⟨(geodesic H hH x y).getVert (n + 1),
    (geodesic H hH x y).getVert (H.dist x y - (n + 1)), ?_,
    ⟨hu2, by omega, by omega⟩, ⟨hw2, by omega, by omega⟩⟩
  rcases between_tripod hH hu2
    ((geodesic H hH x y).getVert (H.dist x y - (n + 1))) with h | h
  · omega
  · omega

/-! ## The shift lemma -/

/-- **The tree shift lemma.**  An action on a tree by graph automorphisms has
bounded shifts along every long segment, with the invariant
`Φ g = d(x,y) - d(x, g·y)`.

This discharges `HasSegmentShift`, which `GGT/HyperbolicTreeAction.lean`
introduced as a hypothesis. -/
theorem hasSegmentShift_of_adj {G : Type u} [Group G] {V : Type v}
    {H : SimpleGraph V} [MulAction G V] (hH : H.IsTree)
    (hadj : ∀ (g : G) (p q : V), H.Adj p q → H.Adj (g • p) (g • q)) (L : ℕ) :
    HasSegmentShift G H L := by
  have hiso := dist_smul_eq hH hadj
  intro n x y hxy
  obtain ⟨u, w, hL, ⟨hu2, hu3, hu4⟩, ⟨hw2, hw3, hw4⟩⟩ :=
    exists_middle_pair hH L n x y hxy
  refine ⟨u, w, fun g => (H.dist x y : ℤ) - (H.dist x (g • y) : ℤ), hL, ?_⟩
  intro g hgx hgy
  refine ⟨?_, ?_⟩
  · show ((H.dist x y : ℤ) - (H.dist x (g • y) : ℤ)).natAbs ≤ n
    have t1 := hH.connected.dist_triangle (u := x) (v := y) (w := g • y)
    have t2 := hH.connected.dist_triangle (u := x) (v := g • y) (w := y)
    have c : H.dist (g • y) y = H.dist y (g • y) := SimpleGraph.dist_comm
    omega
  · intro h hhx hhy hΦ
    have hΦ' : (H.dist x y : ℤ) - (H.dist x (g • y) : ℤ)
        = (H.dist x y : ℤ) - (H.dist x (h • y) : ℤ) := hΦ
    have heq : H.dist x (g • y) = H.dist x (h • y) := by omega
    exact ⟨smul_eq_smul_of_dist_eq hH hiso g h hgx hgy hhx hhy hu2 hu3 hu4 heq,
      smul_eq_smul_of_dist_eq hH hiso g h hgx hgy hhx hhy hw2 hw3 hw4 heq⟩

/-- **`SegmentShiftStatement` is a theorem.**  The named `Prop` of
`GGT/HyperbolicTreeAction.lean` is discharged, so nothing downstream has to
carry it as a hypothesis. -/
theorem segmentShiftStatement : SegmentShiftStatement := by
  intro G _hG V H _hact L hH hadj
  exact hasSegmentShift_of_adj hH hadj L

/-- **An action on a tree by graph automorphisms with trivial pointwise
stabilisers of long segments is acylindrical.**  Unconditional: this is
`isAcylindrical_treeSpace` with its geometric hypothesis discharged by
`hasSegmentShift_of_adj`.

This is the form a Bass--Serre construction consumes --- it asks only for the
graph, the tree hypothesis, an action by automorphisms, and an algebraic
statement about segment stabilisers. -/
theorem isAcylindrical_treeSpace_of_adj {G : Type u} [Group G] {V : Type v}
    {H : SimpleGraph V} [MulAction G V] (hH : H.IsTree) {L : ℕ}
    (hadj : ∀ (g : G) (p q : V), H.Adj p q → H.Adj (g • p) (g • q))
    (hstab : TrivialSegmentStabilizers G H L) :
    IsAcylindrical G (TreeSpace hH) :=
  isAcylindrical_treeSpace hH (hasSegmentShift_of_adj hH hadj L) hstab

end GGT
end GroupApproximation
