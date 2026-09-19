---
rg: 2
id: cat0-cube-complexes-with-property-a-are-finite-dimensional-proof
kind: route
title: Hyperplane coordinates make every cube an isometric Hamming cube with a 1-Lipschitz gate map, and Nowak's cubes then need unbounded support radius
target: cat0-cube-complexes-with-property-a-are-finite-dimensional
requires: [nowak-hamming-cubes-have-property-a-arbitrarily-badly]
---

**Cited cube-complex facts.** Verbatim from Niblo–Reeves, *Groups acting on CAT(0) cube complexes*,
arXiv:math/9702231 (Geom. Topol. 1 (1997) 1–7), p. 5, fetched and read on 2026-09-18. None of these facts uses
finite dimension or local finiteness.

- (H1) "any hyperplane in a CAT(0) cube complex separates it into two components referred to as the half spaces
  associated with the hyperplane."
- (H2) "Sageev, [8], observed that the shortest path in the 1–skeleton crosses any hyperplane at most once, and
  since every edge crosses exactly one hyperplane, the distance between two vertices is the number of
  hyperplanes separating them."

Here a hyperplane is the union of midcubes through the midpoint of an edge. The edges it crosses are its *dual*
edges. In a cube, parallel edges are dual to the same hyperplane, since the midcube through one of them meets
all the parallel ones.

**Step 0 (endpoints of an edge).** Let `e = uv` be an edge dual to `H`. A hyperplane `K ≠ H` does not meet `e`,
by (H2) ("every edge crosses exactly one hyperplane"). So `e` is a path in `X ∖ K` and `u, v` lie on the same
side of `K`. By (H2), `d(u,v) = 1` counts exactly one separating hyperplane, so `H` separates `u` from `v`.

**Step 1 (coordinates on a cube).** Let `C` be an `n`-cube with cube coordinates `C⁽⁰⁾ ≅ {0,1}^n`. Let `H_i` be
the hyperplane dual to the edges of `C` in direction `i`.

- *The `H_i` are distinct.* Suppose `H_i = H_j` with `i ≠ j`. Let `v, v'` be opposite corners of a square of `C`
  in directions `i, j`. The path `v → v + e_i → v'` crosses only `H_i`, and crosses it twice. So by Step 0 no
  hyperplane separates `v` from `v'`, and (H2) gives `d(v,v') = 0`. That is a contradiction.
- *Sides are coordinates.* By Step 0, moving along a direction-`j` edge of `C` switches the side of `H_j` and
  keeps the side of every other hyperplane.
  - So the side of `H_i` of a vertex `w ∈ C⁽⁰⁾` is its `i`-th coordinate, up to a fixed relabelling.
  - All vertices of `C` lie on the same side of every hyperplane other than `H_1, …, H_n`.
- *Isometric.* Let `w, w' ∈ C⁽⁰⁾`. The hyperplanes separating them are exactly the `H_i` with `w_i ≠ w'_i`, so
  (H2) gives `d_X(w,w') = |{i : w_i ≠ w'_i}|`. Hence `C⁽⁰⁾` with the metric of `X⁽⁰⁾` is the Hamming cube
  `Q_n`.

**Step 2 (gate retraction).** For `y ∈ X⁽⁰⁾`, let `π(y) ∈ C⁽⁰⁾` be the vertex whose `i`-th coordinate is the
side of `H_i` containing `y` (H1). By Step 1 this vertex exists, is unique, and `π(w) = w` for `w ∈ C⁽⁰⁾`.

Let `y, y'` be adjacent, with dual hyperplane `K`. By Step 0 they lie on the same side of every hyperplane
except `K`. So `π(y), π(y')` differ in at most one coordinate (the `i` with `H_i = K`, if any), and
`d(π y, π y') ≤ 1`. Applying this along a geodesic edge path gives `d(π y, π y') ≤ d(y, y')` for all `y, y'`.

**Step 3 (pushing a witness onto a cube).** Suppose `X⁽⁰⁾` has property A. Fix `0 < ε < 2`. By item 2 of
`nowak-hamming-cubes-have-property-a-arbitrarily-badly`, there are `S = diam^A_{X⁽⁰⁾}(1,ε) < ∞` and a
nonnegative `ξ : X⁽⁰⁾ → ℓ^1(X⁽⁰⁾)` with the following properties:

- `‖ξ_x‖_1 = 1`;
- `‖ξ_x − ξ_y‖_1 < ε` whenever `d(x,y) ≤ 1`;
- `supp ξ_x ⊆ B̄(x,S)`.

`X` may be locally infinite, so `ξ_x` may have infinite support; it is still an `ℓ^1` function. For
`w ∈ Q = C⁽⁰⁾`, set `η_w(q) = Σ_{π(y) = q} ξ_w(y)`, for `q ∈ Q`. This is an absolutely convergent sum of
nonnegative terms. Then:

- `‖η_w‖_1 = ‖ξ_w‖_1 = 1`, since the terms are nonnegative.
- `‖η_w − η_{w'}‖_1 ≤ ‖ξ_w − ξ_{w'}‖_1 < ε` when `d(w,w') ≤ 1`, since pushforward is an `ℓ^1`-contraction.
- `supp η_w ⊆ π(B̄(w,S)) ⊆ B̄(π w, S) = B̄(w,S) ∩ Q`, since `π` is 1-Lipschitz and fixes `w` (Step 2).

The metric on `Q` is the Hamming metric (Step 1), so `diam^A_{Q_n}(1,ε) ≤ S`.

**Step 4 (conclusion).** Item 1 of `nowak-hamming-cubes-have-property-a-arbitrarily-badly` says
`diam^A_{Q_n}(1,ε) → ∞` (a lim inf). So there is `N` with `diam^A_{Q_n}(1,ε) > S` for all `n ≥ N`, and `X`
has no `n`-cube for any `n ≥ N`. The dimension of `X` is the supremum of its cube dimensions, so it is less
than `N`. ∎

**Remarks.**

- Step 3 is the only place property A is used, and it uses only the `ℓ^1`-witness form, which holds without
  bounded geometry.
- The argument is Nowak's disjoint-union argument, with the 1-Lipschitz gate retractions standing in for the
  separation of the components.
- Any metric space `Y` with 1-Lipschitz retractions onto isometric `Q_n` for infinitely many `n` fails
  property A, by the same Steps 3 and 4.
