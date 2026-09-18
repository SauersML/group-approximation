---
rg: 2
id: surface-group-atoms-wall-cells-proof
kind: route
title: Counting separating walls turns distance profiles on B_n into side vectors for the walls in 𝒲_n; small walls near every ideal point give branching, and every wall of the arrangement is crossed by another wall of it at the corner of its nearest tile
target: surface-group-atoms-are-wall-arrangement-cells
requires:
  - hyperbolic-groups-embed-in-contracting-rsgs
  - sft-irreducible-core-iff-unique-recurrent-component
---

Lane `bh-free-23`, 2026-09-18. Lane proof, elementary hyperbolic geometry. BBMZ labels as in
arXiv:2309.06224v3.

**1. Walls and distance.**
- **Straight walls.** All angles of `P` are equal and `4g` tiles meet at each vertex, so the `4g`
  edges at a vertex are equally spaced, and opposite edges are collinear. Hence each edge lies on
  a complete geodesic made of edges.
- **Fundamental domain.** By Poincaré's polygon theorem, `P` with the standard side pairing is a
  fundamental domain (angle sum `2π`). So tiles correspond to `G`, and adjacent tiles differ by a
  side pairing: the dual graph is `Cay(G,S)`.
- **Upper bound on distance.** Join generic interior points of tiles `x` and `y` by a hyperbolic
  segment that avoids all vertices. It crosses exactly the walls separating `x` and `y`, each
  once, and it passes through a chain of adjacent tiles. So `d(x,y) ≤ #separating walls`.
- **Lower bound on distance.** Every path from `x` to `y` in the dual graph crosses each
  separating wall, so `d(x,y) ≥ #separating walls`.
- **No shared endpoints.** Each wall projects to a closed geodesic on `Σ_g`: the edge graph on the
  surface is finite, and the wall goes straight at every vertex. So each wall is the axis of a
  loxodromic element. In a torsion-free cocompact Fuchsian group, axes with a common endpoint
  coincide. So distinct walls have distinct endpoints.

**2. Atoms.**
- **Profiles are side vectors.** Fix `n`, and let `x` be a tile. For `y ∈ B_n`, the difference
  `d(x,y) − d(x,1)` is a sum over the walls `W` separating `1` and `y`: each contributes `+1` if
  `x` is on `1`'s side and `−1` otherwise. Every such `W` lies in `𝒲_n`. So the profile `d_x|B_n`,
  up to an additive constant, is determined by the side of `x` with respect to each wall in `𝒲_n`.
- **Profiles determine sides.** Conversely, each `W ∈ 𝒲_n` separates `1` from some `y ∈ B_n`. A
  geodesic path from `1` to `y` stays in `B_n` and crosses `W` at an edge `yy'`, with `y, y' ∈ B_n`
  separated by `W` alone. The sign of `d_x(y') − d_x(y)` then gives the side of `x`.
- **Atoms as cells.** Each cell of the finite arrangement `𝒲_n` is a union of tiles. So the atoms
  for `B_n` are exactly the sets `G ∩ R` with `R` a cell. By cocompactness, a cell contains
  infinitely many tiles exactly when it is unbounded.

**3. No isolated points; faithfulness.**
- **Arcs at infinity.** Let `R` be an unbounded cell. It is a convex region bounded by finitely
  many walls with pairwise distinct endpoints, so it has no cusps, and its ideal boundary contains
  a nondegenerate arc `I`.
- **Small walls.** Fix two disjoint open arcs `J_1, J_2 ⊆ int I`. Loxodromic fixed points are
  dense in `S^1`, so for each `i` there is a loxodromic `h_i` attracting into `J_i`. Pick a wall not
  ending at its repelling point. High powers of `h_i` carry that wall to a wall `W_i` with both
  endpoints in `J_i`.
- **The small walls lie in `R`.** No wall of `𝒲_n` has an endpoint in `int I`. So `W_i` crosses no
  wall of `𝒲_n`, and the side `Q_i` of `W_i` facing `J_i` lies in `R`.
- **Branching.** For `N ≥ D(W_1), D(W_2)`, both `W_i` lie in `𝒲_N`. So `R` has unbounded descendant
  cells inside `Q_1` and inside `Q_2`, which are disjoint. Every vertex of the tree of atoms
  therefore branches below itself, and the end space `∂_h G` has no isolated points.
- **Faithfulness.** `G` is torsion-free, so it has no nontrivial finite normal subgroup, and the
  action is faithful (BBMZ `rmk:horofunction_problems`).
- **Conclusion.** The rest of item 3 is BBMZ `thrm:BBM`, `prop:hyp_similarities` and
  `thrm:contracting`, with the reformulation lemma.

**4. No cell is a half-plane.**
- **Setup.** Let `n ≥ 1` and `W ∈ 𝒲_n`. Let `t_0` be a tile on the far side of `W` with
  `|t_0| = D(W) ≤ n`. A geodesic from `1` to `t_0` crosses `W`, and by minimality it does so on its
  last edge. So `t_0` is adjacent across an edge `e ⊆ W` to a near-side tile `t_0'` with
  `|t_0'| = |t_0| − 1`.
- **The crossing wall.** Let `v` be an endpoint of `e`, and let `e'` be the other side of `t_0'`
  at `v`, lying on the wall `U`. The angle of `t_0'` at `v` is `π/2g < π`, so `U ≠ W`. Both pass
  through `v`, so `U` crosses `W`.
- **`U ∈ 𝒲_n`.** Let `u` be the tile across `e'` from `t_0'`, so `|u| ≤ |t_0'| + 1 = |t_0| ≤ n`.
  If `t_0'` is on `1`'s side of `U`, then `u` is not, and `U` separates `1` from `u ∈ B_n`.
  Otherwise `U` separates `1` from `t_0' ∈ B_n`. Either way `U ∈ 𝒲_n`.
- **Conclusion.** `U` meets both sides of `W`. So neither half-plane of `W` is a cell of `𝒲_n`. ∎

(Correction, 2026-09-18: this replaces a gate lemma for half-plane cells, which is vacuous by the
argument above.)
