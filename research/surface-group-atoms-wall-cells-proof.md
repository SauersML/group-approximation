---
rg: 2
id: surface-group-atoms-wall-cells-proof
kind: route
title: Counting separating walls turns distance profiles on B_n into side vectors for the walls in 𝒲_n; small walls near every ideal point give branching, and a cell that is a half-plane has a unique tile on the near side of every wall entering it
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

**4. Half-plane cells are gated.**
- **The far side.** Let `n ≥ 1` and let `R = H` be a cell equal to a half-plane bounded by
  `W ∈ 𝒲_n`. The cell containing `1` is the tile `1` itself, which is bounded because all walls
  around it lie in `𝒲_1`. So `1 ∉ H`, and `H` is the far side of `W`. Since `W ∈ 𝒲_n`, there is some
  `y ∈ H ∩ B_n`.
- **Near-side tiles.** Every wall `W'` entering `H` is not in `𝒲_n`, because `H` is a cell. So `W'`
  separates `1` from no point of `B_n`, and every `y ∈ H ∩ B_n` lies on `1`'s side of `W'`.
- **Uniqueness.** Let `G_0` be the set of tiles of `H` that lie on `1`'s side of every wall entering
  `H`. The walls separating `1` from a tile of `G_0` are the walls that miss `int H` but separate
  `1` from `H`, and this set is the same for every tile of `G_0`. So any two tiles of `G_0` are
  separated by no wall, and `G_0` is a single tile `t_0`. Hence `H ∩ B_n = {t_0}`.
- **Gate formula.** For a tile `x ⊆ H`, every wall separating `t_0` from `x` enters `H` (by
  convexity). A wall entering `H` separates `1` from `x` exactly when it separates `t_0` from `x`.
  So `|x| = |t_0| + d(t_0,x)`.
- **`t_0` is adjacent to `W`.** Since `t_0 ≠ 1`, some neighbour of `t_0` is closer to `1`. The wall
  between them separates `1` from `t_0`, so it does not enter `H` and bounds `t_0`. That wall is
  `W`. So `t_0` is adjacent to `W`, and by the gate formula `D(W) = |t_0|`. ∎
