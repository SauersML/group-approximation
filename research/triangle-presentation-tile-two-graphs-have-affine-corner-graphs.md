---
rg: 2
id: triangle-presentation-tile-two-graphs-have-affine-corner-graphs
kind: claim
title: Corner compatibility graphs of every triangle-presentation tile 2-graph are affine-plane incidence graphs minus a parallel class, hence connected
artifacts:
  - research/artifacts/nv-brick-coding-corner-kill-2026-09-17.md
  - experiments/nv-kazhdan-independence-2026-09-17/corners_all.py
  - experiments/nv-kazhdan-independence-2026-09-17/corners_all.log
  - experiments/nv-brick-coding-2026-09-17/rs2graph.py
distinct_from:
  robertson-steger-a2-two-graphs-are-primitive-and-aperiodic: that is about primitivity and aperiodicity of the colour matrices; this identifies the local square structure at a vertex.
  two-graph-brick-codings-die-at-connected-corners: that is the abstract kill that takes corner connectivity as a hypothesis; this proves the hypothesis for all triangle presentations.
---

Let `T` be a triangle presentation over `PG(2,q)`, `q ≥ 2`, with point–line bijection `λ`,
satisfying:

- (A1) some `z` has `(x,y,z) ∈ T` iff `y ∈ λ(x)`;
- (A2) `(x,y,z) ∈ T ⇒ (y,z,x) ∈ T`;
- (A3) at most one `z` has `(x,y,z) ∈ T`.

Let `Λ_T` be the tile 2-graph of `rs2graph.py`:

- vertices are the tiles `(x,y,z,u,w)` with `(x,y,z), (y,u,w) ∈ T` and `u ≠ z`;
- a colour-1 edge `a → b` exists iff `w_a = z_b` and `y_a ≠ x_b`;
- a colour-2 edge `a → c` exists iff `u_a = x_c` and `w_a ≠ y_c`;
- the squares are the words of shape (2,2).

Assume unique filling (H1): every colour-1-then-2 path `a→b→d` has exactly one `c` with
`a -2-> c -1-> d`.

**Claim.** Fix a tile `a = (x,y,z,u,w)`, and put `ℓ = λ(u)`. Then:

- `w ∈ ℓ`;
- `b ↦ u_b` is a bijection from the colour-1 edges at `a` onto the points off `ℓ`;
- `c ↦ λ(w_c)` is a bijection from the colour-2 edges at `a` onto the lines not through
  `w`;
- `b` and `c` are compatible (some square has first edges `a→b` and `a→c`) iff
  `u_b ∈ λ(w_c)`.

Hence the corner graph `B_1(a)` is the incidence graph of the affine plane
`PG(2,q) \ ℓ` with the parallel class of `w` removed. It is `q`-regular on `q^2 + q^2`
vertices and connected. So (C1) of `two-graph-brick-codings-die-at-connected-corners`
holds for `Λ_T`, and every row sum is `q^2`.

Route: `tile-two-graph-affine-corners-proof`
(Proposition F of the artifact).
