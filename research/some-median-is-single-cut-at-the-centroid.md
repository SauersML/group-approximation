---
rg: 2
id: some-median-is-single-cut-at-the-centroid
kind: claim
title: For every descendant dissection of a rank-three unimodular cell, some median of the cell cuts every piece containing the centroid either not at all or along one of the piece's own first splits
requires:
  - single-cut-is-a-mediant-condition-along-the-median
distinct_from:
  single-cut-is-a-mediant-condition-along-the-median: that gives the local criterion and settles the vertices of the cell; this settles the centroid, where all three medians meet, by a root-system argument in the link.
  edge-split-descendant-dissections-have-single-cut-first-splits: that is (SC), which needs one median good at every vertex on it; this is the case of the one vertex common to all three medians.
---

**ESTABLISHED** (lane bh-major-mcg-2, 2026-09-18). Lane proof, elementary, not
independently reviewed. No priority claimed.

## Setting

- **The cell and the dissection.** Take `m = 2` and `g = Δ = cone(e_0, e_1, e_2)`, by
  equivariance. Let `D` be a descendant dissection of `Δ` and `c = (1,1,1)` the centroid.
  `M_k` is the median through `e_k` and `v_{ij} = e_i + e_j`.
- **Good.** A median is *good at `c`* if every piece of `D` whose closure contains `c`
  is either not straddled by it, or single-cut by it.
- **The link at `c`.** It is `Λ = Z^3/Zc`, and the images of the `e_i` satisfy
  `ē_0 + ē_1 + ē_2 = 0`.
- **Roots.** In the basis `(ē_0, ē_1)`, the directions of the medians at `c` are the
  six roots of a hexagonal lattice, in cyclic order:
  - `ρ_0 = ē_0 = (1,0)`;
  - `ρ_1 = −ē_2 = (1,1)`;
  - `ρ_2 = ē_1 = (0,1)`;
  - `ρ_3 = −ρ_0`, `ρ_4 = −ρ_1`, `ρ_5 = −ρ_2`.

  The median `M_k` has directions `±ē_k`, so the three medians are `{ρ_0, ρ_3}`,
  `{ρ_1, ρ_4}` and `{ρ_2, ρ_5}`. Consecutive roots satisfy
  `ρ_{i−1} + ρ_{i+1} = ρ_i`, and each cone `cone(ρ_{i−1}, ρ_{i+1})` is unimodular.

## Statement

Some median of `Δ` is good at `c`.

## Proof

**Step 1: where `c` can sit.**
- Suppose `c = a x + b y` with `x, y` nonnegative integer vectors and `a, b ≥ 1`. Each
  coordinate `1 = a x_i + b y_i` forces `a = b = 1`, and `x, y` are complementary 0/1
  vectors. So `{x, y} = {e_k, v_{ij}}`.
- Hence if `c` lies in the relative interior of an edge of a piece, that edge is a whole
  median segment `[e_k, v_{ij}]`.
- For the same reason, `c` is created only as the midpoint of an edge `[e_k, v_{ij}]` of
  some ancestor.

**Step 2: `c` inside an edge.**
- Suppose `c` lies inside the edge `[e_k, v_{ij}] ⊂ M_k` of some piece. Then that piece
  lies on one side of `M_k`.
- Near `c`, that piece fills the whole half-disk on its side. So every other piece
  containing `c` lies in the closed opposite half-plane: its corner at `c`, if `c` is a
  vertex, lies in the half-plane bounded by `Rē_k`, and otherwise it has the same edge.
- So no piece containing `c` is straddled by `M_k` at `c`, and `M_k` is good.
- If `D = {Δ}`, every median is a first split of the single piece.

**Step 3: corners at `c` are Stern–Brocot descendants of creation cones.**
- Let `r` have ray `c`, created from the edge `[e_k, v_{ij}]` of an ancestor
  `A = cone(e_k, v_{ij}, z)`. The two children of `A` have corners
  `cone(ē_k, z̄)` and `cone(−ē_k, z̄)` at `c`.
- Unimodularity gives `z̄ = ±ē_{i'} + n ē_k` for the basis complement `ē_{i'}`.
- Later steps either keep the corner (splits at edges `(c, a)`) or split it
  Stern–Brocot-wise (splits at edges `(a, b)`), as in part 2 of
  `single-cut-is-a-mediant-condition-along-the-median`.
- So every corner at `c` is a Stern–Brocot descendant of a creation cone
  `cone(±ρ, z̄)`, which lies in a closed half-plane bounded by a root line.

**Step 4: counting roots in a corner.** Assume now that `c` is a vertex of every piece
containing it, so the corners at `c` form a complete unimodular fan.
- **One interior root is good.** A corner containing exactly one root `ρ_i` in its
  interior lies in `cone(ρ_{i−1}, ρ_{i+1})`. The only unimodular subcone of a unimodular
  cone that contains its mediant `ρ_i` in its interior is the cone itself, so the
  corner's mediant is `ρ_i`, and `ρ_i` is good.
- **Three interior roots are impossible.** A corner with three consecutive roots in its
  interior lies in no half-plane bounded by a root line, which contradicts Step 3.
- **The only possible failure.** A root that is not a fan ray is therefore bad only if it
  lies in a corner containing exactly two consecutive roots `ρ_i, ρ_{i+1}` in its
  interior.

**Step 5: a corner with two roots makes the third median good.**
- By symmetry of the root system, let `κ` contain `ρ_1, ρ_2` in its interior.
- By Step 3, `κ` lies in the upper half-plane bounded by `Rρ_0` and is a Stern–Brocot
  descendant of `cone(ρ_0, (n,1))` or `cone(ρ_3, (n,1))`.
- The descendants containing both `(1,1)` and `(0,1)` are:
  - `κ = cone(ρ_0, (m,1))` with `m ≤ −1`; or
  - `κ = cone(ρ_3, (m,1))` with `m ≥ 2`.
- **We claim `M_0 = {ρ_0, ρ_3}` is good.**

**First case, `κ = cone(ρ_0, (m,1))`.**
- `ρ_0` is a fan ray.
- If `ρ_3` were bad, it would lie in a corner `κ'` with interior roots `ρ_3, ρ_4`,
  since `ρ_2` is inside `κ`.
  - By Step 3, `κ'` descends from a creation cone of `M_2 = {ρ_2, ρ_5}` on the side
    `{x ≤ 0}`.
  - Descendants with `ρ_2` as a ray are excluded, because `ρ_2 ∈ int κ`. So
    `κ' = cone(ρ_5, (−1,k))` with `k ≥ 1`, and `ρ_3` is bad only if `k ≥ 2`.
  - Disjointness from `κ` needs the angle of `(−1,k)` to be at least that of `(m,1)`,
    that is `k ≤ 1/|m|`. So `k = |m| = 1`, and then `ρ_3` is the mediant of `κ'`. If
    `|m| ≥ 2`, no such `κ'` exists.

**Second case, `κ = cone(ρ_3, (m,1))`.**
- `ρ_3` is a fan ray.
- A bad `ρ_0` needs a corner `κ''` with interior roots `ρ_5, ρ_0` descending from a
  creation cone of `M_1 = {ρ_1, ρ_4}`.
  - Excluding `ρ_1`, which lies in `int κ`, gives `κ'' = cone(ρ_4, (k+1, k))` with
    `k ≥ 1`.
  - `ρ_0` is bad only if `k ≥ 2`.
  - Disjointness from `κ` needs `k(m − 1) ≤ 1`, so `k = 1`, and then `ρ_0` is the
    mediant.

**Conclusion.** In both cases `M_0` is good. If no corner contains two roots, every
median is good by Step 4. ∎

## Consequence for (SC)

At the centroid, a single-cut median always exists.

Combined with `single-cut-is-a-mediant-condition-along-the-median`, which settles the
cell's own vertices, (SC) for `D` now needs a median that is also good at the other
vertices of `D` on it. Those are the vertices strictly between `e_k` and `c` and between
`c` and `v_{ij}`.

## Lesson for general BH

- **At the point where all first cuts meet, the cuts form a root system.** Every piece's
  corner there lies in a half-plane bounded by one of the cuts, because a vertex is
  created only on a cut. Counting roots per corner then forces one cut to be clean.
- **Where to look for such constraints.** In non-LCM dissection operads, "some generator
  cut is clean" statements come from the arithmetic of how vertices can be created: here
  `c = x + y` has only three decompositions. That is the constraint to look for at every
  special vertex.
