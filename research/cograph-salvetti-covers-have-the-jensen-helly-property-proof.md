---
rg: 2
id: cograph-salvetti-covers-have-the-jensen-helly-property-proof
kind: route
title: Jensen centres and convex bicombings pass to products and one-vertex wedges, hence to all cograph Salvetti covers
target: cograph-salvetti-covers-have-the-jensen-helly-property
requires: []
artifacts:
  - research/artifacts/zp-raag-rips-cographs-2026-09-13.md
---

Direct proof; full details in the artifact.

A cograph is built from `K_1` by disjoint union and join. Joins give direct
products, whose Salvetti cover is the l^1 product. Disjoint unions give free
products, whose Salvetti cover is tree-graded with pieces glued at single
vertices. Call a space a J-space if it has
- (J) Jensen centres `d(x,b) ≤ ∫ d(x,y) dμ` for finitely supported `μ` on
  vertices, and
- (C) a continuous geodesic bicombing along which every distance function is
  convex.

1. **Base.** `R`: the mean, and straight segments.
2. **Products.** Take coordinatewise centres. The product bicombing has each
   coordinate at constant speed, so distance is a sum of convex functions.
3. **Wedges `A ∨_g B` (Lemma W).** Let `c_A` be the (J)-centre of
   `μ_A + m_B δ_g` in `A`, and `c_B` that of `μ_B + m_A δ_g` in `B`. Put
   `M_A = ∫_A d(g,y) dμ` and `M_B = ∫_B d(g,y) dμ`.
   - If `d(c_A,g) ≥ M_B`, move from `c_A` toward `g` by `M_B`.
   - If `d(c_B,g) ≥ M_A`, do the same symmetrically.
   - Otherwise take `b = g`.
   Each case is checked with the triangle inequality through `g`. The
   bicombing goes through `g`, and convexity holds at `g` because on the far
   side of `g` the distance grows at the full speed `d(c,c')`. Tree-graded
   spaces reduce to finite iterated wedges.
4. **(H).** Balls are convex for the bicombing, so nonempty intersections are
   compact ARs. Borsuk's nerve theorem plus `Ȟ^j(A) = 0` for `j ≥ k`, for
   compact `A` in a contractible `k`-dimensional ball `P`, give Helly number
   `k+1`, as in Lemma H of
   `research/artifacts/zp-raag-rips-products-of-trees-2026-09-13.md`.
5. **(R).** Every point of a `k`-cube is within `k/2` of a corner.

Model test: this recovers the mean for `Z^n` and the tree barycentre for free
groups. For a line wedged at an interior point with the plane it gives the
point at l^1-distance 4.5 from the cut vertex in the counterexample recorded
in `raag-salvetti-covers-have-the-jensen-helly-property`. There the naive
projected mean fails (Case 1: `d(c_A,g) = 5 ≥ M_B = 1/2`, move by `1/2`).
