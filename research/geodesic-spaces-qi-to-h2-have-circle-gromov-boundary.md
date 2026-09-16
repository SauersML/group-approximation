---
rg: 2
id: geodesic-spaces-qi-to-h2-have-circle-gromov-boundary
kind: claim
title: The Gromov boundary of a possibly non-proper geodesic space quasi-isometric to H^2 is a circle in the Gromov-product topology
---

Let `X` be a geodesic metric space quasi-isometric to `H^2`. Write `(x|y)_w` for the Gromov product.
Suppose `δ ≥ 0` satisfies `(x|z)_w ≥ min{(x|y)_w, (y|z)_w} − δ` for all `x, y, z, w ∈ X`, and fix `o ∈ X`.

- `∂X` is the sequential boundary of `busemann-null-isometries-have-no-boundary-contraction`: sequences
  `(y_i)` with `liminf_{i,j} (y_i|y_j)_o = ∞`, modulo `liminf_{i,j} (y_i|w_j)_o = ∞`.
- For `u, v ∈ ∂X` put `⟨u|v⟩_o := inf liminf_{i,j→∞} (y_i|w_j)_o`, the infimum being over all `y_i → u`
  and `w_j → v`. This is Definition 3.4.9, (3.4.5), of Das–Simmons–Urbański, arXiv:1409.2155v7.
- `T` is the topology on `∂X` in which the sets `N_t(u) := {v ∈ ∂X : ⟨v|u⟩_o > t}`, `t ≥ 0`, form a
  neighbourhood base at each `u`. This is the restriction to `∂X` of the topology `T` of the same
  monograph, Section 3.4.2.

**Claim.** `(∂X, T)` is homeomorphic to the circle `S^1`.

`X` need not be proper. For example, glue a unit segment to every point of `H^2`. So the classical
statement for proper spaces does not apply directly.

This claim is an input of `cobounded-qi-h2-focal-via-dsu-classification`, and through it of
`thompson-f-no-cobounded-qi-h2-action-via-busemann`. A direct proof is route
`qi-h2-circle-boundary-via-quantitative-morse-lemma`.

## Attempts

- **2026-09-16, swarm lane zaremsky-2-18: literature check, not established.**
  - Das–Simmons–Urbański, *Geometry and dynamics in Gromov hyperbolic metric spaces*, arXiv:1409.2155v7
    (28 Jun 2016). The PDF was fetched and its text extracted on 2026-09-16.
    - It works without properness throughout, and defines `∂X` and `T` as above.
    - Its Proposition 3.4.18 reads: "The topological space (bord X, T) is completely metrizable. If X
      is proper and geodesic, then bord X (and thus also ∂X) is compact."
    - A text search found no theorem that extends a quasi-isometry to a boundary homeomorphism in this
      non-proper setting.
  - Bridson–Haefliger III.H.3.9, as far as recalled, is stated for proper spaces. It was not re-read.
  - Väisälä, *Gromov hyperbolic spaces*, Expo. Math. 23 (2005), was not obtained. A Helsinki URL for the
    preprint returned 404.
- **Proposed direct proof, not written out.**
  - (G1) For `x, y ∈ X` and a geodesic `[x,y]`: `(x|y)_o ≤ d(o,[x,y]) ≤ (x|y)_o + 2δ`. Apply the
    four-point inequality at base `p ∈ [x,y]`.
  - (G2) The Morse lemma in `H^2`: quasi-geodesic segments stay uniformly close to geodesics.
  - (G3) Using (G1) and (G2), a `(K,C)`-quasi-isometry `φ: X → H^2` satisfies
    `K^{-1}(x|y)_o − A ≤ (φx|φy)_{φo} ≤ K(x|y)_o + A` for a constant `A`.
  - (G4) Hence `φ` maps sequences converging at infinity to such sequences, preserves equivalence, and
    induces a bijection `∂X → ∂H^2`. Its inverse is induced by a quasi-inverse.
  - (G5) By (G3), the boundary products are comparable in the same way. So the bijection and its inverse
    carry basic neighbourhoods into basic neighbourhoods, and it is a homeomorphism for `T`.
  - (G6) For `H^2` itself, `T` agrees with the usual topology of the circle at infinity. Use the disc
    model formula `cosh d = cosh(a − b) cos²(θ/2) + cosh(a + b) sin²(θ/2)` for points at radii `a, b`
    and angle `θ`.
  - The step a referee should attack first is (G3), in particular the lower bound. It needs a uniform
    comparison between `d(φo, [φx,φy])` and `d(o, [x,y])`.
- **2026-09-16, same lane: direct proof written out.** Route
  `qi-h2-circle-boundary-via-quantitative-morse-lemma` carries out (G1)–(G6).
  - (G2) is imported from Gouëzel–Shchur, arXiv:1810.04579v1, Theorem 1.1, quoted verbatim together with
    its definitions. Their quasi-geodesics need not be continuous, and their hyperbolicity is the
    four-point condition used here.
  - The lower bound in (G3) follows from the two-sided Hausdorff bound of that theorem.
  - (G6) is proved from the hyperboloid model. The estimate
    `min{a, b, −log χ} − log 2 ≤ (x|y)_o ≤ min{a, b, −log χ + (1/2)log 2}` also gives the four-point
    inequality for `H^2` with constant `(5/2)log 2`.
