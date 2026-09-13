---
rg: 2
id: l1-products-of-trees-have-contractible-rips-complexes-proof
kind: route
title: Products of trees satisfy Zaremsky's criterion through tree barycentres, Helly number k+1 and rounding
target: l1-products-of-trees-have-contractible-rips-complexes
requires:
  - zaremsky-rips-contractibility-criterion
artifacts:
  - research/artifacts/zp-raag-rips-products-of-trees-2026-09-13.md
---

Full argument in the artifact. Outline, for an integer `t ≥ k(k+1)` and
`r_t = kt/(k+1) + k/2`:

1. **Jensen at the barycentre (Lemma J).** In a finite metric tree, a
   minimizer `b` of `∫ d(·,y)^2 dμ` satisfies `d(x,b) ≤ ∫ d(x,y) dμ(y)` for
   all `x`. Proof by first variation of `b` toward `x`. Coordinatewise this
   gives the same inequality for `d_1` on the product.
2. **Helly number `k+1` (Lemma H)** for `d_1`-balls in the product `P` of
   finite subtrees. The balls are CAT(0)-convex for the l^2 product metric, so
   intersections are ARs. By Borsuk's nerve theorem, a minimal non-intersecting
   subfamily would give a compact `U ⊆ P` with `U ≃ S^{m−1}` and `m − 1 ≥ k`.
   But `Ȟ^j(U) = 0` for `j ≥ k` since `P` is contractible and `k`-dimensional.
3. **Rounding (Lemma R).** Every point of `P` is within `k/2` of a vertex.
4. **Criterion.** If `diam S = t`, any `k+1` of the balls `B(s, kt/(k+1))`,
   `s ∈ S`, meet at the barycentre of their centres, by (1). So all of them
   meet (2), and rounding (3) puts `S` in a vertex ball of radius `r_t < t`. With the centre set
   `Y(S)`, the balls `B(s, kt/(k+1))` and `B(y, t − k/2)` have the
   `k+1`-intersection property. The barycentre of the `S`-members lies within
   `r_t ≤ t − k/2` of each `y`, which is where `t ≥ k(k+1)` is used. So all
   meet, and rounding gives `y_0 ∈ Y(S)` within `t` of every centre. These are
   the hypotheses of `zaremsky-rips-contractibility-criterion` for all
   `t > t_0 = k(k+1) − 1`.

Status: complete argument, unreviewed. It reproves Zaremsky's `Z^n` bound as
the case of lines.
