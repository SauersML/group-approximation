---
rg: 2
id: fpbs-expanding-factor-product-strict-thresholds
kind: claim
title: A Cartesian product with a strongly expanding factor has an L2 gap and strict thresholds
distinct_from:
  fpbs-tree-projected-large-rank-strict-thresholds: that bounds p_c by an embedded free-basis tree over a free quotient of large rank; this bounds p_c by the edge expansion of one Cartesian factor and needs no tree, no free quotient and no rank condition.
  fpbs-hyperbolic-and-nonunimodular-nonuniqueness: that applies to products whose factor is a tree through a nonunimodular automorphism group; this is perturbative and applies to factors with discrete automorphism groups such as hyperbolic tilings.
  fpbs-product-every-generating-set: that is the open root over every generating set of a product; this settles only Cartesian product generating sets whose first factor expands strongly relative to its adjacency norm and the degree of the second.
  fpbs-expansion-thinning-threshold: that is the input p_c <= 1/(1+h) on any graph of edge expansion h; this combines it with walk counting on the product.
artifacts:
  - research/artifacts/fpbs/docs/expanding-factor-product-thresholds.md
---

**ESTABLISHED.** Let `G = Cay(H, S_H)` be `d`-regular with edge expansion
`h = h(G) > 0` and adjacency operator `A_G`, and let `K = Cay(L, S_L)` be
`d_K`-regular. Put `X = G □ K`, the Cayley graph of `H x L` for
`(S_H x {1}) ∪ ({1} x S_L)`. If

```text
1 + h  >  ||A_G||_{2->2} + d_K,
```

then

```text
p_c(X)  <=  1/(1+h)  <  1/||A_X||  <=  p_{2->2}(X)  <=  p_u(X),
```

so `p_c(X) < p_{2->2}(X)` and `p_c(X) < p_u(X)`.

When `L` is amenable, the critical fibre operator over `H` is bounded on these
graphs, so the one-radius condition of
`fpbs-critical-sphere-fibre-operator-below-one` holds there
(`fpbs-sphere-fibre-operator-iff-critical-fibre-l2`).

Method: classical perturbative comparison (Benjamini–Schramm 1996;
Pak–Smirnova-Nagnibeda 2000). No novelty is claimed. Proof:
`fpbs-expanding-factor-product-proof`.
