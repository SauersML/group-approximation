---
rg: 2
id: stinespring-corner-repair-rounds-ucp-factorizations
kind: route
title: Repair the encoding corner, align its support, and trim rectangular blocks to recover an expectation
target: ucp-factorizations-round-to-matrix-expectations
requires: []
artifacts:
  - research/artifacts/ucp-factorization-to-same-dimension-expectation-2026-09-08.md
---

Schwarz for the decoding map and trace preservation of `P` imply
`tau(1-Delta(u)*Delta(u))<=eta=2r+s` uniformly on `U(B)`.
In a Stinespring dilation of `Delta`, average the encoding projection
over the exact compact group `pi(U(B))`. Spectral rounding produces
an invariant projection whose normalized rank differs from one by
at most `2eta`. The encoded source unit ball is within
`2sqrt(2eta)` of the resulting exact image algebra.

A principal-angle rotation nests the repaired support with the
original rank-`d` support. After this rotation the full image-algebra
unit ball and `Delta(B_1)` are paired at distance
`t=(2sqrt(2)+4)sqrt(eta)`. The original map nearly fixes that
algebra, with error `2t+r+s`, and its outputs have distance at most
`s+t` from it.

Self-adjointness converts these two bounds into a comparison with
the compressed expectation. This uses a pointwise inner-product
estimate on a contraction in the original corner; it does not assume
that taking an adjoint preserves the mixed operator norm. If the
repaired support is smaller, add a scalar corner. If it is larger,
trim rectangular Wedderburn blocks, rotate their retained support
into the original corner, and correct the scalar normalization.
The artifact proves this compression lemma in full and obtains the
stated `44 eta^(1/4)` bound in the original dimension.

For the corollary, Kitaev's Theorem 12.3 in
[arXiv:2405.02434v2](https://arxiv.org/html/2405.02434v2#S12.SS2)
supplies UCP maps with both completely bounded factorization errors
`O(epsilon)`. These dominate the two norms used above. This gives
mixed-norm expectation rounding under completely bounded
near-idempotence. It does not upgrade the native defect norm.
