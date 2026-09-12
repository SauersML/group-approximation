---
rg: 2
id: rank-fixed-ideal-conservation-proof
kind: route
title: Count dimensions of exact fixed subspaces under compressors and pass to the rank ultraproduct
target: rank-ultraproduct-compressors-conserve-fixed-right-ideals
requires: []
artifacts:
  - research/artifacts/rank-row-compression-audit-2026-09-12.md
---

## Why sufficient

Complete direct proof, Section 1 of the artifact. Let `K_i` be the exact common kernel of
`sigma_i(s) - 1`, `s` in `S`.

* **Free rounding (Lemma 1).** On `W = im x_i`, each `sigma_i(s) - 1` loses at most its
  rank, so `W n K_i` has codimension at most `sum_s rank((sigma_i(s)-1)x_i)` in `W`, and
  `1 - e_i` kills `K_i`.
* **Tensor degrees (Lemma 2).** Rank of a difference of tensor products is at most the
  sum of the factor ranks times `n^(m-1)`, and `g -> sigma(g^-1)^T` is a homomorphism.
* **Conservation (Theorem 3).**
  * A compressor `u_i` maps `K_i` exactly onto the common kernel of the conjugated
    generators.
  * Those agree up to rank `o(n_i)` with words in the generators, which fix `K_i`, so
    `K_i` and `u_i K_i` agree up to `o(n_i)` dimensions.
  * So compressors preserve `eM`, elements of `Gamma` fix it, and conjugates of those
    fix it too.
