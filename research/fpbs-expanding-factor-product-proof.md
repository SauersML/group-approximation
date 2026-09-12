---
rg: 2
id: fpbs-expanding-factor-product-proof
kind: route
title: The expanding slice bounds p_c and the triangle inequality bounds the product adjacency norm
target: fpbs-expanding-factor-product-strict-thresholds
requires:
  - fpbs-expansion-thinning-threshold
artifacts:
  - research/artifacts/fpbs/docs/expanding-factor-product-thresholds.md
---

Notation as in the target.

1. **`p_c`.** The slice `G x {1}` is a subgraph of `X`. Adding edges can only
   lower `p_c`, so `p_c(X) <= p_c(G)`. By `fpbs-expansion-thinning-threshold`,
   `p_c(G) <= 1/(1+h)`.
2. **Adjacency norm.** On `l2(H x L) = l2(H) ⊗ l2(L)`,
   `A_X = A_G ⊗ I + I ⊗ A_K`. A `d_K`-regular graph has `||A_K|| <= d_K` by
   Schur's test. By the triangle inequality,
   `||A_X|| <= ||A_G|| + d_K < 1 + h`.
3. **Walk counting.** `tau_p(x,y)` is at most the sum of `p^(length)` over paths
   from `x` to `y`, so `T_p <= sum_l p^l A_X^l` entrywise. If `p ||A_X|| < 1`, then
   `||T_p||_{2->2} <= (1 - p||A_X||)^(-1)`. Hence `p_{2->2}(X) >= 1/||A_X||`.
4. **`p_{2->2} <= p_u`.** For `p > p_u` the infinite cluster is unique, so
   `tau_p(x,y) >= theta(p)^2 > 0` for all `x, y`, and `T_p` is unbounded on the
   infinite graph (Hutchcroft arXiv:1804.10191, Section 2; also step 4 of
   `fpbs-tree-projected-large-rank-proof`).
5. **Conclusion.** Steps 1–4 give
   `p_c(X) <= 1/(1+h) < 1/||A_X|| <= p_{2->2}(X) <= p_u(X)`.
6. **Fibre remark.** If `L` is amenable, the fibre comparison is an equality
   (`fpbs-fibre-summed-connectivity-operator`). So `||T_{p_c}|| < infinity` means
   the critical fibre operator over `H` is bounded, which is condition (b) of
   `fpbs-sphere-fibre-operator-iff-critical-fibre-l2`.
