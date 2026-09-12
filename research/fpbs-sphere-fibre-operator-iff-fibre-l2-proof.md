---
rg: 2
id: fpbs-sphere-fibre-operator-iff-fibre-l2-proof
kind: route
title: Absorb the sphere cut below p_c, and run Hutchcroft's averaged complement argument on fibre sums
target: fpbs-sphere-fibre-operator-iff-critical-fibre-l2
requires:
  - fpbs-sphere-cut-fibre-tails-decay-exponentially
  - fpbs-fibre-summed-connectivity-operator
  - fpbs-critical-l2-implies-nonuniqueness
  - fpbs-rd-weighted-bubble-iff-sphere-fibre-operator-below-one
artifacts:
  - research/artifacts/fpbs/docs/sphere-fibre-operator-is-critical-l2.md
---

* **(a) ⟹ (b).** By the sphere cut (`fpbs-sphere-cut-fibre-tails-decay-exponentially`),
  `sigma_p 1_{|.|>=R_0} <= sigma_{p,R_0} * sigma_p` entrywise. So for `p < p_c`,
  `N(sigma_p) <= ||sigma_p 1_{|.|<R_0}||_1 + theta N(sigma_p)`, and
  `N(sigma_p) <= chi_p` is finite. Harris–FKG bounds each small-radius fibre sum by
  `p^(-L) theta`. The uniform bound passes to `p_c` by left-continuity.
* **(b) ⟹ (c).** The sphere cut at radius `r <= m` gives
  `sigma 1_{|.|>=n+m} <= (m+1)^(-1) sigma * (sigma 1_{|.|>=n})`. Iterating with
  `m = n = ceil(e N) - 1` gives `N(sigma 1_{|.|>=r}) <= e N exp(-r/(eN))`.
* **(c) ⟹ (a).** Restrict to one sphere of large radius.
* **L2 gap.** `fpbs-fibre-summed-connectivity-operator` gives
  `||T_{p_c}|| <= N(sigma_{p_c})`, with equality for amenable `H`. Openness of the
  L2 phase turns `||T_{p_c}|| < infinity` into `p_c < p_{2->2}`. This is Hutchcroft
  arXiv:1804.10191, the corollary of `lem:operatorbound`, imported as in
  `fpbs-critical-l2-implies-nonuniqueness`.
* **Consequence.** `fpbs-rd-weighted-bubble-iff-sphere-fibre-operator-below-one`
  identifies the weighted critical fibre bubble with (a) over rapid-decay quotients.

Full proof: artifact Theorem A and Corollary B.
