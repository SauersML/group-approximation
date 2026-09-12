---
rg: 2
id: fpbs-hyperbolic-quotient-fibre-estimates-l2-gap-proof
kind: route
title: Cheeger and the magic lemma on the quotient, then Hutchcroft's operator-norm criterion
target: fpbs-hyperbolic-quotient-fibre-estimates-l2-gap
requires:
  - fpbs-fibre-summed-connectivity-operator
  - fpbs-fibre-bubble-forces-mean-field-susceptibility
artifacts:
  - research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md
---

Theorem 3.1 of the artifact.

* **Quotient Cheeger bound.** For finite `A ⊆ Q`, the magic lemma supplies
  `A'` with `|A'| >= (1-eps)|A|` and two far halfspaces per point. Their
  complement in `A` has at most `N(eps)` points. Each exceptional coset term is
  at most `max sigma <= B^(1/2)`, and each far halfspace contributes at most
  `sh(1/eps) chi_p`. Cheeger's inequality then gives
  `||S_p|| <= chi_p (2(1 - iota(S_p)))^(1/2)`.
* **Combination.** The first required claim moves `||S_p||` to `||T_p||`. The
  second bounds `(p_c-p)chi_p`. Together they give `(p_c - p)||T_p|| -> 0`, and
  Hutchcroft's Corollary 2.6 (arXiv:1804.10191) excludes `p_{2->2} = p_c`.
