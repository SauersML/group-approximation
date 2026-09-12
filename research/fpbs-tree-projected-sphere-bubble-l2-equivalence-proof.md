---
rg: 2
id: fpbs-tree-projected-sphere-bubble-l2-equivalence-proof
kind: route
title: Submultiplicative sphere bubbles through cut fibres feed the two-estimate criterion
target: fpbs-tree-projected-sphere-bubble-l2-equivalence
requires:
  - fpbs-relative-susceptibility-tube-excursion-bound
  - fpbs-hyperbolic-quotient-fibre-estimates-l2-gap
  - fpbs-fibre-summed-connectivity-operator
artifacts:
  - research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md
---

Theorem 4.3 of the artifact.

* **(⇒)** If `p_c < p_{2->2}` then `T_(p_c)` is bounded. Since `H` is amenable,
  `fpbs-fibre-summed-connectivity-operator` gives
  `sum_R b_R(p_c) = ||S_(p_c) delta_1||^2 <= ||T_(p_c)||^2`. So `b_R(p_c) -> 0`.
* **(⇐)** Suppose `b_(R_0)(p_c) = 1 - eta`.
  1. Each `sigma_p(q)` is nondecreasing and left-continuous in `p`, so
     `b_(R_0)(p) <= 1-eta` for all `p < p_c`.
  2. The tube excursion bound with `r = R_0-1` gives
     `chi^H_p <= C_(R_0-1)(p_c) + 1`.
  3. Through cut fibres, `b_(R+R') <= b_R b_(R')`. So the sphere bubbles decay
     geometrically and `sum_R b_R <= const/eta`: the uniform fibre bubble.
  4. `max_(|w|=D) sigma_p(w) <= b_D^(1/2) -> 0`. Branch shares at depth `D` are
     at most `sigma_p(w)`, and far halfspaces pull back into boundedly many
     branches. This gives the far-halfspace share.
  5. `fpbs-hyperbolic-quotient-fibre-estimates-l2-gap` gives `p_c < p_{2->2}`.
