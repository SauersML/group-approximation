---
rg: 2
id: fpbs-hutchcroft-l2-gap-criterion
kind: claim
title: Hutchcroft's two-sided Cheeger bound for the connectivity operator and his criterion for the strict l2 gap
distinct_from:
  fpbs-acylindrically-hyperbolic-critical-l2-gap: that applies the criterion to acylindrically hyperbolic groups using the Choi-Seo estimates; this imports the criterion and its lemmas for every quasi-transitive graph, with no estimate about any class.
  fpbs-critical-l2-implies-nonuniqueness: that imports the consequence p_c<p_u of critical l2 boundedness; this imports the criterion characterizing p_c<p_(2->2), the two-sided Cheeger lemma and the l2 Aizenman-Barsky bound.
---

Published results, imported by citation. Let `G=(V,E)` be a connected,
locally finite, quasi-transitive graph, with adjacency operator `A`,
`tau_p(u,v)=P_p(u<->v)` and `T_p` the operator with kernel `tau_p`. Put
`chi-bar_p = sup_v sum_u tau_p(v,u) = ||T_p||_(1->1)`,
`p_(q->q) = sup{p : ||T_p||_(q->q) < infinity}`, and for `0 <= p < p_c`

    iota(T_p) = 1 - sup_{K finite} sum_{u,v in K} tau_p(u,v) / (chi-bar_p |K|).

1. **Sharpness.** `||T_p||_(1->1) < infinity` iff `p < p_c`. So
   `p_c = p_(1->1) <= p_(2->2)`.
2. **The l2 Aizenman-Barsky bound.** For `q in [1,infinity]` and
   `0 <= p < p_(q->q)`,
   `||T_p||_(q->q) >= (1-p)/(||A||_(q->q) (p_(q->q)-p))`, and
   `||T_(p_(q->q))||_(q->q) = infinity`.
3. **Two-sided Cheeger bound.** For `0 < p < p_(1->1)`,
   `chi-bar_p (1-iota(T_p)) <= ||T_p||_(2->2) <= chi-bar_p sqrt(1-iota(T_p)^2)`.
4. **Criterion.** `p_c < p_(2->2)` iff
   `liminf_{p↑p_c} ((p_c-p)/(1-p)) chi-bar_p sqrt(1-iota(T_p)^2) < 1/||A||_(2->2)`.
   If this holds, then `p_c < p_u` and `nabla_(p_c) < infinity`.
