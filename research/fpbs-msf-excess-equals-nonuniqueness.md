---
rg: 2
id: fpbs-msf-excess-equals-nonuniqueness
kind: claim
title: The free-minus-wired spanning forest excess is exactly the nonuniqueness criterion
distinct_from:
  fpbs-wired-forest-degree-two: that is about the wired uniform spanning forest of an invariant random connected subgraph and its two-ended components; this one compares the free and wired minimal spanning forests of the ambient Cayley graph and identifies their degree gap with an integrated pivotal-separation probability
artifacts:
  - research/artifacts/fpbs/responses/47_0909-191353.md
---

For a locally finite Cayley graph put delta_G = (1/2) E deg_F(o) - 1, where F is the free minimal spanning forest of independent uniform edge labels. Then delta_G = (1/2) sum over edges e at the root of the integral over p in (0,1) of P(the endpoints of e lie in different infinite clusters of the p-percolation of G minus e), and delta_G > 0 if and only if p_c(G) < p_u(G).

This restates the Benjamini-Schramm target as strict positivity of that integral for every nonamenable Cayley graph; it is a reformulation, not a reduction, and no bound on the integral is proved. It also separates the two goals: fixed price concerns an infimum over generating graphings of one action, while nonuniqueness demands a strictly positive excess in this one canonical forest law, so both can hold simultaneously.

Status records a written deduction from imported theorems, not independent validation.
