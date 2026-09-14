---
rg: 2
id: fpbs-pu-nonuniqueness-cannot-separate
kind: claim
title: No unique infinite cluster at p_u holds automatically under threshold collapse
invalidates:
  - fpbs-dead-pu-nonuniqueness-separates
distinct_from:
  fpbs-nonuniqueness-parameter-criterion: that reduces separation to one parameter with infinitely many infinite clusters; this shows the weaker property "not a unique infinite cluster at p_u" is implied by collapse and so cannot serve as that parameter.
---

**ESTABLISHED.** Let `G` be a connected, locally finite, nonamenable
quasi-transitive graph.

1. If `p_c(G) = p_u(G)`, then at `p_u` there is no infinite cluster, and in
   particular no *unique* infinite cluster.
2. `p_c(G) < p_u(G)` holds if and only if `theta(p_u) > 0`, where
   `theta(p) = P_p(o <-> infinity)`. The property "no unique infinite cluster
   at `p_u`" is not used in either direction.

So every theorem whose conclusion is only "no unique infinite cluster at
`p_u`" leaves threshold collapse untouched: Peres 2000, Gaboriau--Tucker-Drob
and Hutchcroft--Pan (`fpbs-pu-nonuniqueness-commuting-subgroups`), and
Lyons--Schramm for Kazhdan groups. Such a theorem separates the thresholds only
together with an infinite cluster at `p_u`, and that input alone already gives
separation. The open core for products, and for any class carrying such a
theorem, is `theta(p_u) > 0`.

DERIVATION
fpbs-pu-nonuniqueness-cannot-separate-proof
