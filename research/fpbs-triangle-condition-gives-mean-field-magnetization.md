---
rg: 2
id: fpbs-triangle-condition-gives-mean-field-magnetization
kind: claim
title: The triangle condition gives the mean-field critical magnetization bound
distinct_from:
  fpbs-nonamenability-bounds-critical-connectivity-operator: that conjectures the critical connectivity operator is bounded; this imports only the Barsky-Aizenman consequence of the weaker triangle condition, and asserts nothing about when that condition holds.
  fpbs-fibre-bubble-forces-mean-field-susceptibility: that derives a susceptibility bound below p_c from a fibre bubble; this imports the critical magnetization and volume-tail exponent under the triangle condition.
---

Published theorem, imported by citation. Let `G` be a connected, locally
finite, quasi-transitive graph and consider Bernoulli bond percolation. Put

    M_{p,h}(v) = P_{p,h}(v <-> ghost) = E_p[1 - exp(-h |K_v|)],

where the ghost field colours each vertex green independently with probability
`1-exp(-h)`. If the triangle condition

    nabla_{p_c}(v) = sum_{u,w} tau_{p_c}(v,u) tau_{p_c}(u,w) tau_{p_c}(w,v) < infinity

holds, then there is `C<infinity` with `M_{p_c,h}(v) <= C sqrt(h)` for all
`h in (0,1]` and every vertex `v`, and equivalently
`P_{p_c}(|K_v| >= n) <= C n^(-1/2)`.

Unconditionally, on every quasi-transitive graph, the lower bound
`P_{p_c}(|K_v| >= n) >= c n^(-1/2)` holds (Aizenman-Barsky), for some `c>0`.

For large `h` the bound is trivial since `M<=1`, so the asymptotic statement
`M ≍ sqrt h` as `h -> 0` gives the uniform bound on `(0,1]`.
