---
rg: 2
id: fpbs-positive-higher-l2-betti-via-filling-density
kind: route
title: Compress beta_k onto the unique cluster and contradict it with a cheap near-critical filling
target: fpbs-bs-positive-higher-l2-betti
requires:
  - fpbs-unique-cluster-forces-higher-filling-density
  - fpbs-near-critical-cluster-filling-density-vanishes
  - fpbs-nonuniqueness-parameter-criterion
---

Fix a Cayley graph `G` of `Gamma` and `k >= 2` with `beta_k^(2)(Gamma) > 0`.
`Gamma` is nonamenable, since infinite amenable groups have all
`beta_k = 0` ([G02, Corollaire 0.1]).

1. By `fpbs-near-critical-cluster-filling-density-vanishes` (H_k), there is
   some `p > p_c` with `F_k(p) < (k+1) beta_k(Gamma)`.
2. Bernoulli percolation at `p` is a free p.m.p. action and has infinite
   clusters. If it had a.s. a unique infinite cluster, then
   `fpbs-unique-cluster-forces-higher-filling-density` would give
   `F_k(p) >= (k+1) beta_k(Gamma)`, a contradiction.
   - The admissible classes agree: under uniqueness, "each component is one
     infinite cluster" means the single component `K_inf`.
3. By ergodicity, the number of infinite clusters at `p` is a.s. constant,
   and it is in `{1, infinity}` (Newman-Schulman). So it is `infinity`.
   `fpbs-nonuniqueness-parameter-criterion` then gives `p_c < p_u`.

**Independent failure points.**

- Step 1 is the hole H_k. It can fail even if `p_c < p_u`.
- Step 2 is established.
- Step 3 is standard and established.

The route is complete exactly when H_k is proved. It is useful only for
`k >= 2`: for `k = 1`, H_1 is automatic and the route recovers the known
theorem `beta_1 > 0 => p_c < p_u`.
