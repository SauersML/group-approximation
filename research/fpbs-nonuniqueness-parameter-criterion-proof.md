---
rg: 2
id: fpbs-nonuniqueness-parameter-criterion-proof
kind: route
title: Combine the trichotomy, simultaneous uniqueness and critical emptiness
target: fpbs-nonuniqueness-parameter-criterion
requires:
  - fpbs-cluster-count-trichotomy
  - fpbs-critical-no-infinite-cluster
---

Both directions use only the two imported inputs.

**(<=)** Suppose `N_infinity(p*) = +infinity` for some `p*`. By the definition
of `p_c` this forces `p* > p_c` (below `p_c` there is no infinite cluster), and
by simultaneous uniqueness (`fpbs-cluster-count-trichotomy`, part 2) it forces
`p* <= p_u` (above `p_u` the cluster is unique). Hence `p_c < p_u`.

**(=>)** Suppose `p_c < p_u` and pick any `p*` with `p_c < p* < p_u`. Then
`N_infinity(p*) != 0` because `p* > p_c` gives an infinite cluster a.s., and
`N_infinity(p*) != 1` because `p* < p_u` is below the uniqueness threshold. By
the trichotomy (`fpbs-cluster-count-trichotomy`, part 1) the only remaining
value is `N_infinity(p*) = +infinity`.

Nonamenability enters only through the inputs; the deduction itself is the
trichotomy plus the two threshold definitions. `fpbs-critical-no-infinite-cluster`
is used to place `p*` strictly above `p_c` in the degenerate discussion and to
keep the criterion aligned with the `N_infinity(p_c) = 0` normalization used
elsewhere in the region.
