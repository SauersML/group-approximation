---
rg: 2
id: atlas-fourteen-edge-core-has-no-collision-to-c6-path-proof
kind: route
title: Separate the two packet rectangles and localize every collision letter
target: atlas-fourteen-edge-core-has-no-collision-to-c6-path
requires:
  - atlas-a4-rank-three-core
  - atlas-a4-19243-s3xs3-localization
  - atlas-two-holonomy-endpoint-localization
  - unitary-k2m-rectangle-synchronization
  - atlas-common-u-c3-compression-is-two-covariance-residuals
---

`atlas-a4-rank-three-core` computes the retained incidence graph exactly as
two disjoint copies of `K_(2,2)`, generated respectively by `H_6` and `K`.
`atlas-a4-19243-s3xs3-localization` places all four second-chart collision
syllables in `K` and none in `H_6`.  The endpoint audit further shows that
the repeated collision involution `b_0` is not among the packet vertices.
This proves the graph-theoretic no-path assertion.

Apply `unitary-k2m-rectangle-synchronization` separately to the two connected
components.  A `K_(2,2)` has one fundamental rectangle, so spanning-tree
gauge fixing leaves exactly one based loop in each component.  Gauge choices
on the two components are independent, and concatenating based loops cannot
create an open path between disconnected vertex sets.  Hence no edge-message
telescope can contain both `a` and `b_0`, as each residual in
`(A4-NOPATH-2)` necessarily does.

The shared literal `U` is not an incidence edge and may not be replaced by
the independently chosen factorization witnesses.  Thus this argument does
not infer failure of the common-`U` estimate; it proves precisely that the
requested minimal incidence path does not exist and identifies simultaneous
double-coset intersection as the first remaining gate.
