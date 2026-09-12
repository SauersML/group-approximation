---
rg: 2
id: integral-unit-conjecture-from-rational-proof
kind: route
title: Trivial units over Q force trivial units over Z
target: integral-unit-conjecture-torsion-free
requires:
  - rational-unit-conjecture-torsion-free
---

Let `G` be torsion-free and let `u in Z[G]` have inverse `v in Z[G]`. Then
`u` is a unit of `Q[G]`, so by the premise `u = lambda g` with
`lambda in Q^x` and `g in G`. Since `u in Z[G]`, `lambda in Z`. Since
`v = lambda^(-1) g^(-1) in Z[G]`, `lambda^(-1) in Z`. So `lambda = +-1`.
QED

The converse needs more. By `rational-units-rescale-to-integral-units` it
holds on every group whose prime-field group rings are domains, so it holds
for all torsion-free groups if the zero-divisor conjecture holds over the
prime fields. It is not recorded as a route here, because the resulting
two-way dependency would be a cycle through an open premise.
