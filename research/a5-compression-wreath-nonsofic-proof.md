---
rg: 2
id: a5-compression-wreath-nonsofic-proof
kind: route
title: Subgroup heredity from the binary Kun-Thom wreath
target: a5-compression-wreath-is-not-sofic
requires:
  - a5-wreath-contains-binary-kun-thom-wreath
  - kun-thom-nonsofic-wreath
artifacts:
  - research/artifacts/invisible-quotients-architecture-audit-2026-08-23.md
---

Subgroups of sofic groups are sofic: a sofic approximation of the ambient group
restricts to one of the subgroup, since the defining condition is a statement
about finitely many elements at a time.

The first prerequisite embeds the binary generalized wreath product
`(Z/2)^(G*/Gamma*) x| G*` into `W_(A_5)`, sitewise by an involution of `A_5`.
The second gives that this binary wreath is nonsofic, `Gamma*` being infranormal
but not normal in `G*` with both groups Kazhdan.

Contrapositive of heredity: `W_(A_5)` is not sofic.

The non-MF clause quoted in the target needs nothing from here.  It follows from
`compression-wreath-five-radicals-coincide`, which computes
`Rad_MF(W_(A_5)) = A_5^(X)`, together with the observation that an MF group has
trivial MF radical.
