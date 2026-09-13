---
rg: 2
id: fp-torsion-group-is-no-limit-of-non-torsion-groups-proof
kind: route
title: If the limit were finitely presented, a late stage with an element of infinite order would be isomorphic to it
target: fp-torsion-group-is-no-limit-of-non-torsion-groups
requires:
  - fp-direct-limit-of-surjections-stabilizes
---

Suppose `G` is finitely presented. By
`fp-direct-limit-of-surjections-stabilizes` there is `i_0` such that the
canonical map `H_i -> G` is an isomorphism for every `i >= i_0`. Infinitely
many stages contain an element of infinite order, so some `H_i` with
`i >= i_0` does. Its image in `G` has infinite order, contradicting that `G`
is torsion. ∎
