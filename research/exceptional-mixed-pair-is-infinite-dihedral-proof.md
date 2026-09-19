---
rg: 2
id: exceptional-mixed-pair-is-infinite-dihedral-proof
kind: route
title: Combine the involution relations with the grading certificate
target: exceptional-mixed-pair-is-infinite-dihedral
requires: []
artifacts:
  - notes/TRUE_MIXED_COMMUTATOR_HAS_INFINITE_ORDER.md
  - GroupApproximation/Sofic/MixedCommutatorDihedral.lean
---

The free product `C2*C2` maps onto `<g,r>`.  Every reduced word is either an
alternating word of odd length or a nonzero power of `gr` up to multiplication
by one of the generators.  An odd alternating word cannot be the identity,
since that would make one involution a power of `gr` and force `gr` to have
finite order.  A nonzero power of `gr` cannot vanish because `(gr)^2=h` has
infinite order.  Thus the quotient map is injective.  The conjugation
identities are the generic two-involution calculation checked in the cited
Lean file.
