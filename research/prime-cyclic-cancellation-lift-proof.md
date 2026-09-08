---
rg: 2
id: prime-cyclic-cancellation-lift-proof
kind: route
title: Lift equal-product blocks through a cyclic coefficient corner and extend their lattice character
target: prime-cyclic-cancellation-lifts-force-reverse-inverses
requires: []
artifacts:
  - research/artifacts/kaplansky-prime-cyclic-cancellation-2026-09-07.md
---

The artifact gives the complete implication proof for arbitrary prime p
and arbitrary group G. Coefficient multiplicities turn BA=1 into one
identity pivot plus blocks of p equal-product occurrences.

When J survives, it has exact order p. The integral coefficient ring
Z[zeta_p][H]/(J-zeta_p) is free over Z[zeta_p] on coset representatives
of <J>. It embeds in the central character corner e C[H] e, so adjoining
the external group labels embeds it in e C[H x G] e. The p coefficients
within each block cancel by 1+zeta_p+...+zeta_p^(p-1)=0. The pivot
contributes one. Characteristic-zero direct finiteness reverses this
identity, and reduction zeta_p->1, H->1 recovers AB=1 over F_p.

An additive label on the normal closure of the unsigned relators exists
exactly when every relator identity has zero total label modulo p. This
constructs the required central extension and proves the diagram criterion.

For scalar coefficients, the same label defines a character on im(V)
exactly when it kills the full integral kernel. Smith coordinates extend
it using roots of unity of p-power order. Hadamard's inequality bounds
the relevant Smith divisibility because every column has norm at most
two, including when repeated group labels make cells share a row or
column. The characteristic-three example and its obstruction at order
three are verified algebraically in the artifact and replayed exactly.

The direct proof establishes only this stated conditional criterion and
the example. It supplies no proof that the criterion holds for all inverse
pairs and adds no Lean kernel theorem. The classical characteristic-zero
theorem is an explicit mathematical input.
