---
rg: 2
id: finite-orbital-checksum-no-go-proof
kind: route
title: Keep unchecked double cosets noncommuting in an invariant graph product
target: finite-orbital-checksum-cannot-expose-sl3-coset-module
requires:
  - wreath-presentation-double-coset-obstruction
---

A finite list of prototype commutators selects finitely many double cosets.
Put an edge precisely on those diagonal orbitals and take the graph product
of vertex `C_2` groups.  Its semidirect product by the actor satisfies every
selected relation, while vertex lamps in an omitted orbital remain
noncommuting.  More generally, if finitely many words valid in the abelian
lamp quotient implied every missing commutator, they would finitely present
that quotient, contradicting the infinite-double-coset wreath obstruction.
