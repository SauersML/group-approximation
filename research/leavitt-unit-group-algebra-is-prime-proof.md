---
rg: 2
id: leavitt-unit-group-algebra-is-prime-proof
kind: route
title: Feed the group into Connell's criterion
target: leavitt-unit-group-algebra-is-prime
requires: [leavitt-unit-group-has-no-finite-normal-subgroup, connell-group-ring-primality]
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
---

## Direct proof

`F_2` is a field, hence a prime ring.  `G = L_(F_2)(1,2)^x` has no nontrivial
finite normal subgroup, by the first prerequisite.  Connell's criterion, the
second prerequisite, gives that `F_2[G]` is prime.

## The version that uses less

The first prerequisite also delivers `Delta(G) = 1`: every finite conjugacy
class of `G` is a singleton, because `G` has no proper finite-index subgroup
and therefore no proper finite-index centralizer.  For that hypothesis the
Delta-method argument is direct and does not need the full criterion — the
annihilator of a nonzero ideal in `K[G]` is controlled by the finite conjugacy
classes, and there are none.  So a reader who wants to drop
`connell-group-ring-primality` from the trust surface can, at the cost of one
page; the import is kept because it is the form the literature states.

The same input gives `Z(S) = F_2[Z(G)] = F_2`, since the center of a group
algebra is spanned by the finite class sums.
