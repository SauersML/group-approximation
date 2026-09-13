---
rg: 2
id: odometer-matrix-tower-regular-embedding-proof
kind: route
title: Refine cyclic matrix units and match restrictions of regular finite-group actions
target: odometer-matrix-towers-host-locally-finite-groups
requires: []
artifacts:
  - research/artifacts/pestov91-universal-locally-finite-host-2026-09-13.md
---

Sections 2--4 give the direct proof. The cyclic cells define unital matrix
units `E_ab^(N)=1_(pi_N=a) u^(a-b)`. Refinement from `N` to `rN` sends
each matrix unit to the sum of its `r` diagonal copies. Flattening three
colours gives `SL_(3N)(F_2) <= EL_3(R)`, including same-colour roots via
a commutator through another colour.

For `L=union_i L_i`, choose factorial dimensions divisible by `|L_i|`.
At each stage use copies of the regular `L_i`-action. The restriction of
the next regular action and the prescribed amplification of the old one
are free `L_i`-sets of the same cardinality. An equivariant bijection
conjugates the next embedding to extend the old embedding exactly.
Their union is faithful. Linear extension is faithful on group algebras
because regular representations detect every coefficient.
