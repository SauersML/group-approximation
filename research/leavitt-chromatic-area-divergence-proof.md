---
rg: 2
id: leavitt-chromatic-area-divergence-proof
kind: route
title: Freeze one shift or cumulative column and apply centralizer-area properness
target: leavitt-chromatic-tables-have-area-divergence
requires:
  - finite-mark-centralizer-commutator-area-is-proper
  - binary-leavitt-shift-graph-has-exact-marked-commutator-table
  - binary-leavitt-cumulative-complete-graph-table
---

The shift table has one fixed vertex `(0,1)` adjacent to every `(1,k)`, and
its exact coefficient computation proves `(CLD2)`.  The cumulative table has
one fixed column `H_0`; every later cumulative row contains both of its
coordinates, so characteristic two proves `(CLD5)`.

In each case the row coefficients are distinct and remain separated modulo
the fixed column involution under the elementary matrix quotient.  Thus each
table supplies an infinite section of the centralizer modulo the marked
order-two subgroup.  Properness of finite-mark commutator filling area forces
the areas on that section to diverge, proving both assertions.
