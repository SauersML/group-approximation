---
rg: 2
id: nonhyperlinear-from-computable-bcv-halt-readable-bound
kind: route
title: Closed route from a computable BCV HALT readable bound
target: non-hyperlinear-group
requires:
  - bcv-halt-completeness-has-computable-readable-factor-bound
  - computable-bcv-halt-bound-diagonalizes-to-finite-readable-gap
  - finite-readable-translate-algebra-groupifies-zpc-gap
  - mikaelian-explicit-higman-embedding
  - local-approximation-properties-are-marked-closed
---

**CLOSED ROUTE.** The first prerequisite is false.
`bcv-no-computable-perfect-halt-readable-bound` proves that no total
computable machine-description bound can control even the smallest
readable algebra among perfect strategies of the halting BCV games.

Had that premise held, the remainder of the route would have been valid:
bounded diagonalization would have supplied a finite-readable NONHALT gap,
finite-readable groupification would have produced a finitely presented
nonhyperlinear stabilizer quotient, and the universal-host embedding would
have put it in the fixed host. But a false antecedent supplies none of those
objects.

Accordingly this node is not evidence that the target is proved. It records
a definitively eliminated strategy for reaching
`non-hyperlinear-group`; a different source of a finite-readable gap or a
different groupification mechanism is still required.
