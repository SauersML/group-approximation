---
rg: 2
id: finite-static-nemesis-core-proof
kind: route
title: Restrict canonical microstates through the embedded base
target: finite-static-nemesis-core-needs-canonical-base-embedding
requires:
  - finite-nemesis-subcover-has-a-uniform-existential-residual-gap
  - existential-fock-library-has-zero-carrier-or-regular-firewall
---

Under base injectivity, every nonidentity base word remains nonidentity in the
extension, so the canonical trace restricts exactly.  A canonical microstate
sequence of the finite extension therefore gives a point of `K_alpha`, and
its finitely many auxiliary tuples make every selected residual tend to zero,
contradicting `(FER3)`.

The free-group quotient example proves that a marked exact representation
does not imply canonical restriction.  Finally `(FSC3)` is the faithful
regular-trace sum of orthogonal equivalent projections; its approximate
finite-prefix form follows by fixed-degree Hilbert--Schmidt telescoping.

