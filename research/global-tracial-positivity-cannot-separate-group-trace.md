---
rg: 2
id: global-tracial-positivity-cannot-separate-group-trace
kind: claim
title: Universal tracial positivity cannot certify a matricial separator that fails in a group trace
artifacts:
  - research/artifacts/nonhyperlinear-random-presentation-and-matricial-separator-2026-08-18.md
---

Let `Gamma=<S|R>` be any group and let `P` be a self-adjoint trace polynomial
in the generators.  If the canonical group trace satisfies

```text
tau_Gamma(P(lambda(S))) < 0,
```

then no positivity certificate whose semantics are valid in **every** tracial
von Neumann algebra satisfying the exact relators `R` can prove `P>=0` from
those relators.

Consequently, a trace-polynomial obstruction to hyperlinearity must be
matricial-only: its matrix inequality may hold in every finite dimension (and
therefore in matrix tracial ultraproducts), but its proof cannot be a global
tracial Positivstellensatz that is sound in arbitrary tracial von Neumann
algebras.
