---
rg: 2
id: q-masa-scale-conservation-proof
kind: route
title: Count one-dimensional q-characters on both sides of the overlap
target: q-masa-selector-bridge-is-scale-conservation
requires:
  - full-q-masa-forgets-selectors-retains-branches
  - finite-graph-of-groups-representation-types-are-integer-flows
---

Because `K` is abelian, restriction of any `D_t`-dimensional old simple is a
direct sum of exactly `D_t` one-dimensional characters, with repetitions
allowed.  A fresh packet simple over a fixed central selector character is
`D_s`-dimensional and restricts as `D_s` copies of that character.  Equality
of the complete `K`-type vectors across an amalgam edge implies equality
after applying the all-ones functional.  This is `(QSC1)`.

Multiplying the two simple counts by their respective dimensions and
normalizing by the common ambient dimension gives `(QSC2)`.  Along a chain,
the intermediate dimensions cancel pairwise, so any unweighted multiplicity
gain is precisely the reciprocal matrix-scale loss.  This is the scalar
dimension coordinate of the general positive integer-flow theorem, now
computed for the proposed flip-free endpoint.
