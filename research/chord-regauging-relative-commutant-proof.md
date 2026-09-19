---
rg: 2
id: chord-regauging-relative-commutant-proof
kind: route
title: Apply conditional rank matching at both chord endpoints
target: chord-regauging-is-relative-commutant-feasibility
requires:
  - sequential-marginal-holonomy-is-conditional-rank-matching
---

Assume `(CRF1)` and call its common value `Z`.  Since `U_i` and `X_i`
commute with `A_i`, so does `Z`; hence `(CRF2)` holds.  Conjugation by `U_i`
preserves every `e_(i,s)` block and gives `(CRF3)`.

Conversely, assume `(CRF2)--(CRF3)`.  Apply
`sequential-marginal-holonomy-is-conditional-rank-matching` to the minimal
projection decomposition of `A_i`.  For each `i`, the conditional rank
equalities give a unitary `U_i in A_i'` with `U_i X_i U_i^*=Z`.  This is
`(CRF1)`.

Finally `(A_0 vee A_1)'=A_0' intersect A_1'`.  If the generated algebra is
the full matrix algebra, its commutant consists only of scalars, proving the
root-block obstruction.
