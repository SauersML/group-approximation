---
rg: 2
id: controlled-pauli-and-commutator-proof
kind: route
title: Decompose into four control sectors and tensor-factor the group commutator
target: controlled-pauli-commutator-is-and-times-multiplicity-commutator
requires: []
---

The four projections

```text
(1-P)(1-Q), (1-P)Q, P(1-Q), PQ
```

are orthogonal and sum to one.  Both controlled gates preserve them.  On the
first three sectors at least one gate is the identity, so the commutator is
one.  On `PQ` the gates are `X` and `Z`, whose commutator is `J`.  Summing the
four restrictions proves `(CPM2)`.

For `(CPM4)`, expand the definition of the group commutator and use
`(A tensor B)^(-1)=A^(-1) tensor B^(-1)`.  If `R=T`, then
`[R,T]=I`; the same holds whenever `R` and `T` commute.
