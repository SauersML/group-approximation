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

For `(CPM5)--(CPM6)`, restrict to a simultaneous selector sector.  If
`a=0`, then `U` commutes with both `X` and `Z`, so on a Pauli irreducible
block `U=1 tensor A_(a,b)`.  If `a=1`, then `U` commutes with `X` and
anticommutes with `Z`; multiplying by `X` puts it in the Pauli commutant,
so `U=X tensor A_(a,b)`.  The same argument with `X,Z` interchanged gives
`V=Z^b tensor B_(a,b)`.  The involution relations make the external factors
involutions.  Therefore

```text
[U,V]=X^a Z^b X^a Z^b tensor
       A_(a,b) B_(a,b) A_(a,b) B_(a,b)
     =J^(ab) tensor [A_(a,b),B_(a,b)].
```

Finally, if `[G,H]=1`, then `T=GH` is an involution and its negative sector
is exactly payload disagreement.  This proves the claimed conditional
selector-gated-equality interpretation.
