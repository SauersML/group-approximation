---
rg: 2
id: unrestricted-sequential-operator-mf-cardinality-proof
kind: route
title: Specialize the index-width bound to the natural numbers
target: sequential-operator-mf-continuum-cardinality-bound
requires:
  - finite-matrix-quotient-cardinality-width-bound
---

Take `J=N`.  Cardinal arithmetic gives

```text
continuum^aleph_0
 =(2^aleph_0)^aleph_0
 =2^(aleph_0*aleph_0)
 =continuum.
```

The unitary-sequence quotient used by `IsOperatorMF` is a quotient of the
corresponding product of finite unitary groups, so `(SCB1)` follows from
`finite-matrix-quotient-cardinality-width-bound`.  Injectivity of the defining
homomorphism gives the same ceiling for the source group.
