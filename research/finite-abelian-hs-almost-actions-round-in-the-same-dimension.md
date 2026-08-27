---
rg: 2
id: finite-abelian-hs-almost-actions-round-in-the-same-dimension
kind: claim
title: Finite abelian HS almost-actions round in the same dimension
distinct_from:
  finite-schur-clifford-packet-flexible-hs-exactification: that permits a flexible dimension change for one fixed finite packet; this removes the dimension change for arbitrary finite abelian groups.
  same-basis-rounding-interface-for-sparse-weyl-sampler: that additionally asks for a bounded-template occurrence test producing the all-pairs hypothesis.
---

ESTABLISHED.  There are universal constants `epsilon_0,C>0` such that the
following holds for every finite abelian group `A`, every `d`, and every map
`f:A->U(d)`.  If

```text
max_(x,y in A) ||f(x)f(y)-f(xy)||_(2,d) <= epsilon <= epsilon_0,
```

then there is an exact unitary representation

```text
pi:A->U(d)
```

in the **same matrix dimension** satisfying

```text
max_x ||f(x)-pi(x)||_(2,d) <= C sqrt(epsilon).                 (FA1)
```

The exponent `1/2` is sufficient for the occurrence compiler.  No constant
depends on `|A|`, `d`, or the irreducible multiplicities.

The dimension-flexibility in the general Gowers--Hatami theorem is therefore
not an analytic obstruction for either same-basis additive group
`A=F_2^n`: all irreducibles of an abelian group are one-dimensional, and the
small dimension discrepancy can be repaired after an invariant-subspace
rounding.  What remains open in
`same-basis-rounding-interface-for-sparse-weyl-sampler` is producing the
all-pairs almost-action estimate from bounded-template occurrence tests
without equality fibers.
