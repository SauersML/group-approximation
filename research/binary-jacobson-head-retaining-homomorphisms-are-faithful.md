---
rg: 2
id: binary-jacobson-head-retaining-homomorphisms-are-faithful
kind: claim
title: Every homomorphism retaining the Jacobson head is faithful on the full elementary group
distinct_from:
  binary-jacobson-elementary-mark-is-finite-quotient-invisible: that proves finite targets kill the infinite simple finitary kernel; this proves that any target which retains one head transvection must retain every element of the ambient elementary group.
  binary-jacobson-steinberg-head-root-is-mf-invisible: that asks whether every norm-corona representation of the Steinberg cover kills the head; this identifies the exact all-or-nothing alternative for representations of its elementary quotient.
---

**ESTABLISHED.**  Let

```text
J=F_2<S,T | TS=1>,             E=EL_5(J),
Q=1-ST,                        w=x_13(Q),
L=GL_fin(N x {1,...,5},F_2).                         (JHF1)
```

Under the faithful action of `E` on five copies of the standard Jacobson
module, `L` is the infinite simple normal subgroup identified by
`binary-jacobson-elementary-mark-is-finite-quotient-invisible`.  It is
self-centralizing:

```text
C_E(L)=1.                                             (JHF2)
```

Consequently, for every group `G` and homomorphism `phi:E->G`,

```text
phi(w)!=1   ==>   phi is injective.                   (JHF3)
```

In particular, a norm-corona model of `E` retaining the head is not a
smaller marked quotient: it is a faithful operator-MF embedding of all of
`E`.  Equivalently, the head is MF-visible in `E` exactly when `E` is
operator-MF.
