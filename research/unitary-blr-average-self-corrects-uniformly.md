---
rg: 2
id: unitary-blr-average-self-corrects-uniformly
kind: claim
title: Average unitary BLR defect self-corrects to a uniform almost-action
---

ESTABLISHED.  Let `A` be a finite abelian group and `f:A->U(d)`.  Put

```text
delta^2=E_(a,b)||f(a)f(b)-f(a+b)||_2^2.                       (UBA1)
```

There is a unitary table `P:A->U(d)` on the same Hilbert space such that

```text
E_x||P(x)-f(x)||_2^2 <=9 delta^2,                             (UBA2)
max_(x,z)||P(x)P(z)-P(x+z)||_2 <=6 delta.                     (UBA3)
```

The constants are independent of `A,d`.  In particular a bounded-template
decoder only needs to recover **average** dense BLR energy; it need not
directly produce the all-pairs hypothesis used by same-dimension abelian HS
stability.

