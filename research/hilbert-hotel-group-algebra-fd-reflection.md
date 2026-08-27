---
rg: 2
id: hilbert-hotel-group-algebra-fd-reflection
kind: claim
title: Every all-fields finite-dimensional group-algebra reflection of the Hilbert hotel is scalar
artifacts:
  - research/hilbert-hotel-group-algebra-fd-reflection-proof.md
---

Let `H=EL_16(L_(F_2)(1,2))`.  For every field `k`, every unital algebra
homomorphism

```text
k[H] -> A,   dim_k(A)<infinity,
```

factors through augmentation `epsilon:k[H]->k`.  Consequently

```text
intersection_(dim A<infinity) ker(k[H]->A) = ker(epsilon).
```

Thus the universal finite-dimensional algebraic quotient of `k[H]` is
exactly `k`, in every characteristic.  Since `H` itself is simple, this is
already the all-fields finite-dimensional reflection of the explicit simple
Kazhdan group.
