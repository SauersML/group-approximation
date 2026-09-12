---
rg: 2
id: leavitt-d4-rank10-n0122-is-projection-fenced-proof
kind: route
title: Exhaust 68 cancellation schemes after imposing three projections
target: leavitt-d4-rank10-n0122-is-projection-fenced
requires:
  - leavitt-d4-length12-rank10-has-15-cyclic-classes
---

The carrier reduction and boundary are those recorded for the canonical
`N(0;122)` system.  Its projections are

```text
K0=c^-1 b c^-1 a c^-1 v c,
K1=d^-1 c d^-1 b,
K2=a^-1 d a^-1 c,
K3=b^-1 p^-1 b^-1 d.
```

Set `K1=K2=K3=1`, equivalently

```text
c=a d^-1a,  b=d c^-1d,  p=b^-1d b^-1.
```

Substitution in the remaining thirteen-syllable carrier identity has exactly
68 minimal noncrossing free-product cancellation schemes.  The attached
exact enumerator performs valid single-occurrence Tietze elimination in each.
In 67 schemes `K0` freely reduces to one.  The sole residue has relations
`a^-5=a^-4=a^3=a^-2=1` and target `a^7`; since `gcd(5,4)=1`, it also forces
`a=1`.  This exhausts every normal-form branch and proves the projection fence
without a coefficient-library assumption.
