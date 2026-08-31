---
rg: 2
id: two-jacobson-commutators-plus-perfectness-have-finite-model
kind: claim
title: Two Jacobson commutator equations and a perfect scalar packet do not force head collapse
distinct_from:
  scalar-rephased-toeplitz-sections-still-collapse-head: that uses the common truncated-shift realization to conjugate the two endpoint transvections; this removes that realization and proves the remaining abstract identities have a finite countermodel
  jacobson-property-t-and-finite-k-do-not-exactify-the-head: that gives a general finite-window firewall; this targets exactly the proposed two-commutator-plus-perfectness argument
  qutrit-first-mixed-orientation-head-return-is-jacobson-quarter-polar: that realizes both commutators with prescribed root actors; this shows why those actor types, rather than the commutator values alone, are load-bearing
---

Let

```text
K=GL_28(F_2),                  C=x_13(1) in K.
```

There are elements `U,V,U',V'` in the finite group `K` such that

```text
[U,V]=C,                    [U',V']=1.                   (TCF1)
```

Hence the two formal endpoint words satisfy

```text
[U,V]C^(-1)=1,
C[U',V']=C!=1.                                         (TCF2)
```

In the left regular representation of `K), every scalar-packet relation
and the first endpoint relation have zero defect, while

```text
||lambda(C[U',V'])-I||_2=sqrt(2).                       (TCF3)
```

Therefore no dimension-free inequality can follow solely from:

1. exactness or perfectness of the finite scalar packet;
2. the equation `[U,V]=C); and
3. the definition of the opposite head word `C[U',V']`.

A successful arbitrary-representation argument must use additional
relations identifying `U,V,U',V'` as the prescribed elementary roots
with common raw `S/T` coefficients and their scalar conjugation orbits.
The two commutator values and perfectness alone admit an exact finite
head-retaining model.

DERIVATION
ore-commutator-countermodel-to-two-word-collapse-proof
