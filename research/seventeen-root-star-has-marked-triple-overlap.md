---
rg: 2
id: seventeen-root-star-has-marked-triple-overlap
kind: claim
title: The rank-twenty root star has prescribed marked triple overlap
artifacts:
  - research/seventeen-root-star-overlap-proof.md
distinct_from:
  marked-copy-collision-forces-overlap-mass: that selects some colliding pair from an arbitrary supercritical projection family; Weyl two-transitivity fixing the marked root makes all ordered pairs in this seventeen-root star equidistributed and yields a lower bound for every prescribed pair.
  binary-leavitt-native-two-scale-cross-gram-positive: that needs the two unequal-scale coefficient transports; this produces a fixed common carrier for two same-coefficient root-position transports.
---

Let `q=s_1t_1` and, in a finite tracial representation of
`St_20(L_(F_2)(1,2))`, let

```text
P=(1-rho(x_13(q)))/2,
Q_i=(1-rho(x_(i,2)(q)))/2,             4<=i<=20.       (SRS1)
```

Then `P,Q_4,...,Q_20` commute.  For every prescribed set of distinct indices
in `{4,...,20}`, the following bounds hold:

```text
tau(P Q_i Q_j)             >= (7/136) tau(P),
tau(P Q_i Q_j Q_k)         >= (11/1360) tau(P),
tau(P Q_i Q_j Q_k Q_l)     >= (1/1190) tau(P),
tau(P Q_i Q_j Q_k Q_l Q_m) >= (1/24752) tau(P).        (SRS2)
```

For operator-norm asymptotic matrix representations, the same bound holds
with an `o(1)` loss after rounding the finitely many root involutions.  In
particular the joint spectral carrier of the four prescribed roots

```text
x_13(q),       x_42(q),       x_52(q),       x_62(q)
```

has normalized mass at least `(11/1360)tau(P)`.

No Property T, stability theorem, adaptive coefficient, or literature input
is used.  The theorem is a same-coefficient root-position carrier statement;
it does not identify these Weyl transports with unequal-scale Leavitt
coefficient transports.

DERIVATION
seventeen-root-star-overlap-proof
