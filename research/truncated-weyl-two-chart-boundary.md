---
rg: 2
id: truncated-weyl-two-chart-boundary
kind: claim
title: Two truncated-Weyl charts localize non-equivariance to one transverse Pauli cell
distinct_from:
  no-linear-symplectic-splitting-of-truncated-weyl-levels: that rules out a module-linear one-chart solution; this gives a two-chart replacement and computes its boundary exactly.
  finite-group-shared-overlap-polar-alignment: that aligns approximate representations on a shared finite subgroup; this identifies the exact shared subgroup and transverse cells to which such alignment should be applied.
---

In the notation of `truncated-polynomial-binary-weyl-expander-tower`, define
two `F_2`-linear embeddings

```text
P_n(a,b)=(ua,b),              Q_n(a,b)=(a,ub).                  (TWC1)
```

Both are symplectic. Their images meet in a nondegenerate symplectic space of
dimension `2(n-1)`. Inside each image the intersection has a hyperbolic
two-dimensional orthogonal complement. Thus the two level-`n` packet charts
share exactly `n-1` Pauli qubits and each carries one different transverse
boundary qubit.

The coordinate swap `F(a,b)=(b,a)` exchanges the charts exactly:

```text
F P_n(a,b)=Q_n(b,a).                                           (TWC2)
```

For the elementary upper and lower transformations

```text
E_r^+(a,b)=(a+rb,b),       E_r^-(a,b)=(a,b+ra),
```

one has the exact covariance laws

```text
E_r^+ Q_n = Q_n E_(ur)^+,
E_r^- P_n = P_n E_(ur)^-.                                     (TWC3)
```

Consequently the failure of a single equivariant nesting is not spread over
the old prefix: it is a one-cell chart transition plus the explicit parameter
drift `r |-> ur`.

