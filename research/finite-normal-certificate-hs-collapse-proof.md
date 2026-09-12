---
rg: 2
id: finite-normal-certificate-hs-collapse-proof
kind: route
title: Bi-invariant telescoping turns each normal certificate into a dimension-free collapse bound
target: finite-normal-certificate-hs-collapse
requires: []
---

Fix `i` and abbreviate

```text
W_i(V)
 = prod_j a_(i,j)(V) beta(V)^(eps_(i,j)) a_(i,j)(V)^*.
```

Because word evaluation is exact and every letter is unitary,

```text
r_i(V)=V(s_i)^* W_i(V).
```

The normalized Hilbert--Schmidt metric is bi-invariant, hence

```text
||V(s_i)-W_i(V)||_2
 = ||r_i(V)-1||_2
 <= eta.                                                (1)
```

For every conjugate factor, unitary invariance gives

```text
||a beta^(eps) a^*-1||_2
 = ||beta^(eps)-1||_2
 = ||beta-1||_2
 <= delta.                                              (2)
```

For unitary matrices `X_1,...,X_m`, repeated use of

```text
||XY-1||_2 <= ||X-1||_2+||Y-1||_2
```

gives the product telescoping estimate

```text
||X_1 ... X_m-1||_2 <= sum_j ||X_j-1||_2.
```

Applying it to the conjugate factors in `W_i(V)` and using `(2)`,

```text
||W_i(V)-1||_2 <= m_i delta <= M delta.                 (3)
```

Finally `(1)` and `(3)` yield

```text
||V(s_i)-1||_2 <= eta+M delta.
```

Taking the maximum over the fixed finite alphabet proves `(NG-CERT)`.
Nothing in the estimate sees the matrix dimension or the conjugator-word
lengths: conjugation is an isometry, and only the number of distinguished
normal-generator occurrences is charged.
