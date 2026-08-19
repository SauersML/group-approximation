---
rg: 2
id: a4-alternating-projections-amplify-line-carrier-proof
kind: route
title: The two principal-angle eigenvalues power to one and three to the minus m
target: a4-alternating-projections-amplify-line-carrier
requires:
  - a4-regular-line-sector-spectral-split
  - a4-line-carriers-explicit-idempotents
---

By `a4-regular-line-sector-spectral-split`, on the range of `P=P_chi` the
positive contraction `PQP` acts by eigenvalue `1` on the line carrier `E` and
by eigenvalue `1/3` on the complementary three-dimensional-irrep contribution.
The explicit-idempotent theorem identifies the first eigenspace with `E` and
shows `E<=P`.  Hence the two spectral projections inside `P` are exactly `E`
and `P-E`, giving

```text
PQP = E + (1/3)(P-E).
```

They are orthogonal projections, so powers are termwise:

```text
(PQP)^m = E + 3^(-m)(P-E).
```

The operator-norm error is therefore `3^(-m)`.  For normalized Hilbert--Schmidt
norm, regularity gives

```text
tau(P)=1/3,
tau(E)=1/12,
tau(P-E)=1/4.
```

Thus

```text
||(PQP)^m-E||_2^2
 = 3^(-2m) tau(P-E)
 = 1/(4*9^m).
```

All traces are normalized and unchanged by regular amplification, so both
bounds are independent of external multiplicity.