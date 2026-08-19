---
rg: 2
id: s3-two-generator-covariance-controls-commutant-distance
kind: claim
title: Two involution covariance defects dominate distance to the S3 commutant
---

Let `rho:S_3->U(d)` be any finite-dimensional unitary representation, let
`s,t` be involutions generating `S_3`, and equip `M_d(C)` with normalized
Hilbert--Schmidt norm.  For every unitary `U`, put

```text
a = ||U rho(s)-rho(s) U||_2,
b = ||U rho(t)-rho(t) U||_2.
```

If `C_K` is the unitary group of the commutant `rho(S_3)'`, then

```text
dist_2(U,C_K)^2 <= a^2+b^2.                           (S3-COV)
```

The constant is independent of `d`, of multiplicities in `rho`, and of the
representation type.

This is the exact finite-group exchange rate needed by the atlas: two named
covariance defects are not merely a proxy for alignment.  Their squared sum
already upper-bounds the squared distance from the relative implementer to a
genuine commuting unitary.
