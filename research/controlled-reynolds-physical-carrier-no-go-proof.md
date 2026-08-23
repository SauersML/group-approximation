---
rg: 2
id: controlled-reynolds-physical-carrier-no-go-proof
kind: route
title: Compare affine physical traces with the quadratic orientation multiplicities
target: controlled-reynolds-density-has-no-fixed-physical-carrier
requires:
  - controlled-fine-reflection-superrank-orientation-law
  - balanced-controlled-whitehead-return-checksum
---

For `rho_+` and `rho_-`, formula `(CFS4)` has one orientation multiplicity
equal to one and the other zero, so `mu^2=1` and `c_G=1/16`.  Their direct
sum has `k_+=k_-=1`, hence `mu=0` and `c_G=1/32`.  This proves `(CRD3)`.

Evaluation of a fixed matrix-valued group-algebra element commutes with
direct sums.  The normalized trace of two equal-dimensional blocks is their
arithmetic mean, proving `(CRD4)`.  If all three errors in `(CRD5)` were
strictly below `1/64`, `(CRD4)` would be simultaneously strictly within
`1/64` of both `1/16` and `1/32`, contradicting the distance `1/32` between
those numbers.

For an ordinary word `w`,

```text
||w(rho_+ direct_sum rho_-)-I||_2^2
 =1/2 ||w(rho_+)-I||_2^2
  +1/2 ||w(rho_-)-I||_2^2.
```

Finite nonnegative sums obey the same identity.  Thus no collection of rows
which vanishes on both orientation extensions can charge their balanced
direct sum, completing the stated extension-selection consequence.
