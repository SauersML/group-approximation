---
rg: 2
id: one-depth-two-cross-whitehead-return-enumeration
kind: route
title: Prefilter all depth-two monomials by the exposed Hecke row and verify the full signed signature
target: one-depth-two-monomial-does-not-return-cross-whitehead
requires:
  - one-depth-one-occurrence-does-not-return-cross-whitehead
  - individual-cross-whiteheads-miss-native-hecke-target
---

Use the faithful prefix-replacement normal form and the exact `8192`-element
signed table for `(L_0,lambda_0)` from the depth-one audit.  Enumerate the
`48` pairs `(mu,nu)` in `(DTM1)`.  At every oriented root position, form the
elementary word `(DTM2)` and the uniquely reverse-matched word `(DTM3)`.

For each relative word `g=LK_i` or `g=J_1^(-1)LK_i`, first compute

```text
g^(-1)x_28(1)g.                                       (DTMP1)
```

Reject it unless the resulting exact Leavitt matrix is constant, belongs to
`L_0`, and has the positive `lambda_0` sign of `x_28(1)`.  The surviving
counts are exactly `(DTM7)`.  For every survivor, apply the identical
membership-and-sign test to the remaining nine generators of `L_0`.

The deterministic MSI artifact asserts the menu size `4032`, total count
`16128`, and the result table `(DTM7)`.  It evaluates both source spellings
as the same matrix `K_i` and their product with `K_i` as the identity.  This
proves `(DTM4)--(DTM8)` with no probabilistic or truncated-algebra step.
