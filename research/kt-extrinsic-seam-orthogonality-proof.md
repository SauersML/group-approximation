---
rg: 2
id: kt-extrinsic-seam-orthogonality-proof
kind: route
title: Project an ambient corrector onto the internal seam representation
target: kt-extrinsic-seam-correctors-are-orthogonal-to-the-afp-paste
requires:
  - kt-internal-c-seam-has-a-kazhdan-gap
  - kt-canonical-afp-seam-has-no-internal-gauge-correction
---

Let `y=E_M(z)`.  Since conditional expectation is `M`-bimodular,

```text
||y v_gamma-rho_gamma y||_2
 <=||z v_gamma-rho_gamma z||_2.                         (KEP1)
```

Because `z` commutes with `R`, bimodularity also gives `y in R' cap M=L(N)`.
Apply `(KIG1)` to `y` and `(KEP1)` to obtain
`kappa||y||_2<=delta`.  This is the first inequality in `(KEO3)`.
Conditional expectation is the orthogonal projection from `L^2(D)` onto
`L^2(M)`, and `||z||_2=1`, so

```text
dist_2(z,M)^2=1-||E_M(z)||_2^2,
```

which proves the second.  For an exact corrector `delta=0`, giving `(KEO2)`.
