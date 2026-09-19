---
rg: 2
id: cyclic-character-orbit-gap-proof
kind: route
title: Put an exact p-th root arbitrarily close to minus one
target: cyclic-character-orbit-pressure-has-vanishing-hs-gap
requires: []
---

For odd `p`, `(p+1)/2` is an integer, so the scalar in `(CCO2)` is a `p`-th
root of unity:

```text
lambda_p^p=exp(pi i (p+1))=1.
```

Since `lambda_p=-exp(pi i/p)`, its distance from `1` tends to `2`.  With
`t=1`, evaluation of the second relator gives

```text
t a t^(-1)a^(-3)=lambda_p^(-2)=exp(-2 pi i/p),
```

whose distance from `1` is exactly `2 sin(pi/p)`.  In dimension one the
normalized Hilbert--Schmidt norm is absolute value, proving `(CCO3)`.

Tensoring this scalar assignment by an identity matrix preserves both
numbers, so amplification cannot restore a constant gap.  The construction
does not assert that the presented group has a particular exact character
orbit size; it proves the narrower and load-bearing point that the displayed
relations used to certify such an orbit do not robustly pin the marked phase.
