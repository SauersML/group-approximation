---
rg: 2
id: local-source-gauge-shadow-reselection-proof
kind: route
title: Compare both shadows at the common output index
target: local-source-gauge-is-coherent-shadow-reselection
requires:
  - relation-defects-obey-permutation-gauge-law
---

Fix one label and suppress it from the notation.

## A local correction gives a new shadow

Let `tau=sigma c`. If `i` is correction-good and `c(i)` is
`sigma`-shadow-good, then

```text
d(x_(tau(i)),U x_i)
 = d(x_(sigma(c(i))),U x_i)
 <= d(x_(sigma(c(i))),U x_(c(i)))
    +d(U x_(c(i)),U x_i)
 <= rho+lambda.
```

Because `c` is a permutation, the inverse image under `c` of the
`sigma`-bad set has the same cardinality. The union bound gives bad density
at most `eta+theta`.

## A second shadow gives a local correction

Conversely let `tau` be a `rho'`-shadow and set
`c=sigma^(-1)tau`. Then `sigma(c(i))=tau(i)`. If `i` is
`tau`-shadow-good and `c(i)` is `sigma`-shadow-good, isometry of `U`
gives

```text
d(x_(c(i)),x_i)
 = d(U x_(c(i)),U x_i)
 <= d(U x_(c(i)),x_(sigma(c(i))))
    +d(x_(tau(i)),U x_i)
 <= rho+rho'.
```

Again the exceptional density is at most `eta+eta'`.

## Relations

By construction `tau_s=sigma_s c_s`. The exact permutation gauge law
rewrites

```text
tau_g tau_h tau_k^(-1)
```

as the corresponding defect expression in `c_g,c_h,c_k`. Hence the two
expressions agree with the identity on exactly the same indices, and their
Hamming errors coincide.

Applying these estimates label by label proves all three clauses and the
quantitative equivalence.
