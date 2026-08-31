---
rg: 2
id: stw22-finite-factor-two-sphere-dichotomy-proof
kind: route
title: Take the minimum of the matrix and diffuse two-sphere moduli
target: stw22-all-finite-factor-weighted-copy-uniform-s2-fillings
requires:
  - stw22-matrix-weighted-copy-uniform-s2-fillings
  - stw22-diffuse-weighted-copy-uniform-s2-fillings
  - stw22-all-finite-factor-weighted-copy-uniform-loop-fillings
artifacts:
  - research/artifacts/stw22-dim3-all-factor-bundle-breakthrough-2026-08-31.md
---

Every finite factor is either a normalized matrix algebra or a diffuse
II1 factor. This is a pointwise dichotomy; it does not require a parameter
space or a continuous choice of type.

In the matrix branch,
`stw22-matrix-weighted-copy-uniform-s2-fillings` gives the modulus

```text
rho_mat(epsilon)=epsilon_0^3/276480,
epsilon_0=min(epsilon,1).                              (AF2-4)
```

It is uniform in the matrix size, copy number, weight, and slack, and every
value is two-connected.

In the diffuse branch, the row-amplified high-low proof takes

```text
eta=(epsilon_0/12)^2,
rho_diff(epsilon)
 =sqrt(eta) rho_St,2(epsilon_0/3)/2,
rho_St,2(t)=min(t,1)^2/1000000.                        (AF2-5)
```

Since `epsilon_0<=1`, (AF2-5) equals

```text
epsilon_0^3/216000000.                                 (AF2-6)
```

It is uniform over all separable-predual II1 factors, copy numbers,
weights, and slack, and every value is two-connected.

The number in (AF2-6) is smaller than (AF2-4), so it works in both cases.
The already established path and loop moduli also work in both cases.
Taking their degreewise minima gives one equi-`LC^2` family. No type
stratification is needed: each assertion is checked inside one value with
the same numerical control.