---
rg: 2
id: finite-field-slicewise-extension-proof
kind: route
title: Slice a configuration along a trace-dual normal basis and apply the binary pair to each slice
target: binary-left-inverse-pairs-extend-over-every-finite-field
requires: []
artifacts:
  - research/artifacts/formalizability-by-shear-decomposition-2026-09-12.md
---

Section 3 of the artifact.
- **Normalize.** Use a constant translation to get `tau(0) = 0`.
- **Slice.** Take a normal basis `beta_j` with trace-dual basis `gamma_j`, which is normal with
  `gamma_j^2 = gamma_(j+1)`. Put `x^(j) = Tr(gamma_j x)` and `tau_k(x) = Sum_j tau(x^(j)) beta_j`.
- **Boolean points.** `x^(j) = x·Tr(gamma_j)`, and `Sum_j Tr(gamma_j) beta_j = 1`, so `tau_k` extends
  `tau`.
- **Left inverse.** The slices of `tau_k(x)` are `tau(x^(j))`, so `sigma_k tau_k = id`.
- **Frobenius.** Squaring shifts the slices cyclically.
- **Formality.** The polynomial criterion is that a nonzero polynomial of degree `d` does not vanish
  on all `F_(2^k)`-points once `2^k > d`.
