---
rg: 2
id: fpbs-flat-rate-from-fourier-algebra
kind: route
title: Fourier-algebra membership of the two-point function at one supercritical parameter gives the flat walk rate there
target: fpbs-flat-walk-rate-past-pc-universal
requires:
  - fpbs-two-point-in-fourier-algebra-near-pc-universal
  - fpbs-two-point-fourier-algebra-criterion
artifacts:
  - research/artifacts/fpbs/docs/fourier-algebra-two-point-2026-09-17.md
---

Hole [A] gives `p_k > p_c` with `tau_(p_k)` in `A(Gamma)`. Item 2 of
`fpbs-two-point-fourier-algebra-criterion` gives
`a_n(p_k) = sum_x mu^(*n)(x) tau_(p_k)(x) <= rho^n` for all `n`, which is
hole [F] with `p_+ = p_k`.

By item 4 of the criterion, [A] follows from `p_c < p_2` or
`p_c < p_(2->2)`. On trees, [F] and [A] have the same threshold,
`p_F = p_A = (d-1)^(-1/2)`. In general it is open whether [F] implies [A].
