---
rg: 2
id: klein-level-one-splitting-is-outside-adjoint-image-proof
kind: route
title: Completeness gives mu equal to 1 while the code size shows up in mu'
target: klein-level-one-splitting-is-outside-adjoint-image
requires:
  - ternary-adjoint-image-is-balanced
artifacts:
  - research/artifacts/klein-target-balanced-invariant-2026-09-12.md
---

Completeness gives `mu(delta_C) = sum S[alpha] T[alpha] = 1`, while `mu'(delta_C) = sum T[alpha] S[alpha] = |C|`.
Similarly `mu(Psi_C) = 1` and `mu'(Psi_C) = |C|^-1`. The balanced invariant then excludes every code
size other than `1 mod 3`, including `C = {0, 1}`. Propositions 3 and 4 of the artifact. Proposition 3
also computes `rho(e_K) = delta Psi` directly as a tensor.
