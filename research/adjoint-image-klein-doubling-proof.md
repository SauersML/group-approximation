---
rg: 2
id: adjoint-image-klein-doubling-proof
kind: route
title: The amplification tensor intertwines the adjoint evaluation with its doubled version
target: adjoint-image-is-stable-under-klein-doubling
requires: []
artifacts:
  - research/artifacts/klein-target-balanced-invariant-2026-09-12.md
---

- On a group element both sides of `delta rho(g) = rho(delta(g)) delta` equal `sum_i s_i g (x) (g^-1 t_i)^op`, using `t_i delta(g) s_j = delta_ij g`.
- Both sides of `Psi rho(delta(g)) = rho(g) Psi` equal `2 sum_j g t_j (x) (s_j g^-1)^op`.
- With `rho(e_K) = delta Psi` and `Psi delta = 1`, `Theta` is multiplicative and `Psi Theta(T) delta = T`.
- The flip `sigma` is an anti-automorphism preserving the image and sends `delta^2` to `Psi^2`.

Proposition 8 and Corollary 9 of the artifact.
