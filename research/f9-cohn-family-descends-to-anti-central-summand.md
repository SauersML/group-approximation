---
rg: 2
id: f9-cohn-family-descends-to-anti-central-summand
kind: route
title: Regular representation of F_9 followed by the matrix-ring embedding carries F_9 Cohn families into S_-
target: ternary-anti-central-summand-has-cohn-family
requires:
  - ternary-anti-central-cohn-family-over-f9
  - anti-central-ternary-summand-contains-its-matrix-ring
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/f9-hadamard-spectral-cohn-attempt-2026-09-12.md
---

Theorem 1.1 of the artifact.
- `rho(a + b i) = [[a, -b], [b, a]]` is a unital ring embedding `F_9 -> M_2(F_3)`.
- `rho (x) id` maps `F_9 (x) S_- = S_-^(9)` unitally into `M_2(S_-)`.
- The unital injective homomorphism `J : M_2(S_-) -> S_-` from the matrix-ring claim finishes the
  composite `Phi`.
- A unital ring homomorphism sends `tau_i sigma_j = delta_ij 1` to the same identities.

This route and `anti-central-cohn-family-extends-to-f9` form an intended equivalence cycle.

*Verification by `w3-vf-linear` (2026-09-12), Section 6.1 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: valid. rho(i)^2 = -I, and rho (x) id and J are unital.*
