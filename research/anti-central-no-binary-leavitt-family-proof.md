---
rg: 2
id: anti-central-no-binary-leavitt-family-proof
kind: route
title: Take canonical traces of the Leavitt relations in the anti-central summand
target: anti-central-ternary-summand-has-no-binary-leavitt-family
requires: []
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/ternary-anti-central-cohn-reformulation-2026-09-12.md
---

Proposition 2.5 of the artifact.

- **Traces.** `tau_C([g][h]) = [gh in C] = [hg in C]`, because `hg = h (gh) h^-1`. So every class
  trace is a trace on `S`, and hence on its direct factor `S_-`. `tau(1_-) = tau(2[1] - 2[z]) = 2`.
- **Leavitt families.** `tau(1_-) = sum_j tau(sigma_j tau_j) = sum_j tau(tau_j sigma_j) = n tau(1_-)`, so
  `2(n - 1) = 0` in `F_3`.
- **Cohn defects.** `tau_C(1_- - sigma_1 tau_1 - sigma_2 tau_2) = tau_C(1_-) - 2 tau_C(1_-)`.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 15 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
