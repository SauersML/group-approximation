---
rg: 2
id: no-weakly-finite-representation-from-defect-killing
kind: route
title: Killing the two-root defect in every weakly finite representation makes every one trivial
target: ternary-leavitt-units-have-no-weakly-finite-representation
requires:
  - ternary-weakly-finite-representations-kill-two-root-defect
  - weakly-finite-leavitt-representations-killing-defect-are-trivial
artifacts:
  - research/artifacts/weakly-finite-representations-of-ternary-leavitt-units-2026-09-12.md
---

Take any weakly finite representation `rho` of `G`. By the first required claim `D_rho = 0`, so by the weakly
finite defect criterion `rho` is trivial.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 38.1 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS as an implication. At `K = F_3` the defect criterion has the same host class, frame and defect `N_23 N_12` that the required killing claim sets to zero, so the two claims compose over every `rho`.*
