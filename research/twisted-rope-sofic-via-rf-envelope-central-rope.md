---
rg: 2
id: twisted-rope-sofic-via-rf-envelope-central-rope
kind: route
title: Realize the twist in the residually finite envelope, then make the central rope sofic through its coset action
target: twisted-rope-sofic-once-first-rope-sofic
requires:
  - twisted-rope-is-a-central-rope-over-an-rf-envelope
  - twisted-rope-envelope-coset-action-is-sofic
artifacts:
  - research/artifacts/twisted-rope-rf-envelope-2026-09-13.md
---

Assume `Gamma_e` is sofic.

1. [[twisted-rope-envelope-coset-action-is-sofic]] makes the action
   `D_e action D_e/C_e` sofic.
2. (E6) of [[twisted-rope-is-a-central-rope-over-an-rf-envelope]] then makes
   `Omega_e` sofic. This uses (E5) and GKP Theorem 3.7, with `D_e` sofic
   because `R-hat` is residually finite.
3. `R_e` is sofic as a subgroup of `Omega_e`, by (E4).
