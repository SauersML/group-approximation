---
rg: 2
id: single-maximal-stage-routed-codes-proof
kind: route
title: Routing is a measure-preserving bijection, so the combining stage is injective, descends to its window subgroup, and meets maximality
target: single-maximal-stage-routed-codes-cannot-compress
requires:
  - measurable-certificate-routing-preserves-bernoulli-measure
  - bernoulli-codes-descend-to-window-subgroup
  - sofic-radical-localizes-bernoulli-deficit-witnesses
artifacts:
  - research/artifacts/defect-coupled-routed-codes-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

Section 2 of the artifact.

1. Theorem A makes `R_1` measure preserving; with Lusin–Souslin its image of the injectivity set is
   conull.
2. So the combining stage `S` is injective on a conull set for the uniform measure.
3. Descent gives an almost everywhere injective code over `K` into `E` symbols.
4. Proposition 1 of the compression artifact over `K`, together with maximality, gives
   `|E| >= |A|`. If `K` is finite, injectivity on a finite uniform space does it directly.
5. `|B| = |E|`. Sofic groups are Rokhlin-maximal by the Sofic-groups consequence of the localization
   theorem.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently, including the
Lusin–Souslin conull image, descent for Borel `f` on `A^K`, and the finite-`K` case
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 2.1).
