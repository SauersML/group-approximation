---
rg: 2
id: infranormal-normal-profinite-closure-proof
kind: route
title: In a finite quotient a compressing conjugate of Gamma equals Gamma, so compressors normalize every K Gamma
target: infranormal-subgroups-have-normal-profinite-closure
requires: []
artifacts:
  - research/artifacts/clifford-cover-orbital-localization-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

Artifact Section 2, Lemma 2.2. For `t in P_Gamma` and `f : G -> G/K`, `f(t Gamma t^(-1))` is a subgroup of
the finite group `f(Gamma)` of the same order, so they are equal: `t (K Gamma) t^(-1) = K Gamma`. The
normalizer of `K Gamma` contains `P_Gamma`, hence `G`. Intersecting over `K` gives normality of `Gammabar`.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently, including Lemma 2.1 and the
closedness of `N` for the Theorem E pair
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 7.2).
