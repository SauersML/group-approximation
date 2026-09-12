---
rg: 2
id: dyadic-root-displacement-calibration-proof
kind: route
title: Trivial summand plus regular modules of the level groups realize every displacement datum
target: dyadic-root-displacement-data-admit-trivial-plus-free-models
requires: []
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/root-displacement-rank-extraction-2026-09-12.md
---

Section 2 of the artifact.

* **The models.** At stage `i`, take `F_2^(m_i) (+) F_2[D_(k_i)]^(r_i)` with trivial proportion
  `1 - epsilon`, and let `D` act through `D_(k_i)` (the identity off it). Along `k_i -> infinity`
  this gives an exact homomorphism in the ultraproduct.
* **Displacement.** Involutions act freely on the regular part, so the displacement is
  `epsilon/2`.
* **Tuple conjugacy.** Restrictions of the regular module to elementary abelian subgroups of
  equal rank are free of equal dimension, so they are intertwined generator by generator.
* **Boolean function.** The constant function on nonzero elements meets the scalar inequalities.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 37 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
