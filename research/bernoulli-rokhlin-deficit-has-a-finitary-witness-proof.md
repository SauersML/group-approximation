---
rg: 2
id: bernoulli-rokhlin-deficit-has-a-finitary-witness-proof
kind: route
title: Code the coordinate relative to translates by typical sets across copies, and approximate generators by cylinders
target: bernoulli-rokhlin-deficit-has-a-finitary-witness
requires: []
artifacts:
  - research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

Complete direct proof, Theorem 3 and Corollary 3.1 of the artifact.

* **Upper bound.** Over `k'` independent copies, record `psi` at every point.
  Also record the index of the copy-tuple of `x(1)` inside a conditional typical
  set of the tuple of `F`-translates of `psi`. The translates are read from
  neighbours, so no markers are needed. The per-copy cost tends to `Phi`.
* **Lower bound.** A generating partition nearly determines `x(1)` from finitely
  many translates. Approximating it in the Rokhlin metric by a cylinder partition
  gives a configuration with `k Phi` at most its entropy plus `eps`.
* **Colimits.** The finitely many coincidences of a witness hold at some finite
  stage of any directed system mapping to `G`, and non-coincidences are never
  created.

Independently re-derived 2026-09-12 by gk-verify-pos: PASS (Section 14 of the
verification artifact).
