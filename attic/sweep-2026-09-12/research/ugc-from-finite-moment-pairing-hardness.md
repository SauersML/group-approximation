---
rg: 2
id: ugc-from-finite-moment-pairing-hardness
kind: route
title: Use the existing long-code noise to replace pointwise richness by a finite density moment
target: unique-games-conjecture
requires:
  - finite-moment-pairing-2to1-hardness
  - finite-density-moments-control-noisy-tails
  - noise-test-sound-on-smooth-design-rich-inputs
artifacts:
  - research/artifacts/unique-games-finite-density-moments-2026-09-12.md
  - research/artifacts/unique-games-smooth-design-richness-2026-09-11.md
---

The September 12 artifact, Section 2, gives the proof modification; this
does not apply the old pointwise-domination theorem to an input failing
its hypotheses. It uses the audited proof of that theorem with exactly
one estimate replaced.

Fix the output error and hence noise `rho<1`, test alphabet `m`, analytic
tolerances, and `K`. Choose `q(m,rho)` from the tail theorem, then obtain
`C(m,K,q)` from the hardness hypothesis. The scalar functions in the
soundness proof are `T_rho F_(u,r)` with Boolean `F_(u,r)`. The new tail
theorem bounds their expected balanced restricted high-degree energy by
`C rho^(d+1)`. Choose `d` to make that quantity smaller than the tolerance
in the high-degree step. This replaces the only use of pointwise domination
for the actual pairing law in the audited proof.

All conditional low-degree expectations are still exact for design
strength `t=8d+1`; imbalance mass is independent of the matching law.
The influence/list rounding then fixes the needed source error `eta`.
Choose the hard alphabet above the analytic lower bound. Completeness and
soundness follow with the same reduction and final rounding. Every
parameter is fixed before invoking source hardness; there is no dependence
of `C` on `t` or `eta` and hence no circular cutoff choice.
