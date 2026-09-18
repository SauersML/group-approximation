---
rg: 2
id: foldable-sft-via-diagonal-time-crossing-wire-tiles
kind: route
title: The diagonal-time SW layout of the minimal crossing-wire shift is corner-deterministic, free, minimal and quantum rigid
target: foldable-free-minimal-quantum-rigid-z2-sft-exists
requires:
  - sw-minimal-crossing-wire-shift-is-rigid
---

Lane route (bh-g2-fixedpoint-a, 2026-09-18). **Conditional** on the diagonal-time layout of
`sw-minimal-crossing-wire-shift-is-rigid` §2, which is designed there and not verified line by line.

That node's ground shift `Ω_SW` has four properties:
- **Free and minimal.** This is Durand–Romashchenko's mechanism, with slots as SW islands.
- **1-rigid over every field.** Crossings make the bottom and left inputs commute, and everything else is
  reached by SW face rules.
- **SW-deterministic.** `x(z) = G(x(z − e_1), x(z − e_2))`, which is corner determinism for the adjacent
  pair `u = −e_1, u' = −e_2`.
- **Causal.** Its simulated rule is causal, as the causality lemma (§1 there) requires of any SW
  fixed point.

These four properties are the target's statement. The payoff over `F_n × Z` goes through
`abht-path-folds-accept-exactly-expansive-rational-half-planes`. Over the Ã2 lattices it goes through
`a2-busemann-transplants-preserve-quantum-rigidity`, whose cone condition is SW-determinism up to a
lattice automorphism, and `busemann-transplant-minimality-is-horospherical-minimality`. The rational
spectrum of the zooms, `minimal-crossing-wire-shift-finite-factors-are-3-groups`, carries over unchanged.
