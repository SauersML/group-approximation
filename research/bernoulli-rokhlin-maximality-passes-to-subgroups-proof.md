---
rg: 2
id: bernoulli-rokhlin-maximality-passes-to-subgroups-proof
kind: route
title: Pull generating partitions back along restriction, and join transversal translates
target: bernoulli-rokhlin-maximality-passes-to-subgroups
requires: []
artifacts:
  - research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md
---

Complete direct proof, Proposition 2 of the artifact.

* **Subgroups.** Restriction `x -> x|_H` is `H`-equivariant and measure-preserving.
  The pullback of an `H`-generating partition generates every coordinate in `H`,
  and then every coordinate `x(g h) = (g^-1.x)(h)`.
* **Finite index.** Joining the translates `t.alpha` over a right transversal
  gives an `H`-generating partition of entropy at most `n H(alpha)`.
