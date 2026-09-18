---
rg: 2
id: kl-holds-over-thompson-v-via-unbounded-unitary-width
kind: route
title: Unbounded compact unitary relator width makes every nonsingular coefficient map over V injective
target: kl-holds-over-thompson-v
requires:
  - thompson-v-has-unbounded-compact-unitary-relator-width
  - kl-kernel-lies-in-the-compact-unitary-width-radical
---

Let `w in V * <t>` have nonzero `t`-exponent sum, and let `a in V` die in `(V * <t>)/<<w>>`.

1. Part (A) of `kl-kernel-lies-in-the-compact-unitary-width-radical` gives `a in Rad_cw(V)`.
2. The first prerequisite is `Rad_cw(V) = 1`, so `a = 1`.

So the coefficient map is injective. The hypothesis is implied by hyperlinearity
(`thompson-v-unbounded-unitary-width-from-hyperlinearity`). So this route needs no more than
`thompson-v-kl-from-hyperlinearity` does.
