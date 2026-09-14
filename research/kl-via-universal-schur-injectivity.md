---
rg: 2
id: kl-via-universal-schur-injectivity
kind: route
title: Universal Schur injectivity turns any coefficient kill into a contradiction
target: kervaire-laudenbach-nonsingular-conjecture
requires: [universal-schur-injectivity-for-nonsingular-adjunctions, kl-failure-yields-a-schur-kill]
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

A violating equation over `G` with killed coefficient `a` gives, with the same
equation, a killed torus class over `G *_(<a>) (<a> x Z)`. That contradicts the
first prerequisite. This route and `universal-schur-injectivity-from-kl` form
a dependency cycle through the root. The cycle is intended: it records an
equivalence whose converse half is still open.
