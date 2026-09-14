---
rg: 2
id: full-site-entropy-from-bernoulli-rokhlin-maximality
kind: route
title: The time-zero partition of an injective automaton image generates, so maximal Rokhlin entropy bounds its entropy
target: injective-ca-images-have-full-single-site-entropy
requires:
  - bernoulli-rokhlin-entropy-maximal-for-every-group
artifacts:
  - research/artifacts/finitary-generation-single-site-criterion-2026-09-12.md
---

The partition of `A^G` by `kappa(x)(e)` generates the shift action. Its names determine `kappa(x)`, and
an automaton left inverse of `kappa` recovers `x`. Every generating partition has entropy at least the
Rokhlin entropy, which is `log |A|` by the prerequisite.
