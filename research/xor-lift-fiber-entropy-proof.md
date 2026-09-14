---
rg: 2
id: xor-lift-fiber-entropy-proof
kind: route
title: Onto window maps preserve uniformity and the global flip makes the fiber bit fair
target: xor-lift-of-bernoulli-has-positive-fiber-entropy
requires: []
artifacts:
  - research/artifacts/decoder-fiber-flip-lifts-2026-09-12.md
---

For every `m`, the map `(Z/2)^[0, m+1] -> (Z/2)^[0, m]` given by adjacent sums
is linear and onto, so it pushes uniform to uniform. Every finite marginal of
`sigma_* lambda` is therefore uniform. The involution adding `1` at every site
preserves `lambda` and satisfies `sigma(x + 1) = sigma(x)`, so the joint law of
`(x(0), sigma(x))` is invariant under `x(0) -> x(0) + 1`. The conditional law of
`x(0)` given `sigma(x)` is uniform, with entropy `log 2`. Complete direct proof.
