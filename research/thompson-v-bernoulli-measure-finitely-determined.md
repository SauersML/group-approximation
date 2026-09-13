---
rg: 2
id: thompson-v-bernoulli-measure-finitely-determined
kind: claim
title: Some nontrivial finite-alphabet Bernoulli measure over Thompson's V is finitely determined in the d-bar sense
distinct_from:
  thompson-v-bernoulli-finitely-determined-iff-pos: that proves this open claim equivalent to POS(V); this is the open d-bar statement itself.
  seward-bernoulli-measures-finitely-determined-under-rbs: that is Seward's theorem over every group under full Bernoulli Rokhlin entropy; this asks for the conclusion over V without that hypothesis.
---

**OPEN.** There are a finite set `L` and a probability vector `λ` on `L`, not a point mass, such that `λ^V` is
finitely determined in the sense of `seward-bernoulli-measures-finitely-determined-under-rbs`.

By `thompson-v-bernoulli-finitely-determined-iff-pos` this is equivalent to POS(V), and it gives POS(V) through
route `thompson-v-positive-rokhlin-from-finite-determination`.

## Attempts

- **d-bar continuity without entropy.** Dead. The Gaussian action `X` of
  `thompson-v-has-a-rigid-free-ergodic-action` is rigid. By Seward–Tucker-Drob (item S1 of
  `research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md`), `X` has free factors of arbitrarily
  small Rokhlin entropy, and factors of a rigid ergodic action are rigid and ergodic. Take one, `Y`, with
  `h^Rok(Y) < H(λ)`. Its shift models converge weak* to `λ^V`
  (`rokhlin-entropy-is-the-bernoulli-approximation-threshold`), but they stay at d-bar distance at least
  `(1 − Σ_l λ(l)^2)/2` (`rigid-actions-have-no-dbar-close-bernoulli-models`). So, whatever the supremum, d-bar
  is not weak*-continuous at `λ^V` among all essentially free measures. A proof must use the entropy window
  `|h_G(L^V, ν) − h_G(L^V, λ^V)| < δ` in the definition.
- **Using the entropy window.** Circular so far. Seward's proof of Corollary 1.6 feeds the window to the
  perturbative factor theorem, which needs `h_G(L^V, λ^V) = H(λ)`. That equality is RBS(V), equivalent to POS(V)
  by the dichotomy. Any other use of the window needs a lower bound on `h_G(L^V, λ^V)`.
- **Where it dies.** No d-bar estimate for measures near `λ^V` is known that does not pass through a lower bound
  for Rokhlin entropy over `V`.
