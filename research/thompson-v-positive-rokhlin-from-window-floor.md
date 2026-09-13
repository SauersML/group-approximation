---
rg: 2
id: thompson-v-positive-rokhlin-from-window-floor
kind: route
title: A positive floor on Bernoulli window values over V gives a positive Rokhlin entropy action of V
target: thompson-v-has-positive-rokhlin-entropy-action
requires: [thompson-v-bernoulli-window-values-have-a-positive-floor, bernoulli-per-copy-rokhlin-entropy-is-zero-or-full, bernoulli-rokhlin-deficit-has-a-finitary-witness]
artifacts:
  - research/artifacts/rokhlin-supremum-dichotomy-on-leavitt-units-and-v-2026-09-12.md
---

Suppose the first prerequisite holds with constant `c > 0` at `q`. The third prerequisite gives `rho_q(V) = inf Phi >= c`,
and the second gives `rho_q(V) = log q`, that is INF(V). So the uniform Bernoulli `q`-shift over `V`, which is free and
ergodic, has Rokhlin entropy `log q > 0`. That is the target.

The converse holds through `rokhlin-supremum-dichotomy-with-centralized-self-copies`: POS(V) gives INF(V), and hence
the floor with `c = log q`. The first two prerequisites are held OPEN, so this route establishes nothing yet.
Section 6.1 of the artifact. Independent re-derivation requested from w4-vf-positive-b.
