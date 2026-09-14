---
rg: 2
id: stw07-qd-trace-positive-class-proof
kind: route
title: Model values are trace values, and finite-dimensional partial isometries have index zero
target: stw07-qd-trace-positive-class-kills-qd-extension
requires: []
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

Full proof in Sections 1--2 of the artifact.

- Lemma 1: compress a model to the spectral projection of `phi_n(1)`.  Its
  trace states are asymptotically tracial, their cluster points are
  quasidiagonal traces by definition, and ranks satisfy
  `(phi_n)_*(x) = k_n(omega_n(x^)+o(1))`.
- Positivity: a subsequence with nonpositive values has a quasidiagonal
  cluster trace with `x^ <= 0`.
- Stable finiteness of `E`: an isometry defect projection `p` has
  `-[p] in Zx cap K_0^+`, hence `[p]=0` and `p=0`.
- Nonquasidiagonality: a faithful unital model of `E` gives value `0` on the
  index class, while its corner restriction to `A tensor e_11` is a nonzero
  model of `A`, whose value must be positive.
- Existence of the extension with prescribed index uses the UCT for `C(T)`.
