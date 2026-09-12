---
rg: 2
id: tester-host-positive-entropy-from-maximal-bernoulli-entropy
kind: route
title: Maximal Bernoulli Rokhlin entropy on the tester host exhibits a positive-entropy free ergodic action
target: tester-host-has-positive-rokhlin-entropy-action
requires:
  - bernoulli-rokhlin-entropy-maximal-on-fixed-tester
---

If `h^Rok_U(2^U, uniform) = log 2`, then the Bernoulli 2-shift over `U` is a free ergodic p.m.p. action of `U` with positive Rokhlin entropy. This is the trivial direction of `tester-host-pos-iff-maximal-bernoulli-rokhlin-entropy`.

It forms a deliberate cycle with `tester-host-maximal-bernoulli-entropy-from-positive-entropy`. The least fixpoint establishes neither claim.
