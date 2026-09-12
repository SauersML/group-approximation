---
rg: 2
id: linear-invariant-output-augmentation-proof
kind: route
title: Take augmentations of the scalar decoder identity
target: linear-invariant-output-automata-fail-augmentation
requires: [central-c3-quadratic-surjunctivity-iff-direct-finiteness]
artifacts:
  - research/artifacts/gottschalk-sofic-radical-localization-2026-09-11.md
---

The prerequisite supplies the scalar duality: `tau_a` is injective iff
`c a = 1` for some `c`. Its proof, equation (10) there, does not depend on the
group or on the central three-cycle.

- Right invariance of the output is `ha = a`.
- If `p` divides `|H|`, `eps(a) = 0` and `eps(c)eps(a) = 1` is impossible.
- Otherwise `ha = a` for all `h` iff `a = ea`, and `1` cannot lie in `e k[G]`
  unless `H = 1`.
