---
rg: 2
id: hamming-transports-are-soficity-proof
kind: route
title: Compose weakly sofic models with their finite actions, amplify by products, and invoke the Kun--Thom separation
target: hamming-transports-of-weak-sofic-models-are-soficity
requires: [weakly-sofic-not-sofic]
artifacts:
  - research/artifacts/weak-sofic-hamming-transport-is-soficity-2026-09-12.md
---

Sections 1--2 of the artifact.

- `x v != y v` iff `y^-1 x` moves `v`. So the Hamming distance between
  `rho_V(x)` and `rho_V(y)` is `l_V(x y^-1)`, by conjugation invariance of
  fixed-point counts.
- Only if: `rho_V o phi` is a permutation model with the displayed defect and
  separation. The diagonal action on `V^r` has `fix = fix_V^r`, which raises
  separation to `1 - (1 - c')^r` while defects grow at most `r`-fold. So the
  data give sofic approximations with any defect and separation.
- If: a sofic approximation is a weakly sofic model with `H = Sym(V)`, the
  Hamming length, and the natural action.
- Consequence: `weakly-sofic-not-sofic` gives a weakly sofic group that is not
  sofic, so that group admits no uniform transport.
- Normal fibres: `z hN = hN` iff `z` is in `N`, so `l_(H/N)` is the indicator of
  the complement of `N`.
