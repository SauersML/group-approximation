---
rg: 2
id: higman-collapse-via-power-uniform-upgrade
kind: route
title: Upgrade the relator defect to the power-uniform defect around the cycle, then collapse the glued exact cycle
target: higman-four-cycle-intrinsic-mf-seed
requires:
  - bs12-conjugator-correction-is-power-uniform-defect
  - higman-tuples-are-near-power-uniform-tuples
  - higman-exact-packet-cycles-collapse-opnorm
---

Item 3(c) of `bs12-conjugator-correction-is-power-uniform-defect` proves
`(PUU)+(CGC) => (HMF5)`, where

- `(PUU)` is `higman-tuples-are-near-power-uniform-tuples`;
- `(CGC)` is `higman-exact-packet-cycles-collapse-opnorm`;
- `(HMF5)` is the uniform operator-norm collapse of
  `higman-four-cycle-intrinsic-mf-seed`.

This route refines `higman-collapse-via-trivially-padded-bs-correction`.

- **Both prerequisites are necessary.**  `(HMF5)` implies `(PUU)` (item 3(a))
  and `(CGC)` (item 3(d)).  So each open prerequisite can fail on its own,
  and if either fails, the target's operator-norm collapse fails.  By
  contrast, `(TPC)` of the older route can fail while `(HMF5)` holds.
- **`(PUU)` is weaker than `(TPC)`.**  `(TPC)` implies `(PUU)` (item 3(b)).
  So the older route factors through this one.
- **`(CGC)` needs no packets.**  By item 2 of the same claim, `(CGC)` is
  equivalent to `(PUC)`: four unitaries with every power-uniform seam defect
  `Delta(U_i, U_(i+1))` small are close to `1`.
