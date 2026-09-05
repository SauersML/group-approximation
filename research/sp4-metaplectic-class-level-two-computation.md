---
rg: 2
id: sp4-metaplectic-class-level-two-computation
kind: route
title: Realize the three pullback classes explicitly and test each sign system against the universal-cover lift pattern
target: sp4-metaplectic-class-is-not-inflated-from-level-two
requires: []
artifacts:
  - experiments/maslov_sector/spin_seed.py
  - experiments/maslov_sector/RESULTS.txt
---

The script `twist_test` step recorded in `RESULTS.txt` takes the spin seed
`rho`, the parities of the eight generator permutations (all odd), and forms
the three projective representations `rho`, `i^{sign} rho`, and `i^{sign} I`.
Each is checked to be scalar on the twenty lifted relators and on `20,000`
sampled relators, and for each the `F_2` system in the eight generator signs
with right-hand side the relator scalar plus the lift exponent mod two is
reduced by Gaussian elimination and found inconsistent.  The three classes
are the whole of `H^2(S_6; Z/2) minus 0`, so the metaplectic class is not
inflated from level two.
