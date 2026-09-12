---
rg: 2
id: sp4-spin-cover-projective-representation-computation
kind: route
title: Pull the basic spin representation of the double cover of S6 back along the odd theta characteristics and test the sign systems
target: sp4-spin-cover-projective-representation-in-dimension-four
requires: []
artifacts:
  - experiments/maslov_sector/spin_seed.py
  - experiments/maslov_sector/spin_phases.py
  - experiments/maslov_sector/RESULTS.txt
---

`spin_seed.py` verifies the affine action formula (homomorphism on all
`16 x 16` generator pairs, parity preserved), computes the permutation of the
six odd characteristics induced by each root generator, decomposes it into
transpositions, and multiplies the corresponding Clifford elements
`Gamma((e_i - e_j)/sqrt 2)` of `Cl(R^5) = M_4(C)` (gamma matrices
`sx x 1, sy x 1, sz x sx, sz x sy, sz x sz`).  `spin_phases.py` evaluates
`rho` on all `304,412` relators, records the scalar `+-1`, and performs
Gaussian elimination over `F_2` on the exponent-sum matrix against the two
target patterns (all `+1`; the universal-cover lifts mod `2`), finding both
systems inconsistent.
