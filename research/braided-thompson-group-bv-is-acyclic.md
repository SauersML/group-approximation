---
rg: 2
id: braided-thompson-group-bv-is-acyclic
kind: claim
title: The braided Thompson group bV is integrally acyclic
distinct_from:
  braided-thompson-group-bv-has-nonzero-homology: that claim is the negation of this one
---

For the Brin–Dehornoy braided Thompson group `bV`, `H_k(bV; Z) = 0` for every
`k ≥ 1`. This is the affirmative answer to Zaremsky Problem 2.9
(`zaremsky-2-09-braided-v-acyclic`).

## Attempts

- Degree one holds: `braided-thompson-group-bv-is-perfect`.
- Szymik–Wahl route: prove homological stability for the stabilization maps
  `bV_{2,r} → bV_{2,r+1}` of the braided Higman–Thompson family in all degrees,
  identify `H_*(bV)` with the homology of the base component of the `E_2` group
  completion, and show that group completion is contractible. The heuristic
  model is the reduced homotopy coequalizer of the degree-one and degree-two
  self-maps of `S^2`, which is contractible. Not yet a proof: the braided
  monoidal groupoid need not be a homotopy pushout of free `E_2`-algebras.
- Extension route: `1 → K → bV → V → 1` with `V` acyclic (Szymik–Wahl). It
  suffices that `H_p(V; H_q(K)) = 0` for all `p ≥ 0`, `q ≥ 1`. The case
  `p = 0`, `q = 1` is done inside the perfectness proof. The next case is
  `H_1(V; C_c(Y, Z))`, with `Y` the unordered configuration space of two points
  of the Cantor set.
