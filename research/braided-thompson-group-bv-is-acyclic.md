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
- Rationally it holds in every degree: `braided-thompson-group-bv-is-rationally-acyclic`
  (unreviewed).
- Reduction route `braided-thompson-group-bv-is-acyclic-from-cantor-modules`: the
  integral statement follows from `cantor-power-function-modules-are-v-acyclic`
  (`C(C^j, Z)` is V-acyclic for all `j ≥ 1`) and Szymik–Wahl. Every other step of
  the rational proof is integral.
- Szymik–Wahl route (open): homological stability for the braided
  Higman–Thompson family in all degrees, plus contractibility of the `E_2` group
  completion of the braided monoidal groupoid of `bV`. Heuristic model: the
  reduced homotopy coequalizer of the degree-1 and degree-2 self-maps of `S^2`,
  which is contractible. The same heuristic in the `E_1` setting would wrongly
  predict that `F` is acyclic (`H_1(F) = Z^2`), so it needs stability to mean
  anything.
