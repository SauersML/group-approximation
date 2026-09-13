---
rg: 2
id: braided-thompson-group-bv-has-nonzero-homology
kind: claim
title: Some integral homology group H_k(bV; Z) with k >= 1 of the braided Thompson group bV is nonzero
---

There is `k ≥ 1` with `H_k(bV; Z) ≠ 0`, where `bV` is the Brin–Dehornoy
braided Thompson group. This is the negative answer to Zaremsky Problem 2.9
(`zaremsky-2-09-braided-v-acyclic`); it is the negation of
`braided-thompson-group-bv-is-acyclic`.

## Attempts

- `k = 1` is impossible: `bV` is perfect (`braided-thompson-group-bv-is-perfect`).
- The first open case is `k = 2`. From the extension `K → bV → V` and
  `H_*(V) = 0`: `H_2(bV) = 0` iff `H_1(V; H_1(K)) = 0` and `H_2(K)_V` is
  killed by the differential from `H_2(V; H_1(K))`. A nonzero class would have
  to come from one of these two terms.
- Bounded cohomology gives no obstruction to acyclicity, so the quasimorphisms
  of Fournier-Facio–Lodha–Zaremsky (arXiv:2204.05272) do not give a nonzero
  class here.
