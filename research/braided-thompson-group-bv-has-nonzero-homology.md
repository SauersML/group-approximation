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
- A nonzero class must be torsion, because `bV` is rationally acyclic
  (`braided-thompson-group-bv-is-rationally-acyclic`, unreviewed).
- Where torsion could come from: nonzero `H_p(V; C(C^j, Z))` for some `j ≥ 1`,
  i.e. failure of `cantor-power-function-modules-are-v-acyclic`, most plausibly
  2-torsion. A counterexample would have to exhibit it, for instance through a
  nonvanishing differential in the Lyndon–Hochschild–Serre spectral sequence of
  the acyclic labelled Thompson group `C(C, Z^j) ⋊ V`.
- Bounded cohomology gives no obstruction to acyclicity, so the quasimorphisms
  of Fournier-Facio–Lodha–Zaremsky (arXiv:2204.05272) do not give a nonzero
  class.
