---
rg: 2
id: braid-arrangement-higher-resonance-varieties-computed
kind: claim
title: "The resonance varieties R^m of the braid arrangement are explicit unions of linear subspaces in every degree 2 <= m <= n-3"
artifacts:
  - research/artifacts/zp-pure-braid-bnsr-middle-range-2026-09-13.md
---

For every `n >= 5` and `2 <= m <= n - 3`, the degree-`m` resonance variety
`R^m(P_n) ⊆ H^1(P_n; C) = C^{binom(n,2)}` of the Orlik–Solomon algebra of the
braid arrangement is given by an explicit finite list of linear subspaces,
each described by equations in the coordinates `a_{ij}`.

Known: `R^1` is the union of the `binom(n,3) + binom(n,4)` planes of the KMM
circles (Cohen–Suciu 1999). `R^m` for `m >= n - 2` is the zero-sum hyperplane.
Propagation `R^1 ⊆ R^2 ⊆ ...` holds (Denham–Suciu–Yuzvinsky).

## Attempts

- Lower bound: by the retract argument, the zero-sum characters supported on
  disjoint blocks `A_1, ..., A_r` with `sum (|A_i| - 2) <= m` lie in `R^m`. So do
  their images under the `S_{n+1}`-symmetry of `M_{0,n+1}`, once that action on
  `H^1` is written down.
- Degree `n - 3`: pullbacks through the `n + 1` forgetful maps
  `M_{0,n+1} -> M_{0,n}` are resonant (fibre-type tensor decomposition of the
  Orlik–Solomon algebra). The reverse inclusion should follow from a
  nonresonance theorem (Yuzvinsky; Cohen–Dimca–Orlik) applied in every affine
  chart plus a combinatorial lemma. Not yet checked against the sources.
- Direct test planned: rank computations of the Aomoto complex of `A_4`
  (Betti numbers `1, 10, 35, 50, 24`) at sample characters, over `Q`.
