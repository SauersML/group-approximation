---
rg: 2
id: braid-arrangement-higher-resonance-varieties-computed
kind: claim
title: "The resonance varieties R^m of the braid arrangement are explicit unions of linear subspaces in every degree 2 <= m <= n-3"
artifacts:
  - research/artifacts/zp-pure-braid-bnsr-middle-range-2026-09-13.md
  - research/artifacts/zp-pure-braid-bnsr-pencils-2026-09-13.md
---

For every `n >= 5` and `2 <= m <= n - 3`, the degree-`m` resonance variety
`R^m(P_n) ⊆ H^1(P_n; C) = C^{binom(n,2)}` of the Orlik–Solomon algebra of the
braid arrangement is given by an explicit finite list of linear subspaces,
each described by equations in the coordinates `a_{ij}`.

Known: `R^1` is the union of the `binom(n,3) + binom(n,4)` planes of the KMM
circles (Cohen–Suciu 1999). `R^m` for `m >= n - 2` is the zero-sum hyperplane.
Propagation `R^1 ⊆ R^2 ⊆ ...` holds (Denham–Suciu–Yuzvinsky).

## Attempts

- Candidate formula (conjecture "pencil depth", artifact
  `zp-pure-braid-bnsr-pencils-2026-09-13.md`, Section 5). Use the symmetric
  coordinates on the `n+1` punctures, and let `L_U` be the pullback of
  `H^1(M_{0,U})`. For a family `F = (U_1, ..., U_r)` with `|U_i| >= 4`, let
  `depth(F)` be the minimum, over set partitions of `F`, of
  `sum_blocks (|∪ block| - 3)`. Then `R^{<=m}(H_n)` should be the union of the
  subspaces `L_{U_1} + ... + L_{U_r}` with `depth(F) <= m`.
- Evidence (random points mod `2^31 - 1`): `n = 5`, degrees <= 2, all 105 pairs
  and 455 triples of pencil planes, the six 5-point subspaces, 5-point plus
  plane, and combinatorial hyperplane sections up to codimension 3. `n = 6`,
  degrees <= 3: sunflower, pairs meeting in 2, a 5-point subspace plus a
  plane, three pairwise-meeting planes, the 6-point subspace. Every case
  matches depth exactly.
- Lower bounds proved: sunflower families
  (`pure-braid-sunflower-characters-obstruct-bnsr-invariants`, via the retract
  argument). Pairs meeting in two points:
  `braid-arrangement-pencils-meeting-in-two-points-are-resonant`, with an exact
  one-point certificate planned.
- Upper bound (no other components): not attempted beyond the sampled
  hyperplane sections. A nonresonance theorem in the style of Yuzvinsky or
  Cohen–Dimca–Orlik, applied in all charts, is the expected tool.
