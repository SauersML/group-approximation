---
rg: 2
id: non-type-f-f-infinity-groups-have-a-non-proper-bnsr-inclusion
kind: claim
title: "Every group G of type F_infinity that is not of type F has some m >= 1 with Sigma^m(G) = Sigma^{m+1}(G)"
distinct_from:
  every-f-infinity-group-has-a-non-proper-bnsr-inclusion: that claim quantifies over all groups of type F_infinity; this is the part not covered by type-f-bnsr-invariants-stabilize-at-dimension, the F_infinity groups with no finite classifying space
---

For every group `G` of type `F_∞` with no finite classifying space there is
`m ≥ 1` with `Σ^m(G) = Σ^{m+1}(G)`.

Together with `type-f-bnsr-invariants-stabilize-at-dimension`, this is
equivalent to the negative answer to Zaremsky Problem 1.18.

## Attempts

- **Proper cocompact finite-dimensional models.** Established: if `G` acts
  properly and cocompactly on a contractible `d`-dimensional complex, the chain
  is constant from `d` (`cocompact-contractible-d-complex-bnsr-stabilize-at-d`).
  So the open part concerns `F_∞` groups with no such action, for example
  every torsion-free group of infinite cohomological dimension.
- **Finite cohomological dimension.** Groups of type `F_∞` with finite `cd`
  but not of type F would be exotic; whether they exist is Zaremsky Problem
  1.21. For them the argument of Proposition 1 in
  `research/artifacts/zp-properly-nested-bnsr-2026-09-13-part1.md` gives
  `Σ^m(G) = Σ^{max(2,cd G)}(G)` for `m ≥ max(2, cd G)`. It uses two imports
  not yet verified from sources: the Novikov-homology criterion for `Σ^m(G;Z)`
  and the Bieri–Renz comparison `Σ^m = Σ^2 ∩ Σ^m(G;Z)`.
- **Infinite cohomological dimension: the real content.** Every such group with
  computed invariants stops at level 2: Thompson's `F` (Witzel–Zaremsky,
  arXiv:1501.06682, Theorem A), `F_{n,∞}` (Zaremsky, arXiv:1502.02620,
  Theorem A), the Stein group `F_{2,3}` (Spahn–Zaremsky, arXiv:2012.05000,
  Theorem 3.9), and the Lodha–Moore groups (Lodha–Zaremsky, arXiv:2007.12518).
  For `F` and `F_{2,3}` the printed descriptions show the Bieri Σ-property
  with two classes in `S \ Σ^1`, and
  `bieri-sigma-property-forces-bnsr-constant-from-rank` explains why they
  stop. The shapes of `Σ^1` for `F_{n,∞}` and for the Lodha–Moore groups were
  not checked here. A proof for all infinite-dimensional groups would need a bound
  on the number of distinct complements `S \ Σ^m` from the `F_∞` property
  alone. None is known to this lane.
