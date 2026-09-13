---
rg: 2
id: every-f-infinity-group-has-a-non-proper-bnsr-inclusion
kind: claim
title: "Every group G of type F_infinity has some m >= 1 with Sigma^m(G) = Sigma^{m+1}(G)"
distinct_from:
  f-infinity-group-with-properly-nested-bnsr-invariants: that claim asserts one F_infinity group whose chain of BNSR invariants drops at every degree; this is its negation, a universal statement that some inclusion is an equality
  zaremsky-1-18-properly-nested-bnsr-invariants: that claim is Problem 1.18 as a question; this is the negative answer
artifacts:
  - research/artifacts/zp-properly-nested-bnsr-2026-09-13-part1.md
---

For every group `G` of type `F_∞` there is `m ≥ 1` with
`Σ^m(G) = Σ^{m+1}(G)`.

This is weaker than eventual constancy, since a chain may pause and then drop
again. Route `every-f-infinity-group-non-proper-bnsr-by-type-f-dichotomy`
splits it into the established type-F case and the open case of `F_∞` groups
with no finite classifying space.

## Attempts

- **Type F.** Established (`type-f-bnsr-invariants-stabilize-at-dimension`).
- **Bieri Σ-property.** Established: the chain is constant from `rank G^{ab}`
  (`bieri-sigma-property-forces-bnsr-constant-from-rank`). Houghton groups, `F`
  and `F_{2,3}` are covered.
- **No uniform mechanism.** The bound "chain length at most `rank G^{ab}`" is
  false in general, although it holds under the Σ-property: products of
  cyclically permuted powers of `F_2` give length `2^k − 1` at rank `3k`
  (artifact §4). A proof would need an invariant, controlled by `F_∞` alone,
  that bounds the number of distinct complements `S(G) \ Σ^m(G)` for groups of
  infinite cohomological dimension. None is known to this lane.
