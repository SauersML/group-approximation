---
rg: 2
id: every-f-infinity-group-has-a-non-proper-bnsr-inclusion
kind: claim
title: "Every group G of type F_infinity has some m >= 1 with Sigma^m(G) = Sigma^{m+1}(G)"
distinct_from:
  f-infinity-group-with-properly-nested-bnsr-invariants: that claim asserts one F_infinity group whose chain of BNSR invariants drops at every degree; this is its negation, a universal statement that some inclusion is an equality
  zaremsky-1-18-properly-nested-bnsr-invariants: that claim is Problem 1.18 as a question; this is the negative answer
---

For every group `G` of type `F_∞` there is `m ≥ 1` with
`Σ^m(G) = Σ^{m+1}(G)`.

This is weaker than "the chain is eventually constant": a chain may be equal at
one degree and drop again later.

## Attempts

- **Finite cohomological dimension (argument written, imports to verify).** If
  `cd G = d < ∞`, then `Σ^m(G) = Σ^{max(2,d)}(G)` for all `m ≥ max(2,d)`; see
  the first Attempts item of
  `f-infinity-group-with-properly-nested-bnsr-invariants`. So the claim holds
  for every `F_∞` group of finite cohomological dimension. The open case is
  infinite cohomological dimension.
- **No uniform mechanism found.** The obvious candidate bound, chain length at
  most `rank G^{ab}`, is false: products of cyclically permuted powers of `F_2`
  give chain length `2^k − 1` at rank `3k` (same node, calibration item). A
  proof of the negative answer would need an invariant, controlled by the
  `F_∞` property alone, that bounds the number of distinct complements
  `S(G) \ Σ^m(G)`. None is known to this lane.
