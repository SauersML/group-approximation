---
rg: 2
id: npa-first-order-nullity-at-most-2k-plus-3
kind: claim
title: The compressed moment kernel has dimension at most two k plus three
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

For every `k >= 3`, `dim ker Phi_k <= 2k+3`; equivalently
`rank Phi_k >= rank Phi_(k-1) + 5k - 1` given the bound at `k-1`.

This is the half the triangular-shell induction is designed to deliver.  It
needs `5k-1` independent new rows at each level, produced as `5k-3` rows whose
leading terms are the non-exceptional new moment classes, plus `2` rows supported
entirely on old classes.

The independence of the two families from each other is not an extra hypothesis:
the two old-class rows have zero coefficient on every new class, while the
`5k-3` shell rows form a unit-triangular block on the new classes, so the only
combination of shell rows with vanishing new-class part is the trivial one.  What
is genuinely needed is that the two old-class rows survive modulo the level-`(k-1)`
row space, which is the separate claim
`npa-two-residual-rows-independent-mod-old-rows`.

## Attempts

The triangular-shell induction is written and is the leading attack; it is
recorded as the route `npa-nullity-upper-bound-via-triangular-shell`, and it
reduces the bound to two prerequisites, one combinatorial and one about the
old-class rows.  It is not a proof yet because the second prerequisite bottoms
out in `npa-unseen-classes-are-free-at-level-k`, which nothing in the chain
proves for general `k`.

The base case is `k = 3` with `dim ker Phi_3 = 9`, taken from computation rather
than from an argument, and inherited from the same `k <= 5` range as everything
else numerical here.

A different attack, not tried: bound `rank Phi_k` from below by exhibiting a
`(5k^2+3k-4)/2`-sized set of rows with a triangular structure over *all* classes
at once rather than shell by shell, which would avoid needing anything about
inheritance from level `k-1`.  This trades a small induction for a large
explicit ordering and may be no easier, but it is the natural way to dodge the
unseen-freeness lemma entirely.
