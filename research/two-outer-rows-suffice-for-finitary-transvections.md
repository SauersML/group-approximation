---
rg: 2
id: two-outer-rows-suffice-for-finitary-transvections
kind: claim
title: Two outer matrix rows already produce every within-ray finitary transvection
distinct_from:
  binary-jacobson-elementary-mark-is-finite-quotient-invisible: that identifies the finitary kernel in rank five, obtaining within-ray transvections through a third outer coordinate; this removes the third row and so extends the same identification to rank two.
  binary-finitary-transvection-uniformly-controls-active-rank: that bounds the active rank of a representation by the rank of one transvection image; this is a generation identity inside the group and says nothing about representations.
  rank-four-jacobson-head-retention-is-faithful: that runs the self-centralizing-kernel argument in rank four, again using a third matrix coordinate; this supplies the identity that makes rank two enough.
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

**ESTABLISHED.**  Let `A` be a unital ring with `ts = 1`, `Q = 1 - st`, and
`Q_(ij) = s^i Q t^j` the resulting matrix units, so that
`Q_(ij)Q_(kl) = delta_(jk)Q_(il)`.  For any `n >= 2`, distinct outer
indices `i != j`, distinct inner indices `a != b` and any inner index `c`,

```text
[I + Q_(ac)E_ij,  I + Q_(cb)E_ji] = I + Q_(ab)E_ii.               (TOR1)
```

Consequently the elementary group `EL_n(A)` contains **every** finitary
transvection of the coefficient module, within a single outer ray as well
as across two of them, already at `n = 2`.  Over `F_2` these transvections
generate the whole finitary invertible group

```text
L_n = GL_fin(N x {1,...,n}, F_2),                                 (TOR2)
```
because finite Gaussian elimination uses only row additions and row
swaps, a swap is a product of three row additions in characteristic two,
and every nonzero pivot over `F_2` is `1`.

The point is the absence of a third outer row.  The published
identifications of the Jacobson finitary kernel obtain within-ray
transvections by commuting through a third matrix coordinate, which needs
`n >= 3`; `(TOR1)` uses only the two rows `i,j` and moves the third index
inside the coefficient ring.

DERIVATION
two-outer-row-transvection-proof
