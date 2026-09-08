---
rg: 2
id: order-two-universal-non-mf-at-ranks-two-and-three
kind: claim
title: Decide whether the universal order-two elementary group is non-MF in ranks two and three
distinct_from:
  order-two-defect-question-reduces-to-one-universal-ring: that is the proved equivalence between the class question and this one ring; this is the analytic endpoint of that reduction, which the reduction does not decide.
  finite-additive-order-one-sided-defects-are-mf-invisible: that establishes the same conclusion for every finite additive order at every rank at least four; this is exactly the residue at ranks two and three, where that route's Kazhdan compression cell is unavailable.
  property-t-free-jacobson-head-collapse: that asks for a property-(T)-free proof of an already established rank-five statement over the binary Jacobson ring; this asks for any proof at all, at ranks two and three, over the integral universal order-two ring.
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

For `A_2 = Z<S,T | TS = 1, 2Q = 0>`, `Q = 1 - ST`, and `n in {2,3}`,
decide whether

```text
EL_n(A_2) is non-MF,                                              (OTL1)
```

equivalently (by `order-two-defect-question-reduces-to-one-universal-ring`)
whether every homomorphism from `EL_n(A_2)` to an MF group kills
`e_12(Q)`.

**Why the two low ranks and no others.**  For `n >= 4`,
`finite-additive-order-one-sided-defects-are-mf-invisible` already gives
the affirmative answer, `A_2` being the ring called `R_q` at `q = 2` in
its route.  The gap is genuinely at `n = 2,3`.

## Attempts

**Rank descent from the established rank-four answer.**  The obvious
attack is `elementary-rank-descent-to-two`, which compresses a higher
rank into rank two and identifies the image as a normal generator.  It
dies immediately: that descent needs a properly infinite unit, and
`order-two-universal-ring-has-no-infinite-corner` proves `A_2` has no
nonzero properly infinite idempotent, in any finite matrix
amplification.  So there is no corner to compress into and no matrix-ring
self-similarity to exploit.

**The fullness-free corner certificate.**  Recorded as the dead route
`order-two-low-rank-via-properly-infinite-corner`, killed by the same
nonexistence statement.

**Rerunning the Kazhdan transport at low rank.**  The rank-four proof
places the head in a compression cell built from property (T) of
`E_3(R_2)` (Ershov--Jaikin-Zapirain) acting inside `E_4(R_2)`.  At
`n = 3` the Kazhdan subgroup would have to be `E_2`, which has no
property (T) over these rings, and at `n = 2` there is no room for the
compression cell at all.  The structural inputs do survive the descent —
`order-two-universal-ring-has-finitary-symbol-sequence` gives the exact
symbol sequence with simple finitary kernel already at `n = 2`, and
`two-outer-rows-suffice-for-finitary-transvections` supplies the
generation — so what is missing is precisely an analytic collapse
mechanism that does not need a Kazhdan subgroup two ranks below.

**Transport from the binary Jacobson ring.**  Blocked in the useful
direction.  `binary-jacobson-mf-implies-order-two-universal-mf` runs from
`J_(F_2)` to `A_2`, so it would need MF of the Jacobson group, not
non-MF; and the reverse has no ring embedding, by the no-go recorded in
the same node.
