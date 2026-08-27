---
rg: 2
id: adaptive-spike-quarantines-have-summable-trace
kind: claim
title: Adaptive clipping can assign every spike a summable global trace budget
distinct_from:
  small-trace-rank-one-quarantine: that cheaply refines one already isolated small-trace region; this chooses clipping thresholds throughout an arbitrary recursive tree so the union of all spike regions has prescribed small trace
  low-gap-witness-spike-or-balanced-cut: that produces one spike with relative trace at most the inverse square clipping threshold; this globally budgets all such outputs
---

Consider any finite or countable adaptive recursive cutting process.  At an
active corner `e_n`, numbered in the order it is encountered, apply
`low-gap-witness-spike-or-balanced-cut` with a clipping threshold `C_n`.
For every prescribed `eta>0`, the thresholds can be selected online so that
all spike projections `r_n<=e_n` are pairwise orthogonal and

```text
tau(sum_n r_n)<=eta.                                    (ASQ1)
```

Indeed choose

```text
C_n^2 >= 2^n tau(e_n)/eta.                              (ASQ2)
```

The spike alternative gives, in the normalized corner trace,

```text
tau(r_n)/tau(e_n)<=C_n^(-2),
```

and hence `tau(r_n)<=eta 2^(-n)`.  Remove every quarantine from all future
active corners.  The `r_n` are then orthogonal and summing proves `(ASQ1)`.
Combining with `small-trace-rank-one-quarantine` makes the total generator
boundary of all spike atoms `O(eta)`.

This completely removes spike trace accumulation as an obstruction.  It
does not solve the balanced-cut boundary: the coarea estimate worsens
linearly with `C_n`, so exponentially increasing thresholds cannot be
inserted into a uniform cut estimate without a separate pinching potential.

## Attempts

Using one fixed clipping threshold at every node only bounds the spike by a
fixed fraction of its parent and can quarantine total trace one along a long
branch.  The online summable allocation `(ASQ2)` fixes exactly that defect.
It deliberately makes no claim that the balanced alternatives obtained at
those thresholds have summable boundary.
