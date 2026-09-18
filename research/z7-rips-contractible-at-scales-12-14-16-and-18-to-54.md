---
rg: 2
id: z7-rips-contractible-at-scales-12-14-16-and-18-to-54
kind: claim
title: The Rips complex of Z^7 in the l^1 metric is contractible at r = 12, 14, 16 and at every scale 18 ≤ r ≤ 54
distinct_from:
  z7-rips-contractible-at-scales-20-to-54-even-and-36-to-54: that covers only the scales with no unbalanced partition (even 20..34 and 36..54); this adds r = 12, 14, 16, 18, 19 and the odd scales 21..35, where unbalanced 7-part partitions exist, using the slack-one extension
  z7-rips-contractible-at-scales-7-and-8: that covers r = 7, 8 by a per-scale certificate on Lmax; this covers r = 12, 14, 16 and 18..54 by a check on partitions of r
  z7-rips-contractible-at-scale-9: that covers r = 9 by a per-scale certificate; this covers r = 12, 14, 16 and 18..54
---

`VR(Z^7, d_1; r)` is contractible for `r ∈ {12, 14, 16}` and for every `r` with `18 ≤ r ≤ 54`. A finite set spans
a simplex iff its `l^1` diameter is at most `r`.

Context. Zaremsky's conjecture says `VR(Z^n, d_1; r)` is contractible for all `r ≥ n`. For `n = 7`, the other
covered scales are:
- `r = 7, 8, 9`, by per-scale certificates;
- `r ≥ n(n+1) − 1 = 55`, Zaremsky's published bound.

With those, `n = 7` is settled at every `r ≥ 18` and at `r = 7, 8, 9, 12, 14, 16`. The scales still open are
`r = 10, 11, 13, 15, 17`. At each of them some unbalanced partition of `r` has six parts, so the slack-one criterion
does not apply.

Proof: route `z7-rips-contractible-at-scales-12-14-16-and-18-to-54-proof`. It applies `zn-rips-slack-sphere-criterion`
after an exhaustive computation on the partitions of `r` into at most 7 parts.
