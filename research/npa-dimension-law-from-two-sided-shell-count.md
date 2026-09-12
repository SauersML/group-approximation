---
rg: 2
id: npa-dimension-law-from-two-sided-shell-count
kind: route
title: Squeeze the nullity between the shell induction and an explicit construction
target: npa-critical-face-first-order-dimension-law
requires:
  - npa-first-order-space-equals-moment-kernel
  - npa-first-order-nullity-at-most-2k-plus-3
  - npa-first-order-nullity-at-least-2k-plus-3
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

The first prerequisite replaces `dim V_k` by `dim ker Phi_k` with no loss, which
is what the other two bound.  Together they give

```text
2k+3  <=  dim ker Phi_k  <=  2k+3,
```

hence the dimension law, and hence by the rank-nullity dictionary the closed form
`rank Phi_k = (5k^2+3k-4)/2`.

The two halves are genuinely independent objects and neither is a restatement of
the target: the upper bound is an induction that must *exhibit enough rows*, the
lower bound must *exhibit enough kernel vectors*, and the current state of the
region is that the first is one lemma short while the second has no construction
in hand at all.
