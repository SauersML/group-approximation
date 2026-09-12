---
rg: 2
id: hard-soft-exponent-conflict-is-a-norm-mismatch
kind: claim
title: The hard-soft threshold exponent conflict is a norm mismatch
invalidates: [hard-soft-threshold-exponent-proof]
distinct_from:
  hard-soft-thresholds-cannot-enter-anchor-contraction: that compares an L2 row-amplitude remainder to squared energy and derives opposite exponent requirements; this corrects that comparison.
  one-anchor-grading-makes-parity-damage-quadratic: that proves the algebraic quadratic remainder; this performs the contraction bookkeeping at the correct norm level.
  central-adaptive-peeling-or-noncentral-stopping: that still has to manufacture operator-small blocks and sum their boundaries; this removes only the claimed scalar exponent obstruction.
---

ESTABLISHED.  Suppose the linearized anchor step contracts the normalized
row residual amplitude `r=sqrt(E)` by `theta<1`, and the nonlinear estimate
has the form

```text
 remainder_amplitude <=C t r.                            (HSN1)
```

Then

```text
 r' <=(theta+Ct)r.                                      (HSN2)
```

Strict contraction requires only `t<(1-theta)/C`.  It does **not** require
`t=o(r)`.  Meanwhile Markov hard reset has squared metric cost

```text
 hard_cost <=C_0 E/t^2.                                 (HSN3)
```

For any fixed sufficiently small `t`, `(HSN3)` vanishes with `E`.  One may
also take `t=E^alpha` for any `0<alpha<1/2`; then hard cost is
`O(E^(1-2alpha))->0` while the nonlinear contraction coefficient tends to
`theta`.

Thus `(HST3)` and the actual soft requirement are compatible.  The claimed
condition `(HST5)` arose by demanding the **amplitude** in `(HSN1)` be
`o(E)` instead of `o(sqrt(E))`, mixing two norm levels.  This refutes
`hard-soft-thresholds-cannot-enter-anchor-contraction` and reopens a
hard-tail/soft-anchor schedule.

This correction does not turn scalar tail bounds into operator bounds.
The remaining genuine problem is exactly
`central-adaptive-peeling-or-noncentral-stopping`: produce reducing blocks
on which the anchor-odd operator norm is at most `t`, with total boundary
and reset displacement tending to zero.
