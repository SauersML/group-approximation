---
rg: 2
id: y-square-coarea-window-proof
kind: route
title: Substitute an energy power into the exact Y-squared coarea estimates
target: y-square-coarea-has-a-compatible-hard-soft-window
requires:
  - one-anchor-odd-spike-has-a-cheap-reducing-cut
  - hard-soft-exponent-conflict-is-a-norm-mismatch
---

Equations `(OSC2)`, `(OSC3)`, and `(OSC5)` give respectively

```text
tau(p)<=||[Q_a,Q_i]||_2^2/(4s),
boundary<=2(q_i+q_a)/s,
||Y_(a,i)||_infty<=sqrt(2s)
```

on the retained block.  Insert `(YSC1)` and `s=E^beta` to obtain
`(YSC3)`.  The inequalities `beta<1`, `beta<1/2`, and `beta>0` make its
three exponents positive; the strongest condition is exactly
`0<beta<1/2`.

The quadratic remainder estimates are norm estimates, so its contribution
is `C sqrt(s)sqrt(E)`, not an energy term to compare with `E`.  Adding it
to a linearly contracted amplitude proves `(YSC4)`.  This calculation is
per cut and contains no claim that overlapping boundaries are summable.

