---
rg: 2
id: sp4-winding-deficit-from-one-scale
kind: route
title: A winding deficit at one defect scale propagates to every smaller scale by tensor superadditivity
target: sp4-quasirep-winding-ratio-has-a-deficit
requires:
  - sp4-quasirep-single-scale-winding-deficit
  - sp4-winding-ratio-is-an-infimum-over-scales
---

Let `r`, `W`, `eps_1` and `c < tau_W` be as in `sp4-quasirep-single-scale-winding-deficit`, so that
`S_W(eps_1) <= c eps_1`.

By item 2 of `sp4-winding-ratio-is-an-infimum-over-scales`,

```text
Theta(W) = limsup_{eps->0+} S_W(eps)/eps = inf_{0 < eps <= a_g} S_W(eps)/eps <= S_W(eps_1)/eps_1 <= c < tau_W.
```

Since `tau_W = |k|/(2 pi beta*_W)`, this is the inequality `Theta(W) < |k|/(2 pi beta*_W)` of
`sp4-quasirep-winding-ratio-has-a-deficit` on the window `W`.
