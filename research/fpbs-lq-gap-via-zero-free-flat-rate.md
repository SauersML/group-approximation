---
rg: 2
id: fpbs-lq-gap-via-zero-free-flat-rate
kind: route
title: Turn a zero-free flat rate past p_c into l2 summability past p_c through the flat-rate point
target: fpbs-two-point-lq-threshold-gap-universal
requires:
  - fpbs-connectivity-polynomials-zero-free-around-criticality
  - fpbs-zero-free-connectivity-gives-flat-rate
  - fpbs-flat-rate-point-equals-l2-point
artifacts:
  - research/artifacts/fpbs-zg-ladder-calibration-2026-09-17.md
---

**The route.**

1. (ZG) together with conclusion (a) of
   `fpbs-zero-free-connectivity-gives-flat-rate` gives `lambda = rho` on an
   interval `I_+` in `(p_c, 1)`.
2. Hence `p_* > p_c`.
3. By `fpbs-flat-rate-point-equals-l2-point`, `p_2 = p_* > p_c`.
4. So some `p > p_c` has `tau_p` in `l^2`. Since `tau_p <= 1`, the function
   `tau_p` is then in `l^q` for every `q >= 2`, which is [Q].

**Purpose.** This route records a transfer of strength, not an easier path. If
the flat-rate point equals the l2 point, the zero-free route proves the l2 gap
`p_c < p_2`. That is strictly more than [Q] needs, since [Q] asks only for
`q > 2`. So (ZG) is at least as hard as the l2 statement. The calibration
artifact finds the zero set of `a_n` pinching the real axis exactly at `p_2`
on every computed graph, which is consistent with this.
