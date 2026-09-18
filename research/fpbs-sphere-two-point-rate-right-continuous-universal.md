---
rg: 2
id: fpbs-sphere-two-point-rate-right-continuous-universal
kind: claim
title: The sphere two-point growth rate tends to zero as p decreases to p_c
distinct_from:
  fpbs-integrated-sensitivity-universal: that is right-continuity of the walk rate lambda at p_c; this is right-continuity of the extrinsic rate g(p)=limsup (1/r) log E_p|K_o ∩ S_r| at p_c with value 0, which implies it.
  fpbs-sphere-two-point-rate-below-arccosh-universal: that asks g(p) below arccosh(1/rho) at one p>p_c; this asks g(p)->0 and implies it.
artifacts:
  - research/artifacts/fpbs/docs/gauge-certificates-and-sphere-rate-2026-09-17.md
---

**OPEN (kernel EG).** For every nonamenable Cayley graph,
`g(p) = limsup_r (1/r) log E_p|K_o ∩ S_r|` tends to `0` as `p` decreases to
`p_c`.

**What it gives.** By `fpbs-sphere-two-point-rate-bounds-walk-rate`, EG implies
(IS) (route `fpbs-integrated-sensitivity-via-sphere-rate`), and hence (G) and
`p_c < p_u`.

**Two parts.**

- **(EG0)** `g(p_c) = 0`. The lower bound `g(p_c) >= 0` is established.
  `g(p_c) <= 0` would follow from Hutchcroft's critical bound
  `tau_{p_c}(o,x) <= gr^{-|x|}` (arXiv:1603.00555), which is not re-verified
  here.
- **(EG1)** Right-continuity at `p_c` of the nondecreasing function `g`.

It holds on regular trees, where `g(p) = log((d-1)p)`.

## Attempts

* **Fixed-radius continuity.** Each `M_r(p)` is continuous in `p`.
  **Where it dies:** `g` is an exponential rate, and continuity at fixed `r`
  says nothing about it. This is the same limit-order break as for `lambda` in
  Section 6.3 of `research/artifacts/fpbs/exploration-pivotal-projections.md`,
  moved from walk time to radius.
