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

* **Pointwise critical gr-decay for EG0 (swarm-0917 w12, minimal-counterexample).**
  The EG0 bullet above derives `g(p_c) <= 0` from `tau_(p_c)(o,x) <= gr^(-|x|)`.
  **Where it dies:** that bound is false. By
  `fpbs-pointwise-critical-growth-decay-fails`, on `T_3 □ T_10`,
  `F_2 x F_6` and `Z x F_3` with standard generators, edge-disjoint diagonal
  two-path blocks at `p0 = 1/(D-1) <= p_c` give
  `tau_(p_c)(o,z_k) gr^(2k) >= R^k`, with `R = 287/256`, `54329/50625` and
  `2425/2401` respectively. Even `C gr^(-(1-eps)|x|)` fails, for `eps < 0.026`
  on `T_3 □ T_10`. Hutchcroft's theorem (arXiv:1605.05301) is about the
  infimum `kappa_(p_c)` only, so no citation repairs EG0. Any route through
  `|S_r| · sup_(S_r) tau_(p_c)` dies at the same step.
* **EG0 through distance types (swarm-0917 w12).** This proves EG0 on
  products of regular trees, including exactly the graphs above: see
  `fpbs-critical-sphere-rate-vanishes-on-tree-products`. There
  `g = sup_v h_v`, where each `h_v` is a lower semicontinuous function of
  `p` for one distance type `v`. So `g` is left-continuous, and `g <= 0` below
  `p_c` by sharpness. This splits universal EG0 into two prerequisites, each of
  which can fail:
  - **(T1)** each sphere `S_r` is covered by `e^(o(r))` classes, and on each
    class the sum of `tau_p` is comparable, up to `e^(o(r))`, to a single
    function of `p` that is lower semicontinuous;
  - **(T2)** those class functions are supermultiplicative under geodesic
    concatenation of classes.

  **Where it stops:** (T1) and (T2) use the product structure, in Steps 0–1
  of the proof. On a general Cayley graph, `x in S_r` and `w in S_s` with
  `|xw| = r+s` carry no a priori fraction of `M_r M_s`. The number of
  factorizations of `z in S_(r+s)` can be exponential. This is open for
  hyperbolic groups too, where cone types are a candidate for (T1). EG1 is
  untouched, since a supremum gives only left-continuity.
