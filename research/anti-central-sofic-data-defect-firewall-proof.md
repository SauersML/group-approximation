---
rg: 2
id: anti-central-sofic-data-defect-firewall-proof
kind: route
title: Compute anti-central regular defect ranks in the Heisenberg group algebra over F_3 and realize them on sofic subgroups and locally finite HNN data
target: anti-central-sofic-data-cannot-force-defect-submultiplicativity
requires:
  - level-unit-hnn-extensions-have-anti-central-rank-models
artifacts:
  - research/artifacts/char-three-anti-central-defect-firewall-2026-09-12.md
---

Artifact Sections 1 and 2.

1. **Consistency and invariance** (Lemma 1.2). `F_3[K'] eps_-` is free over `F_3[K] eps_-` for `K <= K'` both
   containing `z`, and conjugation by a unit is an algebra isomorphism fixing `eps_-`.
2. **Frames** (Proposition 1.3(a)). `iota_A(x_12(1))`, `iota_A(x_23(1))` generate `UT_3(F_3)` of order `27`.
   Disjoint cylinder groups commute and meet trivially, and the product is a `3`-group avoiding `z`.
3. **The count** (Proposition 1.3(c)). With `e_(i,j,k) = x^i y^j c^k`, `rank(YX) = 18 - dim(ker X^2 cap ker Y)`.
   The fixed vectors of `L_y` are orbit sums `f_(i,w)`, and `X^2 f_(i,w)` is the indicator of `d + ib = w`. The
   kernel condition `sum_i p_i(d + ib) = 0` has a 3-dimensional solution space. So `rank(YX) = 15` and
   `rk^-(D_A) = 5/9`. Calibration: the same count gives `3/8` over `F_2[D_8]`.
4. **Products** (Proposition 1.3(d)). The `eps_-`-part of the regular module of `H_1 x ... x H_k x <z>` is the
   tensor product of the regular modules, so ranks multiply to `(5/9)^k`.
5. **Locally finite HNN data** (Theorem 2.1). The twisted regular tower over an exhaustion by finite subgroups
   containing `z`, with exact intertwiners between free modules of equal rank. Anti-central models have no fixed
   vectors because `-b = b` forces `b = 0` in characteristic three.
6. **Sofic subgroups** (Theorem 2.2). Linearize a sofic approximation over `F_3` and compress by
   `f = 2(1 - tau(z))`; asymptotic freeness on finite subgroups gives the profile.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 22.1 (Heisenberg kernel count re-derived) of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
