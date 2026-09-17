---
rg: 2
id: co-sofic-irs-carry-no-strict-design-proof
kind: route
title: Count image patterns on a finite Schreier graph with forward-bad and reverse-bad sites and pass to the limit
target: co-sofic-irs-carry-no-strict-design
requires: []
artifacts:
  - research/artifacts/irs-surjunctivity-heretic-2026-09-17.md
---

Complete direct proof: artifact Section 4. Take a finite `F_r`-set `X` with `|X| = N`, forward-bad
fraction `eps`, reverse-bad fraction `delta`, and forward-good set `G`.

1. **Lower bound.** `x|G = (sigma tau x)|G` is read from `tau x`, and `y -> (sigma y)|G` is onto
   `A^G`. So `|tau(A^X)| >= |A|^((1-eps)N)`.
2. **Excluded patterns.** Let `v` be reverse-bad with witness `p_v`, and suppose
   `B_(R_tau)(v) ⊆ G`. Then `y = tau x` has `sigma y = x` on `B_(R_tau)(v)`, so
   `tau sigma y(v) = y(v)` and `y|B_r(v) != p_v`. At most `eps N d_(R_tau)` reverse-bad vertices fail
   the hypothesis.
3. **Separation.** A greedy `2r`-separated subset `D'` has at least
   `(delta - eps d_(R_tau)) N / d_(2r)` elements, and its `r`-balls are disjoint. Hence
   `|tau(A^X)| <= |A|^N (1 - |A|^(-d_r))^|D'|`.
4. **Combine.** `ln(1-u) <= -u` gives `|D'| <= eps N |A|^(d_r) ln|A|`, and so
   `delta <= (d_(R_tau) + d_(2r)|A|^(d_r) ln|A|) eps`.
5. **Limit.** Forward-bad and reverse-bad are clopen shape events, so `eps_D` and `delta_D` are
   continuous and affine in `mu`. The inequality holds on the closed convex hull of the finite-set IRS,
   which contains every co-sofic IRS.
